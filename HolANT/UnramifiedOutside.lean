/- ========================================================================= -/
/- ANT: Extensions of number fields unramified outside a set of primes     -/
/- ========================================================================= -/
/- File: HolANT/UnramifiedOutside.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/unramified_outside.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antunramifiedoutsidediff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/ideal_norm.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/prime_split.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/decomposition.ml, ANT/nf_valuation.ml, ANT/relative_degree.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/splitting_types.ml, ANT/nf_decomposition.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.UnramifiedOutside fills them).

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
import HolANT.Integral
import HolANT.IdealArith
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
import HolANT.Classgroup
import HolANT.PrimeSplit
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolANT.Decomposition
import HolANT.NfValuation
import HolANT.RelativeDegree
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.SplittingTypes
import HolANT.NfDecomposition

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
open HolANT.DedekindStruct
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.IdealNorm
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.Classgroup
open HolANT.PrimeSplit
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.Decomposition
open HolANT.NfValuation
open HolANT.RelativeDegree
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.SplittingTypes
open HolANT.NfDecomposition

namespace HolANT.UnramifiedOutside

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION ALGEBRAIC_IMP_FIELD_EXTENSION
   CARRIER_SUBFIELD_GENERATED_SUBFIELD DECOMPOSITION_GROUP_RING_OF_INTEGERS
   EMPTY_SUBSET EQ_SYM_EQ EXTENSION FIELD_SUBFIELD_GENERATED
   FINITE_EXTENSION_ISOMORPHISM FINITE_EXTENSION_SUBFIELD_GENERATED
   FINITE_EXTENSION_SUBFIELD_GENERATORS FINITE_IMP_FIELD_EXTENSION
   FINITE_INDUCT_STRONG FORALL_IN_IMAGE FUN_EQ_THM GALOIS_EXTENSION_COMPOSITUM
   GALOIS_EXTENSION_ISOMORPHISM GALOIS_EXTENSION_UNION_FINITE_GALOIS_SUBFIELDS
   GALOIS_GROUP GALOIS_GROUP_EQ_ON_GENERATORS GALOIS_GROUP_I
   GALOIS_GROUP_PERMUTES GALOIS_GROUP_RESTRICTION_NORMAL
   GALOIS_IMP_NORMAL_EXTENSION GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET GROUP_ID
   IMAGE_EQ IMAGE_I IMAGE_INTER_INJ IMP_CONJ INERTIA_GROUP INSERT_SUBSET
   IN_ELIM_THM IN_FINITE_GALOIS_SUBFIELDS IN_INTER IN_SING IN_UNION IN_UNIONS
   I_O_ID I_THM MEMBER_NOT_EMPTY MONO_EXISTS MULT_EQ_1 NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_PRIME_IDEALS_ABOVE NUMBER_FIELD_PRIME_IDEAL_ABOVE
   NUMBER_FIELD_RAMIFICATION_INDEX_TOWER
   NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED
   NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP PERFECT_FIELD_CHAR_0
   PERFECT_FIELD_IMP_SEPARABLE_EXTENSION PERMUTES_INJECTIVE
   PRIME_IDEAL_HOMOMORPHIC_PREIMAGE PRIME_IDEAL_IMP_SUBSET PRIME_IMP_RING_IDEAL
   PRIME_SUBFIELD_TOWER_LAW RING_HOMOMORPHISM_RING_OF_INTEGERS
   RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE RING_MONOMORPHISM_IMP_HOMOMORPHISM
   RING_OF_INTEGERS_SUBFIELD_GENERATED RING_OF_INTEGERS_SUBRING
   RING_OF_INTEGERS_SUBSET RING_SUB RING_SUB_SUBFIELD_GENERATED
   SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED SUBFIELD_GENERATED_IDEMPOT_GEN
   SUBFIELD_GENERATED_INC SUBFIELD_GENERATED_MINIMAL SUBFIELD_OF_IMP_SUBSET
   SUBFIELD_OF_SUBFIELD_GENERATED_SUBFIELD_EQ SUBFIELD_OF_UNIONS_DIRECTED
   SUBFIELD_SUBFIELD_GENERATED SUBGROUP_GENERATED SUBSET SUBSET_REFL
   SUBSET_TRANS TRIVIAL_GALOIS_GROUP TRIVIAL_GROUP_SUBGROUP_GENERATED
   UNION_SUBSET UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED field_extension
   galois_extension group_homomorphism inertia_group number_field
   ring_homomorphism trivial_group weakly_unramified : thm)
  deriving Inhabited

/-- What unramified_outside.ml uses from Session besides theorems. -/
structure UnramifiedOutsideDeps where
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
/- unramified_outside.ml phrases from line 61 to 591                      -/
/- ---------------------------------------------------------------------- -/

structure UnramifiedOutside where
  -- @@FIELDS
  FINITE_SUBEXTENSION_NUMBER_FIELD : thm
  unramified_outside : thm
  UNRAMIFIED_OUTSIDE_BASE : thm
  UNRAMIFIED_OUTSIDE_SUBFIELD : thm
  INERTIA_GROUP_UNRAMIFIED_SUBFIELD : thm
  UNRAMIFIED_OUTSIDE_COMPOSITUM : thm
  maximal_unramified_outside : thm
  MAXIMAL_UNRAMIFIED_OUTSIDE_FINITE_SUBSET : thm
  MAXIMAL_UNRAMIFIED_OUTSIDE : thm
  MAXIMAL_UNRAMIFIED_OUTSIDE_SUBEXTENSION : thm
  MAXIMAL_UNRAMIFIED_OUTSIDE_FINITE_GALOIS : thm
  GALOIS_MAXIMAL_UNRAMIFIED_OUTSIDE : thm
  NUMBER_FIELD_ALGEBRAIC_CLOSURE_GALOIS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupUnramifiedOutside [HolBase] (D : UnramifiedOutsideDeps) :
    ExceptT String IO UnramifiedOutside := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, TAUT, new_definition, .. } := D
  let { ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION, ALGEBRAIC_IMP_FIELD_EXTENSION,
        CARRIER_SUBFIELD_GENERATED_SUBFIELD, DECOMPOSITION_GROUP_RING_OF_INTEGERS,
        EMPTY_SUBSET, EQ_SYM_EQ, EXTENSION, FIELD_SUBFIELD_GENERATED,
        FINITE_EXTENSION_ISOMORPHISM, FINITE_EXTENSION_SUBFIELD_GENERATED,
        FINITE_EXTENSION_SUBFIELD_GENERATORS, FINITE_IMP_FIELD_EXTENSION,
        FINITE_INDUCT_STRONG, FORALL_IN_IMAGE, FUN_EQ_THM, GALOIS_EXTENSION_COMPOSITUM,
        GALOIS_EXTENSION_ISOMORPHISM, GALOIS_EXTENSION_UNION_FINITE_GALOIS_SUBFIELDS,
        GALOIS_GROUP, GALOIS_GROUP_EQ_ON_GENERATORS, GALOIS_GROUP_I,
        GALOIS_GROUP_PERMUTES, GALOIS_GROUP_RESTRICTION_NORMAL,
        GALOIS_IMP_NORMAL_EXTENSION, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET, GROUP_ID,
        IMAGE_EQ, IMAGE_I, IMAGE_INTER_INJ, IMP_CONJ, INERTIA_GROUP, INSERT_SUBSET,
        IN_ELIM_THM, IN_FINITE_GALOIS_SUBFIELDS, IN_INTER, IN_SING, IN_UNION,
        IN_UNIONS, I_O_ID, I_THM, MEMBER_NOT_EMPTY, MONO_EXISTS, MULT_EQ_1,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_PRIME_IDEALS_ABOVE,
        NUMBER_FIELD_PRIME_IDEAL_ABOVE, NUMBER_FIELD_RAMIFICATION_INDEX_TOWER,
        NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED,
        NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP, PERFECT_FIELD_CHAR_0,
        PERFECT_FIELD_IMP_SEPARABLE_EXTENSION, PERMUTES_INJECTIVE,
        PRIME_IDEAL_HOMOMORPHIC_PREIMAGE, PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_RING_IDEAL,
        PRIME_SUBFIELD_TOWER_LAW, RING_HOMOMORPHISM_RING_OF_INTEGERS,
        RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
        RING_OF_INTEGERS_SUBFIELD_GENERATED, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, RING_SUB, RING_SUB_SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED, SUBFIELD_GENERATED_IDEMPOT_GEN,
        SUBFIELD_GENERATED_INC, SUBFIELD_GENERATED_MINIMAL, SUBFIELD_OF_IMP_SUBSET,
        SUBFIELD_OF_SUBFIELD_GENERATED_SUBFIELD_EQ, SUBFIELD_OF_UNIONS_DIRECTED,
        SUBFIELD_SUBFIELD_GENERATED, SUBGROUP_GENERATED, SUBSET, SUBSET_REFL,
        SUBSET_TRANS, TRIVIAL_GALOIS_GROUP, TRIVIAL_GROUP_SUBGROUP_GENERATED,
        UNION_SUBSET, UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED, field_extension,
        galois_extension, group_homomorphism, inertia_group, number_field,
        ring_homomorphism, trivial_group, weakly_unramified, .. } := D.core1
  -- @@SCOPE END

  let FINITE_SUBEXTENSION_NUMBER_FIELD ← prove
    r"!(h:A->B) k l e.
        number_field k /\ field l /\ e subfield_of l /\
        finite_extension(k,subfield_generated l e) h
        ==> ring_carrier(subfield_generated l e) = e /\
            field(subfield_generated l e) /\
            number_field(subfield_generated l e) /\
            ring_homomorphism(k,subfield_generated l e) h"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD, FIELD_SUBFIELD_GENERATED] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP FINITE_IMP_FIELD_EXTENSION)) THEN REWRITE_TAC [field_extension] THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"subfield_generated l (e:B->bool)")] PRIME_SUBFIELD_TOWER_LAW) THEN RULE_ASSUM_TAC (REWRITE_RULE [number_field]) THEN ASM_SIMP_TAC [number_field, RING_MONOMORPHISM_IMP_HOMOMORPHISM])

  let unramified_outside ← new_definition
    r"unramified_outside (k:A ring,l:B ring) (h:A->B) S e <=>
        !p. prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
            ~(p IN S)
            ==> unramified (ring_of_integers k,
                            ring_of_integers(subfield_generated l e)) h p"

  let UNRAMIFIED_OUTSIDE_BASE ← prove
    r"!(h:A->B) k l S.
        number_field k /\ field_extension(k,l) h
        ==> IMAGE h (ring_carrier k) IN finite_galois_subfields(k,l) h /\
            unramified_outside (k,l) h S (IMAGE h (ring_carrier k))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_extension])) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring")] RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE) THEN ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"IMAGE (h:A->B) (ring_carrier k) IN finite_galois_subfields(k,l) h") ASSUME_TAC THENL [ASM_REWRITE_TAC [IN_FINITE_GALOIS_SUBFIELDS, SUBSET_REFL] THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_EXTENSION_ISOMORPHISM, MATCH_MP_TAC GALOIS_EXTENSION_ISOMORPHISM] THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC []] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [IN_FINITE_GALOIS_SUBFIELDS])) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"IMAGE (h:A->B) (ring_carrier k)")] FINITE_SUBEXTENSION_NUMBER_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN REWRITE_TAC [unramified_outside] THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED, PRIME_IMP_RING_IDEAL, NUMBER_FIELD_IMP_FIELD] THEN REWRITE_TAC [weakly_unramified] THEN X_GEN_TAC (← q r"P:B->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"subfield_generated l (IMAGE (h:A->B) (ring_carrier k))"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP) THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"trivial_group(inertia_group
      (k,subfield_generated l (IMAGE (h:A->B) (ring_carrier k))) h
      (ring_of_integers
        (subfield_generated l (IMAGE (h:A->B) (ring_carrier k)))) P)") MP_TAC THENL [REWRITE_TAC [inertia_group] THEN MATCH_MP_TAC TRIVIAL_GROUP_SUBGROUP_GENERATED THEN MATCH_MP_TAC TRIVIAL_GALOIS_GROUP THEN ASM_REWRITE_TAC [SUBSET_REFL], REWRITE_TAC [trivial_group] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [inertia_group, SUBGROUP_GENERATED, GALOIS_GROUP]])

  let UNRAMIFIED_OUTSIDE_SUBFIELD ← prove
    r"!(h:A->B) k l S e e'.
        number_field k /\ field l /\ e subfield_of l /\ e' subfield_of l /\
        IMAGE h (ring_carrier k) SUBSET e /\ e SUBSET e' /\
        finite_extension(k,subfield_generated l e') h /\
        unramified_outside (k,l) h S e'
        ==> finite_extension(k,subfield_generated l e) h /\
            unramified_outside (k,l) h S e"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"subfield_generated l (e':B->bool)"), (← q r"e:B->bool")] FINITE_EXTENSION_SUBFIELD_GENERATED) THEN SUBGOAL_THEN (← q r"subfield_generated (subfield_generated l e') e =
    subfield_generated l (e:B->bool)") SUBST1_TAC THENL [MATCH_MP_TAC SUBFIELD_GENERATED_IDEMPOT_GEN THEN ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o (MATCH_MP FINITE_IMP_FIELD_EXTENSION)) THEN REWRITE_TAC [field_extension] THEN STRIP_TAC THEN FIRST_X_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"e:B->bool")] FINITE_SUBEXTENSION_NUMBER_FIELD) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"e':B->bool")] FINITE_SUBEXTENSION_NUMBER_FIELD) THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN REWRITE_TAC [unramified_outside] THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED, PRIME_IMP_RING_IDEAL, NUMBER_FIELD_IMP_FIELD] THEN REWRITE_TAC [weakly_unramified] THEN X_GEN_TAC (← q r"P:B->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"subfield_generated l (e:B->bool)"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated l (e:B->bool)"), (← q r"subfield_generated l (e':B->bool)"), (← q r"I:B->B"), (← q r"P:B->bool")] NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD, (← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM, IMAGE_I] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"Q:B->bool") STRIP_ASSUME_TAC) o CONJUNCT2) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"subfield_generated l (e:B->bool)"), (← q r"subfield_generated l (e':B->bool)"), (← q r"h:A->B"), (← q r"I:B->B"), (← q r"P:B->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_RAMIFICATION_INDEX_TOWER) THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD, IMAGE_I, I_O_ID] THEN UNDISCH_TAC (← q r"unramified_outside (k,l) (h:A->B) S e'") THEN REWRITE_TAC [unramified_outside] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"p:A->bool"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (MATCH_MP UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED)) THEN REWRITE_TAC [weakly_unramified] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"Q:B->bool"))) THEN ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [EQ_SYM_EQ, MULT_EQ_1] THEN SIMP_TAC [])

  let INERTIA_GROUP_UNRAMIFIED_SUBFIELD ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (q ==> r) ==> (p <=> q) ==> r")
    prove
      r"!(h:A->B) k l e c p Q f.
          number_field k /\ field l /\
          e IN finite_galois_subfields(k,l) h /\
          c IN finite_galois_subfields(k,l) h /\ e SUBSET c /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          prime_ideal (ring_of_integers(subfield_generated l c)) Q /\
          IMAGE h p SUBSET Q /\
          unramified (ring_of_integers k,ring_of_integers(subfield_generated l e))
            h p /\
          f IN group_carrier(inertia_group(k,subfield_generated l c) h
                               (ring_of_integers(subfield_generated l c)) Q)
          ==> !x. x IN e ==> f x = x"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [IN_FINITE_GALOIS_SUBFIELDS]) THEN RULE_ASSUM_TAC (REWRITE_RULE [IMP_CONJ]) THEN REPEAT (FIRST_X_ASSUM ((CONJUNCTS_THEN ASSUME_TAC) o (checkM (fun z8 => (do let z9 ← (do let z10 ← (pure z8); pure (concl z10)); pure (is_conj z9)))))) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"e:B->bool")] FINITE_SUBEXTENSION_NUMBER_FIELD) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"c:B->bool")] FINITE_SUBEXTENSION_NUMBER_FIELD) THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"subfield_generated (subfield_generated l c) e =
      subfield_generated l (e:B->bool)") ASSUME_TAC THENL [MATCH_MP_TAC SUBFIELD_GENERATED_IDEMPOT_GEN THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(ring_of_integers(subfield_generated l e),
                        ring_of_integers(subfield_generated l c)) (I:B->B)") ASSUME_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_RING_OF_INTEGERS THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"subfield_generated l (c:B->bool)"), (← q r"e:B->bool")] FINITE_EXTENSION_SUBFIELD_GENERATED) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun z6 => tactic_of do pure (MP_TAC (← MATCH_MP FINITE_IMP_FIELD_EXTENSION (← (do let z7 ← (pure (CONJUNCTS z6)); liftExcept (last z7)))))) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_carrier(ring_of_integers(subfield_generated l e)) =
      ring_carrier(ring_of_integers(subfield_generated l c)) INTER (e:B->bool)") ASSUME_TAC THENL [ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBFIELD_GENERATED] THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"subfield_generated l (c:B->bool)"), (← q r"ring_of_integers(subfield_generated l (c:B->bool))"), (← q r"Q:B->bool")] (← CONJUNCT1 INERTIA_GROUP)) THEN ANTS_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING, DECOMPOSITION_GROUP_RING_OF_INTEGERS] THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN DISCH_THEN (fun th => tactic_of do pure (UNDISCH_TAC (← q r"(f:B->B) IN group_carrier(inertia_group
        (k:A ring,subfield_generated l c) (h:A->B)
        (ring_of_integers(subfield_generated l c)) Q)") THEN REWRITE_TAC [th, IN_ELIM_THM])) THEN REWRITE_TAC [RING_SUB_SUBFIELD_GENERATED] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!x y. (f:B->B) x = f y <=> x = y") ASSUME_TAC THENL [MATCH_MP_TAC PERMUTES_INJECTIVE THEN EXISTS_TAC (← q r"ring_carrier(subfield_generated l (c:B->bool))") THEN MATCH_MP_TAC GALOIS_GROUP_PERMUTES THEN MAP_EVERY EXISTS_TAC [(← q r"h:A->B"), (← q r"k:A ring")] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(\x. if x IN e then (f:B->B) x else x) IN
      group_carrier(galois_group(k:A ring,subfield_generated l e) (h:A->B)) /\
      IMAGE f e = e") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"subfield_generated l (c:B->bool)"), (← q r"e:B->bool")] GALOIS_GROUP_RESTRICTION_NORMAL) THEN ASM_SIMP_TAC [GALOIS_IMP_NORMAL_EXTENSION, FINITE_IMP_FIELD_EXTENSION, SUBFIELD_OF_SUBFIELD_GENERATED_SUBFIELD_EQ] THEN DISCH_THEN (CONJUNCTS_THEN2 (MP_TAC o (SPEC (← q r"f:B->B"))) (MP_TAC o ((SPEC (← q r"f:B->B")) o (CONJUNCT1 o ((REWRITE_RULE [group_homomorphism, SUBSET, FORALL_IN_IMAGE]) o CONJUNCT1))))) THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"{x | x IN ring_carrier(ring_of_integers(subfield_generated l e)) /\
           (I:B->B) x IN Q} = Q INTER e") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers(subfield_generated l (c:B->bool))"), (← q r"Q:B->bool")] PRIME_IDEAL_IMP_SUBSET) THEN ASM_REWRITE_TAC [I_THM] THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"prime_ideal (ring_of_integers(subfield_generated l e)) (Q INTER e) /\
      IMAGE (h:A->B) p SUBSET Q INTER e") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z5 ← (q r"Q INTER (e:B->bool)"); let z4 ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); liftExcept (rand z2)); pure (z4 == z5)))))) THEN MATCH_MP_TAC PRIME_IDEAL_HOMOMORPHIC_PREIMAGE THEN EXISTS_TAC (← q r"ring_of_integers(subfield_generated l (c:B->bool))") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"subfield_generated l (e:B->bool)"), (← q r"h:A->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [ring_homomorphism]))) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers(k:A ring)"), (← q r"p:A->bool")] PRIME_IDEAL_IMP_SUBSET) THEN MP_TAC (← ISPECL [(← q r"subfield_generated l (e:B->bool)")] RING_OF_INTEGERS_SUBSET) THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"subfield_generated l (e:B->bool)"), (← q r"p:A->bool"), (← q r"Q INTER (e:B->bool)")] NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP) THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD] THEN UNDISCH_TAC (← q r"unramified (ring_of_integers k,
                  ring_of_integers(subfield_generated l e)) (h:A->B) p") THEN DISCH_THEN (MP_TAC o (MATCH_MP UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED)) THEN REWRITE_TAC [weakly_unramified] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"Q INTER (e:B->bool)"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"subfield_generated l (e:B->bool)"), (← q r"ring_of_integers(subfield_generated l (e:B->bool))"), (← q r"Q INTER (e:B->bool)")] (← CONJUNCT1 INERTIA_GROUP)) THEN ANTS_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING, DECOMPOSITION_GROUP_RING_OF_INTEGERS] THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], DISCH_THEN SUBST1_TAC] THEN GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, IN_SING] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"\x. if x IN e then (f:B->B) x else x"))) THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [FUN_EQ_THM, I_THM] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"x:B"))) THEN ASM_REWRITE_TAC []] THEN ASM_REWRITE_TAC [RING_SUB_SUBFIELD_GENERATED] THEN CONJ_TAC THENL [SUBGOAL_THEN (← q r"IMAGE (\x. if x IN e then (f:B->B) x else x) (Q INTER e) =
        IMAGE f (Q INTER e)") SUBST1_TAC THENL [MATCH_MP_TAC IMAGE_EQ THEN SIMP_TAC [IN_INTER], ASM_SIMP_TAC [IMAGE_INTER_INJ]], ALL_TAC] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(y:B) IN e /\
      y IN ring_carrier(ring_of_integers(subfield_generated l c))") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [IN_INTER] THEN MP_TAC (← ISPECL [(← q r"subfield_generated l (e:B->bool)"), (← q r"(f:B->B) y"), (← q r"y:B")] RING_SUB) THEN ASM_SIMP_TAC [RING_SUB_SUBFIELD_GENERATED] THEN ANTS_TAC THENL [ASM SET_TAC [], SIMP_TAC []])

  let UNRAMIFIED_OUTSIDE_COMPOSITUM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(a:B->B) IN s /\ (!f. f IN s ==> f = a) ==> s = {a}")
    prove
      r"!(h:A->B) k l S e1 e2.
          number_field k /\ field l /\
          e1 IN finite_galois_subfields(k,l) h /\
          e2 IN finite_galois_subfields(k,l) h /\
          unramified_outside (k,l) h S e1 /\ unramified_outside (k,l) h S e2
          ==> ring_carrier(subfield_generated l (e1 UNION e2)) IN
              finite_galois_subfields(k,l) h /\
              e1 SUBSET ring_carrier(subfield_generated l (e1 UNION e2)) /\
              e2 SUBSET ring_carrier(subfield_generated l (e1 UNION e2)) /\
              unramified_outside (k,l) h S
               (ring_carrier(subfield_generated l (e1 UNION e2)))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"c = ring_carrier(subfield_generated l (e1 UNION e2:B->bool))") THEN SUBGOAL_THEN (← q r"c IN finite_galois_subfields(k,l) (h:A->B) /\ e1 SUBSET c /\ e2 SUBSET c") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"e1 IN finite_galois_subfields(k,l) (h:A->B)") THEN UNDISCH_TAC (← q r"e2 IN finite_galois_subfields(k,l) (h:A->B)") THEN REWRITE_TAC [IN_FINITE_GALOIS_SUBFIELDS] THEN REPEAT (DISCH_THEN STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"e1:B->bool"), (← q r"e2:B->bool")] GALOIS_EXTENSION_COMPOSITUM) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN EXPAND_TAC "c" THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED, SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN SUBGOAL_THEN (← q r"(e1 UNION e2:B->bool) SUBSET
        ring_carrier(subfield_generated l (e1 UNION e2))") MP_TAC THENL [REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN ASM_SIMP_TAC [UNION_SUBSET, SUBFIELD_OF_IMP_SUBSET], ASM SET_TAC []], ASM_REWRITE_TAC []] THEN MP_TAC (← ASSUME (← q r"c IN finite_galois_subfields(k,l) (h:A->B)")) THEN REWRITE_TAC [IN_FINITE_GALOIS_SUBFIELDS] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"IMAGE (h:A->B) (ring_carrier k) SUBSET e1") ASSUME_TAC THENL [ASM_MESON_TAC [IN_FINITE_GALOIS_SUBFIELDS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"c:B->bool")] FINITE_SUBEXTENSION_NUMBER_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN REWRITE_TAC [unramified_outside] THEN X_GEN_TAC (← q r"p:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED, PRIME_IMP_RING_IDEAL, NUMBER_FIELD_IMP_FIELD] THEN REWRITE_TAC [weakly_unramified] THEN SUBGOAL_THEN (← q r"unramified (ring_of_integers k,ring_of_integers(subfield_generated l e1))
        (h:A->B) p /\
      unramified (ring_of_integers k,ring_of_integers(subfield_generated l e2))
        h p") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [unramified_outside], ALL_TAC] THEN X_GEN_TAC (← q r"Q:B->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"subfield_generated l (c:B->bool)"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_UNRAMIFIED_INERTIA_GROUP) THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [MP_TAC (← ISPEC (← q r"inertia_group(k,subfield_generated l c) (h:A->B)
                     (ring_of_integers(subfield_generated l c)) Q") GROUP_ID) THEN REWRITE_TAC [(← CONJUNCT1 (← CONJUNCT2 INERTIA_GROUP))], X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN e1 UNION e2 ==> (f:B->B) x = I x") ASSUME_TAC THENL [REWRITE_TAC [IN_UNION, I_THM] THEN X_GEN_TAC (← q r"x:B") THEN STRIP_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"e1:B->bool"), (← q r"c:B->bool"), (← q r"p:A->bool"), (← q r"Q:B->bool"), (← q r"f:B->B")] INERTIA_GROUP_UNRAMIFIED_SUBFIELD), MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"e2:B->bool"), (← q r"c:B->bool"), (← q r"p:A->bool"), (← q r"Q:B->bool"), (← q r"f:B->B")] INERTIA_GROUP_UNRAMIFIED_SUBFIELD)] THEN ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC GALOIS_GROUP_EQ_ON_GENERATORS THEN MAP_EVERY EXISTS_TAC [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"subfield_generated l (c:B->bool)"), (← q r"e1 UNION e2:B->bool")] THEN ASM_REWRITE_TAC [GALOIS_GROUP_I] THEN CONJ_TAC THENL [SUBGOAL_THEN (← q r"IMAGE (h:A->B) (ring_carrier k) UNION (e1 UNION e2) = e1 UNION e2") SUBST1_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN wPart lhand (lhand o rand) SUBFIELD_GENERATED_IDEMPOT_GEN THEN ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN SUBST1_TAC] THEN UNDISCH_TAC (← q r"ring_carrier(subfield_generated l (e1 UNION e2:B->bool)) = c") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED], UNDISCH_TAC (← q r"(f:B->B) IN group_carrier(inertia_group
        (k:A ring,subfield_generated l c) (h:A->B)
        (ring_of_integers(subfield_generated l c))
        Q)") THEN REWRITE_TAC [inertia_group] THEN MESON_TAC [GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET, SUBSET]])

  let maximal_unramified_outside ← new_definition
    r"maximal_unramified_outside (k:A ring,l:B ring) (h:A->B) S =
        UNIONS {e | e IN finite_galois_subfields(k,l) h /\
                    unramified_outside (k,l) h S e}"

  let MAXIMAL_UNRAMIFIED_OUTSIDE_FINITE_SUBSET ← prove
    r"!(h:A->B) k l S s.
        number_field k /\ field_extension(k,l) h /\
        FINITE s /\ s SUBSET maximal_unramified_outside (k,l) h S
        ==> ?e. e IN finite_galois_subfields(k,l) h /\
                unramified_outside (k,l) h S e /\ s SUBSET e"
    (REPEAT GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN DISCH_TAC THEN DISCH_TAC THEN SPEC_TAC ((← q r"s:B->bool"), (← q r"s:B->bool")) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL [DISCH_TAC THEN EXISTS_TAC (← q r"IMAGE (h:A->B) (ring_carrier k)") THEN ASM_SIMP_TAC [UNRAMIFIED_OUTSIDE_BASE, EMPTY_SUBSET], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"x:B"), (← q r"t:B->bool")] THEN REWRITE_TAC [INSERT_SUBSET] THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e1:B->bool") STRIP_ASSUME_TAC) THEN UNDISCH_TAC (← q r"(x:B) IN maximal_unramified_outside (k:A ring,l) (h:A->B) S") THEN REWRITE_TAC [maximal_unramified_outside, IN_UNIONS, IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e2:B->bool") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"S:(A->bool)->bool"), (← q r"e1:B->bool"), (← q r"e2:B->bool")] UNRAMIFIED_OUTSIDE_COMPOSITUM) THEN ANTS_TAC THENL [ASM_MESON_TAC [field_extension], STRIP_TAC] THEN EXISTS_TAC (← q r"ring_carrier(subfield_generated l (e1 UNION e2:B->bool))") THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC [])

  let MAXIMAL_UNRAMIFIED_OUTSIDE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(x:B->bool) IN s ==> x SUBSET UNIONS s")
    prove
      r"!(h:A->B) k l S.
          number_field k /\ field_extension(k,l) h
          ==> maximal_unramified_outside (k,l) h S subfield_of l /\
              IMAGE h (ring_carrier k) SUBSET
              maximal_unramified_outside (k,l) h S"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"S:(A->bool)->bool")] UNRAMIFIED_OUTSIDE_BASE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN REWRITE_TAC [maximal_unramified_outside] THEN CONJ_TAC THENL [MATCH_MP_TAC SUBFIELD_OF_UNIONS_DIRECTED THEN REPEAT CONJ_TAC THENL [ASM_MESON_TAC [field_extension], REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN ASM_MESON_TAC [], SIMP_TAC [IN_ELIM_THM, IN_FINITE_GALOIS_SUBFIELDS], REWRITE_TAC [IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"e1:B->bool"), (← q r"e2:B->bool")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"S:(A->bool)->bool"), (← q r"e1:B->bool"), (← q r"e2:B->bool")] UNRAMIFIED_OUTSIDE_COMPOSITUM) THEN ANTS_TAC THENL [ASM_MESON_TAC [field_extension], STRIP_TAC] THEN EXISTS_TAC (← q r"ring_carrier(subfield_generated l (e1 UNION e2:B->bool))") THEN ASM_REWRITE_TAC []], MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [IN_ELIM_THM]])

  let MAXIMAL_UNRAMIFIED_OUTSIDE_SUBEXTENSION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!t. (e:B->bool) SUBSET t /\ t IN s ==> e SUBSET UNIONS s")
    let r8 ← TAUT (← q r"(p <=> q) /\ (q ==> r) ==> (p <=> q) /\ (p ==> r)")
    prove
      r"!(h:A->B) k l S e.
          number_field k /\ field_extension(k,l) h /\
          e subfield_of l /\ IMAGE h (ring_carrier k) SUBSET e /\
          finite_extension(k,subfield_generated l e) h
          ==> (e SUBSET maximal_unramified_outside (k,l) h S <=>
               ?e'. e' IN finite_galois_subfields(k,l) h /\
                    unramified_outside (k,l) h S e' /\ e SUBSET e') /\
              (e SUBSET maximal_unramified_outside (k,l) h S
               ==> unramified_outside (k,l) h S e)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC r8 THEN CONJ_TAC THENL [EQ_TAC THENL [DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"e:B->bool")] FINITE_EXTENSION_SUBFIELD_GENERATORS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"b:B->bool") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"S:(A->bool)->bool"), (← q r"b:B->bool")] MAXIMAL_UNRAMIFIED_OUTSIDE_FINITE_SUBSET) THEN ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"e':B->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_eq z2)) then (do let z7 ← (q r"e:B->bool"); let z6 ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (rand z4)); pure (z6 == z7)) else pure false))))) THEN MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN ASM_MESON_TAC [IN_FINITE_GALOIS_SUBFIELDS, UNION_SUBSET, SUBSET_TRANS], DISCH_THEN (X_CHOOSE_THEN (← q r"e':B->bool") STRIP_ASSUME_TAC) THEN REWRITE_TAC [maximal_unramified_outside] THEN MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"e':B->bool") THEN ASM_REWRITE_TAC [IN_ELIM_THM]], DISCH_THEN (X_CHOOSE_THEN (← q r"e':B->bool") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"S:(A->bool)->bool"), (← q r"e:B->bool"), (← q r"e':B->bool")] UNRAMIFIED_OUTSIDE_SUBFIELD) THEN ASM_MESON_TAC [IN_FINITE_GALOIS_SUBFIELDS, field_extension]])

  let MAXIMAL_UNRAMIFIED_OUTSIDE_FINITE_GALOIS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(x:B->bool) IN s ==> x SUBSET UNIONS s")
    prove
      r"!(h:A->B) k l S e.
          number_field k /\ field_extension(k,l) h /\
          e IN finite_galois_subfields(k,l) h
          ==> (e SUBSET maximal_unramified_outside (k,l) h S <=>
               unramified_outside (k,l) h S e)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"S:(A->bool)->bool"), (← q r"e:B->bool")] MAXIMAL_UNRAMIFIED_OUTSIDE_SUBEXTENSION) THEN ANTS_TAC THENL [ASM_MESON_TAC [IN_FINITE_GALOIS_SUBFIELDS], SIMP_TAC []], DISCH_TAC THEN REWRITE_TAC [maximal_unramified_outside] THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [IN_ELIM_THM]])

  let GALOIS_MAXIMAL_UNRAMIFIED_OUTSIDE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(e:B->bool) IN f ==> e SUBSET UNIONS f")
    prove
      r"!(h:A->B) k l S.
          number_field k /\ field_extension(k,l) h
          ==> galois_extension
               (k,subfield_generated l (maximal_unramified_outside (k,l) h S)) h"
      (REPEAT STRIP_TAC THEN MATCH_MP_TAC GALOIS_EXTENSION_UNION_FINITE_GALOIS_SUBFIELDS THEN ASM_SIMP_TAC [MAXIMAL_UNRAMIFIED_OUTSIDE] THEN REWRITE_TAC [maximal_unramified_outside, IN_UNIONS, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:B->bool") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"e:B->bool") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [IN_ELIM_THM])

  let NUMBER_FIELD_ALGEBRAIC_CLOSURE_GALOIS ← prove
    r"!(h:A->B) k l.
        number_field k /\ algebraic_extension(k,l) h /\
        algebraically_closed_field l
        ==> galois_extension(k,l) h"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [galois_extension] THEN ASM_SIMP_TAC [ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION] THEN MATCH_MP_TAC PERFECT_FIELD_IMP_SEPARABLE_EXTENSION THEN ASM_REWRITE_TAC [] THEN RULE_ASSUM_TAC (REWRITE_RULE [number_field]) THEN ASM_SIMP_TAC [PERFECT_FIELD_CHAR_0] THEN ASM_MESON_TAC [ALGEBRAIC_IMP_FIELD_EXTENSION, field_extension])

  -- @@RETURN BEGIN
  return { FINITE_SUBEXTENSION_NUMBER_FIELD, unramified_outside, UNRAMIFIED_OUTSIDE_BASE,
           UNRAMIFIED_OUTSIDE_SUBFIELD, INERTIA_GROUP_UNRAMIFIED_SUBFIELD,
           UNRAMIFIED_OUTSIDE_COMPOSITUM, maximal_unramified_outside,
           MAXIMAL_UNRAMIFIED_OUTSIDE_FINITE_SUBSET, MAXIMAL_UNRAMIFIED_OUTSIDE,
           MAXIMAL_UNRAMIFIED_OUTSIDE_SUBEXTENSION,
           MAXIMAL_UNRAMIFIED_OUTSIDE_FINITE_GALOIS, GALOIS_MAXIMAL_UNRAMIFIED_OUTSIDE,
           NUMBER_FIELD_ALGEBRAIC_CLOSURE_GALOIS }
  -- @@RETURN END

end HolANT.UnramifiedOutside
