/- ========================================================================= -/
/- ANT: Hilbert formula for the different and the tame exponent of ...     -/
/- ========================================================================= -/
/- File: HolANT/HilbertFormula.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/hilbert_formula.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/anthilbertformuladiff; the rest is by hand.  Its `needs` closure is
  Library/frag.ml, Library/wo.ml, Library/card.ml, Library/prime.ml, Library/grouptheory.ml, Library/matroids.ml, Library/binomial.ml, Library/iter.ml, Library/pocklington.ml, Library/ringtheory.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/different.ml, ANT/finite_field_trace.ml, ANT/relative_degree.ml, ANT/different_extension.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/decomposition.ml, ANT/ramification.ml, ANT/splitting_types.ml, ANT/nf_decomposition.ml, ANT/decomposition_field.ml, Library/integer.ml, Library/multiplicative.ml, Library/primitive.ml, ANT/dedekind_kummer.ml, ANT/split_primes.ml, ANT/conjugate_ideals.ml, ANT/ideal_norm_extension.ml, ANT/hensel.ml, ANT/ideal_euler.ml, ANT/ramification_groups.ml, ANT/power_basis.ml, ANT/power_basis_index.ml, ANT/power_basis_extension.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.HilbertFormula fills them).

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
import HolLibrary.Products
import HolANT.Algmisc
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
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.NormIndex
import HolANT.Classgroup
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.NfValuation
import HolANT.Integrality
import HolANT.Different
import HolANT.FiniteFieldTrace
import HolANT.RelativeDegree
import HolANT.DifferentExtension
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolANT.Decomposition
import HolANT.Ramification
import HolANT.SplittingTypes
import HolANT.NfDecomposition
import HolANT.DecompositionField
import HolLibrary.Integer
import HolLibrary.Multiplicative
import HolLibrary.Primitive
import HolANT.DedekindKummer
import HolANT.SplitPrimes
import HolANT.ConjugateIdeals
import HolANT.IdealNormExtension
import HolANT.Hensel
import HolANT.IdealEuler
import HolANT.RamificationGroups
import HolANT.PowerBasis
import HolANT.PowerBasisIndex
import HolANT.PowerBasisExtension

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
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.NormIndex
open HolANT.Classgroup
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.NfValuation
open HolANT.Integrality
open HolANT.Different
open HolANT.FiniteFieldTrace
open HolANT.RelativeDegree
open HolANT.DifferentExtension
open HolANT.Decomposition
open HolANT.Ramification
open HolANT.SplittingTypes
open HolANT.NfDecomposition
open HolANT.DecompositionField
open HolANT.DedekindKummer
open HolANT.SplitPrimes
open HolANT.ConjugateIdeals
open HolANT.IdealNormExtension
open HolANT.Hensel
open HolANT.IdealEuler
open HolANT.RamificationGroups
open HolANT.PowerBasis
open HolANT.PowerBasisIndex
open HolANT.PowerBasisExtension

namespace HolANT.HilbertFormula

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD_CLAUSES AND_FORALL_THM CARD_DELETE CARD_EQ_0 CARD_NUMSEG_LT CARD_PSUBSET
   CARD_SING CARD_SUBSET DECOMPOSITION_GROUP DEDEKIND_IDEAL_POW_MUL_CANCEL
   DEDEKIND_IDEAL_SUBSET_POW_VALUATION DEDEKIND_IN_IDEAL_POW_VALUATION
   DEDEKIND_RING_OF_INTEGERS EQ_MULT_LCANCEL EQ_TRANS EXISTS_UNIQUE_THM
   EXTENSION FIELD_IMP_NONTRIVIAL_RING FIELD_RING_HOMOMORPHISM_MONOMORPHISM
   FINITE_DELETE FINITE_GALOIS_GROUP FINITE_INTER FINITE_NUMSEG_LT
   FINITE_RESTRICT FINITE_SUBSET FORALL_IN_IMAGE FUN_IN_IMAGE
   GALOIS_EXTENSION_INTERMEDIATE GALOIS_GROUP_I GALOIS_GROUP_PRIME_IDEAL_IMAGE
   GALOIS_GROUP_RING_HOMOMORPHISM GALOIS_GROUP_RING_OF_INTEGERS
   GALOIS_IMP_FIELD_EXTENSION GALOIS_PRIMITIVE_ELEMENT_DERIVATIVE
   GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET GROUP_ID GROUP_INV GROUP_MUL
   IDEAL_GENERATED_SUBSET IDEAL_GENERATED_SUBSET_CARRIER IDEAL_POW_1
   IDEAL_VALUATION_IDEAL_PROD IDEAL_VALUATION_PRINCIPAL_PRODUCT IMAGE_I
   IMAGE_SUBSET IMAGE_o INERTIA_GROUP INERTIA_GROUP_IDEAL_POW
   INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL INERTIA_GROUP_IDEAL_POW_MONO
   INERTIA_GROUP_INTERMEDIATE INERTIA_GROUP_TOWER INERTIA_GROUP_WILD_SUBSET
   INSERT_SUBSET INTER_SUBSET IN_DELETE IN_ELIM_THM IN_GALOIS_GROUP IN_INTER
   IN_RING_IDEAL_0 IN_RING_IDEAL_ADD IN_RING_IDEAL_LMUL IN_RING_IDEAL_NEG
   IN_RING_IDEAL_RMUL IN_RING_IDEAL_SUB_SYM IN_SING IN_UNIV I_O_ID I_THM
   LEFT_SUB_DISTRIB LE_MULT_LCANCEL MAXIMAL_IMP_PRIME_IDEAL
   MAXIMAL_SUPERIDEAL_EXISTS MEMBER_NOT_EMPTY MONO_EXISTS MULT_AC MULT_CLAUSES
   MULT_EQ_0 NOT_LT NSUM_ADD NSUM_CONST NSUM_DELETE NSUM_EQ NSUM_EQ_0
   NSUM_RESTRICT_SET NSUM_SUPERSET NSUM_SWAP NUMBER_FIELD_DECOMPOSITION_FIELD
   NUMBER_FIELD_DECOMPOSITION_GROUP NUMBER_FIELD_DIFFERENT_LOCAL_POWER_BASIS
   NUMBER_FIELD_DIFFERENT_NONZERO NUMBER_FIELD_DIFFERENT_RAMIFIED
   NUMBER_FIELD_DIFFERENT_TOWER NUMBER_FIELD_GALOIS_CLOSURE
   NUMBER_FIELD_HOMOMORPHIC_PREIMAGE NUMBER_FIELD_IDEAL_VALUATION_EXTENSION
   NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_INTERMEDIATE_FIELD
   NUMBER_FIELD_LOCAL_POWER_BASIS NUMBER_FIELD_PRIME_IDEAL_ABOVE
   NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE
   NUMBER_FIELD_RAMIFICATION_INDEX_TOWER NUMBER_FIELD_SEPARABLE_EXTENSION
   NUMBER_FIELD_TOWER_LAW PRIME_IDEAL_IMP_SUBSET PRIME_IMP_RING_IDEAL PSUBSET
   RING_0 RING_1 RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_1 RING_HOMOMORPHISM_ADD
   RING_HOMOMORPHISM_COMPOSE RING_HOMOMORPHISM_IN_CARRIER RING_HOMOMORPHISM_MUL
   RING_HOMOMORPHISM_NEG RING_HOMOMORPHISM_RING_OF_INTEGERS
   RING_HOMOMORPHISM_RING_OF_NUM RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_POW
   RING_IDEAL_NUMBER_FIELD_DIFFERENT RING_MONOMORPHISM_IMP_HOMOMORPHISM
   RING_OF_INTEGERS RING_OF_INTEGERS_FRACTION_FIELD
   RING_OF_INTEGERS_IDEAL_EXTENSION RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME
   RING_OF_INTEGERS_PRIME_IDEAL_ABOVE RING_OF_INTEGERS_SUBRING
   RING_OF_INTEGERS_SUBSET RING_OF_NUM_IN_PRIME_IDEAL
   RING_PRODUCT_RING_OF_INTEGERS RING_SUB RING_SUB_EQ_0 RING_SUB_REFL
   SING_SUBSET SUBFIELD_GENERATED SUBRING_GENERATED_MINIMAL SUBSET SUBSET_INTER
   SUBSET_TRANS SUBSET_UNIV SUB_REFL field_extension inertia_group proper_ideal
   ring_homomorphism subgroup_of subring_of : thm)
  deriving Inhabited

/-- What hilbert_formula.ml uses from Session besides theorems. -/
structure HilbertFormulaDeps where
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
/- hilbert_formula.ml phrases from line 95 to 699                         -/
/- ---------------------------------------------------------------------- -/

structure HilbertFormula01 where
  -- @@FIELDS
  NSUM_CARD_SUBSETS_DELETE : thm
  INERTIA_GROUP_IDEAL_POW_LOCAL_GENERATOR : thm
  NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_ONE_PRIME : thm
  NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_LT : thm
  NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupHilbertFormula01 [HolBase] (D : HilbertFormulaDeps) :
    ExceptT String IO HilbertFormula01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, MESON_TAC, RING_RULE, SET_RULE, SET_TAC, .. } := D
  let { ADD_CLAUSES, CARD_DELETE, CARD_NUMSEG_LT, CARD_SING, DECOMPOSITION_GROUP,
        DEDEKIND_IDEAL_POW_MUL_CANCEL, DEDEKIND_IDEAL_SUBSET_POW_VALUATION,
        DEDEKIND_IN_IDEAL_POW_VALUATION, DEDEKIND_RING_OF_INTEGERS, EQ_TRANS,
        EXTENSION, FINITE_DELETE, FINITE_GALOIS_GROUP, FINITE_NUMSEG_LT,
        FINITE_RESTRICT, FINITE_SUBSET, FORALL_IN_IMAGE, GALOIS_EXTENSION_INTERMEDIATE,
        GALOIS_GROUP_I, GALOIS_GROUP_PRIME_IDEAL_IMAGE, GALOIS_GROUP_RING_HOMOMORPHISM,
        GALOIS_GROUP_RING_OF_INTEGERS, GALOIS_IMP_FIELD_EXTENSION,
        GALOIS_PRIMITIVE_ELEMENT_DERIVATIVE, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET,
        GROUP_ID, IDEAL_POW_1, IDEAL_VALUATION_IDEAL_PROD,
        IDEAL_VALUATION_PRINCIPAL_PRODUCT, IMAGE_I, INERTIA_GROUP,
        INERTIA_GROUP_IDEAL_POW, INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL,
        INERTIA_GROUP_INTERMEDIATE, INSERT_SUBSET, IN_DELETE, IN_ELIM_THM,
        IN_GALOIS_GROUP, IN_RING_IDEAL_0, IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL,
        IN_RING_IDEAL_NEG, IN_RING_IDEAL_RMUL, IN_RING_IDEAL_SUB_SYM, IN_SING, IN_UNIV,
        I_O_ID, I_THM, MULT_CLAUSES, MULT_EQ_0, NOT_LT, NSUM_CONST, NSUM_EQ,
        NSUM_RESTRICT_SET, NSUM_SUPERSET, NSUM_SWAP, NUMBER_FIELD_DECOMPOSITION_FIELD,
        NUMBER_FIELD_DIFFERENT_LOCAL_POWER_BASIS, NUMBER_FIELD_DIFFERENT_NONZERO,
        NUMBER_FIELD_DIFFERENT_RAMIFIED, NUMBER_FIELD_DIFFERENT_TOWER,
        NUMBER_FIELD_IDEAL_VALUATION_EXTENSION, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_INTERMEDIATE_FIELD, NUMBER_FIELD_LOCAL_POWER_BASIS,
        NUMBER_FIELD_PRIME_IDEAL_ABOVE, NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE,
        NUMBER_FIELD_SEPARABLE_EXTENSION, NUMBER_FIELD_TOWER_LAW,
        PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_RING_IDEAL, RING_0, RING_1,
        RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_ADD,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_NEG,
        RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IDEAL_POW, RING_IDEAL_NUMBER_FIELD_DIFFERENT,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FRACTION_FIELD, RING_OF_INTEGERS_IDEAL_EXTENSION,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET,
        RING_PRODUCT_RING_OF_INTEGERS, RING_SUB, RING_SUB_EQ_0, RING_SUB_REFL,
        SUBFIELD_GENERATED, SUBRING_GENERATED_MINIMAL, SUBSET, SUBSET_UNIV, SUB_REFL,
        field_extension, inertia_group, subring_of, .. } := D.core1
  -- @@SCOPE END

  let NSUM_CARD_SUBSETS_DELETE ← prove
    r"!(G:K->bool) e (H:num->K->bool) n.
        FINITE G /\ (!i. i < n ==> H i SUBSET G /\ e IN H i)
        ==> nsum (G DELETE e) (\g. CARD {i | i < n /\ g IN H i}) =
            nsum {i | i < n} (\i. CARD(H i) - 1)"
    (REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS (← q r"nsum (G DELETE e)
      (\g:K. nsum {i | i < (n:num)} (\i. if g IN H i then 1 else 0))") THEN CONJ_TAC THENL [MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"g:K") THEN DISCH_TAC THEN REWRITE_TAC [(← GSYM NSUM_RESTRICT_SET)] THEN SIMP_TAC [NSUM_CONST, FINITE_RESTRICT, FINITE_NUMSEG_LT] THEN REWRITE_TAC [IN_ELIM_THM, MULT_CLAUSES], ALL_TAC] THEN wPart lhand (lhand o rand) NSUM_SWAP THEN ASM_SIMP_TAC [FINITE_DELETE, FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [(← GSYM NSUM_RESTRICT_SET)] THEN ASM_SIMP_TAC [NSUM_CONST, FINITE_RESTRICT, FINITE_DELETE, MULT_CLAUSES] THEN SUBGOAL_THEN (← q r"{g:K | g IN G DELETE e /\ g IN H i} = (H:num->K->bool) i DELETE e") SUBST1_TAC THENL [FIRST_ASSUM (MP_TAC o ((← do let c := (← ASSUME (← q r"i:num < n")); pure (fun th => MATCH_MP th c)) o (checkM (fun z4 => (do let z5 ← (do let z6 ← (pure z4); pure (concl z6)); pure (is_forall z5)))))) THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"FINITE((H:num->K->bool) i) /\ e IN H i") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o ((← do let c := (← ASSUME (← q r"i:num < n")); pure (fun th => MATCH_MP th c)) o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_forall z2)))))) THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"G:K->bool") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [CARD_DELETE])

  let INERTIA_GROUP_IDEAL_POW_LOCAL_GENERATOR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul r t (ring_sub r u x) =
      ring_sub r (ring_mul r t u) (ring_mul r t (x:B))")
    let r32 ← RING_RULE (← q r"ring_sub r (ring_mul r x u) (ring_mul r y v) =
          ring_add r (ring_mul r (ring_sub r x y) u)
                     (ring_mul r y (ring_sub r u (v:B)))")
    let r33 ← RING_RULE (← q r"ring_sub r (ring_add r x u) (ring_add r y v) =
          ring_add r (ring_sub r x y) (ring_sub r u (v:B))")
    let r34 ← RING_RULE (← q r"ring_sub r (ring_neg r x) (ring_neg r y) =
          ring_neg r (ring_sub r x (y:B))")
    prove
      r"!(h:A->B) k l p Q a s f i.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
          a IN ring_carrier(ring_of_integers l) /\
          s IN ring_carrier(ring_of_integers k) /\ ~(s IN p) /\
          (!y. y IN ring_carrier(ring_of_integers l)
               ==> ring_mul l (h s) y IN
                   ring_carrier(subring_generated l
                     (a INSERT IMAGE h (ring_carrier(ring_of_integers k))))) /\
          f IN group_carrier(decomposition_group(k,l) h Q)
          ==> (f IN group_carrier(inertia_group(k,l) h (ring_of_integers l)
                                   (ideal_pow (ring_of_integers l) Q (i + 1))) <=>
               ring_sub l (f a) a IN ideal_pow (ring_of_integers l) Q (i + 1))"
      (REPEAT GEN_TAC THEN ABBREV_TAC (← q r"R = ring_carrier(subring_generated l
            (a INSERT IMAGE (h:A->B) (ring_carrier(ring_of_integers k))))") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"f IN group_carrier(galois_group(k,l) (h:A->B))") ASSUME_TAC THENL [UNDISCH_TAC (← q r"f IN group_carrier(decomposition_group(k,l) (h:A->B) Q)") THEN SIMP_TAC [DECOMPOSITION_GROUP, IN_ELIM_THM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"i:num")] INERTIA_GROUP_IDEAL_POW) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING] THEN REWRITE_TAC [GALOIS_GROUP_RING_OF_INTEGERS], DISCH_THEN SUBST1_TAC] THEN ABBREV_TAC (← q r"J = ideal_pow (ring_of_integers l) Q (i + 1):B->bool") THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN EQ_TAC THENL [DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], DISCH_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_RING_OF_INTEGERS)) THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"!c. c IN ring_carrier k ==> (f:B->B)((h:A->B) c) = h c") ASSUME_TAC THENL [UNDISCH_TAC (← q r"f IN group_carrier(galois_group(k,l) (h:A->B))") THEN SIMP_TAC [IN_GALOIS_GROUP], ALL_TAC] THEN SUBGOAL_THEN (← q r"!z. z IN ring_carrier(ring_of_integers l) ==> (z:B) IN ring_carrier l") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_SUBSET) THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!c. c IN ring_carrier(ring_of_integers k) ==> (c:A) IN ring_carrier k") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!c. c IN ring_carrier(ring_of_integers k)
          ==> (h:A->B) c IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC (← q r"ring_of_integers k:A ring") THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers l) (J:B->bool)") ASSUME_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW], ALL_TAC] THEN SUBGOAL_THEN (← q r"R SUBSET {z:B | z IN ring_carrier(ring_of_integers l) /\
                      ring_sub l (f z) z IN J}") ASSUME_TAC THENL [EXPAND_TAC "R" THEN MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN CONJ_TAC THENL [REWRITE_TAC [INSERT_SUBSET, SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"c:A") THEN DISCH_TAC THEN ASM_SIMP_TAC [RING_SUB_REFL] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool")] IN_RING_IDEAL_0) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN REWRITE_TAC [subring_of, SUBSET, IN_ELIM_THM] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool")] IN_RING_IDEAL_0) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool")] IN_RING_IDEAL_NEG) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool")] IN_RING_IDEAL_ADD) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool")] IN_RING_IDEAL_LMUL) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool")] IN_RING_IDEAL_RMUL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN REPEAT DISCH_TAC THEN MP_TAC (← ISPEC (← q r"l:B ring") (← CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN REWRITE_TAC [subring_of] THEN STRIP_TAC THEN REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 (← ASSUME (← q r"ring_homomorphism(l,l) (f:B->B)"))), (← MATCH_MP RING_HOMOMORPHISM_1 (← ASSUME (← q r"ring_homomorphism(l,l) (f:B->B)")))] THEN ASM_SIMP_TAC [RING_SUB_REFL, RING_0, RING_1] THEN SUBGOAL_THEN (← q r"!z. z IN ring_carrier(ring_of_integers l)
            ==> (z:B) IN ring_carrier l /\ (f:B->B) z IN ring_carrier l /\
                f z IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN REPEAT CONJ_TAC THENL [X_GEN_TAC (← q r"z:B") THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (← do let c := (← ASSUME (← q r"(z:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c))) THEN ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_NEG (← ASSUME (← q r"ring_homomorphism(l,l) (f:B->B)")))] THEN SUBGOAL_THEN (← q r"ring_sub l (ring_neg l ((f:B->B) z)) (ring_neg l z) =
          ring_neg l (ring_sub l (f z) z)") SUBST1_TAC THENL [MATCH_MP_TAC r34 THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC []], MAP_EVERY X_GEN_TAC [(← q r"z:B"), (← q r"w:B")] THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (← do let c := (← ASSUME (← q r"(z:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c))) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (← do let c := (← ASSUME (← q r"(w:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c))) THEN ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_ADD (← ASSUME (← q r"ring_homomorphism(l,l) (f:B->B)")))] THEN SUBGOAL_THEN (← q r"ring_sub l (ring_add l ((f:B->B) z) (f w)) (ring_add l z w) =
          ring_add l (ring_sub l (f z) z) (ring_sub l (f w) w)") SUBST1_TAC THENL [MATCH_MP_TAC r33 THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC []], MAP_EVERY X_GEN_TAC [(← q r"z:B"), (← q r"w:B")] THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (← do let c := (← ASSUME (← q r"(z:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c))) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (← do let c := (← ASSUME (← q r"(w:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c))) THEN ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL (← ASSUME (← q r"ring_homomorphism(l,l) (f:B->B)")))] THEN SUBGOAL_THEN (← q r"ring_sub l (ring_mul l ((f:B->B) z) (f w)) (ring_mul l z w) =
          ring_add l (ring_mul l (ring_sub l (f z) z) (f w))
                     (ring_mul l z (ring_sub l (f w) w))") SUBST1_TAC THENL [MATCH_MP_TAC r32 THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC []]], ALL_TAC] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((← do let c := (← ASSUME (← q r"(x:B) IN ring_carrier(ring_of_integers l)")); pure (fun th => MATCH_MP th c)) o (checkM (fun th => (do if ← (do if ← (do let z16 ← (do let z17 ← (pure th); pure (concl z17)); pure (is_forall z16)) then (do let z18 ← (do let z19 ← (pure th); pure (concl z19)); canM (fun z20 => (do let z21 ← (pure z20); find_termM (fun z22 => (do let z24 ← (pure z22); let z23 ← (q r"R:B->bool"); pure (z23 == z24))) z21)) z18) else pure false) then (do let z25 ← (do let z26 ← (pure th); pure (concl z26)); canM (fun z27 => (do let z28 ← (pure z27); find_termM (fun z29 => (do let z31 ← (pure z29); let z30 ← (q r"ring_mul l ((h:A->B) s)"); pure (z30 == z31))) z28)) z25) else pure false))))) THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"ring_mul l ((h:A->B) s) x")) o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do let z8 ← (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); liftExcept (lhand z9)); canM (fun z11 => (do let z12 ← (pure z11); find_termM (fun z13 => (do let z15 ← (pure z13); let z14 ← (q r"R:B->bool"); pure (z14 == z15))) z12)) z8)))))) THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(h:A->B) s IN ring_carrier(ring_of_integers l) /\
                  (f:B->B) x IN ring_carrier(ring_of_integers l)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~((h:A->B) s IN Q)") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"~((s:A) IN p)") THEN REWRITE_TAC [] THEN FIRST_X_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_eq z2)) then (do let z7 ← (q r"p:A->bool"); let z6 ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (rhs z4)); pure (z6 == z7)) else pure false)))) THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"(h:A->B) s"), (← q r"ring_sub l ((f:B->B) x) x"), (← q r"0"), (← q r"i + 1")] DEDEKIND_IDEAL_POW_MUL_CANCEL) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, ADD_CLAUSES, DEDEKIND_RING_OF_INTEGERS, IDEAL_POW_1, PRIME_IMP_RING_IDEAL] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [MP_TAC (← ISPEC (← q r"ring_of_integers l:B ring") RING_SUB) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier l /\ (f:B->B) x IN ring_carrier l /\
      (h:A->B) s IN ring_carrier l /\ (s:A) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l ((h:A->B) s) (ring_sub l ((f:B->B) x) x) =
      ring_sub l (f (ring_mul l (h s) x)) (ring_mul l (h s) x)") SUBST1_TAC THENL [ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL (← ASSUME (← q r"ring_homomorphism(l,l) (f:B->B)")))] THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC []])

  let NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_ONE_PRIME ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"i + 1 <= v <=> i < v")
    let r17 ← ARITH_RULE (← q r"~(n + 1 <= v) ==> v:num <= n")
    prove
      r"!(h:A->B) k l p Q n.
          number_field l /\ galois_extension(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P} = {Q} /\
          group_carrier(inertia_group(k,l) h (ring_of_integers l)
                          (ideal_pow (ring_of_integers l) Q (n + 1))) = {I}
          ==> ideal_valuation (ring_of_integers l) Q
                (number_field_different (k,l) h) =
              nsum {i | i < n}
                (\i. CARD(group_carrier(inertia_group(k,l) h (ring_of_integers l)
                            (ideal_pow (ring_of_integers l) Q (i + 1)))) - 1)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN (← q r"prime_ideal (ring_of_integers l) (Q:B->bool) /\ IMAGE (h:A->B) p SUBSET Q") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o ((SPEC (← q r"Q:B->bool")) o ((REWRITE_RULE [EXTENSION, IN_ELIM_THM, IN_SING]) o (checkM (fun th => (do if ← (do let z24 ← (do let z25 ← (pure th); pure (concl z25)); pure (is_eq z24)) then (do let z29 ← (q r"{Q:B->bool}"); let z28 ← (do let z26 ← (do let z27 ← (pure th); pure (concl z27)); liftExcept (rhs z26)); pure (z28 == z29)) else pure false)))))) THEN MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_SEPARABLE_EXTENSION) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z23 ← (q r"number_field(l:B ring)"); let z22 ← (do let z21 ← (pure th); pure (concl z21)); pure (z22 == z23)))))) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP DEDEKIND_RING_OF_INTEGERS) o (checkM (fun th => (do let z20 ← (q r"number_field(l:B ring)"); let z19 ← (do let z18 ← (pure th); pure (concl z18)); pure (z19 == z20)))))) THEN ABBREV_TAC (← q r"G = group_carrier(galois_group(k,l) (h:A->B))") THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(decomposition_group(k,l) (h:A->B) Q) <=> f IN G") ASSUME_TAC THENL [EXPAND_TAC "G" THEN REWRITE_TAC [DECOMPOSITION_GROUP] THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"f:B->B") THEN EQ_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(Q:B->bool) SUBSET ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [ASM_SIMP_TAC [PRIME_IDEAL_IMP_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"f:B->B"), (← q r"Q:B->bool")] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING, GALOIS_GROUP_RING_OF_INTEGERS, PRIME_IDEAL_IMP_SUBSET] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"IMAGE (f:B->B) Q IN
                    {P | prime_ideal (ring_of_integers l) P /\
                         IMAGE (h:A->B) p SUBSET P}") MP_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"c:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(c:A) IN {a | a IN ring_carrier k /\ (h:A->B) a IN IMAGE (f:B->B) Q}") MP_TAC THENL [ASM_REWRITE_TAC [], SIMP_TAC [IN_ELIM_THM]], ASM_REWRITE_TAC [IN_SING]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_LOCAL_POWER_BASIS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:B") (X_CHOOSE_THEN (← q r"s:A") STRIP_ASSUME_TAC)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"a:B"), (← q r"s:A"), (← q r"Q:B->bool")] NUMBER_FIELD_DIFFERENT_LOCAL_POWER_BASIS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"(a:B) IN ring_carrier l") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_SUBSET) THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"a:B")] GALOIS_PRIMITIVE_ELEMENT_DERIVATIVE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 (fun (_ : thm) => ALL_TAC) SUBST1_TAC) THEN SUBGOAL_THEN (← q r"FINITE(G:(B->B)->bool) /\ (I:B->B) IN G") STRIP_ASSUME_TAC THENL [EXPAND_TAC "G" THEN ASM_SIMP_TAC [FINITE_GALOIS_GROUP, GALOIS_GROUP_I], ALL_TAC] THEN SUBGOAL_THEN (← q r"!f. f IN G
          ==> (f:B->B) a IN ring_carrier(ring_of_integers l) /\
              ring_sub l a (f a) IN ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [EXPAND_TAC "G" THEN X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_RING_OF_INTEGERS)) THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"a:B"))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPEC (← q r"ring_of_integers l:B ring") RING_SUB) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!f. f IN G /\ ~(f = I) ==> ~(ring_sub l a ((f:B->B) a) = ring_0 l)") ASSUME_TAC THENL [X_GEN_TAC (← q r"f:B->B") THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (← do let c := (← ASSUME (← q r"(f:B->B) IN G")); pure (fun th => MATCH_MP th c))) THEN SUBGOAL_THEN (← q r"(f:B->B) a IN ring_carrier l") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_SUBSET) THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"a:B"), (← q r"(f:B->B) a")] RING_SUB_EQ_0) THEN ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~(f:B->B = I)") THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"a:B")] GALOIS_PRIMITIVE_ELEMENT_DERIVATIVE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (MP_TAC o ((SPECL [(← q r"f:B->B"), (← q r"I:B->B")]) o CONJUNCT1)) THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL [UNDISCH_TAC (← q r"(f:B->B) IN G") THEN EXPAND_TAC "G" THEN SIMP_TAC [], REWRITE_TAC [GALOIS_GROUP_I], REWRITE_TAC [I_THM] THEN FIRST_ASSUM (ACCEPT_TAC o SYM)], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"G DELETE (I:B->B)"), (← q r"\f:B->B. ring_sub l a (f a)")] RING_PRODUCT_RING_OF_INTEGERS) THEN ANTS_TAC THENL [REWRITE_TAC [IN_DELETE] THEN X_GEN_TAC (← q r"f:B->B") THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (← do let c := (← ASSUME (← q r"(f:B->B) IN G")); pure (fun th => MATCH_MP th c))) THEN FIRST_ASSUM ACCEPT_TAC, DISCH_THEN (SUBST1_TAC o SYM)] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"\f:B->B. ring_sub l a (f a)"), (← q r"G DELETE (I:B->B)")] IDEAL_VALUATION_PRINCIPAL_PRODUCT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [FINITE_DELETE, IN_DELETE, RING_OF_INTEGERS] THEN X_GEN_TAC (← q r"f:B->B") THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (← do let c := (← ASSUME (← q r"(f:B->B) IN G")); pure (fun th => MATCH_MP th c))) THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"G:(B->B)->bool"), (← q r"I:B->B"), (← q r"\i. group_carrier(inertia_group(k,l) (h:A->B)
                          (ring_of_integers l)
                          (ideal_pow (ring_of_integers l) Q (i + 1)))"), (← q r"n:num")] NSUM_CARD_SUBSETS_DELETE) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN CONJ_TAC THENL [EXPAND_TAC "G" THEN REWRITE_TAC [inertia_group] THEN REWRITE_TAC [GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET], MP_TAC (← ISPEC (← q r"inertia_group(k,l) (h:A->B) (ring_of_integers l)
            (ideal_pow (ring_of_integers l) Q (i + 1))") GROUP_ID) THEN REWRITE_TAC [(← CONJUNCT1 (← CONJUNCT2 INERTIA_GROUP))]], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"f:B->B") THEN REWRITE_TAC [IN_DELETE] THEN STRIP_TAC THEN REWRITE_TAC [] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (← do let c := (← ASSUME (← q r"(f:B->B) IN G")); pure (fun th => MATCH_MP th c))) THEN SUBGOAL_THEN (← q r"~(ring_sub l a ((f:B->B) a) = ring_0 l)") ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN ABBREV_TAC (← q r"v = ideal_valuation (ring_of_integers l) Q
            (ideal_generated (ring_of_integers l)
               {ring_sub l a ((f:B->B) a)})") THEN SUBGOAL_THEN (← q r"!i. (f:B->B) IN group_carrier(inertia_group(k,l) (h:A->B)
                      (ring_of_integers l)
                      (ideal_pow (ring_of_integers l) Q (i + 1))) <=>
          i + 1 <= v") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:num") THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool"), (← q r"a:B"), (← q r"s:A"), (← q r"f:B->B"), (← q r"i:num")] INERTIA_GROUP_IDEAL_POW_LOCAL_GENERATOR) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"ideal_pow (ring_of_integers l) Q (i + 1):B->bool"), (← q r"(f:B->B) a"), (← q r"a:B")] IN_RING_IDEAL_SUB_SYM) THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW, RING_OF_INTEGERS] THEN ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC, DISCH_THEN SUBST1_TAC] THEN EXPAND_TAC "v" THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"ring_sub l a ((f:B->B) a)"), (← q r"i + 1")] DEDEKIND_IN_IDEAL_POW_VALUATION) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"v:num <= n") ASSUME_TAC THENL [MATCH_MP_TAC r17 THEN FIRST_ASSUM ((fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) o (checkM (fun th => (do if ← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); pure (is_forall z8)) then (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); canM (fun z12 => (do let z13 ← (pure z12); find_termM (fun z14 => (do let z16 ← (pure z14); let z15 ← (q r"v:num"); pure (z15 == z16))) z13)) z10) else pure false)))) THEN FIRST_ASSUM ((fun th => REWRITE_TAC [th]) o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_eq z2)) then (do let z7 ← (q r"{I:B->B}"); let z6 ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (rhs z4)); pure (z6 == z7)) else pure false)))) THEN REWRITE_TAC [IN_SING] THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN ASM_REWRITE_TAC [r1] THEN SUBGOAL_THEN (← q r"{i | i < (n:num) /\ i < v} = {i | i < v}") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN UNDISCH_TAC (← q r"v:num <= n") THEN ARITH_TAC, REWRITE_TAC [CARD_NUMSEG_LT]])

  let NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_LT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(s:(B->B)->bool) INTER t = s <=> s SUBSET t")
    prove
      r"!(h:A->B) k l p Q n.
          number_field l /\ galois_extension(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
          group_carrier(inertia_group(k,l) h (ring_of_integers l)
                          (ideal_pow (ring_of_integers l) Q (n + 1))) = {I}
          ==> ideal_valuation (ring_of_integers l) Q
                (number_field_different (k,l) h) =
              nsum {i | i < n}
                (\i. CARD(group_carrier(inertia_group(k,l) h (ring_of_integers l)
                            (ideal_pow (ring_of_integers l) Q (i + 1)))) - 1)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN ABBREV_TAC (← q r"z = fixed_field l (group_carrier(decomposition_group(k,l) (h:A->B) Q))") THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool"), (← q r"z:B->bool")] NUMBER_FIELD_DECOMPOSITION_FIELD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"z:B->bool")] NUMBER_FIELD_INTERMEDIATE_FIELD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"z:B->bool"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z4 ← (q r"number_field(l:B ring)"); let z3 ← (do let z2 ← (pure th); pure (concl z2)); pure (z3 == z4)))))) THEN SUBGOAL_THEN (← q r"~(Q INTER z = {ring_0(subfield_generated l (z:B->bool))}) /\
      dedekind_domain(ring_of_integers(subfield_generated l (z:B->bool))) /\
      dedekind_domain(ring_of_integers(l:B ring)) /\
      ~(Q = {ring_0(l:B ring)})") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← CONJUNCT1 (← CONJUNCT2 SUBFIELD_GENERATED))] THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], SIMP_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"galois_extension(subfield_generated l z,l) (I:B->B)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"I:B->B"), (← q r"k:A ring"), (← q r"subfield_generated l (z:B->bool)"), (← q r"l:B ring")] GALOIS_EXTENSION_INTERMEDIATE) THEN REWRITE_TAC [I_O_ID, field_extension] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"subfield_generated l (z:B->bool)"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"I:B->B")] NUMBER_FIELD_DIFFERENT_TOWER) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], REWRITE_TAC [I_O_ID]] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated l (z:B->bool)"), (← q r"l:B ring"), (← q r"I:B->B"), (← q r"number_field_different (k,subfield_generated l z)
                      (h:A->B)")] RING_OF_INTEGERS_IDEAL_EXTENSION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_IDEAL_NUMBER_FIELD_DIFFERENT], DISCH_THEN (ASSUME_TAC o CONJUNCT2)] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"subfield_generated l (z:B->bool)"), (← q r"h:A->B")] NUMBER_FIELD_DIFFERENT_NONZERO) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"subfield_generated l (z:B->bool)"), (← q r"l:B ring"), (← q r"I:B->B")] NUMBER_FIELD_DIFFERENT_NONZERO) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"number_field_different (subfield_generated l z,l) (I:B->B)"), (← q r"ideal_generated (ring_of_integers l)
                      (IMAGE (I:B->B)
                        (number_field_different (k,subfield_generated l z)
                           (h:A->B)))")] IDEAL_VALUATION_IDEAL_PROD) THEN ANTS_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS, RING_IDEAL_NUMBER_FIELD_DIFFERENT, RING_IDEAL_IDEAL_GENERATED] THEN ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN SUBGOAL_THEN (← q r"ideal_valuation (ring_of_integers l) Q
        (ideal_generated (ring_of_integers l)
           (IMAGE (I:B->B)
             (number_field_different (k,subfield_generated l z) (h:A->B)))) =
      0") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"subfield_generated l (z:B->bool)"), (← q r"l:B ring"), (← q r"I:B->B"), (← q r"Q INTER (z:B->bool)"), (← q r"Q:B->bool"), (← q r"number_field_different (k,subfield_generated l z)
                        (h:A->B)")] NUMBER_FIELD_IDEAL_VALUATION_EXTENSION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_IDEAL_NUMBER_FIELD_DIFFERENT, IMAGE_I] THEN SET_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [MULT_EQ_0] THEN DISJ2_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers(subfield_generated l (z:B->bool))"), (← q r"Q INTER (z:B->bool)"), (← q r"number_field_different (k,subfield_generated l z)
                        (h:A->B)"), (← q r"1")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_IDEAL_NUMBER_FIELD_DIFFERENT], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers(subfield_generated l (z:B->bool))"), (← q r"Q INTER (z:B->bool)")] IDEAL_POW_1) THEN ANTS_TAC THENL [MATCH_MP_TAC PRIME_IMP_RING_IDEAL THEN ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"subfield_generated l (z:B->bool)"), (← q r"h:A->B"), (← q r"Q INTER (z:B->bool)")] NUMBER_FIELD_DIFFERENT_RAMIFIED) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, REWRITE_TAC [ADD_CLAUSES]] THEN SUBGOAL_THEN (← q r"!i. group_carrier(inertia_group(subfield_generated l z,l) (I:B->B)
                         (ring_of_integers l)
                         (ideal_pow (ring_of_integers l) Q (i + 1))) =
          group_carrier(inertia_group(k,l) (h:A->B) (ring_of_integers l)
                         (ideal_pow (ring_of_integers l) Q (i + 1)))") ASSUME_TAC THENL [X_GEN_TAC (← q r"i:num") THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"z:B->bool"), (← q r"ideal_pow (ring_of_integers l) Q (i + 1):B->bool")] INERTIA_GROUP_INTERMEDIATE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING, RING_IDEAL_IDEAL_POW, GALOIS_GROUP_RING_OF_INTEGERS], DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC [r1] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"i:num")] INERTIA_GROUP_IDEAL_POW) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING, GALOIS_GROUP_RING_OF_INTEGERS], DISCH_THEN SUBST1_TAC] THEN SIMP_TAC [SUBSET, IN_ELIM_THM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:B->B"), (← q r"subfield_generated l (z:B->bool)"), (← q r"l:B ring"), (← q r"Q INTER (z:B->bool)"), (← q r"Q:B->bool"), (← q r"n:num")] NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_ONE_PRIME) THEN ASM_REWRITE_TAC [IMAGE_I])

  let NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA ← prove
    r"!(h:A->B) k l p Q.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
        ==> ideal_valuation (ring_of_integers l) Q
              (number_field_different (k,l) h) =
            nsum (:num)
              (\i. CARD(group_carrier(inertia_group(k,l) h (ring_of_integers l)
                          (ideal_pow (ring_of_integers l) Q (i + 1)))) - 1)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_IMP_FIELD_EXTENSION, field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool")] INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING, GALOIS_GROUP_RING_OF_INTEGERS] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN MP_TAC (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_SIMP_TAC [], DISCH_THEN (X_CHOOSE_TAC (← q r"n:num"))] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool"), (← q r"n:num")] NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_LT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN REWRITE_TAC [SUBSET_UNIV, IN_UNIV, IN_ELIM_THM, NOT_LT] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [CARD_SING, SUB_REFL])

  -- @@RETURN BEGIN
  return { NSUM_CARD_SUBSETS_DELETE, INERTIA_GROUP_IDEAL_POW_LOCAL_GENERATOR,
           NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_ONE_PRIME,
           NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_LT,
           NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- hilbert_formula.ml phrases from line 744 to 906                        -/
/- ---------------------------------------------------------------------- -/

structure HilbertFormula02 where
  -- @@FIELDS
  NUMBER_FIELD_DIFFERENT_VALUATION_GALOIS_OVERFIELD : thm
  NUMBER_FIELD_DIFFERENT_VALUATION_TAME : thm
  NUMBER_FIELD_DIFFERENT_VALUATION_WILD : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupHilbertFormula02 [HolBase] (D : HilbertFormulaDeps) (BHilbertFormula01 : HilbertFormula01) :
    ExceptT String IO HilbertFormula02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC,
        NUM_REDUCE_CONV, SET_RULE, SET_TAC, TAUT, .. } := D
  let { AND_FORALL_THM, CARD_EQ_0, CARD_PSUBSET, CARD_SUBSET,
        DEDEKIND_RING_OF_INTEGERS, EQ_MULT_LCANCEL, EXISTS_UNIQUE_THM,
        FIELD_IMP_NONTRIVIAL_RING, FIELD_RING_HOMOMORPHISM_MONOMORPHISM, FINITE_DELETE,
        FINITE_GALOIS_GROUP, FINITE_INTER, FINITE_NUMSEG_LT, FINITE_SUBSET,
        FUN_IN_IMAGE, GALOIS_EXTENSION_INTERMEDIATE, GALOIS_GROUP_I,
        GALOIS_GROUP_RING_OF_INTEGERS, GALOIS_IMP_FIELD_EXTENSION,
        GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET, GROUP_ID, GROUP_INV, GROUP_MUL,
        IDEAL_GENERATED_SUBSET, IDEAL_GENERATED_SUBSET_CARRIER, IDEAL_POW_1,
        IDEAL_VALUATION_IDEAL_PROD, IMAGE_SUBSET, IMAGE_o, INERTIA_GROUP,
        INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL, INERTIA_GROUP_IDEAL_POW_MONO,
        INERTIA_GROUP_TOWER, INERTIA_GROUP_WILD_SUBSET, INTER_SUBSET, IN_DELETE,
        IN_ELIM_THM, IN_INTER, LEFT_SUB_DISTRIB, LE_MULT_LCANCEL,
        MAXIMAL_IMP_PRIME_IDEAL, MAXIMAL_SUPERIDEAL_EXISTS, MEMBER_NOT_EMPTY,
        MONO_EXISTS, MULT_AC, MULT_CLAUSES, MULT_EQ_0, NOT_LT, NSUM_ADD, NSUM_DELETE,
        NSUM_EQ_0, NUMBER_FIELD_DECOMPOSITION_GROUP, NUMBER_FIELD_DIFFERENT_NONZERO,
        NUMBER_FIELD_DIFFERENT_TOWER, NUMBER_FIELD_GALOIS_CLOSURE,
        NUMBER_FIELD_HOMOMORPHIC_PREIMAGE, NUMBER_FIELD_IDEAL_VALUATION_EXTENSION,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_PRIME_IDEAL_ABOVE,
        NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO, NUMBER_FIELD_RAMIFICATION_INDEX_TOWER,
        NUMBER_FIELD_TOWER_LAW, PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_RING_IDEAL, PSUBSET,
        RING_HOMOMORPHISM_COMPOSE, RING_HOMOMORPHISM_RING_OF_INTEGERS,
        RING_HOMOMORPHISM_RING_OF_NUM, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IDEAL_POW, RING_IDEAL_NUMBER_FIELD_DIFFERENT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FRACTION_FIELD, RING_OF_INTEGERS_IDEAL_EXTENSION,
        RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME, RING_OF_INTEGERS_PRIME_IDEAL_ABOVE,
        RING_OF_INTEGERS_SUBRING, RING_OF_NUM_IN_PRIME_IDEAL, SING_SUBSET, SUBSET,
        SUBSET_INTER, SUBSET_TRANS, SUB_REFL, field_extension, inertia_group,
        proper_ideal, ring_homomorphism, subgroup_of, .. } := D.core1
  let { NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_LT, .. } := BHilbertFormula01
  -- @@SCOPE END

  let NUMBER_FIELD_DIFFERENT_VALUATION_GALOIS_OVERFIELD ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r6 ← ARITH_RULE (← q r"1 <= n <=> ~(n:num = 0)")
    let r7 ← ARITH_RULE (← q r"1 <= b /\ b:num <= a ==> a - 1 = (b - 1) + (a - b)")
    let r8 ← SET_RULE (← q r"{a:C->C} INTER s = {a} <=> a IN s")
    prove
      r"!k:A ring l:B ring m:C ring h j p Q P n.
          field l /\ number_field m /\
          ring_homomorphism(k,l) h /\ ring_homomorphism(l,m) j /\
          galois_extension(k,m) (j o h) /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q /\
          prime_ideal (ring_of_integers m) P /\ IMAGE j Q SUBSET P /\
          group_carrier(inertia_group(k,m) (j o h) (ring_of_integers m)
                         (ideal_pow (ring_of_integers m) P (n + 1))) = {I}
          ==> ramification_index (ring_of_integers l,ring_of_integers m) j P *
              ideal_valuation (ring_of_integers l) Q
                (number_field_different (k,l) h) =
              nsum {i | i < n}
               (\i. CARD(group_carrier(inertia_group(k,m) (j o h)
                           (ring_of_integers m)
                           (ideal_pow (ring_of_integers m) P (i + 1)))) -
                    CARD(group_carrier(inertia_group(l,m) j
                           (ring_of_integers m)
                           (ideal_pow (ring_of_integers m) P (i + 1)))))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field(k:A ring)") ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension], ALL_TAC] THEN SUBGOAL_THEN (← q r"number_field(l:B ring)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"j:B->C")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z11 ← (q r"number_field(m:C ring)"); let z10 ← (do let z9 ← (pure th); pure (concl z9)); pure (z10 == z11)))))) THEN SUBGOAL_THEN (← q r"ring_homomorphism(k,m) ((j:B->C) o (h:A->B))") ASSUME_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"l:B ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE ((j:B->C) o (h:A->B)) p SUBSET P") ASSUME_TAC THENL [REWRITE_TAC [IMAGE_o] THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC (← q r"IMAGE (j:B->C) Q") THEN ASM_SIMP_TAC [IMAGE_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"galois_extension(l,m) (j:B->C)") ASSUME_TAC THENL [MATCH_MP_TAC GALOIS_EXTENSION_INTERMEDIATE THEN MAP_EVERY EXISTS_TAC [(← q r"h:A->B"), (← q r"k:A ring")] THEN ASM_REWRITE_TAC [field_extension] THEN CONJ_TAC THEN MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(Q = {ring_0(l:B ring)})") ASSUME_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"h:A->B"), (← q r"p:A->bool")] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"FINITE(group_carrier(galois_group(k,m) ((j:B->C) o (h:A->B)))) /\
      (I:C->C) IN group_carrier(galois_group(l,m) j)") STRIP_ASSUME_TAC THENL [REWRITE_TAC [GALOIS_GROUP_I] THEN MATCH_MP_TAC FINITE_GALOIS_GROUP THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"m:C ring"), (← q r"(j:B->C) o (h:A->B)")] NUMBER_FIELD_TOWER_LAW) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. group_carrier(inertia_group(l,m) (j:B->C) (ring_of_integers m)
                         (ideal_pow (ring_of_integers m) P (i + 1))) =
          group_carrier(inertia_group(k,m) (j o (h:A->B)) (ring_of_integers m)
                         (ideal_pow (ring_of_integers m) P (i + 1))) INTER
          group_carrier(galois_group(l,m) j)") ASSUME_TAC THENL [GEN_TAC THEN MATCH_MP_TAC INERTIA_GROUP_TOWER THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING, RING_IDEAL_IDEAL_POW, GALOIS_GROUP_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"j:B->C"), (← q r"l:B ring"), (← q r"m:C ring"), (← q r"Q:B->bool"), (← q r"P:C->bool"), (← q r"n:num")] NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_LT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [r8], DISCH_THEN (LABEL_TAC "hl")] THEN MP_TAC (← ISPECL [(← q r"(j:B->C) o (h:A->B)"), (← q r"k:A ring"), (← q r"m:C ring"), (← q r"p:A->bool"), (← q r"P:C->bool"), (← q r"n:num")] NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_LT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (LABEL_TAC "hk")] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"m:C ring"), (← q r"h:A->B"), (← q r"j:B->C")] NUMBER_FIELD_DIFFERENT_TOWER) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (LABEL_TAC "tower")] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"j:B->C"), (← q r"number_field_different (k,l) (h:A->B)")] RING_OF_INTEGERS_IDEAL_EXTENSION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_IDEAL_NUMBER_FIELD_DIFFERENT], DISCH_THEN (ASSUME_TAC o CONJUNCT2)] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_DIFFERENT_NONZERO) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"j:B->C")] NUMBER_FIELD_DIFFERENT_NONZERO) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers m:C ring"), (← q r"P:C->bool"), (← q r"number_field_different (l,m) (j:B->C)"), (← q r"ideal_generated (ring_of_integers m)
                      (IMAGE (j:B->C) (number_field_different (k,l) (h:A->B)))")] IDEAL_VALUATION_IDEAL_PROD) THEN ANTS_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS, RING_IDEAL_NUMBER_FIELD_DIFFERENT, RING_IDEAL_IDEAL_GENERATED] THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS] THEN MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"(j:B->C) o (h:A->B)"), (← q r"p:A->bool")] THEN ASM_REWRITE_TAC [], DISCH_THEN (LABEL_TAC "prod")] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"j:B->C"), (← q r"Q:B->bool"), (← q r"P:C->bool"), (← q r"number_field_different (k,l) (h:A->B)")] NUMBER_FIELD_IDEAL_VALUATION_EXTENSION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_IDEAL_NUMBER_FIELD_DIFFERENT], DISCH_THEN (LABEL_TAC "ext")] THEN SUBGOAL_THEN (← q r"!i. CARD(group_carrier(inertia_group(k,m) ((j:B->C) o (h:A->B))
                (ring_of_integers m)
                (ideal_pow (ring_of_integers m) P (i + 1)))) - 1 =
          (CARD(group_carrier(inertia_group(l,m) j (ring_of_integers m)
                (ideal_pow (ring_of_integers m) P (i + 1)))) - 1) +
          (CARD(group_carrier(inertia_group(k,m) (j o h) (ring_of_integers m)
                (ideal_pow (ring_of_integers m) P (i + 1)))) -
           CARD(group_carrier(inertia_group(l,m) j (ring_of_integers m)
                (ideal_pow (ring_of_integers m) P (i + 1)))))") (LABEL_TAC "pt") THENL [X_GEN_TAC (← q r"i:num") THEN MATCH_MP_TAC r7 THEN SUBGOAL_THEN (← q r"FINITE(group_carrier(inertia_group(k,m) ((j:B->C) o (h:A->B))
          (ring_of_integers m) (ideal_pow (ring_of_integers m) P (i + 1))))") ASSUME_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"group_carrier(galois_group(k,m) ((j:B->C) o (h:A->B)))") THEN ASM_REWRITE_TAC [inertia_group, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET], ALL_TAC] THEN CONJ_TAC THENL [REWRITE_TAC [r6] THEN ASM_SIMP_TAC [CARD_EQ_0, FINITE_INTER] THEN REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY)] THEN EXISTS_TAC (← q r"I:C->C") THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o ((SPEC (← q r"i:num")) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do pure (Prod.snd (← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (dest_forall z4))))); pure (is_eq z3)) else pure false)))))) THEN MP_TAC (← ISPEC (← q r"inertia_group(l,m) (j:B->C) (ring_of_integers m)
            (ideal_pow (ring_of_integers m) P (i + 1))") GROUP_ID) THEN REWRITE_TAC [(← CONJUNCT1 (← CONJUNCT2 INERTIA_GROUP))], ASM_REWRITE_TAC [] THEN MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC [INTER_SUBSET]], ALL_TAC] THEN REMOVE_THEN "hk" MP_TAC THEN REMOVE_THEN "tower" SUBST1_TAC THEN REMOVE_THEN "prod" SUBST1_TAC THEN REMOVE_THEN "hl" SUBST1_TAC THEN REMOVE_THEN "ext" SUBST1_TAC THEN REMOVE_THEN "pt" (fun th => REWRITE_TAC [th]) THEN SIMP_TAC [NSUM_ADD, FINITE_NUMSEG_LT] THEN ARITH_TAC)

  let (NUMBER_FIELD_DIFFERENT_VALUATION_TAME, NUMBER_FIELD_DIFFERENT_VALUATION_WILD) ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"(e1:num) * v = e1 * (e2 - 1)"
    let q2 ← q r"(G:num->(B#num->B#num)->bool) i INTER H = G i"
    let q3 ← q r"(G:num->(B#num->B#num)->bool) 1 SUBSET G' 0 <=>
          ~((c:num) divides e2)"
    let q4 ← q r"(G:num->(B#num->B#num)->bool) i SUBSET G 1"
    let q5 ← q r"i:num"
    let q6 ← q r"nsum ({i | i < N + 1} DELETE 0)
          (\i. CARD((G:num->(B#num->B#num)->bool) i) -
               CARD((G':num->(B#num->B#num)->bool) i)) = 0"
    let q7 ← q r"(e1:num) * v <= e1 * (e2 - 1)"
    let v8 ← GSYM NOT_LT
    let q9 ← q r"1"
    let q10 ← q r"{i | i < N + 1} DELETE 0"
    let q11 ← q r"\i. CARD((G:num->(B#num->B#num)->bool) i) -
             CARD((G':num->(B#num->B#num)->bool) i)"
    let v12 ← ISPECL [q11, q10, q9] NSUM_DELETE
    let q13 ← q r"a:num < b ==> 1 <= b - a"
    let r14 ← ARITH_RULE q13
    let q15 ← q r"1 <= CARD((G:num->(B#num->B#num)->bool) 1) -
             CARD((G':num->(B#num->B#num)->bool) 1)"
    let q16 ← q r"(G:num->(B#num->B#num)->bool) 1 = {I}"
    let q17 ← q r"~((G:num->(B#num->B#num)->bool) 1 SUBSET H)"
    let q18 ← q r"~(N:num = 0)"
    let q19 ← q r"(G:num->(B#num->B#num)->bool) 1 SUBSET G' 0 <=>
          ~((c:num) divides e2)"
    let q20 ← q r"~((G:num->(B#num->B#num)->bool) 1 SUBSET H)"
    let q21 ← q r"(c:num) divides e2"
    let q22 ← q r"CARD((G':num->(B#num->B#num)->bool) 0) = e1"
    let v23 ← ASSUME q22
    let q24 ← q r"CARD((G:num->(B#num->B#num)->bool) 0) = e1 * e2"
    let v25 ← ASSUME q24
    let q32 ← q r"0"
    let q33 ← q r"{i | i < N + 1}"
    let q34 ← q r"\i. CARD((G:num->(B#num->B#num)->bool) i) -
           CARD((G':num->(B#num->B#num)->bool) i)"
    let v35 ← ISPECL [q34, q33, q32] NSUM_DELETE
    let q36 ← q r"(G:num->(B#num->B#num)->bool) 0"
    let v37 ← ISPEC q36 CARD_EQ_0
    let q38 ← q r"(G':num->(B#num->B#num)->bool) 0"
    let v39 ← ISPEC q38 CARD_EQ_0
    let q40 ← q r"~(e1:num = 0) /\ ~(e2:num = 0)"
    let q41 ← q r"(I:B#num->B#num) IN H /\
      (!i. (I:B#num->B#num) IN (G:num->(B#num->B#num)->bool) i) /\
      (!i. FINITE((G':num->(B#num->B#num)->bool) i))"
    let v42 ← CONJUNCT2 INERTIA_GROUP
    let v43 ← CONJUNCT1 v42
    let q44 ← q r"inertia_group(l,m) (j:B->B#num) (ring_of_integers m)
            (ideal_pow (ring_of_integers m) P (i + 1))"
    let v45 ← ISPEC q44 GROUP_ID
    let q46 ← q r"group_carrier(galois_group(k,m) ((j:B->B#num) o (h:A->B)))"
    let q47 ← q r"(!i. (G':num->(B#num->B#num)->bool) i = G i INTER H) /\
      (!i. FINITE((G:num->(B#num->B#num)->bool) i)) /\
      (!i i'. i <= i' ==> (G:num->(B#num->B#num)->bool) i' SUBSET G i) /\
      (!i. (I:B#num->B#num) IN G' i) /\
      CARD((G:num->(B#num->B#num)->bool) 0) = e1 * e2 /\
      CARD((G':num->(B#num->B#num)->bool) 0) = e1 /\
      (G 1 SUBSET G' 0 <=> ~(c divides e2)) /\
      (!i. N <= i ==> G i = {I:B#num->B#num}) /\
      e1 * v = nsum {i | i < N + 1} (\i. CARD(G i) - CARD(G' i))"
    let q48 ← q r"c = ring_char(quotient_ring (ring_of_integers l) (Q:B->bool))"
    let q49 ← q r"v = ideal_valuation (ring_of_integers l) Q
            (number_field_different (k,l) (h:A->B))"
    let q50 ← q r"e2 = ramification_index (ring_of_integers k,ring_of_integers l)
             (h:A->B) Q"
    let q51 ← q r"e1 = ramification_index (ring_of_integers l,ring_of_integers m)
             (j:B->B#num) P"
    let q52 ← q r"H = group_carrier(galois_group(l,m) (j:B->B#num))"
    let q53 ← q r"(!i. (G:num->(B#num->B#num)->bool) i =
           group_carrier(inertia_group(k,m) ((j:B->B#num) o (h:A->B))
              (ring_of_integers m)
              (ideal_pow (ring_of_integers m) P (i + 1)))) /\
      (!i. (G':num->(B#num->B#num)->bool) i =
           group_carrier(inertia_group(l,m) (j:B->B#num)
              (ring_of_integers m)
              (ideal_pow (ring_of_integers m) P (i + 1))))"
    let q54 ← q r"G' = \i. group_carrier(inertia_group(l,m) (j:B->B#num)
                (ring_of_integers m)
                (ideal_pow (ring_of_integers m) P (i + 1)))"
    let q55 ← q r"G = \i. group_carrier(inertia_group(k,m) ((j:B->B#num) o (h:A->B))
                (ring_of_integers m)
                (ideal_pow (ring_of_integers m) P (i + 1)))"
    let q56 ← q r"N + 1"
    let q57 ← q r"P:B#num->bool"
    let q58 ← q r"Q:B->bool"
    let q59 ← q r"p:A->bool"
    let q60 ← q r"j:B->B#num"
    let q61 ← q r"h:A->B"
    let q62 ← q r"m:(B#num)ring"
    let q63 ← q r"l:B ring"
    let q64 ← q r"k:A ring"
    let v65 ← ISPECL [q64, q63, q62, q61, q60, q59, q58, q57, q56] NUMBER_FIELD_DIFFERENT_VALUATION_GALOIS_OVERFIELD
    let q66 ← q r"N:num"
    let q67 ← q r"P:B#num->bool"
    let q68 ← q r"ring_of_integers m:(B#num)ring"
    let q69 ← q r"m:(B#num)ring"
    let q70 ← q r"k:A ring"
    let q71 ← q r"(j:B->B#num) o (h:A->B)"
    let v72 ← ISPECL [q71, q70, q69, q68, q67] INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL
    let q73 ← q r"ramification_index (ring_of_integers k,ring_of_integers l)
                      (h:A->B) Q"
    let q74 ← q r"group_carrier(inertia_group(l,m) (j:B->B#num)
                      (ring_of_integers m) P)"
    let q75 ← q r"P:B#num->bool"
    let q76 ← q r"ring_of_integers m:(B#num)ring"
    let q77 ← q r"m:(B#num)ring"
    let q78 ← q r"k:A ring"
    let q79 ← q r"(j:B->B#num) o (h:A->B)"
    let v80 ← ISPECL [q79, q78, q77, q76, q75, q74, q73] INERTIA_GROUP_WILD_SUBSET
    let q81 ← q r"P:B#num->bool"
    let q82 ← q r"ring_of_integers m:(B#num)ring"
    let q83 ← q r"m:(B#num)ring"
    let q84 ← q r"l:B ring"
    let q85 ← q r"k:A ring"
    let q86 ← q r"j:B->B#num"
    let q87 ← q r"h:A->B"
    let v88 ← ISPECL [q87, q86, q85, q84, q83, q82, q81] INERTIA_GROUP_TOWER
    let v89 ← CONJUNCT2 INERTIA_GROUP
    let q90 ← q r"inertia_group(l,m) (j:B->B#num) (ring_of_integers m) P"
    let v91 ← ISPEC q90 GROUP_MUL
    let q92 ← q r"inertia_group(l,m) (j:B->B#num) (ring_of_integers m) P"
    let v93 ← ISPEC q92 GROUP_INV
    let q94 ← q r"inertia_group(l,m) (j:B->B#num) (ring_of_integers m) P"
    let v95 ← ISPEC q94 GROUP_ID
    let v96 ← CONJUNCT2 INERTIA_GROUP
    let q97 ← q r"group_carrier(inertia_group(l,m) (j:B->B#num) (ring_of_integers m) P)
      subgroup_of inertia_group(k,m) (j o (h:A->B)) (ring_of_integers m) P"
    let q98 ← q r"P:B#num->bool"
    let q99 ← q r"Q:B->bool"
    let q100 ← q r"j:B->B#num"
    let q101 ← q r"h:A->B"
    let q102 ← q r"m:(B#num)ring"
    let q103 ← q r"l:B ring"
    let q104 ← q r"k:A ring"
    let v105 ← ISPECL [q104, q103, q102, q101, q100, q99, q98] NUMBER_FIELD_RAMIFICATION_INDEX_TOWER
    let q106 ← q r"P:B#num->bool"
    let q107 ← q r"Q:B->bool"
    let q108 ← q r"m:(B#num)ring"
    let q109 ← q r"l:B ring"
    let q110 ← q r"j:B->B#num"
    let v111 ← ISPECL [q110, q109, q108, q107, q106] NUMBER_FIELD_DECOMPOSITION_GROUP
    let q112 ← q r"P:B#num->bool"
    let q113 ← q r"p:A->bool"
    let q114 ← q r"m:(B#num)ring"
    let q115 ← q r"k:A ring"
    let q116 ← q r"(j:B->B#num) o (h:A->B)"
    let v117 ← ISPECL [q116, q115, q114, q113, q112] NUMBER_FIELD_DECOMPOSITION_GROUP
    let q118 ← q r"q:num"
    let q119 ← q r"P:B#num->bool"
    let q120 ← q r"ring_of_integers m:(B#num)ring"
    let v121 ← ISPECL [q120, q119, q118] RING_OF_NUM_IN_PRIME_IDEAL
    let q122 ← q r"q:num"
    let q123 ← q r"Q:B->bool"
    let q124 ← q r"ring_of_integers l:B ring"
    let v125 ← ISPECL [q124, q123, q122] RING_OF_NUM_IN_PRIME_IDEAL
    let q132 ← q r"q:num"
    let q133 ← q r"ring_of_num m q IN (P:B#num->bool)"
    let q134 ← q r"q:num"
    let q135 ← q r"Q:B->bool"
    let q136 ← q r"l:B ring"
    let v137 ← ISPECL [q136, q135] RING_OF_INTEGERS_PRIME_IDEAL_ABOVE
    let q138 ← q r"ring_char(quotient_ring (ring_of_integers m) (P:B#num->bool)) =
      ring_char(quotient_ring (ring_of_integers l) (Q:B->bool))"
    let q139 ← q r"m:(B#num)ring"
    let v140 ← ISPEC q139 RING_OF_INTEGERS_FRACTION_FIELD
    let q141 ← q r"(j:B->B#num) o (h:A->B)"
    let q142 ← q r"m:(B#num)ring"
    let q143 ← q r"k:A ring"
    let v144 ← ISPECL [q143, q142, q141] NUMBER_FIELD_TOWER_LAW
    let q145 ← q r"finite_extension(k,m) ((j:B->B#num) o (h:A->B)) /\
      dedekind_domain(ring_of_integers m:(B#num)ring) /\
      field_of_fractions(ring_of_integers m:(B#num)ring,m) I"
    let q146 ← q r"P:B#num->bool"
    let q147 ← q r"p:A->bool"
    let q148 ← q r"m:(B#num)ring"
    let q149 ← q r"k:A ring"
    let q150 ← q r"(j:B->B#num) o (h:A->B)"
    let v151 ← ISPECL [q150, q149, q148, q147, q146] NUMBER_FIELD_PRIME_IDEAL_ABOVE
    let q152 ← q r"k:A ring"
    let q153 ← q r"h:A->B"
    let q154 ← q r"galois_extension(l,m) (j:B->B#num)"
    let q155 ← q r"IMAGE (j:B->B#num) Q"
    let q156 ← q r"IMAGE ((j:B->B#num) o (h:A->B)) p SUBSET P"
    let q157 ← q r"l:B ring"
    let q158 ← q r"ring_homomorphism(k,m) ((j:B->B#num) o (h:A->B))"
    let q159 ← q r"j:B->B#num"
    let q160 ← q r"m:(B#num)ring"
    let q161 ← q r"l:B ring"
    let v162 ← ISPECL [q161, q160, q159] RING_HOMOMORPHISM_RING_OF_INTEGERS
    let q163 ← q r"IMAGE (j:B->B#num) (ring_carrier(ring_of_integers l))"
    let q164 ← q r"(s:B#num->bool) SUBSET c ==> c INTER s SUBSET g ==> s SUBSET g"
    let r165 ← SET_RULE q164
    let q166 ← q r"IMAGE (j:B->B#num) Q"
    let q167 ← q r"ring_of_integers m:(B#num)ring"
    let v168 ← ISPECL [q167, q166] IDEAL_GENERATED_SUBSET_CARRIER
    let q169 ← q r"ideal_generated (ring_of_integers m) (IMAGE (j:B->B#num) Q)"
    let q170 ← q r"P:B#num->bool"
    let q171 ← q r"ideal_generated (ring_of_integers m)
                        (IMAGE (j:B->B#num) Q)"
    let q172 ← q r"ring_of_integers m:(B#num)ring"
    let v173 ← ISPECL [q172, q171] MAXIMAL_SUPERIDEAL_EXISTS
    let q174 ← q r"Q:B->bool"
    let q175 ← q r"j:B->B#num"
    let q176 ← q r"m:(B#num)ring"
    let q177 ← q r"l:B ring"
    let v178 ← ISPECL [q177, q176, q175, q174] RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME
    let q179 ← q r"?P. prime_ideal (ring_of_integers m) P /\
          IMAGE (j:B->B#num) Q SUBSET P"
    let q180 ← q r"p:A->bool"
    let q181 ← q r"h:A->B"
    let q182 ← q r"k:A ring"
    let q183 ← q r"~(Q = {ring_0(l:B ring)})"
    let q187 ← q r"j:B->B#num"
    let q188 ← q r"m:(B#num)ring"
    let q189 ← q r"h:A->B"
    let q190 ← q r"l:B ring"
    let q191 ← q r"k:A ring"
    let v192 ← ISPECL [q191, q190, q189] NUMBER_FIELD_GALOIS_CLOSURE
    let p196 ← prove r"!k:A ring l:B ring h p Q.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
        ==> 1 <= ramification_index (ring_of_integers k,ring_of_integers l)
                   h Q /\
            (~(ring_char(quotient_ring (ring_of_integers l) Q) divides
               ramification_index (ring_of_integers k,ring_of_integers l) h Q)
             ==> ideal_valuation (ring_of_integers l) Q
                   (number_field_different (k,l) h) =
                 ramification_index (ring_of_integers k,ring_of_integers l)
                   h Q - 1) /\
            (ring_char(quotient_ring (ring_of_integers l) Q) divides
             ramification_index (ring_of_integers k,ring_of_integers l) h Q
             ==> ramification_index (ring_of_integers k,ring_of_integers l)
                   h Q <=
                 ideal_valuation (ring_of_integers l) Q
                   (number_field_different (k,l) h))" (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z195 ← (q r"number_field(l:B ring)"); let z194 ← (do let z193 ← (pure th); pure (concl z193)); pure (z194 == z195)))))) THEN MP_TAC v192 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN q188 (X_CHOOSE_THEN q187 STRIP_ASSUME_TAC)) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z186 ← (q r"number_field(m:(B#num)ring)"); let z185 ← (do let z184 ← (pure th); pure (concl z184)); pure (z185 == z186)))))) THEN SUBGOAL_THEN q183 ASSUME_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO THEN MAP_EVERY EXISTS_TAC [q182, q181, q180] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q179 STRIP_ASSUME_TAC THENL [MP_TAC v178 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC v173 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [proper_ideal, PSUBSET, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_SUBSET], ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q170 THEN STRIP_TAC THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL] THEN TRANS_TAC SUBSET_TRANS q169 THEN ASM_REWRITE_TAC [] THEN MP_TAC v168 THEN MATCH_MP_TAC r165 THEN TRANS_TAC SUBSET_TRANS q163 THEN CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_SIMP_TAC [PRIME_IDEAL_IMP_SUBSET], MP_TAC v162 THEN ASM_REWRITE_TAC [] THEN SIMP_TAC [ring_homomorphism]], ALL_TAC] THEN SUBGOAL_THEN q158 ASSUME_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC q157 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q156 ASSUME_TAC THENL [REWRITE_TAC [IMAGE_o] THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC q155 THEN ASM_SIMP_TAC [IMAGE_SUBSET], ALL_TAC] THEN SUBGOAL_THEN q154 ASSUME_TAC THENL [MATCH_MP_TAC GALOIS_EXTENSION_INTERMEDIATE THEN MAP_EVERY EXISTS_TAC [q153, q152] THEN ASM_REWRITE_TAC [field_extension] THEN CONJ_TAC THEN MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING], ALL_TAC] THEN MP_TAC v151 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN SUBGOAL_THEN q145 STRIP_ASSUME_TAC THENL [MP_TAC v144 THEN MP_TAC v140 THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN q138 ASSUME_TAC THENL [MP_TAC v137 THEN ASM_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN ((X_CHOOSE_THEN q134 STRIP_ASSUME_TAC) o CONJUNCT1) THEN SUBGOAL_THEN q133 ASSUME_TAC THENL [FIRST_ASSUM (SUBST1_TAC o (SYM o ((SPEC q132) o ((MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM) o (checkM (fun th => (do let z131 ← (q r"ring_homomorphism(l,m) (j:B->B#num)"); let z130 ← (do let z129 ← (pure th); pure (concl z129)); pure (z130 == z131)))))))) THEN FIRST_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do let z128 ← (q r"IMAGE (j:B->B#num) Q SUBSET P"); let z127 ← (do let z126 ← (pure th); pure (concl z126)); pure (z127 == z128)))))) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC v125 THEN MP_TAC v121 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN MESON_TAC [], ALL_TAC] THEN MP_TAC v117 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (ASSUME_TAC o (CONJUNCT1 o CONJUNCT2))] THEN MP_TAC v111 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (ASSUME_TAC o (CONJUNCT1 o CONJUNCT2))] THEN MP_TAC v105 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN SUBGOAL_THEN q97 ASSUME_TAC THENL [REWRITE_TAC [subgroup_of, v96] THEN MP_TAC v95 THEN MP_TAC v93 THEN MP_TAC v91 THEN REWRITE_TAC [v89] THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC [] THEN MP_TAC v88 THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING, PRIME_IMP_RING_IDEAL] THEN REWRITE_TAC [GALOIS_GROUP_RING_OF_INTEGERS], DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [INTER_SUBSET]], ALL_TAC] THEN MP_TAC v80 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING, GALOIS_GROUP_RING_OF_INTEGERS] THEN REWRITE_TAC [MULT_AC], ASM_REWRITE_TAC [] THEN DISCH_TAC] THEN MP_TAC v72 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING, GALOIS_GROUP_RING_OF_INTEGERS], DISCH_THEN (X_CHOOSE_TAC q66)] THEN MP_TAC v65 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC, DISCH_TAC] THEN ABBREV_TAC q55 THEN ABBREV_TAC q54 THEN SUBGOAL_THEN q53 STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["G", "G'"] THEN REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC q52 THEN ABBREV_TAC q51 THEN ABBREV_TAC q50 THEN ABBREV_TAC q49 THEN ABBREV_TAC q48 THEN SUBGOAL_THEN q47 MP_TAC THENL [REPEAT CONJ_TAC THENL [ASM_REWRITE_TAC [] THEN GEN_TAC THEN EXPAND_TAC "H" THEN MATCH_MP_TAC INERTIA_GROUP_TOWER THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING, RING_IDEAL_IDEAL_POW, GALOIS_GROUP_RING_OF_INTEGERS], ASM_REWRITE_TAC [] THEN GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC q46 THEN REWRITE_TAC [inertia_group, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET] THEN ASM_SIMP_TAC [FINITE_GALOIS_GROUP], ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC INERTIA_GROUP_IDEAL_POW_MONO THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING, GALOIS_GROUP_RING_OF_INTEGERS], ASM_REWRITE_TAC [] THEN GEN_TAC THEN MP_TAC v45 THEN REWRITE_TAC [v43], ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC [IDEAL_POW_1, PRIME_IMP_RING_IDEAL], ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC [IDEAL_POW_1, PRIME_IMP_RING_IDEAL], ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC [IDEAL_POW_1, PRIME_IMP_RING_IDEAL], ASM_REWRITE_TAC [], ASM_REWRITE_TAC []], ALL_TAC] THEN POP_ASSUM_LIST (fun _ => ALL_TAC) THEN STRIP_TAC THEN SUBGOAL_THEN q41 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [IN_INTER, FINITE_INTER], ALL_TAC] THEN SUBGOAL_THEN q40 STRIP_ASSUME_TAC THENL [MP_TAC v39 THEN MP_TAC v37 THEN ASM_REWRITE_TAC [MULT_EQ_0] THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC v35 THEN ANTS_TAC THENL [REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN ARITH_TAC, ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z26 ← (do let z27 ← (pure th); pure (concl z27)); pure (is_eq z26)) then (do let z31 ← (q r"e1 * v:num"); let z30 ← (do let z28 ← (do let z29 ← (pure th); pure (concl z29)); liftExcept (lhs z28)); pure (z30 == z31)) else pure false))))) THEN REWRITE_TAC [] THEN REWRITE_TAC [v25, v23] THEN DISCH_TAC THEN ASM_CASES_TAC q21 THEN ASM_REWRITE_TAC [] THENL [SUBGOAL_THEN q20 ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC q19 THEN ASM_REWRITE_TAC [SUBSET_INTER] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q18 ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC q17 THEN REWRITE_TAC [] THEN SUBGOAL_THEN q16 SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ASM_REWRITE_TAC [SING_SUBSET]], ALL_TAC] THEN SUBGOAL_THEN q15 ASSUME_TAC THENL [MATCH_MP_TAC r14 THEN MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC [PSUBSET] THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC v12 THEN ANTS_TAC THENL [REWRITE_TAC [FINITE_DELETE, FINITE_NUMSEG_LT, IN_DELETE, IN_ELIM_THM] THEN ASM_ARITH_TAC, REWRITE_TAC [] THEN DISCH_TAC] THEN CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [v8] THEN DISCH_TAC THEN SUBGOAL_THEN q7 MP_TAC THENL [REWRITE_TAC [LE_MULT_LCANCEL] THEN ASM_ARITH_TAC, REWRITE_TAC [LEFT_SUB_DISTRIB, MULT_CLAUSES] THEN ASM_ARITH_TAC], SUBGOAL_THEN q6 ASSUME_TAC THENL [MATCH_MP_TAC NSUM_EQ_0 THEN X_GEN_TAC q5 THEN REWRITE_TAC [IN_DELETE, IN_ELIM_THM] THEN STRIP_TAC THEN REWRITE_TAC [] THEN SUBGOAL_THEN q4 MP_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN UNDISCH_TAC q3 THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN q2 (fun th => REWRITE_TAC [th, SUB_REFL]) THEN ASM SET_TAC [], ALL_TAC] THEN CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q1 MP_TAC THENL [REWRITE_TAC [LEFT_SUB_DISTRIB, MULT_CLAUSES] THEN ASM_ARITH_TAC, ASM_REWRITE_TAC [EQ_MULT_LCANCEL]]])
    let core := p196
    let q197 ← q r"ring_char(quotient_ring (ring_of_integers l) (Q:B->bool)) divides
    ramification_index (ring_of_integers k,ring_of_integers l) (h:A->B) Q"
    let q198 ← q r"(p ==> q /\ r) ==> (p ==> q) /\ (p ==> r)"
    let r199 ← TAUT q198
    let p200 ← prove r"(!k:A ring l:B ring h p Q.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
        ==> ramification_index (ring_of_integers k,ring_of_integers l) h Q - 1
            <= ideal_valuation (ring_of_integers l) Q
                 (number_field_different (k,l) h) /\
            (ideal_valuation (ring_of_integers l) Q
               (number_field_different (k,l) h) =
             ramification_index (ring_of_integers k,ring_of_integers l) h Q - 1
             <=> ~(ring_char(quotient_ring (ring_of_integers l) Q) divides
                   ramification_index (ring_of_integers k,ring_of_integers l)
                                      h Q))) /\
   (!k:A ring l:B ring h p Q.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
        ==> (ramification_index (ring_of_integers k,ring_of_integers l) h Q <=
             ideal_valuation (ring_of_integers l) Q
               (number_field_different (k,l) h) <=>
             ring_char(quotient_ring (ring_of_integers l) Q) divides
             ramification_index (ring_of_integers k,ring_of_integers l) h Q))" (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC r199 THEN DISCH_THEN (MP_TAC o (MATCH_MP core)) THEN ASM_CASES_TAC q197 THEN ASM_REWRITE_TAC [] THEN ARITH_TAC)
    CONJ_PAIR p200

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_DIFFERENT_VALUATION_GALOIS_OVERFIELD,
           NUMBER_FIELD_DIFFERENT_VALUATION_TAME, NUMBER_FIELD_DIFFERENT_VALUATION_WILD }
  -- @@RETURN END

end HolANT.HilbertFormula
