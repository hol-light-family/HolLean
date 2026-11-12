/- ========================================================================= -/
/- ANT: The valuation subrings of Q-bar over a prime p are of rank one     -/
/- ========================================================================= -/
/- File: HolANT/ValuationRankOne.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/valuation_rank_one.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antvaluationrankonediff; the rest is by hand.  Its `needs` closure is
  Library/wo.ml, Library/card.ml, Library/matroids.ml, Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/ringtheory.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/ideal_norm.ml, ANT/valuation_ring.ml, ANT/dedekind_absolute.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/nf_valuation.ml, ANT/prime_split.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/decomposition.ml, ANT/relative_degree.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/splitting_types.ml, ANT/nf_decomposition.ml, ANT/valuation_residue.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.ValuationRankOne fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left; where a proof applies rules that print or use
  counters (MESON, ARITH_RULE, ...) they are bound first, in OCaml's order.
-/

import HolANT.Prelude
import HolLibrary.Wo
import HolLibrary.Card
import HolLibrary.Matroids
import HolLibrary.Binomial
import HolLibrary.Iter
import HolLibrary.Prime
import HolLibrary.Pocklington
import HolLibrary.RingTheory
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolLibrary.FieldTheory
import HolANT.IdealArith
import HolLibrary.Products
import HolANT.Algmisc
import HolANT.Integral
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.IdealNorm
import HolANT.ValuationRing
import HolANT.DedekindAbsolute
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.Classgroup
import HolANT.NfValuation
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
import HolANT.RelativeDegree
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.SplittingTypes
import HolANT.NfDecomposition
import HolANT.ValuationResidue
import HolMultiLib.Misc
import HolMultiLib.Metric
import HolMultiLib.Homology
import HolMultiLib.Vectors
import HolMultiLib.Determinants
import HolMultiLib.Topology
import HolMultiLib.Convex
import HolMultiLib.Paths
import HolMultiLib.Polytope
import HolMultiLib.Degree
import HolMultiLib.Derivatives
import HolMultiLib.Integration
import HolMultiLib.Measure
import HolMultiLib.ComplexAlgebra
import HolMultiLib.Complexes
import HolMultiLib.Canal
import HolMultiLib.Transcendentals

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
open HolANT.ValuationRing
open HolANT.DedekindAbsolute
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.Classgroup
open HolANT.NfValuation
open HolANT.PrimeSplit
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.Decomposition
open HolANT.RelativeDegree
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.SplittingTypes
open HolANT.NfDecomposition
open HolANT.ValuationResidue

namespace HolANT.ValuationRankOne

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CARRIER_SUBFIELD_GENERATED_SUBFIELD CONJ_ASSOC DEDEKIND_RING_OF_INTEGERS
   DEDEKIND_VALUATION_ADD DEDEKIND_VALUATION_IMAGE DEDEKIND_VALUATION_MUL
   DEDEKIND_VALUATION_PRIME_IDEAL DEDEKIND_VALUATION_RAMIFICATION_INDEX
   DIVIDES_ZERO EMPTY_SUBSET FIELD_IMP_INTEGRAL_DOMAIN FINITE_EMPTY
   FINITE_INSERT FINITE_SING IMAGE_I INSERT_SUBSET INTEGRAL_DOMAIN_MUL_EQ_0
   INT_MIN_LE INT_MUL_LZERO INT_OF_NUM_EQ INT_OF_NUM_LT IN_INSERT IN_SING
   IN_SUBFIELD_ADD IN_SUBFIELD_MUL IN_SUBRING_0 I_THM MONO_OR
   NONARCHIMEDEAN_ABSOLUTE_VALUE NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC PRIME_0 PRIME_GE_2
   RAMIFICATION_INDEX_PRIME REAL_ADD_RDISTRIB REAL_DIV_REFL REAL_LE_DIV2_EQ
   REAL_LE_MAX REAL_LE_RDIV_EQ REAL_LE_REFL REAL_LT_IMP_LE REAL_LT_IMP_NZ
   REAL_MIN_LE REAL_MUL_LZERO REAL_MUL_RZERO REAL_NEG_ADD REAL_OF_INT_CLAUSES
   REAL_OF_NUM_EQ REAL_OF_NUM_LT REAL_POS REAL_POW_1 RING_ADD_LZERO
   RING_ADD_RZERO RING_CHAR_SUBFIELD_GENERATED RING_CHAR_SUBRING_GENERATED
   RING_MONOMORPHISM_BETWEEN_SUBRINGS RING_MONOMORPHISM_I
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MONOMORPHISM_RING_OF_INTEGERS
   RING_MUL_LZERO RING_MUL_RZERO RING_OF_INTEGERS
   RING_OF_INTEGERS_FRACTION_FIELD RING_OF_INTEGERS_SUBFIELD_GENERATED
   RING_OF_INT_EQ_0 RING_OF_INT_OF_NUM RING_OF_INT_SUBFIELD_GENERATED
   RING_OF_NUM RING_OF_NUM_EQ_0 RING_OF_NUM_SUBFIELD_GENERATED RPOW_0 RPOW_ADD
   RPOW_MONO_LE RPOW_MONO_LE_EQ RPOW_NEG RPOW_POS_LT RPOW_POW SING_SUBSET
   SUBFIELD_GENERATED SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED
   SUBFIELD_GENERATED_INC_GEN SUBFIELD_GENERATED_MINIMAL SUBFIELD_OF_IMP_SUBSET
   SUBFIELD_SUBFIELD_GENERATED SUBRING_GENERATED_BY_SUBFIELD_GENERATED SUBSET
   VALUATION_SUBRING_NUMBER_SUBFIELD VALUATION_SUBRING_NUMBER_SUBFIELD_VALUATION
   algebraic_extension int_add_th int_le int_mul_th int_of_num_th number_field
   real_div ring_of_integers valuation_subring : thm)
  deriving Inhabited

/-- What valuation_rank_one.ml uses from Session besides theorems. -/
structure ValuationRankOneDeps where
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
/- valuation_rank_one.ml phrases from line 64 to 560                      -/
/- ---------------------------------------------------------------------- -/

structure ValuationRankOne where
  -- @@FIELDS
  VALUATION_SUBRING_NUMBER_SUBFIELD_RAMIFICATION : thm
  VALUATION_SUBRING_NUMBER_SUBFIELD_TOWER : thm
  VALUATION_SUBRING_NUMBER_SUBFIELD_RATIO : thm
  ALGEBRAIC_VALUATION_SUBRING_RANK_ONE : thm
  ALGEBRAIC_VALUATION_SUBRING_ABSOLUTE_VALUE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupValuationRankOne [HolBase] (D : ValuationRankOneDeps) :
    ExceptT String IO ValuationRankOne := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, ASM_REAL_ARITH_TAC, INTEGER_RULE,
        MESON_TAC, REAL_ARITH_TAC, REAL_FIELD, SET_TAC, TAUT, .. } := D
  let { CARRIER_SUBFIELD_GENERATED_SUBFIELD, CONJ_ASSOC, DEDEKIND_RING_OF_INTEGERS,
        DEDEKIND_VALUATION_ADD, DEDEKIND_VALUATION_IMAGE, DEDEKIND_VALUATION_MUL,
        DEDEKIND_VALUATION_PRIME_IDEAL, DEDEKIND_VALUATION_RAMIFICATION_INDEX,
        DIVIDES_ZERO, EMPTY_SUBSET, FIELD_IMP_INTEGRAL_DOMAIN, FINITE_EMPTY,
        FINITE_INSERT, FINITE_SING, IMAGE_I, INSERT_SUBSET, INTEGRAL_DOMAIN_MUL_EQ_0,
        INT_MIN_LE, INT_MUL_LZERO, INT_OF_NUM_EQ, INT_OF_NUM_LT, IN_INSERT, IN_SING,
        IN_SUBFIELD_ADD, IN_SUBFIELD_MUL, IN_SUBRING_0, I_THM, MONO_OR,
        NONARCHIMEDEAN_ABSOLUTE_VALUE, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC, PRIME_0, PRIME_GE_2,
        RAMIFICATION_INDEX_PRIME, REAL_ADD_RDISTRIB, REAL_DIV_REFL, REAL_LE_DIV2_EQ,
        REAL_LE_MAX, REAL_LE_RDIV_EQ, REAL_LE_REFL, REAL_LT_IMP_LE, REAL_LT_IMP_NZ,
        REAL_MIN_LE, REAL_MUL_LZERO, REAL_MUL_RZERO, REAL_NEG_ADD, REAL_OF_INT_CLAUSES,
        REAL_OF_NUM_EQ, REAL_OF_NUM_LT, REAL_POS, REAL_POW_1, RING_ADD_LZERO,
        RING_ADD_RZERO, RING_CHAR_SUBFIELD_GENERATED, RING_CHAR_SUBRING_GENERATED,
        RING_MONOMORPHISM_BETWEEN_SUBRINGS, RING_MONOMORPHISM_I,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_RING_OF_INTEGERS,
        RING_MUL_LZERO, RING_MUL_RZERO, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FRACTION_FIELD, RING_OF_INTEGERS_SUBFIELD_GENERATED,
        RING_OF_INT_EQ_0, RING_OF_INT_OF_NUM, RING_OF_INT_SUBFIELD_GENERATED,
        RING_OF_NUM, RING_OF_NUM_EQ_0, RING_OF_NUM_SUBFIELD_GENERATED, RPOW_0,
        RPOW_ADD, RPOW_MONO_LE, RPOW_MONO_LE_EQ, RPOW_NEG, RPOW_POS_LT, RPOW_POW,
        SING_SUBSET, SUBFIELD_GENERATED, SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_INC_GEN, SUBFIELD_GENERATED_MINIMAL, SUBFIELD_OF_IMP_SUBSET,
        SUBFIELD_SUBFIELD_GENERATED, SUBRING_GENERATED_BY_SUBFIELD_GENERATED, SUBSET,
        VALUATION_SUBRING_NUMBER_SUBFIELD, VALUATION_SUBRING_NUMBER_SUBFIELD_VALUATION,
        algebraic_extension, int_add_th, int_le, int_mul_th, int_of_num_th,
        number_field, real_div, ring_of_integers, valuation_subring, .. } := D.core1
  -- @@SCOPE END

  let VALUATION_SUBRING_NUMBER_SUBFIELD_RAMIFICATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INTEGER_RULE (← q r"(x:int) divides x")
    prove
      r"!(k:A ring) v m p l.
          valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
          prime p /\ (!n. ring_of_int k n IN m <=> &p divides n) /\
          l subfield_of k /\ number_field(subfield_generated k l)
          ==> ~(m INTER ring_carrier(ring_of_integers(subfield_generated k l)) =
                {ring_0 k}) /\
              dedekind_valuation
               (ring_of_integers(subfield_generated k l),subfield_generated k l)
               I (m INTER ring_carrier(ring_of_integers(subfield_generated k l)))
               (ring_of_num k p) =
              &(ramification_index
                 (integer_ring,ring_of_integers(subfield_generated k l))
                 (ring_of_int(ring_of_integers(subfield_generated k l)))
                 (m INTER
                  ring_carrier(ring_of_integers(subfield_generated k l)))) /\
              ~(ramification_index
                 (integer_ring,ring_of_integers(subfield_generated k l))
                 (ring_of_int(ring_of_integers(subfield_generated k l)))
                 (m INTER
                  ring_carrier(ring_of_integers(subfield_generated k l))) = 0)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool"), (← q r"l:A->bool")] VALUATION_SUBRING_NUMBER_SUBFIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o ((SPEC (← q r"&p:int")) o CONJUNCT1))) THEN REWRITE_TAC [r1] THEN REWRITE_TAC [RING_OF_INT_SUBFIELD_GENERATED, RING_OF_INT_OF_NUM, RING_OF_NUM_SUBFIELD_GENERATED] THEN ABBREV_TAC (← q r"O = ring_of_integers(subfield_generated k (l:A->bool))") THEN ABBREV_TAC (← q r"Q = m INTER ring_carrier(O:A ring)") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_of_num (O:A ring) p = ring_of_num k p") ASSUME_TAC THENL [EXPAND_TAC "O" THEN REWRITE_TAC [RING_OF_INTEGERS, RING_OF_NUM_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_num k p IN ring_carrier(O:A ring) /\
                  ~(ring_of_num k p = ring_0(O:A ring))") STRIP_ASSUME_TAC THENL [UNDISCH_THEN (← q r"ring_of_num (O:A ring) p = ring_of_num k p") (SUBST1_TAC o SYM) THEN REWRITE_TAC [RING_OF_NUM] THEN EXPAND_TAC "O" THEN REWRITE_TAC [RING_OF_INTEGERS, RING_OF_NUM_SUBFIELD_GENERATED, (← CONJUNCT2 SUBFIELD_GENERATED), RING_OF_NUM_EQ_0] THEN REWRITE_TAC [ring_of_integers, RING_CHAR_SUBRING_GENERATED] THEN UNDISCH_TAC (← q r"number_field(subfield_generated k (l:A->bool))") THEN SIMP_TAC [number_field] THEN DISCH_TAC THEN REWRITE_TAC [DIVIDES_ZERO] THEN ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(Q = {ring_0 k:A})") (fun th => REWRITE_TAC [th]) THENL [UNDISCH_TAC (← q r"~(ring_of_num k p = ring_0(O:A ring))") THEN EXPAND_TAC "O" THEN REWRITE_TAC [RING_OF_INTEGERS, (← CONJUNCT2 SUBFIELD_GENERATED)] THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"O:A ring"), (← q r"Q:A->bool"), (← q r"p:num")] RAMIFICATION_INDEX_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"O:A ring"), (← q r"subfield_generated k (l:A->bool)"), (← q r"I:A->A"), (← q r"Q:A->bool"), (← q r"ring_of_num k p:A")] DEDEKIND_VALUATION_PRIME_IDEAL) THEN MP_TAC (← ISPECL [(← q r"O:A ring"), (← q r"subfield_generated k (l:A->bool)"), (← q r"I:A->A"), (← q r"Q:A->bool"), (← q r"ring_of_num k p:A")] DEDEKIND_VALUATION_IMAGE) THEN ASM_REWRITE_TAC [I_THM] THEN SUBGOAL_THEN (← q r"dedekind_domain(O:A ring) /\
      ring_monomorphism(O,subfield_generated k (l:A->bool)) I /\
      ~(Q = {ring_0(O:A ring)})") (fun th => REWRITE_TAC [th]) THENL [REPEAT CONJ_TAC THENL [EXPAND_TAC "O" THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS], EXPAND_TAC "O" THEN REWRITE_TAC [RING_OF_INTEGERS_FRACTION_FIELD], ASM SET_TAC []], DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [INT_OF_NUM_LT, INT_OF_NUM_EQ] THEN ARITH_TAC])

  let VALUATION_SUBRING_NUMBER_SUBFIELD_TOWER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INTEGER_RULE (← q r"!x:int. &0 divides x <=> x = &0")
    let r2 ← INTEGER_RULE (← q r"(x:int) divides x")
    prove
      r"!(k:A ring) v m p l l' x.
          valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
          prime p /\ (!n. ring_of_int k n IN m <=> &p divides n) /\
          l subfield_of k /\ number_field(subfield_generated k l) /\
          l' subfield_of k /\ number_field(subfield_generated k l') /\
          l SUBSET l' /\ x IN l /\ ~(x = ring_0 k)
          ==> dedekind_valuation
               (ring_of_integers(subfield_generated k l'),
                subfield_generated k l') I
               (m INTER
                ring_carrier(ring_of_integers(subfield_generated k l'))) x =
              &(ramification_index
                 (ring_of_integers(subfield_generated k l),
                  ring_of_integers(subfield_generated k l')) I
                 (m INTER
                  ring_carrier(ring_of_integers(subfield_generated k l')))) *
              dedekind_valuation
               (ring_of_integers(subfield_generated k l),subfield_generated k l)
               I (m INTER ring_carrier(ring_of_integers(subfield_generated k l)))
               x"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool"), (← q r"l:A->bool")] VALUATION_SUBRING_NUMBER_SUBFIELD) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool"), (← q r"l':A->bool")] VALUATION_SUBRING_NUMBER_SUBFIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o CONJUNCT1)) THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o CONJUNCT1)) THEN SUBGOAL_THEN (← q r"ring_monomorphism(subfield_generated k l,subfield_generated k l')
                       (I:A->A)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:A->bool")] SUBRING_GENERATED_BY_SUBFIELD_GENERATED) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l':A->bool")] SUBRING_GENERATED_BY_SUBFIELD_GENERATED) THEN ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN MATCH_MP_TAC RING_MONOMORPHISM_BETWEEN_SUBRINGS THEN ASM_REWRITE_TAC [RING_MONOMORPHISM_I, IMAGE_I], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_char(k:A ring) = 0") ASSUME_TAC THENL [UNDISCH_TAC (← q r"number_field(subfield_generated k (l:A->bool))") THEN SIMP_TAC [number_field, RING_CHAR_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"{a | a IN ring_carrier(ring_of_integers(subfield_generated k l)) /\
           a IN m INTER
                ring_carrier(ring_of_integers(subfield_generated k l'))} =
      m INTER ring_carrier(ring_of_integers(subfield_generated k (l:A->bool)))") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBFIELD_GENERATED] THEN ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(m INTER ring_carrier(ring_of_integers(subfield_generated k l)) =
        {ring_0(ring_of_integers(subfield_generated k (l:A->bool)))})") ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC (← q r"!n. ring_of_int (subfield_generated k (l:A->bool)) n IN
            m INTER ring_carrier (ring_of_integers (subfield_generated k l)) <=>
            &p divides n") THEN DISCH_THEN (MP_TAC o (SPEC (← q r"&p:int"))) THEN ASM_REWRITE_TAC [r2, IN_SING, RING_OF_INTEGERS, RING_OF_INT_SUBFIELD_GENERATED, SUBFIELD_GENERATED, RING_OF_INT_EQ_0] THEN REWRITE_TAC [r1, INT_OF_NUM_EQ] THEN ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers(subfield_generated k (l:A->bool))"), (← q r"ring_of_integers(subfield_generated k (l':A->bool))"), (← q r"subfield_generated k (l:A->bool)"), (← q r"subfield_generated k (l':A->bool)"), (← q r"I:A->A"), (← q r"I:A->A"), (← q r"I:A->A"), (← q r"I:A->A"), (← q r"m INTER
       ring_carrier(ring_of_integers(subfield_generated k (l':A->bool)))"), (← q r"x:A")] DEDEKIND_VALUATION_RAMIFICATION_INDEX) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, NUMBER_FIELD_IMP_FIELD, RING_OF_INTEGERS_FRACTION_FIELD, RING_MONOMORPHISM_RING_OF_INTEGERS, RING_MONOMORPHISM_IMP_HOMOMORPHISM, I_THM, CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN MP_TAC (← ISPEC (← q r"subfield_generated k (l:A->bool)") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD, RING_OF_INTEGERS, (← CONJUNCT2 SUBFIELD_GENERATED)])

  let VALUATION_SUBRING_NUMBER_SUBFIELD_RATIO ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"!n a b:real. ~(n = &0) ==> (n * a) / (n * b) = a / b"
    let r2 ← REAL_FIELD q1
    let q3 ← q r"n = 0"
    let p4 ← prove r"!a b c d (n:num) (n':num).
        c = &n * a /\ d = &n * b /\ d = &n' /\ ~(n' = 0)
        ==> real_of_int c / real_of_int d = real_of_int a / real_of_int b" (REPEAT GEN_TAC THEN ASM_CASES_TAC q3 THENL [ASM_REWRITE_TAC [INT_MUL_LZERO] THEN MESON_TAC [INT_OF_NUM_EQ], DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC (CONJUNCTS_THEN2 SUBST1_TAC (fun (_ : thm) => ALL_TAC))) THEN REWRITE_TAC [int_mul_th, int_of_num_th] THEN MATCH_MP_TAC r2 THEN ASM_REWRITE_TAC [REAL_OF_NUM_EQ]])
    let q5 ← q r"(p /\ q /\ r ==> s) ==> p ==> q ==> t /\ r ==> s"
    let r6 ← TAUT q5
    let q7 ← q r"x:A"
    let q8 ← q r"l':A->bool"
    let q9 ← q r"l:A->bool"
    let q10 ← q r"p:num"
    let q11 ← q r"m:A->bool"
    let q12 ← q r"v:A->bool"
    let q13 ← q r"k:A ring"
    let v14 ← ISPECL [q13, q12, q11, q10, q9, q8, q7] VALUATION_SUBRING_NUMBER_SUBFIELD_TOWER
    let q15 ← q r"ring_of_num k p:A"
    let q16 ← q r"l':A->bool"
    let q17 ← q r"l:A->bool"
    let q18 ← q r"p:num"
    let q19 ← q r"m:A->bool"
    let q20 ← q r"v:A->bool"
    let q21 ← q r"k:A ring"
    let v22 ← ISPECL [q21, q20, q19, q18, q17, q16, q15] VALUATION_SUBRING_NUMBER_SUBFIELD_TOWER
    let q23 ← q r"l':A->bool"
    let q24 ← q r"p:num"
    let q25 ← q r"m:A->bool"
    let q26 ← q r"v:A->bool"
    let q27 ← q r"k:A ring"
    let v28 ← ISPECL [q27, q26, q25, q24, q23] VALUATION_SUBRING_NUMBER_SUBFIELD_RAMIFICATION
    let q29 ← q r"number_field(subfield_generated k (l:A->bool))"
    let q30 ← q r"p:num"
    let q31 ← q r"subfield_generated k (l:A->bool)"
    let v32 ← ISPECL [q31, q30] RING_OF_NUM
    let q33 ← q r"ring_of_num k p IN (l:A->bool) /\ ~(ring_of_num k p = ring_0 k)"
    prove
      r"!(k:A ring) v m p l l' x.
          valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
          prime p /\ (!n. ring_of_int k n IN m <=> &p divides n) /\
          l subfield_of k /\ number_field(subfield_generated k l) /\
          l' subfield_of k /\ number_field(subfield_generated k l') /\
          l SUBSET l' /\ x IN l /\ ~(x = ring_0 k)
          ==> real_of_int
               (dedekind_valuation
                 (ring_of_integers(subfield_generated k l'),
                  subfield_generated k l') I
                 (m INTER
                  ring_carrier(ring_of_integers(subfield_generated k l'))) x) /
              real_of_int
               (dedekind_valuation
                 (ring_of_integers(subfield_generated k l'),
                  subfield_generated k l') I
                 (m INTER
                  ring_carrier(ring_of_integers(subfield_generated k l')))
                 (ring_of_num k p)) =
              real_of_int
               (dedekind_valuation
                 (ring_of_integers(subfield_generated k l),
                  subfield_generated k l) I
                 (m INTER
                  ring_carrier(ring_of_integers(subfield_generated k l))) x) /
              real_of_int
               (dedekind_valuation
                 (ring_of_integers(subfield_generated k l),
                  subfield_generated k l) I
                 (m INTER
                  ring_carrier(ring_of_integers(subfield_generated k l)))
                 (ring_of_num k p))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q33 STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [MP_TAC v32 THEN ASM_SIMP_TAC [RING_OF_NUM_SUBFIELD_GENERATED, CARRIER_SUBFIELD_GENERATED_SUBFIELD], REWRITE_TAC [RING_OF_NUM_EQ_0] THEN UNDISCH_TAC q29 THEN SIMP_TAC [number_field, RING_CHAR_SUBFIELD_GENERATED] THEN REWRITE_TAC [DIVIDES_ZERO] THEN ASM_MESON_TAC [PRIME_0]], ALL_TAC] THEN MP_TAC v28 THEN MP_TAC v22 THEN MP_TAC v14 THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r6 THEN MATCH_ACCEPT_TAC p4)

  let ALGEBRAIC_VALUATION_SUBRING_RANK_ONE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r")
    let r2 ← TAUT (← q r"p /\ q /\ (p /\ q ==> r) /\ s ==> p /\ q /\ r /\ s")
    prove
      r"!(k:A ring) v m p.
          ring_char k = 0 /\
          algebraic_extension(subfield_generated k {ring_0 k},k) I /\
          valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
          prime p /\ (!n. ring_of_int k n IN m <=> &p divides n)
          ==> ?w:A->real.
               (!x y. x IN ring_carrier k /\ y IN ring_carrier k /\
                      ~(x = ring_0 k) /\ ~(y = ring_0 k)
                      ==> w(ring_mul k x y) = w x + w y) /\
               (!x y. x IN ring_carrier k /\ y IN ring_carrier k /\
                      ~(x = ring_0 k) /\ ~(y = ring_0 k) /\
                      ~(ring_add k x y = ring_0 k)
                      ==> min (w x) (w y) <= w(ring_add k x y)) /\
               (!x. x IN ring_carrier k /\ ~(x = ring_0 k)
                    ==> (x IN v <=> &0 <= w x)) /\
               w(ring_of_num k p) = &1 /\
               (!l x. l subfield_of k /\ number_field(subfield_generated k l) /\
                      x IN l /\ ~(x = ring_0 k)
                      ==> w x =
                          real_of_int
                           (dedekind_valuation
                             (ring_of_integers(subfield_generated k l),
                              subfield_generated k l) I
                             (m INTER ring_carrier
                                (ring_of_integers(subfield_generated k l)))
                             x) /
                          &(ramification_index
                             (integer_ring,
                              ring_of_integers(subfield_generated k l))
                             (ring_of_int
                               (ring_of_integers(subfield_generated k l)))
                             (m INTER ring_carrier
                                (ring_of_integers(subfield_generated k l)))))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN SUBGOAL_THEN (← q r"!s. FINITE s /\ s SUBSET ring_carrier k
          ==> ring_carrier(subfield_generated k s) subfield_of k /\
              number_field(subfield_generated k
                            (ring_carrier(subfield_generated k (s:A->bool))))") (LABEL_TAC "nf") THENL [GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED, SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN MATCH_MP_TAC NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"algebraic_extension(subfield_generated k {ring_0 k},k) (I:A->A)") THEN REWRITE_TAC [algebraic_extension] THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!l. l subfield_of k /\ number_field(subfield_generated k l)
          ==> ~(m INTER ring_carrier(ring_of_integers(subfield_generated k l)) =
                {ring_0 k}) /\
              &0 < real_of_int
                    (dedekind_valuation
                      (ring_of_integers(subfield_generated k l),
                       subfield_generated k l) I
                      (m INTER ring_carrier
                         (ring_of_integers(subfield_generated k (l:A->bool))))
                      (ring_of_num k p))") (LABEL_TAC "pos") THENL [X_GEN_TAC (← q r"l:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool"), (← q r"p:num"), (← q r"l:A->bool")] VALUATION_SUBRING_NUMBER_SUBFIELD_RAMIFICATION) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [int_of_num_th, REAL_OF_NUM_LT] THEN ASM_ARITH_TAC, ALL_TAC] THEN ABBREV_TAC (← q r"R = \(l:A->bool) (x:A). real_of_int
                   (dedekind_valuation
                     (ring_of_integers(subfield_generated k l),
                      subfield_generated k l) I
                     (m INTER ring_carrier
                        (ring_of_integers(subfield_generated k l))) x) /
                 real_of_int
                   (dedekind_valuation
                     (ring_of_integers(subfield_generated k l),
                      subfield_generated k l) I
                     (m INTER ring_carrier
                        (ring_of_integers(subfield_generated k l)))
                     (ring_of_num k p))") THEN SUBGOAL_THEN (← q r"!l l' x. l subfield_of k /\ number_field(subfield_generated k l) /\
               l' subfield_of k /\ number_field(subfield_generated k l') /\
               l SUBSET l' /\ x IN l /\ ~(x = ring_0 k)
               ==> (R:(A->bool)->A->real) l' x = R l x") (LABEL_TAC "rat") THENL [REPEAT STRIP_TAC THEN EXPAND_TAC "R" THEN MATCH_MP_TAC VALUATION_SUBRING_NUMBER_SUBFIELD_RATIO THEN EXISTS_TAC (← q r"v:A->bool") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!l x. l subfield_of k /\ number_field(subfield_generated k l) /\
            x IN l /\ ~(x = ring_0 k)
            ==> (R:(A->bool)->A->real) l x =
                R (ring_carrier(subfield_generated k {x})) x") (LABEL_TAC "K") THENL [REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [SUBFIELD_OF_IMP_SUBSET, SUBSET], ALL_TAC] THEN USE_THEN "nf" (MP_TAC o (SPEC (← q r"{x:A}"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [FINITE_SING, SING_SUBSET], STRIP_TAC] THEN USE_THEN "rat" MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_SING]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!l x y. l subfield_of k /\ number_field(subfield_generated k l) /\
              x IN l /\ y IN l /\ ~(x = ring_0 k) /\ ~(y = ring_0 k)
              ==> (R:(A->bool)->A->real) l (ring_mul k x y) = R l x + R l y /\
                  (~(ring_add k x y = ring_0 k)
                   ==> min (R l x) (R l y) <= R l (ring_add k x y))") (LABEL_TAC "hom") THENL [REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "pos" (MP_TAC o (SPEC (← q r"l:A->bool"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool"), (← q r"l:A->bool")] VALUATION_SUBRING_NUMBER_SUBFIELD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (ASSUME_TAC o CONJUNCT1)] THEN EXPAND_TAC "R" THEN MP_TAC (← ISPECL [(← q r"ring_of_integers(subfield_generated k (l:A->bool))"), (← q r"subfield_generated k (l:A->bool)"), (← q r"I:A->A"), (← q r"m INTER
         ring_carrier(ring_of_integers(subfield_generated k (l:A->bool)))"), (← q r"x:A"), (← q r"y:A")] DEDEKIND_VALUATION_MUL) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers(subfield_generated k (l:A->bool))"), (← q r"subfield_generated k (l:A->bool)"), (← q r"I:A->A"), (← q r"m INTER
         ring_carrier(ring_of_integers(subfield_generated k (l:A->bool)))"), (← q r"x:A"), (← q r"y:A")] DEDEKIND_VALUATION_ADD) THEN MP_TAC (← ISPEC (← q r"subfield_generated k (l:A->bool)") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD, RING_OF_INTEGERS, (← CONJUNCT2 SUBFIELD_GENERATED), I_THM] THEN ASM_SIMP_TAC [CARRIER_SUBFIELD_GENERATED_SUBFIELD] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN DISCH_TAC THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN CONJ_TAC THENL [REWRITE_TAC [int_add_th, real_div, REAL_ADD_RDISTRIB], DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun z3 => (do let z4 ← (do let z5 ← (pure z3); pure (concl z5)); pure (is_imp z4))))) THEN ASM_REWRITE_TAC [INT_MIN_LE, REAL_MIN_LE] THEN ASM_SIMP_TAC [REAL_LE_DIV2_EQ, REAL_OF_INT_CLAUSES]], ALL_TAC] THEN EXISTS_TAC (← q r"\x:A. (R:(A->bool)->A->real)
            (ring_carrier(subfield_generated k {x})) x") THEN REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN USE_THEN "nf" (MP_TAC o (SPEC (← q r"{x:A,y}"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY, INSERT_SUBSET, EMPTY_SUBSET], STRIP_TAC] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier(subfield_generated k {x,y}) /\
        (y:A) IN ring_carrier(subfield_generated k {x,y}) /\
        ring_mul k x y IN ring_carrier(subfield_generated k {x,y}) /\
        ~(ring_mul k x y = ring_0 k)") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r2 THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_INSERT], MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_INSERT], ASM_MESON_TAC [IN_SUBFIELD_MUL], ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN]], ALL_TAC] THEN USE_THEN "K" (MP_TAC o (SPECL [(← q r"ring_carrier(subfield_generated k {x:A,y})"), (← q r"ring_mul k x y:A")])) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN USE_THEN "K" (MP_TAC o (SPECL [(← q r"ring_carrier(subfield_generated k {x:A,y})"), (← q r"x:A")])) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN USE_THEN "K" (MP_TAC o (SPECL [(← q r"ring_carrier(subfield_generated k {x:A,y})"), (← q r"y:A")])) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN USE_THEN "hom" (MP_TAC o (SPECL [(← q r"ring_carrier(subfield_generated k {x:A,y})"), (← q r"x:A"), (← q r"y:A")])) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], SIMP_TAC []], MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN USE_THEN "nf" (MP_TAC o (SPEC (← q r"{x:A,y}"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY, INSERT_SUBSET, EMPTY_SUBSET], STRIP_TAC] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier(subfield_generated k {x,y}) /\
        (y:A) IN ring_carrier(subfield_generated k {x,y}) /\
        ring_add k x y IN ring_carrier(subfield_generated k {x,y})") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r1 THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_INSERT], MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_INSERT], ASM_MESON_TAC [IN_SUBFIELD_ADD]], ALL_TAC] THEN USE_THEN "K" (MP_TAC o (SPECL [(← q r"ring_carrier(subfield_generated k {x:A,y})"), (← q r"ring_add k x y:A")])) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN USE_THEN "K" (MP_TAC o (SPECL [(← q r"ring_carrier(subfield_generated k {x:A,y})"), (← q r"x:A")])) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN USE_THEN "K" (MP_TAC o (SPECL [(← q r"ring_carrier(subfield_generated k {x:A,y})"), (← q r"y:A")])) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN USE_THEN "hom" (MP_TAC o (SPECL [(← q r"ring_carrier(subfield_generated k {x:A,y})"), (← q r"x:A"), (← q r"y:A")])) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ASM_SIMP_TAC []], X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN USE_THEN "nf" (MP_TAC o (SPEC (← q r"{x:A}"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [FINITE_SING, SING_SUBSET], STRIP_TAC] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier(subfield_generated k {x})") ASSUME_TAC THENL [MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_SING], ALL_TAC] THEN USE_THEN "pos" (MP_TAC o (SPEC (← q r"ring_carrier(subfield_generated k {x:A})"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool"), (← q r"ring_carrier(subfield_generated k {x:A})"), (← q r"x:A")] VALUATION_SUBRING_NUMBER_SUBFIELD_VALUATION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN EXPAND_TAC "R" THEN ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_MUL_LZERO] THEN REWRITE_TAC [int_le, int_of_num_th], SUBGOAL_THEN (← q r"ring_of_num k p IN ring_carrier(k:A ring)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_NUM], ALL_TAC] THEN USE_THEN "nf" (MP_TAC o (SPEC (← q r"{ring_of_num k p:A}"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [FINITE_SING, SING_SUBSET], STRIP_TAC] THEN USE_THEN "pos" (MP_TAC o (SPEC (← q r"ring_carrier(subfield_generated k {ring_of_num k p:A})"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN EXPAND_TAC "R" THEN MATCH_MP_TAC REAL_DIV_REFL THEN ASM_REAL_ARITH_TAC, MAP_EVERY X_GEN_TAC [(← q r"l:A->bool"), (← q r"x:A")] THEN STRIP_TAC THEN USE_THEN "K" (MP_TAC o (SPECL [(← q r"l:A->bool"), (← q r"x:A")])) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN EXPAND_TAC "R" THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"v:A->bool"), (← q r"m:A->bool"), (← q r"p:num"), (← q r"l:A->bool")] VALUATION_SUBRING_NUMBER_SUBFIELD_RAMIFICATION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN ASM_REWRITE_TAC [int_of_num_th]])

  let ALGEBRAIC_VALUATION_SUBRING_ABSOLUTE_VALUE ← prove
    r"!(k:A ring) v m p.
        ring_char k = 0 /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I /\
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
        prime p /\ (!n. ring_of_int k n IN m <=> &p divides n)
        ==> ?f:A->real.
             nonarchimedean_absolute_value k f /\
             (!x. x IN ring_carrier k ==> (x IN v <=> f x <= &1)) /\
             f(ring_of_num k p) = inv(&p) /\
             (!l x. l subfield_of k /\ number_field(subfield_generated k l) /\
                    x IN l /\ ~(x = ring_0 k)
                    ==> f x =
                        &p rpow
                        --(real_of_int
                            (dedekind_valuation
                              (ring_of_integers(subfield_generated k l),
                               subfield_generated k l) I
                              (m INTER ring_carrier
                                (ring_of_integers(subfield_generated k l)))
                              x) /
                           &(ramification_index
                              (integer_ring,
                               ring_of_integers(subfield_generated k l))
                              (ring_of_int
                                (ring_of_integers(subfield_generated k l)))
                              (m INTER
                               ring_carrier
                                (ring_of_integers
                                  (subfield_generated k l))))))"
    (REWRITE_TAC [NONARCHIMEDEAN_ABSOLUTE_VALUE, (← GSYM CONJ_ASSOC)] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP ALGEBRAIC_VALUATION_SUBRING_RANK_ONE)) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"w:A->real") STRIP_ASSUME_TAC) THEN FIRST_X_ASSUM (STRIP_ASSUME_TAC o (checkM (fun z8 => (do let z9 ← (do let z10 ← (pure z8); pure (concl z10)); pure (is_conj z9))))) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [valuation_subring])) THEN SUBGOAL_THEN (← q r"&1 < (&p:real) /\ &0 < (&p:real)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP PRIME_GE_2)) THEN REWRITE_TAC [REAL_OF_NUM_LT] THEN ARITH_TAC, ALL_TAC] THEN EXISTS_TAC (← q r"\x:A. if x = ring_0 k then &0 else &p rpow --(w x)") THEN REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [REAL_LE_REFL, RPOW_POS_LT, REAL_LT_IMP_LE, REAL_LT_IMP_NZ], MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"x:A = ring_0 k") THEN ASM_SIMP_TAC [RING_MUL_LZERO, REAL_MUL_LZERO] THEN ASM_CASES_TAC (← q r"y:A = ring_0 k") THEN ASM_SIMP_TAC [RING_MUL_RZERO, REAL_MUL_RZERO] THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN] THEN ASM_SIMP_TAC [REAL_NEG_ADD, RPOW_ADD], MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"x:A = ring_0 k") THENL [ASM_SIMP_TAC [RING_ADD_LZERO] THEN COND_CASES_TAC THEN ASM_SIMP_TAC [REAL_LE_MAX, REAL_LE_REFL], ALL_TAC] THEN ASM_CASES_TAC (← q r"y:A = ring_0 k") THENL [ASM_SIMP_TAC [RING_ADD_RZERO, REAL_LE_MAX, REAL_LE_REFL], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN COND_CASES_TAC THENL [ASM_SIMP_TAC [REAL_LE_MAX, RPOW_POS_LT, REAL_LT_IMP_LE], ALL_TAC] THEN FIRST_ASSUM (MP_TAC o ((SPECL [(← q r"x:A"), (← q r"y:A")]) o (checkM (fun th => (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); canM (fun z3 => (do let z4 ← (pure z3); find_termM (fun z5 => (do let z7 ← (pure z5); let z6 ← (q r"min:real->real->real"); pure (z6 == z7))) z4)) z1))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [REAL_MIN_LE, REAL_LE_MAX] THEN MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC RPOW_MONO_LE THEN ASM_SIMP_TAC [REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC, X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"x:A = ring_0 k") THEN ASM_REWRITE_TAC [REAL_POS] THENL [FIRST_ASSUM (MATCH_ACCEPT_TAC o (MATCH_MP IN_SUBRING_0)), ALL_TAC] THEN SUBGOAL_THEN (← q r"(x:A) IN v <=> &0 <= (w:A->real) x") SUBST1_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [(← GSYM (← SPEC (← q r"&p:real") RPOW_0))] THEN ASM_SIMP_TAC [RPOW_MONO_LE_EQ] THEN REAL_ARITH_TAC, SUBGOAL_THEN (← q r"~(ring_of_num k p = ring_0 (k:A ring))") ASSUME_TAC THENL [ASM_REWRITE_TAC [RING_OF_NUM_EQ_0, DIVIDES_ZERO] THEN ASM_MESON_TAC [PRIME_0], ASM_REWRITE_TAC [RPOW_NEG, RPOW_POW, REAL_POW_1]], MAP_EVERY X_GEN_TAC [(← q r"l:A->bool"), (← q r"x:A")] THEN STRIP_TAC THEN ASM_SIMP_TAC []])

  -- @@RETURN BEGIN
  return { VALUATION_SUBRING_NUMBER_SUBFIELD_RAMIFICATION,
           VALUATION_SUBRING_NUMBER_SUBFIELD_TOWER,
           VALUATION_SUBRING_NUMBER_SUBFIELD_RATIO, ALGEBRAIC_VALUATION_SUBRING_RANK_ONE,
           ALGEBRAIC_VALUATION_SUBRING_ABSOLUTE_VALUE }
  -- @@RETURN END

end HolANT.ValuationRankOne
