/- ========================================================================= -/
/- ANT: Quadratic fields                                                   -/
/- ========================================================================= -/
/- File: HolANT/QuadraticIdeals.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/quadratic_ideals.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antquadraticidealsdiff; the rest is by hand.  Its `needs` closure is
  Library/integer.ml, Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, ANT/ideal_arith.ml, Library/isum.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/quadratic.ml, ANT/prime_split.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/trace_form.ml, ANT/relative_split.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/decomposition.ml, ANT/nf_valuation.ml, ANT/relative_degree.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/splitting_types.ml, ANT/nf_decomposition.ml, ANT/conjugate_ideals.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.QuadraticIdeals fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left; where a proof applies rules that print or use
  counters (MESON, ARITH_RULE, ...) they are bound first, in OCaml's order.
-/

import HolANT.Prelude
import HolLibrary.Integer
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
import HolANT.NormIndex
import HolANT.Discriminant
import HolANT.Quadratic
import HolANT.PrimeSplit
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolANT.Decomposition
import HolANT.NfValuation
import HolANT.RelativeDegree
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.SplittingTypes
import HolANT.NfDecomposition
import HolANT.ConjugateIdeals

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
open HolANT.NormIndex
open HolANT.Discriminant
open HolANT.Quadratic
open HolANT.PrimeSplit
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.Decomposition
open HolANT.NfValuation
open HolANT.RelativeDegree
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.SplittingTypes
open HolANT.NfDecomposition
open HolANT.ConjugateIdeals

namespace HolANT.QuadraticIdeals

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRA_TRACE_NORM_GALOIS ARITH_EQ CARD_CLAUSES CARD_SUBSET_EQ DE_MORGAN_THM
   EMPTY_SUBSET EQ_TRANS EXTENSION FIELD_EXTENSION_SUBFIELD_GENERATED
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_SUBFIELD_GENERATED FINITE_EMPTY
   FINITE_GALOIS_GROUP FINITE_INSERT FINITE_SING FORALL_UNWIND_THM2
   GALOIS_EXTENSION_EQ_CARD GALOIS_GROUP_EQ_ON_GENERATORS GALOIS_GROUP_FIXES
   GALOIS_GROUP_I GALOIS_GROUP_IMAGE_IDEAL_GENERATED GALOIS_GROUP_IN_CARRIER
   GALOIS_GROUP_RING_HOMOMORPHISM GALOIS_GROUP_RING_OF_INTEGERS_IDEAL HAS_SIZE
   IDEAL_GENERATED_PAIR_EQ IDEAL_PRODUCT_INSERT IDEAL_PRODUCT_SING IMAGE_CLAUSES
   IMAGE_I INSERT_SUBSET INTEGRAL_DOMAIN_MUL_LCANCEL INTEGRAL_ELEMENT_QUADRATIC
   INT_MUL_DIV_EQ INT_MUL_SYM IN_ELIM_THM IN_INSERT IN_RING_IDEAL_NEG IN_SING
   I_THM KUMMER_EXTENSION_ABELIAN LEFT_IMP_EXISTS_THM NOT_IN_EMPTY
   NUMBER_FIELD_GALOIS_PRODUCT_IDEAL NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_RING_OF_NUM_EQ_0 PRIME_SUBFIELD_MINIMAL
   QUADRATIC_FIELD_COORDINATES QUADRATIC_FIELD_INTEGER_SQUARE
   QUADRATIC_FIELD_TRACE RING_1 RING_1_IN_SUBFIELD_GENERATED RING_ADD
   RING_ADD_LZERO RING_ADD_RNEG RING_CARRIER_SUBFIELD_GENERATED_SUBSET
   RING_HOMOMORPHISM_1 RING_HOMOMORPHISM_ADD RING_HOMOMORPHISM_MUL
   RING_HOMOMORPHISM_POW RING_HOMOMORPHISM_RING_OF_INT
   RING_HOMOMORPHISM_RING_OF_NUM RING_HOMOMORPHISM_SUB RING_MUL RING_MUL_LZERO
   RING_MUL_SYM RING_NEG RING_NEG_IN_SUBFIELD_GENERATED RING_NEG_NEG RING_OF_INT
   RING_OF_INTEGERS RING_OF_INTEGERS_CARRIER RING_OF_INT_0 RING_OF_INT_1
   RING_OF_INT_ADD RING_OF_INT_IN_SUBFIELD_GENERATED RING_OF_INT_MUL
   RING_OF_INT_NEG RING_OF_INT_OF_NUM RING_OF_INT_POW RING_OF_INT_SUB
   RING_OF_NUM RING_POW RING_POW_SUBFIELD_GENERATED RING_PRODUCT_CLAUSES
   RING_PRODUCT_SING RING_SUB RING_SUM_CLAUSES RING_SUM_SING SUBFIELD_GENERATED
   SUBFIELD_GENERATED_HALF_SUCC SUBFIELD_GENERATED_INC SUBFIELD_GENERATED_MONO
   SUBFIELD_GENERATED_SUPERSET SUBFIELD_SUBFIELD_GENERATED_EQ SUBSET : thm)
  deriving Inhabited

/-- What quadratic_ideals.ml uses from Session besides theorems. -/
structure QuadraticIdealsDeps where
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
/- quadratic_ideals.ml phrases from line 60 to 548                        -/
/- ---------------------------------------------------------------------- -/

structure QuadraticIdeals where
  -- @@FIELDS
  QUADRATIC_FIELD_SUBFIELD_GENERATED : thm
  QUADRATIC_FIELD_GALOIS_EXTENSION : thm
  QUADRATIC_FIELD_GALOIS_GROUP : thm
  QUADRATIC_FIELD_CONJUGATION_EXISTS : thm
  QUADRATIC_FIELD_NORM_TRACE_CONJUGATE : thm
  QUADRATIC_FIELD_NORM : thm
  QUADRATIC_FIELD_NORM_TRACE_SQRT : thm
  QUADRATIC_FIELD_NORM_TRACE_HALF : thm
  QUADRATIC_FIELD_NORM_TRACE_INTEGRAL_BASIS : thm
  QUADRATIC_FIELD_IDEAL_MUL_CONJUGATE : thm
  QUADRATIC_FIELD_CONJUGATE_PRIME_PAIR : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupQuadraticIdeals [HolBase] (D : QuadraticIdealsDeps) :
    ExceptT String IO QuadraticIdeals := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, HAS_SIZE_CONV, INTEGER_RULE, INTEGRAL_DOMAIN_RULE,
        NUM_REDUCE_CONV, RING_RULE, SET_TAC, TAUT, .. } := D
  let { ALGEBRA_TRACE_NORM_GALOIS, ARITH_EQ, CARD_CLAUSES, CARD_SUBSET_EQ,
        DE_MORGAN_THM, EMPTY_SUBSET, EQ_TRANS, EXTENSION,
        FIELD_EXTENSION_SUBFIELD_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_SUBFIELD_GENERATED, FINITE_EMPTY, FINITE_GALOIS_GROUP, FINITE_INSERT,
        FINITE_SING, FORALL_UNWIND_THM2, GALOIS_EXTENSION_EQ_CARD,
        GALOIS_GROUP_EQ_ON_GENERATORS, GALOIS_GROUP_FIXES, GALOIS_GROUP_I,
        GALOIS_GROUP_IMAGE_IDEAL_GENERATED, GALOIS_GROUP_IN_CARRIER,
        GALOIS_GROUP_RING_HOMOMORPHISM, GALOIS_GROUP_RING_OF_INTEGERS_IDEAL, HAS_SIZE,
        IDEAL_GENERATED_PAIR_EQ, IDEAL_PRODUCT_INSERT, IDEAL_PRODUCT_SING,
        IMAGE_CLAUSES, IMAGE_I, INSERT_SUBSET, INTEGRAL_DOMAIN_MUL_LCANCEL,
        INTEGRAL_ELEMENT_QUADRATIC, INT_MUL_DIV_EQ, INT_MUL_SYM, IN_ELIM_THM,
        IN_INSERT, IN_RING_IDEAL_NEG, IN_SING, I_THM, KUMMER_EXTENSION_ABELIAN,
        LEFT_IMP_EXISTS_THM, NOT_IN_EMPTY, NUMBER_FIELD_GALOIS_PRODUCT_IDEAL,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_RING_OF_NUM_EQ_0, PRIME_SUBFIELD_MINIMAL,
        QUADRATIC_FIELD_COORDINATES, QUADRATIC_FIELD_INTEGER_SQUARE,
        QUADRATIC_FIELD_TRACE, RING_1, RING_1_IN_SUBFIELD_GENERATED, RING_ADD,
        RING_ADD_LZERO, RING_ADD_RNEG, RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
        RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_ADD, RING_HOMOMORPHISM_MUL,
        RING_HOMOMORPHISM_POW, RING_HOMOMORPHISM_RING_OF_INT,
        RING_HOMOMORPHISM_RING_OF_NUM, RING_HOMOMORPHISM_SUB, RING_MUL, RING_MUL_LZERO,
        RING_MUL_SYM, RING_NEG, RING_NEG_IN_SUBFIELD_GENERATED, RING_NEG_NEG,
        RING_OF_INT, RING_OF_INTEGERS, RING_OF_INTEGERS_CARRIER, RING_OF_INT_0,
        RING_OF_INT_1, RING_OF_INT_ADD, RING_OF_INT_IN_SUBFIELD_GENERATED,
        RING_OF_INT_MUL, RING_OF_INT_NEG, RING_OF_INT_OF_NUM, RING_OF_INT_POW,
        RING_OF_INT_SUB, RING_OF_NUM, RING_POW, RING_POW_SUBFIELD_GENERATED,
        RING_PRODUCT_CLAUSES, RING_PRODUCT_SING, RING_SUB, RING_SUM_CLAUSES,
        RING_SUM_SING, SUBFIELD_GENERATED, SUBFIELD_GENERATED_HALF_SUCC,
        SUBFIELD_GENERATED_INC, SUBFIELD_GENERATED_MONO, SUBFIELD_GENERATED_SUPERSET,
        SUBFIELD_SUBFIELD_GENERATED_EQ, SUBSET, .. } := D.core1
  -- @@SCOPE END

  let QUADRATIC_FIELD_SUBFIELD_GENERATED ← prove
    r"!k:A ring x.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k}))
        ==> subfield_generated k {x} = k"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN REWRITE_TAC [SUBFIELD_GENERATED_SUPERSET, SUBSET] THEN X_GEN_TAC (← q r"z:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"z:A")] QUADRATIC_FIELD_COORDINATES) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_carrier(subfield_generated k {ring_0 k}) SUBSET
    ring_carrier(subfield_generated k {x:A})") ASSUME_TAC THENL [MATCH_MP_TAC PRIME_SUBFIELD_MINIMAL THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED_EQ, FIELD_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier(subfield_generated k {x})") ASSUME_TAC THENL [MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier(subfield_generated k {x}) /\
    (b:A) IN ring_carrier(subfield_generated k {x})") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {x:A}"), (← q r"b:A"), (← q r"x:A")] RING_MUL) THEN ASM_REWRITE_TAC [SUBFIELD_GENERATED] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {x:A}"), (← q r"a:A"), (← q r"ring_mul k b x:A")] RING_ADD) THEN ASM_REWRITE_TAC [SUBFIELD_GENERATED])

  let QUADRATIC_FIELD_GALOIS_EXTENSION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!r:A ring. ring_1 r = ring_neg r (ring_1 r) <=>
                     ring_of_num r 2 = ring_0 r")
    let r2 ← INTEGRAL_DOMAIN_RULE (← q r"!r x:A. integral_domain r /\ x IN ring_carrier r
                    ==> (ring_pow r x 2 = ring_1 r <=>
                         x = ring_1 r \/ x = ring_neg r (ring_1 r))")
    prove
      r"!k:A ring.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2
          ==> finite_extension (subfield_generated k {ring_0 k},k) I /\
              galois_extension (subfield_generated k {ring_0 k},k) I /\
              group_carrier(galois_group(subfield_generated k {ring_0 k},k) I)
              HAS_SIZE 2"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPEC (← q r"k:A ring") QUADRATIC_FIELD_INTEGER_SQUARE) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"w:A"), (← q r"m:int")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"w:A"), (← q r"2")] KUMMER_EXTENSION_ABELIAN) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED, IMAGE_I] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [RING_POW_SUBFIELD_GENERATED, (← CONJUNCT2 SUBFIELD_GENERATED)] THEN SUBGOAL_THEN (← q r"{y | y IN ring_carrier(subfield_generated k {ring_0 k}) /\
               ring_pow k y 2 = ring_1 k} =
          {ring_1 k, ring_neg k (ring_1 k:A)}") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY] THEN X_GEN_TAC (← q r"y:A") THEN ASM_CASES_TAC (← q r"(y:A) IN ring_carrier(subfield_generated k {ring_0 k})") THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"y:A")] r2) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}")] RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN ASM SET_TAC [], DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []], ASM_REWRITE_TAC [DE_MORGAN_THM] THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE [RING_1_IN_SUBFIELD_GENERATED]) THEN ASM_MESON_TAC [RING_1_IN_SUBFIELD_GENERATED, RING_NEG_IN_SUBFIELD_GENERATED]], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_1 k = ring_neg k (ring_1 k:A))") ASSUME_TAC THENL [REWRITE_TAC [r1] THEN ASM_SIMP_TAC [NUMBER_FIELD_RING_OF_NUM_EQ_0, ARITH_EQ], ASM_SIMP_TAC [HAS_SIZE, FINITE_INSERT, FINITE_EMPTY, CARD_CLAUSES, IN_INSERT, NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV], ASM_REWRITE_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED], REWRITE_TAC [SUBFIELD_GENERATED_SUPERSET] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"w:A")] QUADRATIC_FIELD_SUBFIELD_GENERATED) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [(← SYM th)])) THEN MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN SET_TAC []], STRIP_TAC] THEN ASM_SIMP_TAC [HAS_SIZE, FINITE_GALOIS_GROUP] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring")] GALOIS_EXTENSION_EQ_CARD) THEN ASM_SIMP_TAC [])

  let QUADRATIC_FIELD_GALOIS_GROUP ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!r a b x:A. a IN ring_carrier r /\ b IN ring_carrier r /\
                x IN ring_carrier r
                ==> ring_add r a (ring_mul r b (ring_neg r x)) =
                    ring_sub r a (ring_mul r b x)")
    let r2 ← TAUT (← q r"~p ==> p \/ q ==> q")
    let r3 ← INTEGRAL_DOMAIN_RULE (← q r"!r x y:A. integral_domain r /\ x IN ring_carrier r /\
                y IN ring_carrier r
                ==> (ring_pow r x 2 = ring_pow r y 2 <=>
                     x = y \/ x = ring_neg r y)")
    prove
      r"!k:A ring x s.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\
          ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
          ring_pow k x 2 IN ring_carrier(subfield_generated k {ring_0 k}) /\
          s IN group_carrier(galois_group(subfield_generated k {ring_0 k},k) I) /\
          ~(s = I)
          ==> group_carrier(galois_group(subfield_generated k {ring_0 k},k) I) =
              {I,s} /\
              s x = ring_neg k x /\
              !a b. a IN ring_carrier(subfield_generated k {ring_0 k}) /\
                    b IN ring_carrier(subfield_generated k {ring_0 k})
                    ==> s(ring_add k a (ring_mul k b x)) =
                        ring_sub k a (ring_mul k b x)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPEC (← q r"k:A ring") QUADRATIC_FIELD_GALOIS_EXTENSION) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(k,k) (s:A->A)") ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_RING_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y. y IN ring_carrier(subfield_generated k {ring_0 k}) ==> (s:A->A) y = y") ASSUME_TAC THENL [X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"s:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"y:A")] GALOIS_GROUP_FIXES) THEN ASM_REWRITE_TAC [I_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_carrier(subfield_generated k {ring_0 k}) SUBSET
                  ring_carrier(k:A ring)") ASSUME_TAC THENL [REWRITE_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(s:A->A) x = ring_neg k x") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"(s:A->A) x"), (← q r"x:A")] r3) THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN SUBGOAL_THEN (← q r"(s:A->A) x IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_IN_CARRIER], ASM_REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"ring_pow k ((s:A->A) x) 2 = ring_pow k x 2") (fun th => REWRITE_TAC [th]) THENL [MP_TAC (← ISPECL [(← q r"x:A"), (← q r"2")] (← MATCH_MP RING_HOMOMORPHISM_POW (← ASSUME (← q r"ring_homomorphism(k,k) (s:A->A)")))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [], ALL_TAC] THEN MATCH_MP_TAC r2 THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~(s:A->A = I)") THEN REWRITE_TAC [] THEN MATCH_MP_TAC GALOIS_GROUP_EQ_ON_GENERATORS THEN MAP_EVERY EXISTS_TAC [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"{x:A}")] THEN ASM_REWRITE_TAC [GALOIS_GROUP_I, IN_SING, I_THM, FORALL_UNWIND_THM2] THEN REWRITE_TAC [SUBFIELD_GENERATED_SUPERSET] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] QUADRATIC_FIELD_SUBFIELD_GENERATED) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [(← SYM th)])) THEN MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN SET_TAC [], ASM_REWRITE_TAC []] THEN CONJ_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN RULE_ASSUM_TAC (REWRITE_RULE [HAS_SIZE]) THEN ASM_REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET, GALOIS_GROUP_I] THEN ASM_SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY, IN_INSERT, NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV, ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k /\ (b:A) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [RING_MUL, (← MATCH_MP RING_HOMOMORPHISM_ADD th), (← MATCH_MP RING_HOMOMORPHISM_MUL th)])) THEN ASM_SIMP_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"b:A"), (← q r"x:A")] r1) THEN ASM_REWRITE_TAC [])

  let QUADRATIC_FIELD_CONJUGATION_EXISTS ← prove
    r"!k:A ring.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2
        ==> ?s. s IN group_carrier
                  (galois_group(subfield_generated k {ring_0 k},k) I) /\
                ~(s = I)"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (CONJUNCT2 o (CONJUNCT2 o (MATCH_MP QUADRATIC_FIELD_GALOIS_EXTENSION)))) THEN CONV_TAC (LAND_CONV HAS_SIZE_CONV) THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"f:A->A"), (← q r"g:A->A")] THEN STRIP_TAC THEN ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN ASM_CASES_TAC (← q r"f:A->A = I") THENL [EXISTS_TAC (← q r"g:A->A") THEN ASM_MESON_TAC [], EXISTS_TAC (← q r"f:A->A") THEN ASM_REWRITE_TAC []])

  let QUADRATIC_FIELD_NORM_TRACE_CONJUGATE ← prove
    r"!k:A ring s z.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        s IN group_carrier(galois_group(subfield_generated k {ring_0 k},k) I) /\
        ~(s = I) /\ z IN ring_carrier k
        ==> algebra_norm (subfield_generated k {ring_0 k},k) I z =
            ring_mul k z (s z) /\
            algebra_trace (subfield_generated k {ring_0 k},k) I z =
            ring_add k z (s z)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPEC (← q r"k:A ring") QUADRATIC_FIELD_INTEGER_SQUARE) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"w:A"), (← q r"m:int")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"w:A"), (← q r"s:A->A")] QUADRATIC_FIELD_GALOIS_GROUP) THEN ASM_REWRITE_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN MP_TAC (← ISPEC (← q r"k:A ring") QUADRATIC_FIELD_GALOIS_EXTENSION) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"z:A")] ALGEBRA_TRACE_NORM_GALOIS) THEN ASM_REWRITE_TAC [I_THM] THEN DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC) THEN SUBGOAL_THEN (← q r"(s:A->A) z IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_IN_CARRIER], ALL_TAC] THEN ASM_SIMP_TAC [RING_PRODUCT_CLAUSES, RING_SUM_CLAUSES, FINITE_SING, IN_SING, RING_PRODUCT_SING, RING_SUM_SING, I_THM] THEN ASM_MESON_TAC [])

  let QUADRATIC_FIELD_NORM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!r a b x:A. a IN ring_carrier r /\ b IN ring_carrier r /\
                x IN ring_carrier r
                ==> ring_mul r (ring_add r a (ring_mul r b x))
                               (ring_sub r a (ring_mul r b x)) =
                    ring_sub r (ring_pow r a 2)
                               (ring_mul r (ring_pow r b 2)
                                           (ring_pow r x 2))")
    prove
      r"!k:A ring x a b.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\
          ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
          ring_pow k x 2 IN ring_carrier(subfield_generated k {ring_0 k}) /\
          a IN ring_carrier(subfield_generated k {ring_0 k}) /\
          b IN ring_carrier(subfield_generated k {ring_0 k})
          ==> algebra_norm (subfield_generated k {ring_0 k},k) I
                (ring_add k a (ring_mul k b x)) =
              ring_sub k (ring_pow k a 2)
                         (ring_mul k (ring_pow k b 2) (ring_pow k x 2))"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") QUADRATIC_FIELD_CONJUGATION_EXISTS) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"s:A->A") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"s:A->A")] QUADRATIC_FIELD_GALOIS_GROUP) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k /\ (b:A) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:A->A"), (← q r"ring_add k a (ring_mul k b x):A")] QUADRATIC_FIELD_NORM_TRACE_CONJUGATE) THEN ASM_SIMP_TAC [RING_ADD, RING_MUL] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"b:A"), (← q r"x:A")] r1) THEN ASM_REWRITE_TAC [])

  let QUADRATIC_FIELD_NORM_TRACE_SQRT ← prove
    r"!k:A ring x d a b.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 = ring_of_int k d
        ==> algebra_norm (subfield_generated k {ring_0 k},k) I
              (ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k b) x)) =
            ring_of_int k (a pow 2 - d * b pow 2) /\
            algebra_trace (subfield_generated k {ring_0 k},k) I
              (ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k b) x)) =
            ring_of_int k (&2 * a)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"ring_of_int k a:A"), (← q r"ring_of_int k b:A")] QUADRATIC_FIELD_NORM) THEN ASM_REWRITE_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [RING_OF_INT_SUB, RING_OF_INT_MUL, RING_OF_INT_POW] THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_MUL_SYM THEN SIMP_TAC [RING_POW, RING_OF_INT], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"ring_of_int k a:A"), (← q r"ring_of_int k b:A")] QUADRATIC_FIELD_TRACE) THEN ASM_REWRITE_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [RING_OF_INT_MUL, RING_OF_INT_OF_NUM]])

  let QUADRATIC_FIELD_NORM_TRACE_HALF ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!r a b w:A.
        a IN ring_carrier r /\ b IN ring_carrier r /\ w IN ring_carrier r
        ==> ring_add r (ring_add r a (ring_mul r b w))
                       (ring_add r a (ring_mul r b (ring_sub r (ring_1 r) w))) =
            ring_add r (ring_mul r (ring_of_num r 2) a) b")
    let r2 ← RING_RULE (← q r"!r a b w t:A.
        a IN ring_carrier r /\ b IN ring_carrier r /\ w IN ring_carrier r /\
        t IN ring_carrier r /\ ring_pow r w 2 = ring_sub r w t
        ==> ring_mul r (ring_add r a (ring_mul r b w))
                       (ring_add r a (ring_mul r b (ring_sub r (ring_1 r) w))) =
            ring_add r (ring_pow r a 2)
                       (ring_add r (ring_mul r a b)
                                   (ring_mul r t (ring_pow r b 2)))")
    let r3 ← RING_RULE (← q r"!r x w u e:A. x IN ring_carrier r /\ w IN ring_carrier r /\
                    u IN ring_carrier r /\ e IN ring_carrier r /\
                    ring_mul r (ring_of_num r 2) w = ring_add r (ring_1 r) x /\
                    ring_pow r x 2 = e /\
                    ring_mul r (ring_of_num r 4) u = ring_sub r (ring_1 r) e
                    ==> ring_mul r (ring_of_num r 4) (ring_pow r w 2) =
                        ring_mul r (ring_of_num r 4) (ring_sub r w u)")
    let r4 ← INTEGER_RULE (← q r"!d n:int. (d == &1) (mod n) ==> n divides (&1 - d)")
    let r5 ← RING_RULE (← q r"!r x w:A. x IN ring_carrier r /\ w IN ring_carrier r /\
                ring_mul r (ring_of_num r 2) w = ring_add r (ring_1 r) x
                ==> ring_add r (ring_1 r) (ring_neg r x) =
                    ring_mul r (ring_of_num r 2)
                               (ring_sub r (ring_1 r) w)")
    prove
      r"!k:A ring x d a b.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\
          ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
          ring_pow k x 2 = ring_of_int k d /\ (d == &1) (mod &4)
          ==> algebra_norm (subfield_generated k {ring_0 k},k) I
                (ring_add k (ring_of_int k a)
                   (ring_mul k (ring_of_int k b)
                      (ring_div k (ring_add k (ring_1 k) x)
                                  (ring_of_num k 2)))) =
              ring_of_int k (a pow 2 + a * b + ((&1 - d) div &4) * b pow 2) /\
              algebra_trace (subfield_generated k {ring_0 k},k) I
                (ring_add k (ring_of_int k a)
                   (ring_mul k (ring_of_int k b)
                      (ring_div k (ring_add k (ring_1 k) x)
                                  (ring_of_num k 2)))) =
              ring_of_int k (&2 * a + b)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN (← q r"~(ring_of_num k 2 = ring_0 (k:A ring)) /\
                  ~(ring_of_num k 4 = ring_0 (k:A ring))") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_RING_OF_NUM_EQ_0, ARITH_EQ], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{ring_0 k:A}"), (← q r"x:A")] SUBFIELD_GENERATED_HALF_SUCC) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"w = ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2):A") THEN STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") QUADRATIC_FIELD_CONJUGATION_EXISTS) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"s:A->A") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"s:A->A")] QUADRATIC_FIELD_GALOIS_GROUP) THEN ASM_REWRITE_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism(k,k) (s:A->A)") ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_RING_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN (← q r"(s:A->A) w = ring_sub k (ring_1 k) w") ASSUME_TAC THENL [MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"ring_of_num k 2:A")] THEN ASM_SIMP_TAC [RING_OF_NUM, RING_SUB, RING_1] THEN CONJ_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_IN_CARRIER], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"(s:A->A)(ring_mul k (ring_of_num k 2) w)") THEN CONJ_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (SIMP_TAC [RING_OF_NUM, (← ASSUME (← q r"(w:A) IN ring_carrier k")), (← MATCH_MP RING_HOMOMORPHISM_MUL th), (← MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th)])), ALL_TAC] THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [RING_1, (← MATCH_MP RING_HOMOMORPHISM_ADD th), (← MATCH_MP RING_HOMOMORPHISM_1 th)])) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"w:A")] r5) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"t = (&1 - d) div &4:int") THEN SUBGOAL_THEN (← q r"&4 * t:int = &1 - d") ASSUME_TAC THENL [EXPAND_TAC "t" THEN ONCE_REWRITE_TAC [INT_MUL_SYM] THEN REWRITE_TAC [INT_MUL_DIV_EQ] THEN MATCH_MP_TAC r4 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow k w 2 = ring_sub k w (ring_of_int k t):A") ASSUME_TAC THENL [MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"ring_of_num k 4:A")] THEN ASM_SIMP_TAC [RING_OF_NUM, RING_SUB, RING_POW, RING_OF_INT] THEN SUBGOAL_THEN (← q r"ring_mul k (ring_of_num k 4) (ring_of_int k t) =
                    ring_sub k (ring_1 k) (ring_of_int k d):A") MP_TAC THENL [REWRITE_TAC [(← GSYM RING_OF_INT_OF_NUM), (← GSYM RING_OF_INT_MUL), (← GSYM RING_OF_INT_1), (← GSYM RING_OF_INT_SUB)] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"w:A"), (← q r"ring_of_int k t:A"), (← q r"ring_of_int k d:A")] r3) THEN ASM_REWRITE_TAC [RING_OF_INT], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"s:A->A"), (← q r"ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k b) w)
                    :A")] QUADRATIC_FIELD_NORM_TRACE_CONJUGATE) THEN ASM_SIMP_TAC [RING_ADD, RING_MUL, RING_OF_INT] THEN DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC) THEN FIRST_ASSUM (fun th => tactic_of do pure (SIMP_TAC [RING_MUL, RING_OF_INT, (← ASSUME (← q r"(w:A) IN ring_carrier k")), (← MATCH_MP RING_HOMOMORPHISM_ADD th), (← MATCH_MP RING_HOMOMORPHISM_MUL th), (← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th)])) THEN REWRITE_TAC [(← ASSUME (← q r"(s:A->A) w = ring_sub k (ring_1 k) w"))] THEN REWRITE_TAC [RING_OF_INT_ADD, RING_OF_INT_MUL, RING_OF_INT_POW, RING_OF_INT_OF_NUM] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_of_int k a:A"), (← q r"ring_of_int k b:A"), (← q r"w:A"), (← q r"ring_of_int k t:A")] r2), MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_of_int k a:A"), (← q r"ring_of_int k b:A"), (← q r"w:A")] r1)] THEN ASM_REWRITE_TAC [RING_OF_INT])

  let QUADRATIC_FIELD_NORM_TRACE_INTEGRAL_BASIS ← prove
    r"!k:A ring x d w a b.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 = ring_of_int k d /\
        w = (if (d == &1) (mod &4)
             then ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2)
             else x)
        ==> algebra_norm (subfield_generated k {ring_0 k},k) I
              (ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k b) w)) =
            ring_of_int k (if (d == &1) (mod &4)
                           then a pow 2 + a * b + ((&1 - d) div &4) * b pow 2
                           else a pow 2 - d * b pow 2) /\
            algebra_trace (subfield_generated k {ring_0 k},k) I
              (ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k b) w)) =
            ring_of_int k (if (d == &1) (mod &4) then &2 * a + b else &2 * a)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN COND_CASES_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int"), (← q r"a:int"), (← q r"b:int")] QUADRATIC_FIELD_NORM_TRACE_HALF), MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"d:int"), (← q r"a:int"), (← q r"b:int")] QUADRATIC_FIELD_NORM_TRACE_SQRT)] THEN ASM_REWRITE_TAC [])

  let QUADRATIC_FIELD_IDEAL_MUL_CONJUGATE ← prove
    r"!k:A ring s j.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        s IN group_carrier(galois_group(subfield_generated k {ring_0 k},k) I) /\
        ~(s = I) /\
        ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
        ==> ideal_prod (ring_of_integers k) j (IMAGE s j) =
            ideal_generated (ring_of_integers k)
              {ring_of_num k (ideal_norm (ring_of_integers k) j)}"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") QUADRATIC_FIELD_INTEGER_SQUARE) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"w:A"), (← q r"m:int")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"w:A"), (← q r"s:A->A")] QUADRATIC_FIELD_GALOIS_GROUP) THEN ASM_REWRITE_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN MP_TAC (← ISPEC (← q r"k:A ring") QUADRATIC_FIELD_GALOIS_EXTENSION) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"j:A->bool")] NUMBER_FIELD_GALOIS_PRODUCT_IDEAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"s:A->A"), (← q r"j:A->bool")] GALOIS_GROUP_RING_OF_INTEGERS_IDEAL) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN ASM_SIMP_TAC [IDEAL_PRODUCT_INSERT, FINITE_SING, IN_SING, IDEAL_PRODUCT_SING, IMAGE_I])

  let QUADRATIC_FIELD_CONJUGATE_PRIME_PAIR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!r x y:A. x IN ring_carrier r /\ y IN ring_carrier r
                ==> ring_sub r (ring_neg r x) y =
                    ring_neg r (ring_add r x y)")
    prove
      r"!k:A ring x d s p y.
          number_field k /\
          extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
          x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
          ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
          s IN group_carrier(galois_group(subfield_generated k {ring_0 k},k) I) /\
          ~(s = I)
          ==> IMAGE s (ideal_generated (ring_of_integers k)
                         {ring_of_num k p, ring_sub k x (ring_of_int k y)}) =
              ideal_generated (ring_of_integers k)
                {ring_of_num k p, ring_add k x (ring_of_int k y)}"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"s:A->A")] QUADRATIC_FIELD_GALOIS_GROUP) THEN ASM_REWRITE_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_QUADRATIC THEN MAP_EVERY EXISTS_TAC [(← q r"&0:int"), (← q r"--d:int")] THEN ASM_SIMP_TAC [RING_OF_INT_0, RING_MUL_LZERO, RING_ADD_LZERO, RING_NEG, RING_OF_INT, RING_OF_INT_NEG, RING_ADD_RNEG], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_num k p IN ring_carrier(ring_of_integers k) /\
      ring_of_int k y IN ring_carrier(ring_of_integers k) /\
      ring_sub k x (ring_of_int k y) IN ring_carrier(ring_of_integers k) /\
      ring_add k x (ring_of_int k y) IN ring_carrier(ring_of_integers k) /\
      ring_neg k (ring_add k x (ring_of_int k y)) IN
      ring_carrier(ring_of_integers (k:A ring))") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_SUB) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_ADD) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_NEG) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_OF_INT) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_OF_NUM) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"s:A->A"), (← q r"{ring_of_num k p, ring_sub k x (ring_of_int k y):A}")] GALOIS_GROUP_IMAGE_IDEAL_GENERATED) THEN ASM_REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IMAGE_CLAUSES] THEN SUBGOAL_THEN (← q r"ring_homomorphism(k,k) (s:A->A)") ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_RING_HOMOMORPHISM], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th)])) THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [RING_OF_INT, (← MATCH_MP RING_HOMOMORPHISM_SUB th), (← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th)])) THEN SUBGOAL_THEN (← q r"ring_sub k (ring_neg k x) (ring_of_int k y) =
      ring_neg k (ring_add k x (ring_of_int k y)):A") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"ring_of_int k y:A")] r1) THEN ASM_REWRITE_TAC [RING_OF_INT], ALL_TAC] THEN MATCH_MP_TAC IDEAL_GENERATED_PAIR_EQ THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"j:A->bool") THEN STRIP_TAC THEN MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool")] IN_RING_IDEAL_NEG)) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THENL [SUBGOAL_THEN (← q r"ring_add k x (ring_of_int k y) =
                    ring_neg k (ring_neg k (ring_add k x (ring_of_int k y))):A") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_NEG_NEG THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A"), (← q r"ring_of_int k y:A")] RING_ADD) THEN ASM_REWRITE_TAC [RING_OF_INT], ASM_SIMP_TAC []], ASM_SIMP_TAC []])

  -- @@RETURN BEGIN
  return { QUADRATIC_FIELD_SUBFIELD_GENERATED, QUADRATIC_FIELD_GALOIS_EXTENSION,
           QUADRATIC_FIELD_GALOIS_GROUP, QUADRATIC_FIELD_CONJUGATION_EXISTS,
           QUADRATIC_FIELD_NORM_TRACE_CONJUGATE, QUADRATIC_FIELD_NORM,
           QUADRATIC_FIELD_NORM_TRACE_SQRT, QUADRATIC_FIELD_NORM_TRACE_HALF,
           QUADRATIC_FIELD_NORM_TRACE_INTEGRAL_BASIS,
           QUADRATIC_FIELD_IDEAL_MUL_CONJUGATE, QUADRATIC_FIELD_CONJUGATE_PRIME_PAIR }
  -- @@RETURN END

end HolANT.QuadraticIdeals
