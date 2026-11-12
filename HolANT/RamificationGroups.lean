/- ========================================================================= -/
/- ANT: Higher ramification groups (Serre, Local Fields IV 1-2) at a ...   -/
/- ========================================================================= -/
/- File: HolANT/RamificationGroups.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/ramification_groups.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antramificationgroupsdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/ideal_norm.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/prime_split.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/decomposition.ml, ANT/nf_valuation.ml, ANT/relative_degree.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/splitting_types.ml, ANT/nf_decomposition.ml, ANT/hensel.ml, ANT/ideal_euler.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.RamificationGroups fills them).

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
import HolANT.Hensel
import HolANT.IdealEuler

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
open HolANT.Hensel
open HolANT.IdealEuler

namespace HolANT.RamificationGroups

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD1 ADD_CLAUSES ADD_EQ_0 ADD_SYM ARITH ARITH_EQ CARD_DELETE CARD_EQ_0
   CARD_EQ_CARD_IMP CARD_SING CARRIER_SUBGROUP_GENERATED_SUBGROUP
   DECOMPOSITION_GROUP DEDEKIND_IDEAL_POW_MUL_CANCEL
   DEDEKIND_IDEAL_POW_UNIFORMIZER_SPLIT DEDEKIND_IN_IDEAL_POW_VALUATION
   DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL DEDEKIND_PRIME_IDEAL_LOCAL_GENERATOR
   DEDEKIND_PRIME_IDEAL_UNIFORMIZER DEDEKIND_RING_OF_INTEGERS DIVIDES_ONE
   DIVIDES_PRIMEPOW DIVIDES_REFL EQ_MULT_RCANCEL EQ_TRANS EXP EXP_EQ_0 EXTENSION
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_QUOTIENT_RING FIELD_UNIT_GROUP FINITE_DIFF
   FINITE_FIELD_CYCLIC_UNIT_GROUP FINITE_GALOIS_GROUP FINITE_IMAGE
   FINITE_IMP_FIELD_EXTENSION FINITE_INTEGRAL_DOMAIN_CHAR FINITE_PGROUP_SING
   FINITE_SUBSET FIRST_GROUP_ISOMORPHISM_THEOREM FORALL_IN_IMAGE FUN_EQ_THM
   FUN_IN_IMAGE GALOIS_GROUP GALOIS_GROUP_PERMUTES
   GALOIS_GROUP_PRIME_IDEAL_IMAGE GALOIS_GROUP_RING_HOMOMORPHISM
   GALOIS_GROUP_RING_OF_INTEGERS GALOIS_GROUP_SUBRING_IMAGE
   GALOIS_IMP_FIELD_EXTENSION GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET
   GROUP_HOMOMORPHISM GROUP_ID GROUP_INV GROUP_MUL GROUP_MUL_RINV GROUP_POW_1
   GROUP_POW_EQ_ID GROUP_POW_MUL GROUP_POW_SUBGROUP_GENERATED IDEAL_POW_0
   IDEAL_POW_1 IDEAL_POW_ANTIMONO IDEAL_POW_SUBSET_PRIME_IDEAL INERTIA_GROUP
   INERTIA_GROUP_NORMAL_SUBGROUP INTEGRAL_DOMAIN_CHAR
   INTEGRAL_DOMAIN_MUL_LCANCEL IN_ELIM_THM IN_RING_IDEAL_0 IN_RING_IDEAL_ADD
   IN_RING_IDEAL_LMUL IN_RING_IDEAL_RMUL IN_RING_IDEAL_SUB IN_SING
   ISOMORPHIC_GROUP_CARD_EQ ISOMORPHIC_GROUP_CYCLICITY I_THM LAGRANGE_THEOREM
   LAGRANGE_THEOREM_RIGHT LEFT_IMP_EXISTS_THM LE_0 LE_ADD_RCANCEL LE_TRANS
   MAXIMAL_IDEAL_FINITE_QUOTIENT_POW_CARD MONO_EXISTS MULT_AC : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (MULT_CLAUSES MULT_SYM NORMAL_PGROUP_SUBSET_COPRIME_INDEX
   NORMAL_SUBGROUP_GROUP_KERNEL NORMAL_SUBGROUP_IMP_SUBGROUP NOT_SUC
   NUMBER_FIELD_DECOMPOSITION_GROUP NUMBER_FIELD_PRIME_IDEAL_ABOVE
   NUMBER_FIELD_TOWER_LAW PERMUTES_IN_IMAGE PGROUP_SING PRIME_GE_2
   PRIME_IMP_RING_IDEAL QUOTIENT_GROUP QUOTIENT_RING QUOTIENT_RING_0
   QUOTIENT_RING_1 QUOTIENT_RING_ADD QUOTIENT_RING_CARRIER QUOTIENT_RING_MUL
   RIGHT_FORALL_IMP_THM RIGHT_IMP_EXISTS_THM RING_0 RING_1 RING_ADD
   RING_ADDITIVE_GROUP RING_CARRIER_NONEMPTY
   RING_CARRIER_SUBRING_GENERATED_SUBSET RING_CHAR_DIVIDES_ORDER
   RING_CHAR_FINITE RING_COSET_0 RING_COSET_EQ RING_COSET_EQ_IDEAL
   RING_HOMOMORPHISM_1 RING_HOMOMORPHISM_ADD RING_HOMOMORPHISM_MUL
   RING_HOMOMORPHISM_RING_COSET RING_HOMOMORPHISM_RING_OF_NUM
   RING_HOMOMORPHISM_SUB RING_IDEAL_ADD_IN_EQ RING_IDEAL_IDEAL_POW
   RING_IDEAL_IMP_SUBSET RING_ISOMORPHISM_IDEAL_POW
   RING_ISOMORPHISM_IMP_HOMOMORPHISM RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL
   RING_MUL_IN_IDEAL_POW RING_MUL_LID RING_MUL_LZERO RING_MUL_RZERO
   RING_OF_INTEGERS_FRACTION_FIELD RING_OF_INTEGERS_SUBRING RING_OF_NUM
   RING_OF_NUM_0 RING_OF_NUM_EQ_0 RING_POW RING_SUB RING_SUB_EQ_0 RING_SUB_REFL
   RING_SUB_SUBRING_GENERATED SKOLEM_THM SUBGROUP_GROUP_IMAGE
   SUBGROUP_OF_CYCLIC_GROUP SUBGROUP_OF_IMP_SUBSET
   SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ SUBRING_GENERATED SUBSET
   SUBSET_ANTISYM SUC_SUB1 TRIVIAL_SUBGROUP_OF UNIT_GROUP decomposition_group
   divides field_extension field_of_fractions group_kernel group_pow
   inertia_group num_FINITE o_THM permutes ring_homomorphism ring_of_num
   ring_pow ring_unit subgroup_of : thm)
  deriving Inhabited

/-- What ramification_groups.ml uses from Session besides theorems. -/
structure RamificationGroupsDeps where
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
  NUMBER_TAC : tactic
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
/- ramification_groups.ml phrases from line 118 to 721                    -/
/- ---------------------------------------------------------------------- -/

structure RamificationGroups01 where
  -- @@FIELDS
  RING_HOMOMORPHISM_POW_DIFFERENCE : thm
  DEDEKIND_UNIFORMIZER_CONGRUENCE_STEP : thm
  DEDEKIND_UNIFORMIZER_CONGRUENCE : thm
  DECOMPOSITION_GROUP_IDEAL_POW : thm
  INERTIA_GROUP_IDEAL_POW_0 : thm
  INERTIA_GROUP_IDEAL_POW : thm
  INERTIA_GROUP_IDEAL_POW_MONO : thm
  INERTIA_GROUP_IDEAL_POW_NORMAL : thm
  INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL : thm
  INERTIA_GROUP_IDEAL_POW_UNIFORMIZER : thm
  DEDEKIND_IDEAL_POW_UNIFORMIZER_MUL : thm
  DEDEKIND_IDEAL_POW_UNIFORMIZER_UNIQUE : thm
  INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM : thm
  INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_EXISTS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupRamificationGroups01 [HolBase] (D : RamificationGroupsDeps) :
    ExceptT String IO RamificationGroups01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC,
        RING_RULE, SET_TAC, TAUT, .. } := D
  let { ADD1, ADD_CLAUSES, ADD_EQ_0, ADD_SYM, ARITH, ARITH_EQ, DECOMPOSITION_GROUP,
        DEDEKIND_IDEAL_POW_MUL_CANCEL, DEDEKIND_IDEAL_POW_UNIFORMIZER_SPLIT,
        DEDEKIND_IN_IDEAL_POW_VALUATION, DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL,
        DEDEKIND_PRIME_IDEAL_LOCAL_GENERATOR, EQ_TRANS, EXTENSION,
        FIELD_IMP_INTEGRAL_DOMAIN, FINITE_GALOIS_GROUP, FINITE_IMAGE,
        FINITE_IMP_FIELD_EXTENSION, FORALL_IN_IMAGE, FUN_EQ_THM, FUN_IN_IMAGE,
        GALOIS_GROUP_PERMUTES, GALOIS_GROUP_PRIME_IDEAL_IMAGE,
        GALOIS_GROUP_RING_HOMOMORPHISM, GALOIS_GROUP_SUBRING_IMAGE, GROUP_ID,
        IDEAL_POW_0, IDEAL_POW_1, IDEAL_POW_ANTIMONO, IDEAL_POW_SUBSET_PRIME_IDEAL,
        INERTIA_GROUP, INERTIA_GROUP_NORMAL_SUBGROUP, INTEGRAL_DOMAIN_MUL_LCANCEL,
        IN_ELIM_THM, IN_RING_IDEAL_0, IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL,
        IN_RING_IDEAL_RMUL, IN_RING_IDEAL_SUB, IN_SING, I_THM, LEFT_IMP_EXISTS_THM,
        LE_ADD_RCANCEL, LE_TRANS, MAXIMAL_IDEAL_FINITE_QUOTIENT_POW_CARD, MONO_EXISTS, .. } := D.core1
  let { NOT_SUC, PERMUTES_IN_IMAGE, PRIME_IMP_RING_IDEAL, RIGHT_FORALL_IMP_THM,
        RIGHT_IMP_EXISTS_THM, RING_0, RING_1, RING_CARRIER_SUBRING_GENERATED_SUBSET,
        RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_SUB,
        RING_IDEAL_ADD_IN_EQ, RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET,
        RING_ISOMORPHISM_IDEAL_POW, RING_ISOMORPHISM_IMP_HOMOMORPHISM, RING_MUL,
        RING_MUL_IN_IDEAL_POW, RING_MUL_LZERO, RING_MUL_RZERO, RING_OF_NUM,
        RING_OF_NUM_0, RING_POW, RING_SUB, RING_SUB_EQ_0, RING_SUB_REFL,
        RING_SUB_SUBRING_GENERATED, SKOLEM_THM, SUBRING_GENERATED, SUBSET,
        SUBSET_ANTISYM, decomposition_group, field_extension, field_of_fractions,
        num_FINITE, permutes, ring_homomorphism, ring_of_num, ring_pow, .. } := D.core2
  -- @@SCOPE END

  let RING_HOMOMORPHISM_POW_DIFFERENCE ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"!r x a X Y M:A.
          x IN ring_carrier r /\ a IN ring_carrier r /\
          X IN ring_carrier r /\ Y IN ring_carrier r /\ M IN ring_carrier r
          ==> ring_sub r
               (ring_mul r x (ring_sub r (ring_mul r a Y) (ring_mul r x X)))
               (ring_mul r (ring_add r M (ring_1 r))
                 (ring_mul r (ring_mul r x X) (ring_sub r a x))) =
              ring_add r
               (ring_mul r (ring_sub r (ring_mul r x (ring_sub r Y X))
                             (ring_mul r M (ring_mul r X (ring_sub r a x)))) a)
               (ring_mul r M (ring_mul r X
                 (ring_mul r (ring_sub r a x) (ring_sub r a x))))"
    let r2 ← RING_RULE q1
    let q3 ← q r"ring_sub r
       (ring_mul r x (ring_sub r (ring_mul r a Y) (ring_mul r x X)))
       (ring_mul r (ring_add r M (ring_1 r))
         (ring_mul r (ring_mul r x X) (ring_sub r a x))) =
      ring_add r
       (ring_mul r (ring_sub r (ring_mul r x (ring_sub r Y X))
                     (ring_mul r M (ring_mul r X (ring_sub r a x)))) a)
       (ring_mul r M (ring_mul r X
         (ring_mul r (ring_sub r a x) (ring_sub r a (x:A)))))"
    let p4 ← prove r"!r k x a X Y M:A.
        ring_ideal r k /\ x IN ring_carrier r /\ a IN ring_carrier r /\
        X IN ring_carrier r /\ Y IN ring_carrier r /\ M IN ring_carrier r /\
        ring_sub r (ring_mul r x (ring_sub r Y X))
                   (ring_mul r M (ring_mul r X (ring_sub r a x))) IN k /\
        ring_mul r (ring_sub r a x) (ring_sub r a x) IN k
        ==> ring_sub r
             (ring_mul r x (ring_sub r (ring_mul r a Y) (ring_mul r x X)))
             (ring_mul r (ring_add r M (ring_1 r))
               (ring_mul r (ring_mul r x X) (ring_sub r a x))) IN k" (REPEAT STRIP_TAC THEN SUBGOAL_THEN q3 SUBST1_TAC THENL [MATCH_MP_TAC r2 THEN ASM_REWRITE_TAC [], MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_REWRITE_TAC [], MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_REWRITE_TAC []]])
    let lemma := p4
    let q5 ← q r"(f:A->A) x IN ring_carrier r"
    prove
      r"!r k (f:A->A) x m.
          ring_homomorphism(r,r) f /\ ring_ideal r k /\ x IN ring_carrier r /\
          ring_mul r (ring_sub r (f x) x) (ring_sub r (f x) x) IN k
          ==> ring_sub r
               (ring_mul r x (ring_sub r (f(ring_pow r x m)) (ring_pow r x m)))
               (ring_mul r (ring_of_num r m)
                 (ring_mul r (ring_pow r x m) (ring_sub r (f x) x))) IN k"
      (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o ((REWRITE_RULE [SUBSET, FORALL_IN_IMAGE]) o (CONJUNCT1 o (REWRITE_RULE [ring_homomorphism])))) THEN SUBGOAL_THEN q5 ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN INDUCT_TAC THENL [REWRITE_TAC [ring_pow, RING_OF_NUM_0] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_1 th)])) THEN ASM_SIMP_TAC [RING_SUB_REFL, RING_1, RING_MUL_RZERO, RING_MUL_LZERO, RING_MUL, RING_SUB, RING_0, IN_RING_IDEAL_0], REWRITE_TAC [ring_pow, ring_of_num] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th), RING_POW])) THEN MATCH_MP_TAC lemma THEN ASM_SIMP_TAC [RING_POW, RING_OF_NUM]])

  let DEDEKIND_UNIFORMIZER_CONGRUENCE_STEP ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!r a b c d:A.
        a IN ring_carrier r /\ b IN ring_carrier r /\
        c IN ring_carrier r /\ d IN ring_carrier r
        ==> ring_sub r a b =
            ring_sub r (ring_sub r c d)
                       (ring_sub r (ring_sub r c a) (ring_sub r d b))")
    let r2 ← RING_RULE (← q r"ring_add r (ring_sub r a b) b = a:A")
    let r6 ← RING_RULE (← q r"!r s y t z fs fy ft fz:A.
          s IN ring_carrier r /\ y IN ring_carrier r /\
          t IN ring_carrier r /\ z IN ring_carrier r /\
          fs IN ring_carrier r /\ fy IN ring_carrier r /\
          ft IN ring_carrier r /\ fz IN ring_carrier r /\
          ring_mul r s y = ring_mul r t z /\
          ring_mul r fs fy = ring_mul r ft fz
          ==> ring_mul r s (ring_sub r fy y) =
              ring_sub r (ring_add r (ring_mul r (ring_sub r ft t) fz)
                                     (ring_mul r t (ring_sub r fz z)))
                         (ring_mul r (ring_sub r fs s) fy)")
    let r10 ← RING_RULE (← q r"ring_add r (ring_sub r a b) b = a:A")
    prove
      r"!r p (f:A->A) t n.
          dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
          FINITE(ring_carrier(quotient_ring r p)) /\
          ring_homomorphism(r,r) f /\
          t IN p /\ ~(t IN ideal_pow r p 2) /\ ~(n = 0) /\
          (!x. x IN ring_carrier r ==> ring_sub r (f x) x IN ideal_pow r p n) /\
          ring_sub r (f t) t IN ideal_pow r p (n + 1)
          ==> !x. x IN ring_carrier r
                  ==> ring_sub r (f x) x IN ideal_pow r p (n + 1)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"maximal_ideal r (p:A->bool)") ASSUME_TAC THENL [ASM_MESON_TAC [DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o ((REWRITE_RULE [SUBSET, FORALL_IN_IMAGE]) o (CONJUNCT1 o (REWRITE_RULE [ring_homomorphism])))) THEN SUBGOAL_THEN (← q r"(p:A->bool) SUBSET ring_carrier r") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier r") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_pow r p n SUBSET (p:A->bool)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"1:num"), (← q r"n:num")] IDEAL_POW_ANTIMONO) THEN ASM_SIMP_TAC [IDEAL_POW_1] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"!y. y IN p ==> (f:A->A) y IN p") ASSUME_TAC THENL [X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier r") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(f:A->A) y = ring_add r (ring_sub r (f y) y) y") SUBST1_TAC THENL [ASM_SIMP_TAC [r10], MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do let z9 ← (q r"ideal_pow r p n SUBSET (p:A->bool)"); let z8 ← (do let z7 ← (pure th); pure (concl z7)); pure (z8 == z9)))))) THEN ASM_SIMP_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y. y IN p ==> ring_sub r ((f:A->A) y) y IN ideal_pow r p (n + 1)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"t:A")] DEDEKIND_PRIME_IDEAL_LOCAL_GENERATOR) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"s:A") STRIP_ASSUME_TAC) THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"y:A"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"z:A") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier r") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul r ((f:A->A) s) (f y) = ring_mul r (f t) (f z)") ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP RING_HOMOMORPHISM_MUL)) THEN DISCH_THEN (fun th => tactic_of do pure (ASM_SIMP_TAC [(← GSYM th)])), ALL_TAC] THEN MATCH_MP_TAC DEDEKIND_IDEAL_POW_MUL_CANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"s:A"), (← q r"0:num")] THEN ASM_SIMP_TAC [RING_SUB, ADD_CLAUSES, IDEAL_POW_1] THEN SUBGOAL_THEN (← q r"ring_mul r s (ring_sub r ((f:A->A) y) y) =
        ring_sub r (ring_add r (ring_mul r (ring_sub r (f t) t) (f z))
                               (ring_mul r t (ring_sub r (f z) z)))
                   (ring_mul r (ring_sub r (f s) s) (f y))") SUBST1_TAC THENL [MATCH_MP_TAC r6 THEN ASM_SIMP_TAC [], ALL_TAC] THEN MATCH_MP_TAC IN_RING_IDEAL_SUB THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN CONJ_TAC THENL [MATCH_MP_TAC IN_RING_IDEAL_ADD THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN CONJ_TAC THENL [MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW], ONCE_REWRITE_TAC [ADD_SYM] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC [IDEAL_POW_1]], MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC [IDEAL_POW_1]], ALL_TAC] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"(x:A) IN p") THENL [ASM_SIMP_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"q = CARD(ring_carrier(quotient_ring r (p:A->bool)))") THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool")] MAXIMAL_IDEAL_FINITE_QUOTIENT_POW_CARD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o (SPEC (← q r"x:A")))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(f:A->A) x IN ring_carrier r /\
                  ring_pow r x q IN ring_carrier r /\
                  f(ring_pow r x q) IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_pow r p (n + 1):A->bool"), (← q r"f:A->A"), (← q r"x:A"), (← q r"q:num")] RING_HOMOMORPHISM_POW_DIFFERENCE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC [IDEAL_POW_1] THEN FIRST_X_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do let z5 ← (q r"ideal_pow r p n SUBSET (p:A->bool)"); let z4 ← (do let z3 ← (pure th); pure (concl z3)); pure (z4 == z5)))))) THEN ASM_SIMP_TAC [], DISCH_TAC] THEN SUBGOAL_THEN (← q r"!a b:A. a IN ring_carrier r /\ b IN ideal_pow r p (n + 1) /\
              ring_sub r a b IN ideal_pow r p (n + 1)
              ==> a IN ideal_pow r p (n + 1)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(b:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"a:A = ring_add r (ring_sub r a b) b") SUBST1_TAC THENL [ASM_SIMP_TAC [r2], ASM_SIMP_TAC [IN_RING_IDEAL_ADD, RING_IDEAL_IDEAL_POW]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub r ((f:A->A)(ring_pow r x q)) (ring_pow r x q)
      IN ideal_pow r p (n + 1)") ASSUME_TAC THENL [MATCH_MP_TAC DEDEKIND_IDEAL_POW_MUL_CANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"x:A"), (← q r"0:num")] THEN ASM_SIMP_TAC [ADD_CLAUSES, IDEAL_POW_1, RING_SUB] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC (← q r"ring_mul r (ring_of_num r q)
          (ring_mul r (ring_pow r x q) (ring_sub r ((f:A->A) x) x))") THEN ASM_SIMP_TAC [RING_MUL, RING_SUB] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC [IDEAL_POW_1] THEN MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub r ((f:A->A) x) x =
      ring_sub r (ring_sub r (f(ring_pow r x q)) (ring_pow r x q))
                 (ring_sub r (f(ring_sub r (ring_pow r x q) x))
                             (ring_sub r (ring_pow r x q) x))") SUBST1_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_SUB th)])) THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [], MATCH_MP_TAC IN_RING_IDEAL_SUB THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW]])

  let DEDEKIND_UNIFORMIZER_CONGRUENCE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"n + 1 <= SUC n + 1")
    prove
      r"!r p (f:A->A) t n.
          dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
          FINITE(ring_carrier(quotient_ring r p)) /\
          ring_homomorphism(r,r) f /\
          (!x. x IN ring_carrier r ==> ring_sub r (f x) x IN p) /\
          t IN p /\ ~(t IN ideal_pow r p 2)
          ==> ((!x. x IN ring_carrier r
                    ==> ring_sub r (f x) x IN ideal_pow r p (n + 1)) <=>
               ring_sub r (f t) t IN ideal_pow r p (n + 1))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [PRIME_IMP_RING_IDEAL, RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN EQ_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SPEC_TAC ((← q r"n:num"), (← q r"n:num")) THEN INDUCT_TAC THENL [ASM_SIMP_TAC [ADD_CLAUSES, IDEAL_POW_1, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN DISCH_TAC THEN MATCH_MP_TAC DEDEKIND_UNIFORMIZER_CONGRUENCE_STEP THEN EXISTS_TAC (← q r"t:A") THEN ASM_REWRITE_TAC [NOT_SUC] THEN REWRITE_TAC [ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"n + 1:num"), (← q r"SUC n + 1")] IDEAL_POW_ANTIMONO) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_IDEAL_IMP_SUBSET, r1] THEN ASM SET_TAC [])

  let DECOMPOSITION_GROUP_IDEAL_POW ← prove
    r"!(h:A->B) k l b Q i.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        prime_ideal b Q
        ==> decomposition_group(k,l) h (ideal_pow b Q (i + 1)) =
            decomposition_group(k,l) h Q"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [decomposition_group] THEN AP_TERM_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"f:B->B") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"f IN group_carrier(galois_group(k,l) (h:A->B))") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"f:B->B")] GALOIS_GROUP_SUBRING_IMAGE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"b:B ring"), (← q r"f:B->B"), (← q r"Q:B->bool"), (← q r"i + 1:num")] RING_ISOMORPHISM_IDEAL_POW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"f:B->B"), (← q r"Q:B->bool")] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN STRIP_TAC THEN EQ_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"!J:B->bool. ring_ideal b J ==> ideal_pow b J (i + 1) SUBSET J") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"J:B->bool"), (← q r"1:num"), (← q r"i + 1:num")] IDEAL_POW_ANTIMONO) THEN ASM_SIMP_TAC [IDEAL_POW_1, RING_IDEAL_IMP_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC, ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"IMAGE (f:B->B) Q"), (← q r"i + 1:num")] IDEAL_POW_SUBSET_PRIME_IDEAL) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, ADD_EQ_0, ARITH_EQ] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [], MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"IMAGE (f:B->B) Q"), (← q r"Q:B->bool"), (← q r"i + 1:num")] IDEAL_POW_SUBSET_PRIME_IDEAL) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, ADD_EQ_0, ARITH_EQ] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN UNDISCH_TAC (← q r"ideal_pow b (IMAGE (f:B->B) Q) (i + 1) = ideal_pow b Q (i + 1)") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC []])

  let INERTIA_GROUP_IDEAL_POW_0 ← prove
    r"!(h:A->B) k l b Q.
        ring_ideal b Q
        ==> inertia_group(k,l) h b (ideal_pow b Q 1) =
            inertia_group(k,l) h b Q"
    (SIMP_TAC [IDEAL_POW_1])

  let INERTIA_GROUP_IDEAL_POW ← prove
    r"!(h:A->B) k l b Q i.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        prime_ideal b Q
        ==> group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1))) =
            {f | f IN group_carrier(decomposition_group(k,l) h Q) /\
                 !x. x IN ring_carrier b
                     ==> ring_sub l (f x) x IN ideal_pow b Q (i + 1)}"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"i:num")] DECOMPOSITION_GROUP_IDEAL_POW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [INERTIA_GROUP, RING_IDEAL_IDEAL_POW, DECOMPOSITION_GROUP, IN_ELIM_THM] THEN SET_TAC [])

  let INERTIA_GROUP_IDEAL_POW_MONO ← prove
    r"!(h:A->B) k l b Q i j.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        prime_ideal b Q /\ i <= j
        ==> group_carrier(inertia_group(k,l) h b (ideal_pow b Q (j + 1)))
            SUBSET
            group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1)))"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [INERTIA_GROUP_IDEAL_POW] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"i + 1:num"), (← q r"j + 1:num")] IDEAL_POW_ANTIMONO) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_IDEAL_IMP_SUBSET, LE_ADD_RCANCEL] THEN SET_TAC [])

  let INERTIA_GROUP_IDEAL_POW_NORMAL ← prove
    r"!(h:A->B) k l b Q i.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        prime_ideal b Q
        ==> group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1)))
            normal_subgroup_of decomposition_group(k,l) h Q"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"i:num")] DECOMPOSITION_GROUP_IDEAL_POW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC INERTIA_GROUP_NORMAL_SUBGROUP THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW])

  let INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r10 ← TAUT (← q r"p ==> ~p ==> q")
    prove
      r"!(h:A->B) k l b Q.
          finite_extension(k,l) h /\
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          dedekind_domain b /\ field_of_fractions(b,l) I /\
          prime_ideal b Q /\ ~(Q = {ring_0 l})
          ==> ?N. !i. N <= i
                      ==> group_carrier
                           (inertia_group(k,l) h b (ideal_pow b Q (i + 1))) =
                          {I}"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP FINITE_IMP_FIELD_EXTENSION)) THEN REWRITE_TAC [field_extension] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_0 b = ring_0 (l:B ring) /\ ring_sub b = ring_sub l /\
      ring_mul b = ring_mul l /\ ring_carrier b SUBSET ring_carrier l") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED), RING_SUB_SUBRING_GENERATED, RING_CARRIER_SUBRING_GENERATED_SUBSET], ALL_TAC] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [I_THM]) o (GEN_REWRITE_RULE id [field_of_fractions]))) THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(galois_group(k,l) (h:A->B)) /\ ~(f = I)
          ==> ?x. x IN ring_carrier b /\ ~(f x = x)") ASSUME_TAC THENL [X_GEN_TAC (← q r"f:B->B") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"!x:B. x IN ring_carrier b ==> f x = x") THENL [ALL_TAC, ASM_MESON_TAC []] THEN UNDISCH_TAC (← q r"~(f:B->B = I)") THEN MATCH_MP_TAC r10 THEN REWRITE_TAC [FUN_EQ_THM, I_THM] THEN X_GEN_TAC (← q r"z:B") THEN ASM_CASES_TAC (← q r"(z:B) IN ring_carrier l") THENL [ALL_TAC, FIRST_ASSUM (MP_TAC o (CONJUNCT1 o ((REWRITE_RULE [permutes]) o (MATCH_MP GALOIS_GROUP_PERMUTES)))) THEN ASM_SIMP_TAC []] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"z:B")) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); canM (fun z3 => (do let z4 ← (pure z3); find_termM (fun z5 => (do let z7 ← (pure z5); let z6 ← (q r"ring_mul (l:B ring)"); pure (z6 == z7))) z4)) z1) then (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); pure (is_forall z8)) else pure false))))) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:B"), (← q r"s:B")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(s:B) IN ring_carrier l /\ (a:B) IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(f:B->B) z IN ring_carrier l") ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_PERMUTES)) THEN DISCH_THEN (fun th => tactic_of do pure (ASM_REWRITE_TAC [(← MATCH_MP PERMUTES_IN_IMAGE th)])), ALL_TAC] THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"l:B ring"), (← q r"s:B")] THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM)) THEN DISCH_THEN (MP_TAC o ((SPECL [(← q r"s:B"), (← q r"z:B")]) o (MATCH_MP RING_HOMOMORPHISM_MUL))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [] THEN TRANS_TAC EQ_TRANS (← q r"(f:B->B)(ring_mul l s z)") THEN CONJ_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM)) THEN DISCH_THEN (MP_TAC o ((SPECL [(← q r"s:B"), (← q r"z:B")]) o (MATCH_MP RING_HOMOMORPHISM_MUL))) THEN ASM_SIMP_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← SYM th)])) THEN ASM_SIMP_TAC [], ASM_SIMP_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(galois_group(k,l) (h:A->B)) /\ ~(f = I)
          ==> ?m. ~(f IN group_carrier
                          (inertia_group(k,l) h b (ideal_pow b Q (m + 1))))") MP_TAC THENL [X_GEN_TAC (← q r"f:B->B") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"f:B->B"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"x:B") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"ring_sub l ((f:B->B) x) x IN ring_carrier b /\
        ~(ring_sub l (f x) x = ring_0 b)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"ring_sub b = ring_sub (l:B ring)") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"(f:B->B) x IN ring_carrier b") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [RING_SUB, RING_SUB_EQ_0], ALL_TAC] THEN EXISTS_TAC (← q r"ideal_valuation b Q (ideal_generated b {ring_sub l ((f:B->B) x) x})") THEN ASM_SIMP_TAC [INERTIA_GROUP_IDEAL_POW, IN_ELIM_THM] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"x:B")) o CONJUNCT2)) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"ring_sub l ((f:B->B) x) x"), (← q r"ideal_valuation b Q
                       (ideal_generated b {ring_sub l ((f:B->B) x) x}) + 1")] DEDEKIND_IN_IDEAL_POW_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ARITH_TAC, ALL_TAC] THEN DISCH_THEN (MP_TAC o (REWRITE_RULE [RIGHT_IMP_EXISTS_THM, SKOLEM_THM])) THEN DISCH_THEN (X_CHOOSE_TAC (← q r"m:(B->B)->num")) THEN MP_TAC (← ISPEC (← q r"IMAGE (m:(B->B)->num) (group_carrier(galois_group(k,l) (h:A->B)))") num_FINITE) THEN ASM_SIMP_TAC [FINITE_IMAGE, FINITE_GALOIS_GROUP, FORALL_IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"N:num") THEN DISCH_TAC THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"f:B->B") THEN REWRITE_TAC [IN_SING] THEN EQ_TAC THENL [DISCH_TAC THEN SUBGOAL_THEN (← q r"f IN group_carrier(galois_group(k,l) (h:A->B))") ASSUME_TAC THENL [UNDISCH_TAC (← q r"f IN group_carrier(inertia_group(k,l) (h:A->B) b
                                  (ideal_pow b Q (i + 1)))") THEN ASM_SIMP_TAC [INERTIA_GROUP_IDEAL_POW, DECOMPOSITION_GROUP, IN_ELIM_THM], ALL_TAC] THEN ASM_CASES_TAC (← q r"f:B->B = I") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"group_carrier(inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1)))
          SUBSET
          group_carrier(inertia_group(k,l) h b (ideal_pow b Q (m(f:B->B) + 1)))") MP_TAC THENL [MATCH_MP_TAC INERTIA_GROUP_IDEAL_POW_MONO THEN ASM_REWRITE_TAC [] THEN TRANS_TAC LE_TRANS (← q r"N:num") THEN ASM_SIMP_TAC [], ASM SET_TAC []], DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPEC (← q r"inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1))") GROUP_ID) THEN REWRITE_TAC [(← CONJUNCT1 (← CONJUNCT2 INERTIA_GROUP))]])

  let INERTIA_GROUP_IDEAL_POW_UNIFORMIZER ← prove
    r"!(h:A->B) k l b Q t f n.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        dedekind_domain b /\ prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
        FINITE(ring_carrier(quotient_ring b Q)) /\
        t IN Q /\ ~(t IN ideal_pow b Q 2) /\
        f IN group_carrier(inertia_group(k,l) h b Q)
        ==> (f IN group_carrier
                    (inertia_group(k,l) h b (ideal_pow b Q (n + 1))) <=>
             ring_sub l (f t) t IN ideal_pow b Q (n + 1))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_0 b = ring_0 (l:B ring) /\ ring_sub b = ring_sub l") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED), RING_SUB_SUBRING_GENERATED], ALL_TAC] THEN UNDISCH_TAC (← q r"f IN group_carrier(inertia_group(k,l) (h:A->B) b Q)") THEN ASM_SIMP_TAC [INERTIA_GROUP, INERTIA_GROUP_IDEAL_POW, PRIME_IMP_RING_IDEAL, DECOMPOSITION_GROUP, IN_ELIM_THM] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"f:B->B")] GALOIS_GROUP_SUBRING_IMAGE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN FIRST_X_ASSUM (SUBST_ALL_TAC o (SYM o (checkM (fun th => (do let z3 ← (q r"ring_sub b = ring_sub (l:B ring)"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3)))))) THEN MATCH_MP_TAC DEDEKIND_UNIFORMIZER_CONGRUENCE THEN ASM_SIMP_TAC [RING_ISOMORPHISM_IMP_HOMOMORPHISM])

  let DEDEKIND_IDEAL_POW_UNIFORMIZER_MUL ← prove
    r"!r p (t:A) x n.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
        t IN p /\ ~(t IN ideal_pow r p 2) /\ x IN ring_carrier r
        ==> (ring_mul r t x IN ideal_pow r p (n + 1) <=>
             x IN ideal_pow r p n)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"(p:A->bool) SUBSET ring_carrier r /\ (t:A) IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN EQ_TAC THEN DISCH_TAC THENL [MATCH_MP_TAC DEDEKIND_IDEAL_POW_MUL_CANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"t:A"), (← q r"1:num")] THEN ASM_REWRITE_TAC [ARITH], MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC [IDEAL_POW_1]])

  let DEDEKIND_IDEAL_POW_UNIFORMIZER_UNIQUE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_add r (ring_sub r x (ring_mul r c t))
                 (ring_mul r t (ring_sub r c d)) =
      ring_sub r x (ring_mul r d t):A")
    prove
      r"!r p (t:A) x c d n.
          dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
          t IN p /\ ~(t IN ideal_pow r p 2) /\
          x IN ring_carrier r /\ c IN ring_carrier r /\ d IN ring_carrier r /\
          ring_sub r x (ring_mul r c t) IN ideal_pow r p (n + 1)
          ==> (ring_sub r x (ring_mul r d t) IN ideal_pow r p (n + 1) <=>
               ring_sub r c d IN ideal_pow r p n)"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [PRIME_IMP_RING_IDEAL, RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub r x (ring_mul r d t) =
      ring_add r (ring_sub r x (ring_mul r c t))
                 (ring_mul r t (ring_sub r c d)):A") SUBST1_TAC THENL [ASM_SIMP_TAC [r1], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_pow r p (n + 1):A->bool"), (← q r"ring_sub r x (ring_mul r c t):A"), (← q r"ring_mul r t (ring_sub r c d):A")] RING_IDEAL_ADD_IN_EQ) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, RING_MUL, RING_SUB], ALL_TAC] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN MATCH_MP_TAC DEDEKIND_IDEAL_POW_UNIFORMIZER_MUL THEN ASM_SIMP_TAC [RING_SUB])

  let INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM ← prove
    r"!(h:A->B) k l b Q i f.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        prime_ideal b Q /\
        f IN group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1)))
        ==> ring_isomorphism(b,b) f /\
            (!j x. x IN ideal_pow b Q j ==> f x IN ideal_pow b Q j) /\
            (!x. x IN ring_carrier b
                 ==> ring_sub l (f x) x IN ideal_pow b Q (i + 1))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN UNDISCH_TAC (← q r"f IN group_carrier
          (inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1)))") THEN ASM_SIMP_TAC [INERTIA_GROUP_IDEAL_POW, DECOMPOSITION_GROUP, IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"f:B->B")] GALOIS_GROUP_SUBRING_IMAGE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [(← q r"j:num"), (← q r"x:B")] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"b:B ring"), (← q r"f:B->B"), (← q r"Q:B->bool"), (← q r"j:num")] RING_ISOMORPHISM_IDEAL_POW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [FUN_IN_IMAGE])

  let INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_EXISTS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!r F t a w:B.
      F IN ring_carrier r /\ t IN ring_carrier r /\ a IN ring_carrier r /\
      w IN ring_carrier r /\ ring_sub r F t = ring_add r (ring_mul r t a) w
      ==> ring_sub r F (ring_mul r (ring_add r (ring_1 r) a) t) = w")
    let r2 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!(h:A->B) k l b Q t i f.
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          dedekind_domain b /\ prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
          t IN Q /\ ~(t IN ideal_pow b Q 2) /\
          f IN group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1)))
          ==> ?a. a IN ideal_pow b Q i /\
                  ring_sub l (f t) (ring_mul l (ring_add l (ring_1 l) a) t)
                  IN ideal_pow b Q (i + 2)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"i:num"), (← q r"f:B->B")] INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_0 l = ring_0 (b:B ring) /\ ring_1 l = ring_1 b /\
      ring_sub l = ring_sub b /\ ring_mul l = ring_mul b /\
      ring_add l = ring_add b") (fun th => RULE_ASSUM_TAC (REWRITE_RULE [th]) THEN REWRITE_TAC [th]) THENL [UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED), RING_SUB_SUBRING_GENERATED], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"!j. ideal_pow b Q j SUBSET ring_carrier (b:B ring)") ASSUME_TAC THENL [MESON_TAC [RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(t:B) IN ring_carrier b /\ (f:B->B) t IN ring_carrier b") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r2 THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ONCE_REWRITE_TAC [(← GSYM (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool")] IDEAL_POW_0))] THEN ASM_SIMP_TAC []], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"t:B"), (← q r"ring_sub b ((f:B->B) t) t"), (← q r"i:num")] DEDEKIND_IDEAL_POW_UNIFORMIZER_SPLIT) THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"a:B") THEN DISCH_THEN (X_CHOOSE_THEN (← q r"w:B") STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(a:B) IN ring_carrier b /\ (w:B) IN ring_carrier b") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub b ((f:B->B) t) (ring_mul b (ring_add b (ring_1 b) a) t) = w") (fun th => ASM_REWRITE_TAC [th]) THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [])

  -- @@RETURN BEGIN
  return { RING_HOMOMORPHISM_POW_DIFFERENCE, DEDEKIND_UNIFORMIZER_CONGRUENCE_STEP,
           DEDEKIND_UNIFORMIZER_CONGRUENCE, DECOMPOSITION_GROUP_IDEAL_POW,
           INERTIA_GROUP_IDEAL_POW_0, INERTIA_GROUP_IDEAL_POW,
           INERTIA_GROUP_IDEAL_POW_MONO, INERTIA_GROUP_IDEAL_POW_NORMAL,
           INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL,
           INERTIA_GROUP_IDEAL_POW_UNIFORMIZER, DEDEKIND_IDEAL_POW_UNIFORMIZER_MUL,
           DEDEKIND_IDEAL_POW_UNIFORMIZER_UNIQUE, INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM,
           INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_EXISTS }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- ramification_groups.ml phrases from line 776 to 1427                   -/
/- ---------------------------------------------------------------------- -/

structure RamificationGroups02 where
  -- @@FIELDS
  INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_MUL : thm
  INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_ADD : thm
  INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_KERNEL : thm
  INERTIA_GROUP_TAME_HOMOMORPHISM : thm
  INERTIA_GROUP_TAME_QUOTIENT : thm
  INERTIA_GROUP_WILD_MAP : thm
  INERTIA_GROUP_WILD_HOMOMORPHISM : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupRamificationGroups02 [HolBase] (D : RamificationGroupsDeps) (BRamificationGroups01 : RamificationGroups01) :
    ExceptT String IO RamificationGroups02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC,
        NUMBER_TAC, RING_RULE, SET_RULE, SET_TAC, TAUT, .. } := D
  let { ADD1, ADD_CLAUSES, ARITH, CARD_DELETE, CARD_EQ_0, CARD_EQ_CARD_IMP,
        CARRIER_SUBGROUP_GENERATED_SUBGROUP, DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL,
        DEDEKIND_PRIME_IDEAL_UNIFORMIZER, EXTENSION, FIELD_QUOTIENT_RING,
        FIELD_UNIT_GROUP, FINITE_DIFF, FINITE_FIELD_CYCLIC_UNIT_GROUP, FINITE_SUBSET,
        FIRST_GROUP_ISOMORPHISM_THEOREM, FORALL_IN_IMAGE, FUN_IN_IMAGE,
        GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET, GROUP_HOMOMORPHISM, GROUP_ID,
        GROUP_INV, GROUP_MUL, GROUP_MUL_RINV, IDEAL_POW_0, IDEAL_POW_1,
        IDEAL_POW_ANTIMONO, INERTIA_GROUP, IN_ELIM_THM, IN_RING_IDEAL_0,
        IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL, ISOMORPHIC_GROUP_CARD_EQ,
        ISOMORPHIC_GROUP_CYCLICITY, I_THM, LAGRANGE_THEOREM, LE_0, MONO_EXISTS, .. } := D.core1
  let { NOT_SUC, PRIME_IMP_RING_IDEAL, QUOTIENT_RING, QUOTIENT_RING_0, QUOTIENT_RING_1,
        QUOTIENT_RING_ADD, QUOTIENT_RING_CARRIER, QUOTIENT_RING_MUL,
        RIGHT_IMP_EXISTS_THM, RING_0, RING_1, RING_ADD, RING_ADDITIVE_GROUP,
        RING_CARRIER_NONEMPTY, RING_CHAR_DIVIDES_ORDER, RING_COSET_EQ,
        RING_COSET_EQ_IDEAL, RING_HOMOMORPHISM_ADD, RING_HOMOMORPHISM_MUL,
        RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET, RING_ISOMORPHISM_IMP_HOMOMORPHISM,
        RING_MUL, RING_MUL_IN_IDEAL_POW, RING_MUL_LID, RING_SUB, RING_SUB_REFL,
        RING_SUB_SUBRING_GENERATED, SKOLEM_THM, SUBGROUP_GROUP_IMAGE,
        SUBGROUP_OF_CYCLIC_GROUP, SUBRING_GENERATED, SUBSET, SUC_SUB1, UNIT_GROUP,
        group_kernel, inertia_group, o_THM, ring_unit, subgroup_of, .. } := D.core2
  let { DEDEKIND_IDEAL_POW_UNIFORMIZER_UNIQUE, INERTIA_GROUP_IDEAL_POW_0,
        INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM, INERTIA_GROUP_IDEAL_POW_MONO,
        INERTIA_GROUP_IDEAL_POW_UNIFORMIZER,
        INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_EXISTS, .. } := BRamificationGroups01
  -- @@SCOPE END

  let INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_MUL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!r A F W c d t:B.
        A IN ring_carrier r /\ F IN ring_carrier r /\ W IN ring_carrier r /\
        c IN ring_carrier r /\ d IN ring_carrier r /\ t IN ring_carrier r
        ==> ring_sub r (ring_add r (ring_mul r A F) W)
                       (ring_mul r (ring_mul r c d) t) =
            ring_add r
             (ring_add r (ring_mul r (ring_sub r A d) F)
                         (ring_mul r d (ring_sub r F (ring_mul r c t))))
             W")
    let r2 ← RING_RULE (← q r"ring_add r a (ring_sub r x a) = x:B")
    prove
      r"!(h:A->B) k l b Q t i f g c d.
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          prime_ideal b Q /\ t IN Q /\
          f IN group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1))) /\
          g IN group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1))) /\
          c IN ring_carrier b /\ d IN ring_carrier b /\
          ring_sub l (f t) (ring_mul l c t) IN ideal_pow b Q (i + 2) /\
          ring_sub l (g t) (ring_mul l d t) IN ideal_pow b Q (i + 2)
          ==> ring_sub l ((f o g) t) (ring_mul l (ring_mul l c d) t)
              IN ideal_pow b Q (i + 2)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"i:num"), (← q r"g:B->B")] INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o (CONJUNCT1 o CONJUNCT2)) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"i:num"), (← q r"f:B->B")] INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC o (MATCH_MP RING_ISOMORPHISM_IMP_HOMOMORPHISM)) STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"ring_0 l = ring_0 (b:B ring) /\ ring_1 l = ring_1 b /\
      ring_sub l = ring_sub b /\ ring_mul l = ring_mul b /\
      ring_add l = ring_add b") (fun th => RULE_ASSUM_TAC (REWRITE_RULE [th]) THEN REWRITE_TAC [th]) THENL [UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED), RING_SUB_SUBRING_GENERATED], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"!j. ideal_pow b Q j SUBSET ring_carrier (b:B ring)") ASSUME_TAC THENL [MESON_TAC [RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(Q:B->bool) SUBSET ring_carrier b /\ (t:B) IN ideal_pow b Q 1") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, IDEAL_POW_1], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN ring_carrier b
          ==> (f:B->B) x IN ring_carrier b /\ (g:B->B) x IN ring_carrier b") ASSUME_TAC THENL [ONCE_REWRITE_TAC [(← GSYM (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool")] IDEAL_POW_0))] THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(t:B) IN ring_carrier b") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"w = ring_sub b ((g:B->B) t) (ring_mul b d t)") THEN SUBGOAL_THEN (← q r"(w:B) IN ring_carrier b") ASSUME_TAC THENL [EXPAND_TAC "w" THEN ASM_SIMP_TAC [RING_SUB, RING_MUL], ALL_TAC] THEN REWRITE_TAC [o_THM] THEN SUBGOAL_THEN (← q r"(g:B->B) t = ring_add b (ring_mul b d t) w") SUBST1_TAC THENL [EXPAND_TAC "w" THEN ASM_SIMP_TAC [RING_MUL, r2], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_ADD th), (← MATCH_MP RING_HOMOMORPHISM_MUL th), RING_MUL])) THEN SUBGOAL_THEN (← q r"ring_sub b
       (ring_add b (ring_mul b ((f:B->B) d) (f t)) (f w))
       (ring_mul b (ring_mul b c d) t) =
      ring_add b
       (ring_add b (ring_mul b (ring_sub b (f d) d) (f t))
                   (ring_mul b d (ring_sub b (f t) (ring_mul b c t))))
       (f w)") SUBST1_TAC THENL [MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [], ALL_TAC] THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC []] THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN CONJ_TAC THENL [SUBGOAL_THEN (← q r"i + 2 = (i + 1) + 1") SUBST1_TAC THENL [ARITH_TAC, ALL_TAC] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC [], MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW]])

  let INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_ADD ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!r x a c t:B.
        x IN ring_carrier r /\ a IN ring_carrier r /\
        c IN ring_carrier r /\ t IN ring_carrier r
        ==> ring_sub r x
             (ring_mul r (ring_add r (ring_1 r) (ring_add r a c)) t) =
            ring_add r
             (ring_sub r x
               (ring_mul r (ring_mul r (ring_add r (ring_1 r) a)
                                       (ring_add r (ring_1 r) c)) t))
             (ring_mul r (ring_mul r a c) t)")
    prove
      r"!(h:A->B) k l b Q t i f g a c.
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          prime_ideal b Q /\ t IN Q /\ 1 <= i /\
          f IN group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1))) /\
          g IN group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1))) /\
          a IN ideal_pow b Q i /\ c IN ideal_pow b Q i /\
          ring_sub l (f t) (ring_mul l (ring_add l (ring_1 l) a) t)
          IN ideal_pow b Q (i + 2) /\
          ring_sub l (g t) (ring_mul l (ring_add l (ring_1 l) c) t)
          IN ideal_pow b Q (i + 2)
          ==> ring_sub l ((f o g) t)
               (ring_mul l (ring_add l (ring_1 l) (ring_add l a c)) t)
              IN ideal_pow b Q (i + 2)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY (fun v => tactic_of do pure (MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"i:num"), v] INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"0:num")) o (CONJUNCT1 o CONJUNCT2))) THEN REWRITE_TAC [IDEAL_POW_0] THEN DISCH_TAC)) [(← q r"f:B->B"), (← q r"g:B->B")] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"t:B"), (← q r"i:num"), (← q r"f:B->B"), (← q r"g:B->B"), (← q r"ring_add l (ring_1 l) (a:B)"), (← q r"ring_add l (ring_1 l) (c:B)")] INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_MUL) THEN SUBGOAL_THEN (← q r"ring_0 l = ring_0 (b:B ring) /\ ring_1 l = ring_1 b /\
      ring_sub l = ring_sub b /\ ring_mul l = ring_mul b /\
      ring_add l = ring_add b") (fun th => RULE_ASSUM_TAC (REWRITE_RULE [th]) THEN REWRITE_TAC [th]) THENL [UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED), RING_SUB_SUBRING_GENERATED], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"!j. ideal_pow b Q j SUBSET ring_carrier (b:B ring)") ASSUME_TAC THENL [MESON_TAC [RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(t:B) IN ring_carrier b /\ (a:B) IN ring_carrier b /\
      (c:B) IN ring_carrier b") STRIP_ASSUME_TAC THENL [FIRST_X_ASSUM (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"1:num") th) THEN MP_TAC (← SPEC (← q r"i:num") th))) THEN ASM_SIMP_TAC [IDEAL_POW_1, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"((f:B->B) o (g:B->B)) t IN ring_carrier b") ASSUME_TAC THENL [REWRITE_TAC [o_THM] THEN ASM_SIMP_TAC [], ALL_TAC] THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_ADD, RING_1], DISCH_TAC] THEN SUBGOAL_THEN (← q r"ring_sub b (((f:B->B) o (g:B->B)) t)
       (ring_mul b (ring_add b (ring_1 b) (ring_add b a c)) t) =
      ring_add b
       (ring_sub b ((f o g) t)
         (ring_mul b (ring_mul b (ring_add b (ring_1 b) a)
                                 (ring_add b (ring_1 b) c)) t))
       (ring_mul b (ring_mul b a c) t)") SUBST1_TAC THENL [MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN SUBGOAL_THEN (← q r"ideal_pow b Q ((i + i) + 1) SUBSET ideal_pow b (Q:B->bool) (i + 2)") MP_TAC THENL [MATCH_MP_TAC IDEAL_POW_ANTIMONO THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN ASM_ARITH_TAC, REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC [IDEAL_POW_1, RING_MUL_IN_IDEAL_POW, RING_IDEAL_IMP_SUBSET])

  let INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_KERNEL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"(i + 1) + 1 = i + 2")
    let r2 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    let r3 ← ARITH_RULE (← q r"(i + 1) + 1 = i + 2")
    prove
      r"!(h:A->B) k l b Q t i f c.
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          dedekind_domain b /\ prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
          FINITE(ring_carrier(quotient_ring b Q)) /\
          t IN Q /\ ~(t IN ideal_pow b Q 2) /\
          f IN group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1))) /\
          c IN ring_carrier b /\
          ring_sub l (f t) (ring_mul l c t) IN ideal_pow b Q (i + 2)
          ==> (f IN group_carrier
                     (inertia_group(k,l) h b (ideal_pow b Q (i + 2))) <=>
               ring_sub l c (ring_1 l) IN ideal_pow b Q (i + 1))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"t:B"), (← q r"f:B->B"), (← q r"i + 1:num")] INERTIA_GROUP_IDEAL_POW_UNIFORMIZER) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"0:num"), (← q r"i:num")] INERTIA_GROUP_IDEAL_POW_MONO) THEN ASM_SIMP_TAC [LE_0, ADD_CLAUSES, INERTIA_GROUP_IDEAL_POW_0] THEN REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [], REWRITE_TAC [r3] THEN DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"i:num"), (← q r"f:B->B")] INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o (CONJUNCT1 o CONJUNCT2)) THEN SUBGOAL_THEN (← q r"ring_0 l = ring_0 (b:B ring) /\ ring_1 l = ring_1 b /\
      ring_sub l = ring_sub b /\ ring_mul l = ring_mul b /\
      ring_add l = ring_add b") (fun th => RULE_ASSUM_TAC (REWRITE_RULE [th]) THEN REWRITE_TAC [th]) THENL [UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED), RING_SUB_SUBRING_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"(t:B) IN ring_carrier b /\ (f:B->B) t IN ring_carrier b") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r2 THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ONCE_REWRITE_TAC [(← GSYM (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool")] IDEAL_POW_0))] THEN ASM_SIMP_TAC []], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"t:B"), (← q r"(f:B->B) t"), (← q r"c:B"), (← q r"ring_1 b:B"), (← q r"i + 1:num")] DEDEKIND_IDEAL_POW_UNIFORMIZER_UNIQUE) THEN ASM_SIMP_TAC [RING_1, RING_MUL_LID, r1])

  let INERTIA_GROUP_TAME_HOMOMORPHISM ← prove
    r"!(h:A->B) k l b Q t.
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        dedekind_domain b /\ prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
        FINITE(ring_carrier(quotient_ring b Q)) /\
        t IN Q /\ ~(t IN ideal_pow b Q 2)
        ==> ?theta.
              group_homomorphism
               (inertia_group(k,l) h b Q,unit_group(quotient_ring b Q))
               theta /\
              (!f c. f IN group_carrier(inertia_group(k,l) h b Q) /\
                     c IN ring_carrier b /\
                     ring_sub l (f t) (ring_mul l c t) IN ideal_pow b Q 2
                     ==> theta f = ring_coset b Q c) /\
              group_kernel(inertia_group(k,l) h b Q,
                           unit_group(quotient_ring b Q)) theta =
              group_carrier(inertia_group(k,l) h b (ideal_pow b Q 2))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"inertia_group(k,l) (h:A->B) b (ideal_pow b Q (0 + 1)) =
    inertia_group(k,l) h b Q /\
    ideal_pow b Q (0 + 1) = Q /\ 0 + 2 = 2 /\
    ideal_pow b (Q:B->bool) 0 = ring_carrier b") (LABEL_TAC "i0") THENL [ASM_SIMP_TAC [ADD_CLAUSES, IDEAL_POW_1, IDEAL_POW_0, INERTIA_GROUP_IDEAL_POW_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_0 l = ring_0 (b:B ring) /\ ring_1 l = ring_1 b /\
    ring_sub l = ring_sub b /\ ring_mul l = ring_mul b /\
    ring_add l = ring_add b") (fun th => RULE_ASSUM_TAC (REWRITE_RULE [th]) THEN REWRITE_TAC [th] THEN LABEL_TAC "lb" th) THENL [UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED), RING_SUB_SUBRING_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"(t:B) IN ring_carrier b") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!f x. f IN group_carrier(inertia_group(k,l) (h:A->B) b Q) /\
          x IN ring_carrier b
          ==> f x IN ring_carrier b") ASSUME_TAC THENL [REWRITE_TAC [inertia_group] THEN ASM_MESON_TAC [GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET, SUBSET, FUN_IN_IMAGE], ALL_TAC] THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(inertia_group(k,l) (h:A->B) b Q)
        ==> ?c. c IN ring_carrier b /\
                ring_sub b (f t) (ring_mul b c t) IN ideal_pow b Q 2") MP_TAC THENL [X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"t:B"), (← q r"0:num"), (← q r"f:B->B")] INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_EXISTS) THEN REMOVE_THEN "lb" (fun th => REWRITE_TAC [th] THEN LABEL_TAC "lb" th) THEN USE_THEN "i0" (fun th => REWRITE_TAC [th]) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:B") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"ring_add b (ring_1 b) a:B") THEN ASM_SIMP_TAC [RING_ADD, RING_1], ALL_TAC] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"C:(B->B)->B") (LABEL_TAC "C")) o (REWRITE_RULE [RIGHT_IMP_EXISTS_THM, SKOLEM_THM])) THEN SUBGOAL_THEN (← q r"!f c. f IN group_carrier(inertia_group(k,l) (h:A->B) b Q) /\
          c IN ring_carrier b /\
          ring_sub b (f t) (ring_mul b c t) IN ideal_pow b Q 2
          ==> ring_coset b Q ((C:(B->B)->B) f) = ring_coset b Q c") (LABEL_TAC "uniq") THENL [REPEAT STRIP_TAC THEN USE_THEN "C" (MP_TAC o (SPEC (← q r"f:B->B"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN ASM_SIMP_TAC [RING_COSET_EQ] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"t:B"), (← q r"(f:B->B) t"), (← q r"(C:(B->B)->B) f"), (← q r"c:B"), (← q r"1:num")] DEDEKIND_IDEAL_POW_UNIFORMIZER_UNIQUE) THEN ASM_SIMP_TAC [ARITH, IDEAL_POW_1], ALL_TAC] THEN SUBGOAL_THEN (← q r"!f g. f IN group_carrier(inertia_group(k,l) (h:A->B) b Q) /\
          g IN group_carrier(inertia_group(k,l) h b Q)
          ==> ring_coset b Q ((C:(B->B)->B) (f o g)) =
              ring_mul (quotient_ring b Q)
               (ring_coset b Q (C f)) (ring_coset b Q (C g))") (LABEL_TAC "mul") THENL [REPEAT STRIP_TAC THEN MAP_EVERY (fun v => USE_THEN "C" (MP_TAC o (SPEC v)) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC]) [(← q r"f:B->B"), (← q r"g:B->B")] THEN ASM_SIMP_TAC [QUOTIENT_RING_MUL] THEN USE_THEN "uniq" MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_MUL] THEN CONJ_TAC THENL [MP_TAC (← ISPEC (← q r"inertia_group(k,l) (h:A->B) b Q") GROUP_MUL) THEN ASM_SIMP_TAC [(← CONJUNCT2 INERTIA_GROUP)], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"t:B"), (← q r"0:num"), (← q r"f:B->B"), (← q r"g:B->B"), (← q r"(C:(B->B)->B) f"), (← q r"(C:(B->B)->B) g")] INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_MUL) THEN USE_THEN "lb" (fun th => REWRITE_TAC [th]) THEN USE_THEN "i0" (fun th => REWRITE_TAC [th]) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(I:B->B) IN group_carrier(inertia_group(k,l) (h:A->B) b Q)") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"inertia_group(k,l) (h:A->B) b Q") GROUP_ID) THEN REWRITE_TAC [(← CONJUNCT1 (← CONJUNCT2 INERTIA_GROUP))], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_coset b Q ((C:(B->B)->B) I) = ring_coset b Q (ring_1 b)") ASSUME_TAC THENL [USE_THEN "uniq" MATCH_MP_TAC THEN ASM_SIMP_TAC [I_THM, RING_MUL_LID, RING_SUB_REFL, IN_RING_IDEAL_0, RING_IDEAL_IDEAL_POW, RING_1], ALL_TAC] THEN EXISTS_TAC (← q r"\f:B->B. ring_coset b Q ((C:(B->B)->B) f)") THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [REWRITE_TAC [GROUP_HOMOMORPHISM, SUBSET, FORALL_IN_IMAGE] THEN REWRITE_TAC [(← CONJUNCT2 INERTIA_GROUP), UNIT_GROUP, IN_ELIM_THM] THEN ASM_SIMP_TAC [] THEN X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"inverse(f:B->B) IN group_carrier(inertia_group(k,l) (h:A->B) b Q)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"inertia_group(k,l) (h:A->B) b Q"), (← q r"f:B->B")] GROUP_INV) THEN ASM_REWRITE_TAC [(← CONJUNCT2 INERTIA_GROUP)], ALL_TAC] THEN REWRITE_TAC [ring_unit] THEN ASM_SIMP_TAC [(← CONJUNCT1 QUOTIENT_RING), IN_ELIM_THM] THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN EXISTS_TAC (← q r"ring_coset b Q ((C:(B->B)->B) (inverse f))") THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN USE_THEN "mul" (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← MATCH_MP th (← CONJ (← ASSUME (← q r"(f:B->B) IN group_carrier(inertia_group(k,l) (h:A->B) b Q)")) (← ASSUME (← q r"inverse(f:B->B) IN group_carrier(inertia_group(k,l) (h:A->B) b Q)")))))])) THEN MP_TAC (← ISPECL [(← q r"inertia_group(k,l) (h:A->B) b Q"), (← q r"f:B->B")] GROUP_MUL_RINV) THEN ASM_REWRITE_TAC [(← CONJUNCT2 INERTIA_GROUP)] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [QUOTIENT_RING_1], ALL_TAC] THEN REWRITE_TAC [group_kernel, UNIT_GROUP] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"f:B->B") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [QUOTIENT_RING_1] THEN ASM_CASES_TAC (← q r"f IN group_carrier(inertia_group(k,l) (h:A->B) b Q)") THEN ASM_REWRITE_TAC [] THENL [ALL_TAC, MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"0:num"), (← q r"1:num")] INERTIA_GROUP_IDEAL_POW_MONO) THEN USE_THEN "i0" (fun th => REWRITE_TAC [th, ARITH]) THEN ASM_REWRITE_TAC [ARITH] THEN ASM SET_TAC []] THEN USE_THEN "C" (MP_TAC o (SPEC (← q r"f:B->B"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN ASM_SIMP_TAC [RING_COSET_EQ, RING_1] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"t:B"), (← q r"0:num"), (← q r"f:B->B"), (← q r"(C:(B->B)->B) f")] INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_KERNEL) THEN USE_THEN "lb" (fun th => REWRITE_TAC [th]) THEN USE_THEN "i0" (fun th => REWRITE_TAC [th]) THEN ASM_SIMP_TAC [])

  let INERTIA_GROUP_TAME_QUOTIENT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let p1 ← prove r"!d:num q:num p:num.
          d divides q - 1 /\ p divides q /\ ~(q = 0) ==> coprime(d,p)" (GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [NOT_SUC, SUC_SUB1, ADD1] THEN NUMBER_TAC)
    let lemma := p1
    let q2 ← q r"CARD(ring_carrier(quotient_ring b (Q:B->bool)))"
    let q3 ← q r"CARD(group_image(inertia_group(k,l) (h:A->B) b Q,
                     unit_group(quotient_ring b Q)) theta) divides
    CARD(ring_carrier(quotient_ring b Q)) - 1"
    let q4 ← q r"(s:A->bool) DIFF {a} = s DELETE a"
    let r5 ← SET_RULE q4
    let q6 ← q r"CARD(group_carrier(unit_group(quotient_ring b (Q:B->bool)))) =
    CARD(ring_carrier(quotient_ring b Q)) - 1"
    let q7 ← q r"group_carrier(unit_group(quotient_ring b (Q:B->bool)))"
    let q8 ← q r"CARD(group_carrier(quotient_group (inertia_group(k,l) (h:A->B) b Q)
      (group_kernel(inertia_group(k,l) h b Q,unit_group(quotient_ring b Q))
                   theta))) =
    CARD(group_image(inertia_group(k,l) h b Q,unit_group(quotient_ring b Q))
                    theta)"
    let q9 ← q r"FINITE(group_carrier(unit_group(quotient_ring b (Q:B->bool))))"
    let q10 ← q r"field(quotient_ring b (Q:B->bool))"
    let q11 ← q r"theta:(B->B)->(B->bool)"
    let q12 ← q r"t:B"
    let q13 ← q r"Q:B->bool"
    let q14 ← q r"b:B ring"
    let q15 ← q r"l:B ring"
    let q16 ← q r"k:A ring"
    let q17 ← q r"h:A->B"
    let v18 ← ISPECL [q17, q16, q15, q14, q13, q12] INERTIA_GROUP_TAME_HOMOMORPHISM
    let q19 ← q r"t:B"
    let q20 ← q r"Q:B->bool"
    let q21 ← q r"b:B ring"
    let v22 ← ISPECL [q21, q20] DEDEKIND_PRIME_IDEAL_UNIFORMIZER
    let v23 ← CONJUNCT2 SUBRING_GENERATED
    let q24 ← q r"subring_generated l (ring_carrier b) = (b:B ring)"
    let q25 ← q r"ring_0 b = ring_0 (l:B ring)"
    prove
      r"!(h:A->B) k l b Q.
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          dedekind_domain b /\ prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
          FINITE(ring_carrier(quotient_ring b Q))
          ==> cyclic_group
               (quotient_group (inertia_group(k,l) h b Q)
                 (group_carrier(inertia_group(k,l) h b (ideal_pow b Q 2)))) /\
              CARD(group_carrier
               (quotient_group (inertia_group(k,l) h b Q)
                 (group_carrier(inertia_group(k,l) h b (ideal_pow b Q 2)))))
              divides CARD(ring_carrier(quotient_ring b Q)) - 1 /\
              coprime(CARD(group_carrier
                       (quotient_group (inertia_group(k,l) h b Q)
                         (group_carrier
                           (inertia_group(k,l) h b (ideal_pow b Q 2))))),
                      ring_char(quotient_ring b Q))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN q25 ASSUME_TAC THENL [UNDISCH_TAC q24 THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN REWRITE_TAC [v23], ALL_TAC] THEN MP_TAC v22 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q19 STRIP_ASSUME_TAC) THEN MP_TAC v18 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q11 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (fun (_ : thm) => ALL_TAC) (SUBST1_TAC o SYM)))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FIRST_GROUP_ISOMORPHISM_THEOREM)) THEN SUBGOAL_THEN q10 ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_QUOTIENT_RING, PRIME_IMP_RING_IDEAL] THEN MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q9 ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_UNIT_GROUP, FINITE_DIFF], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP SUBGROUP_GROUP_IMAGE)) THEN SUBGOAL_THEN q8 SUBST1_TAC THENL [MATCH_MP_TAC CARD_EQ_CARD_IMP THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC q7 THEN ASM_MESON_TAC [subgroup_of], FIRST_ASSUM (MP_TAC o (MATCH_MP ISOMORPHIC_GROUP_CARD_EQ)) THEN ASM_SIMP_TAC [CARRIER_SUBGROUP_GENERATED_SUBGROUP]], ALL_TAC] THEN SUBGOAL_THEN q6 ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_UNIT_GROUP, r5, CARD_DELETE, RING_0], ALL_TAC] THEN SUBGOAL_THEN q3 ASSUME_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN MATCH_MP_TAC LAGRANGE_THEOREM THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP ISOMORPHIC_GROUP_CYCLICITY th)])) THEN MATCH_MP_TAC SUBGROUP_OF_CYCLIC_GROUP THEN ASM_SIMP_TAC [FINITE_FIELD_CYCLIC_UNIT_GROUP], MATCH_MP_TAC lemma THEN EXISTS_TAC q2 THEN ASM_SIMP_TAC [RING_CHAR_DIVIDES_ORDER, CARD_EQ_0, RING_CARRIER_NONEMPTY]])

  let INERTIA_GROUP_WILD_MAP ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_sub r (ring_add r (ring_1 r) x) (ring_1 r) = x:B")
    let r2 ← RING_RULE (← q r"ring_sub r (ring_add r (ring_1 r) c) (ring_add r (ring_1 r) a) =
      ring_sub r c a:B")
    let r3 ← ARITH_RULE (← q r"(i + 1) + 1 = i + 2")
    prove
      r"!(h:A->B) k l b Q t i.
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          dedekind_domain b /\ prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
          FINITE(ring_carrier(quotient_ring b Q)) /\
          t IN Q /\ ~(t IN ideal_pow b Q 2) /\ 1 <= i
          ==> ?theta.
                (!f. f IN group_carrier
                           (inertia_group(k,l) h b (ideal_pow b Q (i + 1)))
                     ==> ?a. a IN ideal_pow b Q i /\
                             theta f = ring_coset b (ideal_pow b Q (i + 1)) a) /\
                (!f g. f IN group_carrier
                             (inertia_group(k,l) h b (ideal_pow b Q (i + 1))) /\
                       g IN group_carrier
                             (inertia_group(k,l) h b (ideal_pow b Q (i + 1)))
                       ==> theta(f o g) =
                           ring_add (quotient_ring b (ideal_pow b Q (i + 1)))
                                    (theta f) (theta g)) /\
                (!f a. f IN group_carrier
                             (inertia_group(k,l) h b (ideal_pow b Q (i + 1))) /\
                       a IN ideal_pow b Q i /\
                       ring_sub l (f t) (ring_mul l (ring_add l (ring_1 l) a) t)
                       IN ideal_pow b Q (i + 2)
                       ==> theta f = ring_coset b (ideal_pow b Q (i + 1)) a) /\
                (!f. f IN group_carrier
                           (inertia_group(k,l) h b (ideal_pow b Q (i + 1)))
                     ==> (theta f =
                          ring_0 (quotient_ring b (ideal_pow b Q (i + 1))) <=>
                          f IN group_carrier
                           (inertia_group(k,l) h b (ideal_pow b Q (i + 2)))))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier
                (inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1)))
          ==> ?a. a IN ideal_pow b Q i /\
                  ring_sub l (f t) (ring_mul l (ring_add l (ring_1 l) a) t)
                  IN ideal_pow b Q (i + 2)") MP_TAC THENL [X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"t:B"), (← q r"i:num"), (← q r"f:B->B")] INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_EXISTS) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"C:(B->B)->B") (LABEL_TAC "C")) o (REWRITE_RULE [RIGHT_IMP_EXISTS_THM, SKOLEM_THM])) THEN SUBGOAL_THEN (← q r"ring_0 l = ring_0 (b:B ring) /\ ring_1 l = ring_1 b /\
      ring_sub l = ring_sub b /\ ring_mul l = ring_mul b /\
      ring_add l = ring_add b") (fun th => RULE_ASSUM_TAC (REWRITE_RULE [th]) THEN REWRITE_TAC [th] THEN LABEL_TAC "lb" th) THENL [UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED), RING_SUB_SUBRING_GENERATED], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"!j. ideal_pow b Q j SUBSET ring_carrier (b:B ring)") ASSUME_TAC THENL [MESON_TAC [RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(t:B) IN ring_carrier b") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier
                (inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1)))
          ==> (C:(B->B)->B) f IN ring_carrier b /\ f t IN ring_carrier b") ASSUME_TAC THENL [X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN USE_THEN "C" (MP_TAC o (SPEC (← q r"f:B->B"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN CONJ_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"i:num"), (← q r"f:B->B")] INERTIA_GROUP_IDEAL_POW_AUTOMORPHISM) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPECL [(← q r"0:num"), (← q r"t:B")]) o (CONJUNCT1 o CONJUNCT2))) THEN ASM_REWRITE_TAC [IDEAL_POW_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"!f a. f IN group_carrier
                  (inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1))) /\
            a IN ring_carrier b /\
            ring_sub b (f t) (ring_mul b (ring_add b (ring_1 b) a) t)
            IN ideal_pow b Q (i + 2)
            ==> ring_sub b ((C:(B->B)->B) f) a IN ideal_pow b Q (i + 1)") (LABEL_TAC "uniq") THENL [REPEAT STRIP_TAC THEN USE_THEN "C" (MP_TAC o (SPEC (← q r"f:B->B"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"t:B"), (← q r"(f:B->B) t"), (← q r"ring_add b (ring_1 b) ((C:(B->B)->B) f)"), (← q r"ring_add b (ring_1 b) (a:B)"), (← q r"i + 1:num")] DEDEKIND_IDEAL_POW_UNIFORMIZER_UNIQUE) THEN ASM_SIMP_TAC [RING_ADD, RING_1, r3] THEN ASM_SIMP_TAC [r2], ALL_TAC] THEN EXISTS_TAC (← q r"\f:B->B. ring_coset b (ideal_pow b Q (i + 1)) ((C:(B->B)->B) f)") THEN REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN EXISTS_TAC (← q r"(C:(B->B)->B) f") THEN USE_THEN "C" (MP_TAC o (SPEC (← q r"f:B->B"))) THEN ASM_SIMP_TAC [], MAP_EVERY X_GEN_TAC [(← q r"f:B->B"), (← q r"g:B->B")] THEN STRIP_TAC THEN MAP_EVERY (fun v => USE_THEN "C" (MP_TAC o (SPEC v)) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC]) [(← q r"f:B->B"), (← q r"g:B->B")] THEN SUBGOAL_THEN (← q r"(f:B->B) o g IN
        group_carrier(inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1)))") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1))") GROUP_MUL) THEN ASM_SIMP_TAC [(← CONJUNCT2 INERTIA_GROUP)], ALL_TAC] THEN ASM_SIMP_TAC [QUOTIENT_RING_ADD, RING_IDEAL_IDEAL_POW, RING_COSET_EQ, RING_ADD] THEN USE_THEN "uniq" MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_ADD] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"t:B"), (← q r"i:num"), (← q r"f:B->B"), (← q r"g:B->B"), (← q r"(C:(B->B)->B) f"), (← q r"(C:(B->B)->B) g")] INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_ADD) THEN USE_THEN "lb" (fun th => REWRITE_TAC [th]) THEN ASM_SIMP_TAC [], MAP_EVERY X_GEN_TAC [(← q r"f:B->B"), (← q r"a:B")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:B) IN ring_carrier b") ASSUME_TAC THENL [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_COSET_EQ, RING_IDEAL_IDEAL_POW] THEN USE_THEN "uniq" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN USE_THEN "C" (MP_TAC o (SPEC (← q r"f:B->B"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN ASM_SIMP_TAC [QUOTIENT_RING_0, RING_IDEAL_IDEAL_POW, RING_COSET_EQ_IDEAL] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"t:B"), (← q r"i:num"), (← q r"f:B->B"), (← q r"ring_add b (ring_1 b) ((C:(B->B)->B) f)")] INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_KERNEL) THEN USE_THEN "lb" (fun th => REWRITE_TAC [th]) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_ADD, RING_1], DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC [r1]])

  let INERTIA_GROUP_WILD_HOMOMORPHISM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"(i:num) <= i + 1 /\ (i + 1) + 1 = i + 2")
    prove
      r"!(h:A->B) k l b Q t i.
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          dedekind_domain b /\ prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
          FINITE(ring_carrier(quotient_ring b Q)) /\
          t IN Q /\ ~(t IN ideal_pow b Q 2) /\ 1 <= i
          ==> ?theta.
                group_homomorphism
                 (inertia_group(k,l) h b (ideal_pow b Q (i + 1)),
                  ring_additive_group(quotient_ring b (ideal_pow b Q (i + 1))))
                 theta /\
                group_kernel
                 (inertia_group(k,l) h b (ideal_pow b Q (i + 1)),
                  ring_additive_group(quotient_ring b (ideal_pow b Q (i + 1))))
                 theta =
                group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 2))) /\
                (!f. f IN group_carrier
                           (inertia_group(k,l) h b (ideal_pow b Q (i + 1)))
                     ==> ?a. a IN ideal_pow b Q i /\
                             theta f = ring_coset b (ideal_pow b Q (i + 1)) a) /\
                (!f a. f IN group_carrier
                             (inertia_group(k,l) h b (ideal_pow b Q (i + 1))) /\
                       a IN ideal_pow b Q i /\
                       ring_sub l (f t) (ring_mul l (ring_add l (ring_1 l) a) t)
                       IN ideal_pow b Q (i + 2)
                       ==> theta f = ring_coset b (ideal_pow b Q (i + 1)) a)"
      (REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP INERTIA_GROUP_WILD_MAP)) THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"theta:(B->B)->(B->bool)") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (STRIP_ASSUME_TAC o (checkM (fun z10 => (do let z11 ← (do let z12 ← (pure z10); pure (concl z12)); pure (is_conj z11))))) THEN SUBGOAL_THEN (← q r"ring_ideal b (ideal_pow b Q (i + 1):B->bool)") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN CONJ_TAC THENL [REWRITE_TAC [GROUP_HOMOMORPHISM, RING_ADDITIVE_GROUP, INERTIA_GROUP] THEN ASM_SIMP_TAC [] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"f:B->B")) o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_forall z2)) then (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); canM (fun z6 => (do let z7 ← (pure z6); find_termM (fun z8 => (do let z9 ← (pure z8); pure (is_exists z9))) z7)) z4) else pure false))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:B") STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN EXISTS_TAC (← q r"a:B") THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"i:num")] RING_IDEAL_IDEAL_POW) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN REWRITE_TAC [group_kernel, RING_ADDITIVE_GROUP] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"f:B->B") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"(f:B->B) IN
      group_carrier(inertia_group(k:A ring,l) h b (ideal_pow b Q (i + 1)))") THEN ASM_SIMP_TAC [] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"i:num"), (← q r"i + 1")] INERTIA_GROUP_IDEAL_POW_MONO) THEN ASM_REWRITE_TAC [r1] THEN ASM SET_TAC [])

  -- @@RETURN BEGIN
  return { INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_MUL,
           INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_ADD,
           INERTIA_GROUP_IDEAL_POW_UNIFORMIZER_KERNEL, INERTIA_GROUP_TAME_HOMOMORPHISM,
           INERTIA_GROUP_TAME_QUOTIENT, INERTIA_GROUP_WILD_MAP,
           INERTIA_GROUP_WILD_HOMOMORPHISM }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- ramification_groups.ml phrases from line 1488 to 1807                  -/
/- ---------------------------------------------------------------------- -/

structure RamificationGroups03 where
  -- @@FIELDS
  INERTIA_GROUP_IDEAL_POW_CHAR_POW : thm
  INERTIA_GROUP_WILD_PGROUP : thm
  INERTIA_GROUP_WILD_SUBSET : thm
  INERTIA_GROUP_WILD_TRIVIAL : thm
  NUMBER_FIELD_WILD_INERTIA_TRIVIAL : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupRamificationGroups03 [HolBase] (D : RamificationGroupsDeps) (BRamificationGroups01 : RamificationGroups01) (BRamificationGroups02 : RamificationGroups02) :
    ExceptT String IO RamificationGroups03 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, NUMBER_RULE,
        RING_RULE, SET_RULE, .. } := D
  let { ADD_CLAUSES, CARD_SING, CARRIER_SUBGROUP_GENERATED_SUBGROUP,
        DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL, DEDEKIND_PRIME_IDEAL_UNIFORMIZER,
        DEDEKIND_RING_OF_INTEGERS, DIVIDES_ONE, DIVIDES_PRIMEPOW, DIVIDES_REFL,
        EQ_MULT_RCANCEL, EXP, EXP_EQ_0, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_QUOTIENT_RING,
        FINITE_GALOIS_GROUP, FINITE_INTEGRAL_DOMAIN_CHAR, FINITE_PGROUP_SING,
        FINITE_SUBSET, GALOIS_GROUP, GALOIS_GROUP_RING_OF_INTEGERS,
        GALOIS_IMP_FIELD_EXTENSION, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET, GROUP_ID,
        GROUP_MUL, GROUP_POW_1, GROUP_POW_EQ_ID, GROUP_POW_MUL,
        GROUP_POW_SUBGROUP_GENERATED, IDEAL_POW_1, INERTIA_GROUP, INTEGRAL_DOMAIN_CHAR,
        IN_SING, LAGRANGE_THEOREM, LAGRANGE_THEOREM_RIGHT, MULT_AC, .. } := D.core1
  let { MULT_CLAUSES, MULT_SYM, NORMAL_PGROUP_SUBSET_COPRIME_INDEX,
        NORMAL_SUBGROUP_GROUP_KERNEL, NORMAL_SUBGROUP_IMP_SUBGROUP,
        NUMBER_FIELD_DECOMPOSITION_GROUP, NUMBER_FIELD_PRIME_IDEAL_ABOVE,
        NUMBER_FIELD_TOWER_LAW, PGROUP_SING, PRIME_GE_2, PRIME_IMP_RING_IDEAL,
        QUOTIENT_GROUP, QUOTIENT_RING_0, QUOTIENT_RING_ADD, RING_CHAR_FINITE,
        RING_COSET_0, RING_COSET_EQ_IDEAL, RING_HOMOMORPHISM_RING_COSET,
        RING_HOMOMORPHISM_RING_OF_NUM, RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_MUL_IN_IDEAL_POW,
        RING_MUL_LZERO, RING_OF_INTEGERS_FRACTION_FIELD, RING_OF_INTEGERS_SUBRING,
        RING_OF_NUM, RING_OF_NUM_EQ_0, SUBGROUP_OF_IMP_SUBSET,
        SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ, SUBRING_GENERATED, SUBSET,
        TRIVIAL_SUBGROUP_OF, divides, field_extension, group_pow, inertia_group,
        ring_of_num, .. } := D.core2
  let { INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL, .. } := BRamificationGroups01
  let { INERTIA_GROUP_TAME_HOMOMORPHISM, INERTIA_GROUP_TAME_QUOTIENT,
        INERTIA_GROUP_WILD_MAP, .. } := BRamificationGroups02
  -- @@SCOPE END

  let INERTIA_GROUP_IDEAL_POW_CHAR_POW ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"i + 1 = 1 + i:num")
    let r9 ← RING_RULE (← q r"ring_add r a (ring_mul r n a) =
        ring_mul r (ring_add r n (ring_1 r)) a:B")
    prove
      r"!(h:A->B) k l b Q i f.
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          dedekind_domain b /\ prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
          FINITE(ring_carrier(quotient_ring b Q)) /\ 1 <= i /\
          f IN group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 1)))
          ==> group_pow (galois_group(k,l) h) f (ring_char(quotient_ring b Q))
              IN group_carrier(inertia_group(k,l) h b (ideal_pow b Q (i + 2)))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_0 b = ring_0 (l:B ring)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED)], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool")] DEDEKIND_PRIME_IDEAL_UNIFORMIZER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:B") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"t:B"), (← q r"i:num")] INERTIA_GROUP_WILD_MAP) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"theta:(B->B)->(B->bool)") STRIP_ASSUME_TAC) THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"f:B->B")) o (checkM (fun th => (do if ← (do let z21 ← (do let z22 ← (pure th); pure (concl z22)); pure (is_forall z21)) then (do let z23 ← (do let z24 ← (pure th); pure (concl z24)); canM (fun z25 => (do let z26 ← (pure z25); find_termM (fun z27 => (do let z28 ← (pure z27); pure (is_exists z28))) z26)) z23) else pure false))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:B") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(a:B) IN ring_carrier b") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!n. group_pow (galois_group(k,l) h) f n IN
          group_carrier(inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1))) /\
          theta(group_pow (galois_group(k,l) h) f n) =
          ring_coset b (ideal_pow b Q (i + 1)) (ring_mul b (ring_of_num b n) a)") ASSUME_TAC THENL [FIRST_X_ASSUM (SUBST_ALL_TAC o (SYM o (checkM (fun th => (do let z20 ← (q r"ring_0 b = ring_0 (l:B ring)"); let z19 ← (do let z18 ← (pure th); pure (concl z18)); pure (z19 == z20)))))) THEN INDUCT_TAC THEN REWRITE_TAC [group_pow, (← CONJUNCT2 GALOIS_GROUP), ring_of_num] THENL [SUBGOAL_THEN (← q r"!j. (I:B->B) IN group_carrier(inertia_group(k,l) (h:A->B) b j)") ASSUME_TAC THENL [GEN_TAC THEN MP_TAC (← ISPEC (← q r"inertia_group(k,l) (h:A->B) b j") GROUP_ID) THEN REWRITE_TAC [(← CONJUNCT1 (← CONJUNCT2 INERTIA_GROUP))], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_LZERO, RING_COSET_0, RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET, (← GSYM QUOTIENT_RING_0)] THEN MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"ideal_pow b Q (i + 1):B->bool")] QUOTIENT_RING_0) THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [], FIRST_X_ASSUM (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"f o group_pow (galois_group(k,l) (h:A->B)) f n IN
          group_carrier(inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1)))") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"inertia_group(k,l) (h:A->B) b (ideal_pow b Q (i + 1))") GROUP_MUL) THEN ASM_SIMP_TAC [(← CONJUNCT2 INERTIA_GROUP)], ASM_REWRITE_TAC []] THEN FIRST_ASSUM (fun th => tactic_of do pure (W (fun (_asl, _w) => tactic_of do pure (MP_TAC (← SPECL [(← q r"f:B->B"), (← q r"group_pow (galois_group(k,l) (h:A->B)) (f:B->B) n")] (← (do let z10 ← (pure th); checkM (fun th => (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); canM (fun z13 => (do let z14 ← (pure z13); find_termM (fun z15 => (do let z17 ← (pure z15); let z16 ← (q r"g:B->B"); pure (z16 == z17))) z14)) z11)) z10))))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC [QUOTIENT_RING_ADD, RING_IDEAL_IDEAL_POW, RING_MUL, RING_OF_NUM] THEN AP_TERM_TAC THEN ASM_SIMP_TAC [RING_OF_NUM, r9]], SUBGOAL_THEN (← q r"ring_of_num b (ring_char(quotient_ring b (Q:B->bool))) IN Q") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool")] RING_HOMOMORPHISM_RING_COSET) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"ring_char(quotient_ring b (Q:B->bool))")) o (MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM))) THEN MP_TAC (← ISPECL [(← q r"quotient_ring b (Q:B->bool)"), (← q r"ring_char(quotient_ring b (Q:B->bool))")] RING_OF_NUM_EQ_0) THEN REWRITE_TAC [DIVIDES_REFL] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [QUOTIENT_RING_0, RING_COSET_EQ_IDEAL, RING_OF_NUM], ALL_TAC] THEN FIRST_X_ASSUM (STRIP_ASSUME_TAC o (SPEC (← q r"ring_char(quotient_ring b (Q:B->bool))"))) THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"group_pow (galois_group(k,l) (h:A->B)) (f:B->B)
           (ring_char(quotient_ring b (Q:B->bool)))")) o (checkM (fun th => (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); canM (fun z4 => (do let z5 ← (pure z4); find_termM (fun z6 => (do let z8 ← (pure z6); let z7 ← (q r"ring_0:(B->bool)ring->B->bool"); pure (z7 == z8))) z5)) z2))))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [QUOTIENT_RING_0, RING_IDEAL_IDEAL_POW, RING_COSET_EQ_IDEAL, RING_MUL, RING_OF_NUM] THEN ONCE_REWRITE_TAC [r1] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC [IDEAL_POW_1, RING_IDEAL_IMP_SUBSET]])

  let INERTIA_GROUP_WILD_PGROUP ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r8 ← ARITH_RULE (← q r"(N + 1) + 1 = N + 2:num")
    let r9 ← ARITH_RULE (← q r"N <= N + 1:num")
    let r10 ← ARITH_RULE (← q r"(m + 1) + 1 = m + 2:num")
    let r11 ← ARITH_RULE (← q r"1 <= m + 1:num")
    let r12 ← ARITH_RULE (← q r"SUC m + 2 = (m + 1) + 2")
    prove
      r"!(h:A->B) k l b Q.
          finite_extension(k,l) h /\
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          dedekind_domain b /\ field_of_fractions(b,l) I /\
          prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
          FINITE(ring_carrier(quotient_ring b Q))
          ==> pgroup {ring_char(quotient_ring b Q)}
                     (inertia_group(k,l) h b (ideal_pow b Q 2))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"prime(ring_char(quotient_ring b (Q:B->bool)))") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"quotient_ring b (Q:B->bool)") INTEGRAL_DOMAIN_CHAR) THEN ANTS_TAC THENL [MATCH_MP_TAC FIELD_IMP_INTEGRAL_DOMAIN THEN ASM_SIMP_TAC [FIELD_QUOTIENT_RING, PRIME_IMP_RING_IDEAL] THEN MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN ASM_REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED)], ASM_MESON_TAC [RING_CHAR_FINITE]], ALL_TAC] THEN ASM_SIMP_TAC [PGROUP_SING] THEN X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"!m. group_pow (galois_group(k,l) (h:A->B)) f
            (ring_char(quotient_ring b (Q:B->bool)) EXP m) IN
          group_carrier(inertia_group(k,l) h b (ideal_pow b Q (m + 2)))") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"!g j. g IN group_carrier(inertia_group(k,l) (h:A->B) b j)
                ==> g IN group_carrier(galois_group(k,l) h)") ASSUME_TAC THENL [REWRITE_TAC [inertia_group] THEN MESON_TAC [GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET, SUBSET], ALL_TAC] THEN INDUCT_TAC THENL [REWRITE_TAC [EXP, ADD_CLAUSES] THEN ASM_MESON_TAC [GROUP_POW_1], ALL_TAC] THEN REWRITE_TAC [EXP] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN SUBGOAL_THEN (← q r"(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [GROUP_POW_MUL] THEN REWRITE_TAC [r12] THEN MATCH_MP_TAC INERTIA_GROUP_IDEAL_POW_CHAR_POW THEN ASM_REWRITE_TAC [r11, r10], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"N:num") (MP_TAC o (SPEC (← q r"N + 1:num")))) THEN REWRITE_TAC [r9, r8] THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"N:num")) o (checkM (fun th => (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); canM (fun z3 => (do let z4 ← (pure z3); find_termM (fun z5 => (do let z7 ← (pure z5); let z6 ← (q r"(EXP)"); pure (z6 == z7))) z4)) z1))))) THEN ASM_REWRITE_TAC [IN_SING] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"group_pow (inertia_group(k,l) (h:A->B) b (ideal_pow b Q 2)) =
      group_pow (galois_group(k,l) h)") ASSUME_TAC THENL [REWRITE_TAC [inertia_group, GROUP_POW_SUBGROUP_GENERATED], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"inertia_group(k,l) (h:A->B) b (ideal_pow b Q 2)"), (← q r"f:B->B"), (← q r"ring_char(quotient_ring b (Q:B->bool)) EXP N")] GROUP_POW_EQ_ID) THEN ASM_REWRITE_TAC [(← CONJUNCT1 (← CONJUNCT2 INERTIA_GROUP))] THEN ASM_SIMP_TAC [DIVIDES_PRIMEPOW] THEN MESON_TAC [])

  let INERTIA_GROUP_WILD_SUBSET ← prove
    r"!(h:A->B) k l b Q c m.
        finite_extension(k,l) h /\
        subring_generated l (ring_carrier b) = b /\
        (!f. f IN group_carrier(galois_group(k,l) h)
             ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
        dedekind_domain b /\ field_of_fractions(b,l) I /\
        prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
        FINITE(ring_carrier(quotient_ring b Q)) /\
        c subgroup_of inertia_group(k,l) h b Q /\
        CARD(group_carrier(inertia_group(k,l) h b Q)) = m * CARD c
        ==> (group_carrier(inertia_group(k,l) h b (ideal_pow b Q 2))
             SUBSET c <=>
             ~(ring_char(quotient_ring b Q) divides m))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"p = ring_char(quotient_ring b (Q:B->bool))") THEN SUBGOAL_THEN (← q r"ring_0 b = ring_0 (l:B ring)") ASSUME_TAC THENL [UNDISCH_TAC (← q r"subring_generated l (ring_carrier b) = (b:B ring)") THEN DISCH_THEN (fun th => tactic_of do pure (ONCE_REWRITE_TAC [(← SYM th)])) THEN REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED)], ALL_TAC] THEN SUBGOAL_THEN (← q r"prime p") ASSUME_TAC THENL [EXPAND_TAC "p" THEN MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_CHAR THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FIELD_IMP_INTEGRAL_DOMAIN THEN ASM_SIMP_TAC [FIELD_QUOTIENT_RING, PRIME_IMP_RING_IDEAL] THEN MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"G0 = inertia_group(k,l) (h:A->B) b Q") THEN ABBREV_TAC (← q r"N = group_carrier(inertia_group(k,l) (h:A->B) b (ideal_pow b Q 2))") THEN SUBGOAL_THEN (← q r"FINITE(group_carrier(G0:(B->B)group)) /\ FINITE(N:(B->B)->bool)") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["G0", "N"] THEN CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"group_carrier(galois_group(k,l) (h:A->B))") THEN REWRITE_TAC [inertia_group, GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET] THEN ASM_SIMP_TAC [FINITE_GALOIS_GROUP], ALL_TAC] THEN SUBGOAL_THEN (← q r"(N:(B->B)->bool) normal_subgroup_of G0") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"b:B ring"), (← q r"Q:B->bool")] DEDEKIND_PRIME_IDEAL_UNIFORMIZER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:B") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"t:B")] INERTIA_GROUP_TAME_HOMOMORPHISM) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"theta:(B->B)->(B->bool)") (CONJUNCTS_THEN2 (ASSUME_TAC o (MATCH_MP NORMAL_SUBGROUP_GROUP_KERNEL)) (SUBST_ALL_TAC o CONJUNCT2))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"?j. CARD(N:(B->B)->bool) = p EXP j") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] INERTIA_GROUP_WILD_PGROUP) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"inertia_group(k,l) (h:A->B) b (ideal_pow b Q 2)"), (← q r"p:num")] FINITE_PGROUP_SING) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"?d. coprime(d,p) /\ CARD(group_carrier(G0:(B->B)group)) =
        d * CARD(N:(B->B)->bool)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool")] INERTIA_GROUP_TAME_QUOTIENT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o (CONJUNCT2 o CONJUNCT2)) THEN MP_TAC (← ISPECL [(← q r"G0:(B->B)group"), (← q r"N:(B->B)->bool")] LAGRANGE_THEOREM_RIGHT) THEN ASM_SIMP_TAC [NORMAL_SUBGROUP_IMP_SUBGROUP, (← GSYM QUOTIENT_GROUP)] THEN DISCH_TAC THEN EXISTS_TAC (← q r"CARD(group_carrier(quotient_group G0 (N:(B->B)->bool)))") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN EQ_TAC THENL [DISCH_TAC, DISCH_TAC THEN MATCH_MP_TAC NORMAL_PGROUP_SUBSET_COPRIME_INDEX THEN MAP_EVERY EXISTS_TAC [(← q r"G0:(B->B)group"), (← q r"p:num"), (← q r"m:num"), (← q r"j:num")] THEN ASM_REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"CARD(N:(B->B)->bool) divides CARD(c:(B->B)->bool)") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"subgroup_generated G0 (c:(B->B)->bool)"), (← q r"N:(B->B)->bool")] LAGRANGE_THEOREM) THEN ASM_SIMP_TAC [CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"group_carrier(G0:(B->B)group)") THEN ASM_SIMP_TAC [SUBGROUP_OF_IMP_SUBSET], ASM_SIMP_TAC [SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ] THEN ASM_SIMP_TAC [NORMAL_SUBGROUP_IMP_SUBGROUP]], ALL_TAC] THEN DISCH_THEN ((X_CHOOSE_TAC (← q r"e:num")) o (REWRITE_RULE [divides])) THEN SUBGOAL_THEN (← q r"~(p:num = 0) /\ ~(p = 1)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP PRIME_GE_2)) THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"~(CARD(N:(B->B)->bool) = 0)") ASSUME_TAC THENL [ASM_REWRITE_TAC [EXP_EQ_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"d:num = m * e") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"d:num"), (← q r"m * e:num"), (← q r"CARD(N:(B->B)->bool)")] EQ_MULT_RCANCEL) THEN REWRITE_TAC [(← ASSUME (← q r"~(CARD(N:(B->B)->bool) = 0)"))] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); pure (is_eq z7)) then (do let z12 ← (q r"d * CARD(N:(B->B)->bool)"); let z11 ← (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); liftExcept (rhs z9)); pure (z11 == z12)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [MULT_AC], ALL_TAC] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(p:num) divides 1") MP_TAC THENL [UNDISCH_TAC (← q r"coprime(d:num,p)") THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"d:num"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (lhs z3)); pure (z5 == z6)) else pure false)))) THEN UNDISCH_TAC (← q r"p divides (m:num)") THEN CONV_TAC NUMBER_RULE, ASM_REWRITE_TAC [DIVIDES_ONE]])

  let INERTIA_GROUP_WILD_TRIVIAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(a:B->B) IN s ==> (s = {a} <=> s SUBSET {a})")
    prove
      r"!(h:A->B) k l b Q.
          finite_extension(k,l) h /\
          subring_generated l (ring_carrier b) = b /\
          (!f. f IN group_carrier(galois_group(k,l) h)
               ==> IMAGE f (ring_carrier b) SUBSET ring_carrier b) /\
          dedekind_domain b /\ field_of_fractions(b,l) I /\
          prime_ideal b Q /\ ~(Q = {ring_0 l}) /\
          FINITE(ring_carrier(quotient_ring b Q))
          ==> (group_carrier(inertia_group(k,l) h b (ideal_pow b Q 2)) = {I} <=>
               ~(ring_char(quotient_ring b Q) divides
                 CARD(group_carrier(inertia_group(k,l) h b Q))))"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"b:B ring"), (← q r"Q:B->bool"), (← q r"{I:B->B}"), (← q r"CARD(group_carrier(inertia_group(k,l) (h:A->B) b Q))")] INERTIA_GROUP_WILD_SUBSET) THEN ASM_REWRITE_TAC [CARD_SING, MULT_CLAUSES] THEN ANTS_TAC THENL [MP_TAC (← ISPEC (← q r"inertia_group(k,l) (h:A->B) b Q") TRIVIAL_SUBGROUP_OF) THEN REWRITE_TAC [(← CONJUNCT2 INERTIA_GROUP)], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC r1 THEN MP_TAC (← ISPEC (← q r"inertia_group(k,l) (h:A->B) b (ideal_pow b Q 2)") GROUP_ID) THEN REWRITE_TAC [(← CONJUNCT2 INERTIA_GROUP)])

  let NUMBER_FIELD_WILD_INERTIA_TRIVIAL ← prove
    r"!(h:A->B) k l p Q.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
        ==> (group_carrier
              (inertia_group(k,l) h (ring_of_integers l)
                (ideal_pow (ring_of_integers l) Q 2)) = {I} <=>
             ~(ring_char(quotient_ring (ring_of_integers l) Q) divides
               ramification_index (ring_of_integers k,ring_of_integers l)
                                  h Q))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_IMP_FIELD_EXTENSION, field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_DECOMPOSITION_GROUP) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o (SYM o (CONJUNCT1 o CONJUNCT2))) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC INERTIA_GROUP_WILD_TRIVIAL THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING, DEDEKIND_RING_OF_INTEGERS, GALOIS_GROUP_RING_OF_INTEGERS] THEN REPEAT CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_SIMP_TAC [], MESON_TAC [GALOIS_GROUP_RING_OF_INTEGERS], MP_TAC (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_SIMP_TAC []])

  -- @@RETURN BEGIN
  return { INERTIA_GROUP_IDEAL_POW_CHAR_POW, INERTIA_GROUP_WILD_PGROUP,
           INERTIA_GROUP_WILD_SUBSET, INERTIA_GROUP_WILD_TRIVIAL,
           NUMBER_FIELD_WILD_INERTIA_TRIVIAL }
  -- @@RETURN END

end HolANT.RamificationGroups
