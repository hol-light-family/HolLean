/- ========================================================================= -/
/- ANT: The ring of S-integers of a Dedekind domain and of a number ...    -/
/- ========================================================================= -/
/- File: HolANT/SIntegers.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/s_integers.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antsintegersdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/ring_groups.ml, Library/permutations.ml, Library/ring_det.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, Library/matroids.ml, Library/fieldtheory.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, Library/isum.ml, ANT/ideal_norm.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/classgroup_group.ml, ANT/fractional_ideals.ml, ANT/dedekind_criteria.ml, ANT/nf_valuation.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.SIntegers fills them).

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
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.RingGroups
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolANT.IdealArith
import HolLibrary.Products
import HolANT.Algmisc
import HolLibrary.Matroids
import HolLibrary.FieldTheory
import HolANT.Integral
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolLibrary.Isum
import HolANT.IdealNorm
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.Classgroup
import HolANT.ClassgroupGroup
import HolANT.FractionalIdeals
import HolANT.DedekindCriteria
import HolANT.NfValuation

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
open HolANT.Classgroup
open HolANT.ClassgroupGroup
open HolANT.FractionalIdeals
open HolANT.DedekindCriteria
open HolANT.NfValuation

namespace HolANT.SIntegers

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ABELIAN_CLASS_GROUP ABELIAN_GROUP_SUM_MUL CARD_DIVIDES_GROUP_EPIMORPHIC_IMAGE
   CARRIER_SUBRING_GENERATED_SUBRING CLASS_GROUP
   CLASS_GROUP_SUM_PRIME_CLASSES_EQ_ID DEDEKIND_CLASS_GROUP_EXTENSION
   DEDEKIND_EQ_IDEALS_INVERTIBLE DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE
   DEDEKIND_IDEAL_SUBSET_POW_VALUATION DEDEKIND_IDEAL_SUBSET_VALUATION
   DEDEKIND_IN_IDEAL_POW_VALUATION DEDEKIND_KRULL_DIMENSION_ONE
   DEDEKIND_VALUATION DEDEKIND_VALUATION_1 DEDEKIND_VALUATION_ADD
   DEDEKIND_VALUATION_FINITE DEDEKIND_VALUATION_IMAGE
   DEDEKIND_VALUATION_INTEGRAL DEDEKIND_VALUATION_INV DEDEKIND_VALUATION_MUL
   DEDEKIND_VALUATION_NEG DEDEKIND_VALUATION_POS DEDEKIND_VALUATION_PRIME_IDEAL
   DEDEKIND_VALUATION_RING_DVR DEDEKIND_VALUATION_UNIT EQ_TRANS EXISTS_IN_IMAGE
   EXTENSION EXTENSIONAL FIELD_FRACTION_NONZERO FIELD_IMP_INTEGRAL_DOMAIN
   FIELD_INV_EQ_0 FIELD_MUL_EQ_0 FIELD_MUL_RINV FIELD_NONTRIVIAL
   FIELD_OF_FRACTIONS_IMP_MONOMORPHISM FIELD_UNIT FINITE_IMAGE FINITE_RESTRICT
   FINITE_SUBSET FINITE_UNION FINITE_UNIONS FIRST_GROUP_EPIMORPHISM_THEOREM
   FORALL_AND_THM FORALL_IN_GSPEC FORALL_IN_IMAGE FORALL_IN_UNIONS FUN_EQ_THM
   GROUP_HOMOMORPHISM GROUP_HOMOMORPHISM_UNIT_GROUP GROUP_ID GROUP_SUM
   GROUP_SUM_EQ GROUP_ZPOW GROUP_ZPOW_ADD IDEAL_CLASS_EQ_ID
   IDEAL_CLASS_EQ_SUM_PRIME_CLASSES IDEAL_CLASS_IN_CLASS_GROUP IDEAL_GENERATED_0
   IDEAL_GENERATED_EQ_0 IDEAL_GENERATED_IMAGE_IDEAL_GENERATED
   IDEAL_GENERATED_INC IDEAL_GENERATED_MINIMAL IDEAL_GENERATED_MINIMAL_EQ
   IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0 IDEAL_POW_EQ_ZERO
   IDEAL_POW_HOMOMORPHIC_IMAGE IDEAL_PROD_HOMOMORPHIC_IMAGE IDEAL_VALUATION_EQ_0
   IDEAL_VALUATION_FINITE_SUPPORT IDEAL_VALUATION_IDEAL_POW
   IDEAL_VALUATION_IDEAL_PROD IDEAL_VALUATION_PRIME IDEAL_VALUATION_UNIQUE
   IMAGE_CLAUSES IMAGE_I IMP_CONJ INTEGER_GROUP
   INTEGRAL_DOMAIN_SUBRING_GENERATED INT_LE_REFL INT_OF_NUM_ADD INT_OF_NUM_LE
   INT_OF_NUM_SUC INT_POS INT_SUB_RZERO IN_ELIM_THM IN_IDEAL_GENERATED_SELF
   IN_IDEAL_GENERATED_SING_EQ IN_IMAGE IN_RING_IDEAL_0 IN_SING IN_SUBGROUP_SUM
   IN_SUBGROUP_ZPOW IN_UNION : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (IN_UNIONS IN_UNIV ISOMORPHIC_GROUP_SYM I_DEF I_THM LE LEFT_IMP_EXISTS_THM
   LE_REFL MONO_EXISTS MULT_CLAUSES NOT_IN_EMPTY NUMBER_FIELD_CLASS_GROUP_FINITE
   PRIME_IDEAL_HOMOMORPHIC_PREIMAGE PRIME_IMP_PROPER_IDEAL PRIME_IMP_RING_IDEAL
   PRODUCT_GROUP PSUBSET PSUBSET_ALT RESTRICTION RESTRICTION_EXTENSION
   RESTRICTION_IN_CARTESIAN_PRODUCT RIGHT_EXISTS_IMP_THM RIGHT_FORALL_IMP_THM
   RING_0 RING_1 RING_ADD RING_ADD_LZERO RING_ADD_RDISTRIB RING_ADD_RZERO
   RING_CARRIER_SUBRING_GENERATED_SUBSET RING_HOMOMORPHISM_0
   RING_HOMOMORPHISM_ADD RING_HOMOMORPHISM_IN_CARRIER RING_HOMOMORPHISM_MUL
   RING_HOMOMORPHISM_NEG RING_IDEAL_0 RING_IDEAL_HOMOMORPHIC_PREIMAGE
   RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_POW RING_IDEAL_IMP_SUBSET
   RING_INV RING_MONOMORPHISM_EQ_0 RING_MONOMORPHISM_IMP_HOMOMORPHISM
   RING_MONOMORPHISM_INCLUSION RING_MONOMORPHISM_INJECTIVE_EQ
   RING_MONOMORPHISM_INTO_SUBRING RING_MUL RING_MUL_ASSOC RING_MUL_LNEG
   RING_MUL_LZERO RING_MUL_RID RING_MUL_RZERO RING_NEG RING_NEG_EQ_0
   RING_OF_INTEGERS RING_OF_INTEGERS_FRACTION_FIELD RING_OF_INTEGERS_SUBRING
   RING_OF_INT_SUBRING_GENERATED RING_OF_NUM_SUBRING_GENERATED
   RING_POW_SUBRING_GENERATED RING_SUB_SUBRING_GENERATED RING_UNIT_IN_CARRIER
   RING_UNIT_SUBRING_GENERATED SING_SUBSET SKOLEM_THM SUBGROUP_GENERATED_INC
   SUBGROUP_GENERATED_MINIMAL SUBGROUP_GROUP_KERNEL SUBGROUP_SUBGROUP_GENERATED
   SUBRING_GENERATED SUBRING_GENERATED_MONO SUBSET SUBSET_ANTISYM
   TRIVIAL_CLASS_GROUP UNIT_GROUP cartesian_product class_number
   field_of_fractions group_epimorphism group_exactness group_homomorphism
   group_image group_kernel group_monomorphism ideal_classes ideal_prod
   prime_ideal principal_ideal proper_ideal ring_divides ring_ideal ring_setmul
   subring_of trivial_group : thm)
  deriving Inhabited

/-- What s_integers.ml uses from Session besides theorems. -/
structure SIntegersDeps where
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
/- s_integers.ml phrases from line 115 to 730                             -/
/- ---------------------------------------------------------------------- -/

structure SIntegers01 where
  -- @@FIELDS
  ring_of_s_integers : thm
  RING_OF_S_INTEGERS : thm
  RING_OF_S_INTEGERS_SUBSET : thm
  RING_OF_S_INTEGERS_SUBRING_OF : thm
  RING_OF_S_INTEGERS_CARRIER : thm
  RING_OF_S_INTEGERS_SUBRING : thm
  INTEGRAL_DOMAIN_RING_OF_S_INTEGERS : thm
  RING_OF_S_INTEGERS_MONO : thm
  RING_OF_S_INTEGERS_IMAGE : thm
  RING_MONOMORPHISM_RING_OF_S_INTEGERS : thm
  FIELD_OF_FRACTIONS_RING_OF_S_INTEGERS : thm
  RING_OF_S_INTEGERS_EMPTY : thm
  RING_UNIT_RING_OF_S_INTEGERS : thm
  RING_OF_S_INTEGERS_COMPLEMENT_SING : thm
  RING_OF_S_INTEGERS_VALUATION_IDEAL : thm
  RING_OF_S_INTEGERS_IDEAL_EXTENSION : thm
  RING_OF_S_INTEGERS_IDEAL_CONTRACTION : thm
  RING_OF_S_INTEGERS_IDEAL_EXTENSION_EQ_CARRIER : thm
  RING_OF_S_INTEGERS_IDEAL_EXTENSION_PRIME : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupSIntegers01 [HolBase] (D : SIntegersDeps) :
    ExceptT String IO SIntegers01 := do
  -- @@SCOPE BEGIN
  let { ASM_INT_ARITH_TAC, ASM_MESON_TAC, INT_ARITH_TAC, MESON, RING_RULE, SET_RULE,
        SET_TAC, TAUT, new_definition, .. } := D
  let { CARRIER_SUBRING_GENERATED_SUBRING, DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE,
        DEDEKIND_IDEAL_SUBSET_VALUATION, DEDEKIND_KRULL_DIMENSION_ONE,
        DEDEKIND_VALUATION, DEDEKIND_VALUATION_1, DEDEKIND_VALUATION_ADD,
        DEDEKIND_VALUATION_IMAGE, DEDEKIND_VALUATION_INTEGRAL, DEDEKIND_VALUATION_INV,
        DEDEKIND_VALUATION_MUL, DEDEKIND_VALUATION_NEG, DEDEKIND_VALUATION_POS,
        DEDEKIND_VALUATION_RING_DVR, EXTENSION, FIELD_FRACTION_NONZERO,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_INV_EQ_0, FIELD_MUL_EQ_0, FIELD_MUL_RINV,
        FIELD_NONTRIVIAL, FIELD_OF_FRACTIONS_IMP_MONOMORPHISM, FIELD_UNIT,
        FORALL_AND_THM, FORALL_IN_GSPEC, FORALL_IN_IMAGE, IDEAL_GENERATED_EQ_0,
        IDEAL_GENERATED_INC, IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_MINIMAL_EQ,
        IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0, IDEAL_VALUATION_EQ_0,
        IDEAL_VALUATION_IDEAL_PROD, IDEAL_VALUATION_PRIME,
        INTEGRAL_DOMAIN_SUBRING_GENERATED, INT_LE_REFL, INT_OF_NUM_ADD, INT_OF_NUM_LE,
        INT_POS, INT_SUB_RZERO, IN_ELIM_THM, IN_IDEAL_GENERATED_SELF, IN_IMAGE,
        IN_RING_IDEAL_0, IN_SING, .. } := D.core1
  let { I_DEF, I_THM, LE, LEFT_IMP_EXISTS_THM, NOT_IN_EMPTY, PRIME_IMP_RING_IDEAL,
        RING_0, RING_1, RING_ADD, RING_ADD_LZERO, RING_ADD_RDISTRIB, RING_ADD_RZERO,
        RING_CARRIER_SUBRING_GENERATED_SUBSET, RING_HOMOMORPHISM_0,
        RING_HOMOMORPHISM_ADD, RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_MUL,
        RING_HOMOMORPHISM_NEG, RING_IDEAL_0, RING_IDEAL_HOMOMORPHIC_PREIMAGE,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IMP_SUBSET, RING_INV,
        RING_MONOMORPHISM_EQ_0, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
        RING_MONOMORPHISM_INCLUSION, RING_MONOMORPHISM_INTO_SUBRING, RING_MUL,
        RING_MUL_ASSOC, RING_MUL_LNEG, RING_MUL_LZERO, RING_MUL_RID, RING_MUL_RZERO,
        RING_NEG, RING_NEG_EQ_0, RING_OF_INT_SUBRING_GENERATED,
        RING_OF_NUM_SUBRING_GENERATED, RING_POW_SUBRING_GENERATED,
        RING_SUB_SUBRING_GENERATED, RING_UNIT_SUBRING_GENERATED, SING_SUBSET,
        SUBRING_GENERATED, SUBRING_GENERATED_MONO, SUBSET, SUBSET_ANTISYM,
        field_of_fractions, ideal_prod, ring_ideal, ring_setmul, subring_of, .. } := D.core2
  -- @@SCOPE END

  let ring_of_s_integers ← new_definition
    r"ring_of_s_integers (r:A ring,k:B ring) (h:A->B) S =
  subring_generated k
   {x | x IN ring_carrier k /\
        !P. prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN S)
            ==> x = ring_0 k \/ &0 <= dedekind_valuation (r,k) h P x}"

  let RING_OF_S_INTEGERS ← prove
    r"(!r k (h:A->B) S. ring_0(ring_of_s_integers (r,k) h S) = ring_0 k) /\
   (!r k (h:A->B) S. ring_1(ring_of_s_integers (r,k) h S) = ring_1 k) /\
   (!r k (h:A->B) S. ring_neg(ring_of_s_integers (r,k) h S) = ring_neg k) /\
   (!r k (h:A->B) S. ring_add(ring_of_s_integers (r,k) h S) = ring_add k) /\
   (!r k (h:A->B) S. ring_mul(ring_of_s_integers (r,k) h S) = ring_mul k) /\
   (!r k (h:A->B) S. ring_sub(ring_of_s_integers (r,k) h S) = ring_sub k) /\
   (!r k (h:A->B) S. ring_pow(ring_of_s_integers (r,k) h S) = ring_pow k) /\
   (!r k (h:A->B) S.
        ring_of_num(ring_of_s_integers (r,k) h S) = ring_of_num k) /\
   (!r k (h:A->B) S.
        ring_of_int(ring_of_s_integers (r,k) h S) = ring_of_int k)"
    (REWRITE_TAC [ring_of_s_integers, SUBRING_GENERATED, RING_SUB_SUBRING_GENERATED, RING_POW_SUBRING_GENERATED, RING_OF_NUM_SUBRING_GENERATED, RING_OF_INT_SUBRING_GENERATED])

  let RING_OF_S_INTEGERS_SUBSET ← prove
    r"!r k (h:A->B) S.
        ring_carrier(ring_of_s_integers (r,k) h S) SUBSET ring_carrier k"
    (REWRITE_TAC [ring_of_s_integers, RING_CARRIER_SUBRING_GENERATED_SUBSET])

  let RING_OF_S_INTEGERS_SUBRING_OF ← prove
    r"!r k (h:A->B) S.
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> {x | x IN ring_carrier k /\
                 !P. prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN S)
                     ==> x = ring_0 k \/
                         &0 <= dedekind_valuation (r,k) h P x}
            subring_of k"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN REWRITE_TAC [subring_of, SUBSET, IN_ELIM_THM] THEN SIMP_TAC [RING_0, RING_1, RING_NEG, RING_ADD, RING_MUL] THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [DEDEKIND_VALUATION_1, INT_LE_REFL], REPEAT STRIP_TAC THEN ASM_SIMP_TAC [DEDEKIND_VALUATION_NEG, RING_NEG_EQ_0], MAP_EVERY X_GEN_TAC [(← q r"x:B"), (← q r"y:B")] THEN STRIP_TAC THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN REPEAT (FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:A->bool")))) THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_SIMP_TAC [RING_ADD_LZERO] THEN ASM_CASES_TAC (← q r"y:B = ring_0 k") THEN ASM_SIMP_TAC [RING_ADD_RZERO] THEN REPEAT DISCH_TAC THEN ASM_CASES_TAC (← q r"ring_add k x y = ring_0 k:B") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"x:B"), (← q r"y:B")] DEDEKIND_VALUATION_ADD) THEN ASM_REWRITE_TAC [] THEN ASM_INT_ARITH_TAC, MAP_EVERY X_GEN_TAC [(← q r"x:B"), (← q r"y:B")] THEN STRIP_TAC THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN REPEAT (FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:A->bool")))) THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_SIMP_TAC [RING_MUL_LZERO] THEN ASM_CASES_TAC (← q r"y:B = ring_0 k") THEN ASM_SIMP_TAC [RING_MUL_RZERO] THEN ASM_SIMP_TAC [DEDEKIND_VALUATION_MUL] THEN INT_ARITH_TAC])

  let RING_OF_S_INTEGERS_CARRIER ← prove
    r"!r k (h:A->B) S.
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> ring_carrier(ring_of_s_integers (r,k) h S) =
            {x | x IN ring_carrier k /\
                 !P. prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN S)
                     ==> x = ring_0 k \/
                         &0 <= dedekind_valuation (r,k) h P x}"
    (SIMP_TAC [ring_of_s_integers, CARRIER_SUBRING_GENERATED_SUBRING, RING_OF_S_INTEGERS_SUBRING_OF])

  let RING_OF_S_INTEGERS_SUBRING ← prove
    r"!r k (h:A->B) S.
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> ring_carrier(ring_of_s_integers (r,k) h S) subring_of k /\
            subring_generated k (ring_carrier(ring_of_s_integers (r,k) h S)) =
            ring_of_s_integers (r,k) h S"
    (SIMP_TAC [RING_OF_S_INTEGERS_CARRIER, RING_OF_S_INTEGERS_SUBRING_OF] THEN REWRITE_TAC [ring_of_s_integers])

  let INTEGRAL_DOMAIN_RING_OF_S_INTEGERS ← prove
    r"!r k (h:A->B) S.
        field k ==> integral_domain(ring_of_s_integers (r,k) h S)"
    (SIMP_TAC [ring_of_s_integers, INTEGRAL_DOMAIN_SUBRING_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN])

  let RING_OF_S_INTEGERS_MONO ← prove
    r"!r k (h:A->B) S S'.
        S SUBSET S'
        ==> ring_carrier(ring_of_s_integers (r,k) h S) SUBSET
            ring_carrier(ring_of_s_integers (r,k) h S')"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [ring_of_s_integers] THEN MATCH_MP_TAC SUBRING_GENERATED_MONO THEN ASM SET_TAC [])

  let RING_OF_S_INTEGERS_IMAGE ← prove
    r"!r k (h:A->B) S.
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> IMAGE h (ring_carrier r) SUBSET
            ring_carrier(ring_of_s_integers (r,k) h S)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN ASM_SIMP_TAC [RING_OF_S_INTEGERS_CARRIER, SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"a:A = ring_0 r") THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_0], DISJ2_TAC] THEN ASM_SIMP_TAC [DEDEKIND_VALUATION_IMAGE, INT_POS])

  let RING_MONOMORPHISM_RING_OF_S_INTEGERS ← prove
    r"!r k (h:A->B) S.
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> ring_monomorphism(r,ring_of_s_integers (r,k) h S) h"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] RING_OF_S_INTEGERS_IMAGE) THEN ASM_SIMP_TAC [RING_OF_S_INTEGERS_CARRIER] THEN DISCH_TAC THEN REWRITE_TAC [ring_of_s_integers] THEN MATCH_MP_TAC RING_MONOMORPHISM_INTO_SUBRING THEN ASM_REWRITE_TAC [])

  let FIELD_OF_FRACTIONS_RING_OF_S_INTEGERS ← prove
    r"!r k (h:A->B) S.
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> field_of_fractions (ring_of_s_integers (r,k) h S,k) I"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] RING_OF_S_INTEGERS_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN REWRITE_TAC [field_of_fractions] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [REWRITE_TAC [ring_of_s_integers, (← REWRITE_RULE [(← GSYM I_DEF)] RING_MONOMORPHISM_INCLUSION)], ALL_TAC] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"x:B")) o (CONJUNCT2 o (CONJUNCT2 o (GEN_REWRITE_RULE id [field_of_fractions]))))) THEN ASM_REWRITE_TAC [I_THM] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"(h:A->B) a"), (← q r"(h:A->B) b")] THEN ASM_REWRITE_TAC [RING_OF_S_INTEGERS] THEN REPEAT CONJ_TAC THENL [ASM SET_TAC [], ASM SET_TAC [], ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0]])

  let RING_OF_S_INTEGERS_EMPTY ← prove
    r"!r k (h:A->B).
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> ring_carrier(ring_of_s_integers (r,k) h {}) =
            IMAGE h (ring_carrier r)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN ASM_SIMP_TAC [RING_OF_S_INTEGERS_CARRIER, NOT_IN_EMPTY] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:B") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"(x:B) IN ring_carrier k") THENL [ASM_REWRITE_TAC [], ASM_REWRITE_TAC [IN_IMAGE] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER]] THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THENL [ASM_REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"ring_0 r:A") THEN ASM_MESON_TAC [RING_HOMOMORPHISM_0, RING_0], ASM_SIMP_TAC [DEDEKIND_VALUATION_INTEGRAL]])

  let RING_UNIT_RING_OF_S_INTEGERS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(p ==> q) /\ (p ==> r) <=> p ==> q /\ r")
    prove
      r"!r k (h:A->B) S x.
          dedekind_domain r /\ field_of_fractions (r,k) h
          ==> (ring_unit (ring_of_s_integers (r,k) h S) x <=>
               x IN ring_carrier k /\ ~(x = ring_0 k) /\
               !P. prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN S)
                   ==> dedekind_valuation (r,k) h P x = &0)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN REWRITE_TAC [ring_of_s_integers] THEN ASM_SIMP_TAC [RING_UNIT_SUBRING_GENERATED, RING_OF_S_INTEGERS_SUBRING_OF, FIELD_UNIT] THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"(x:B) IN ring_carrier k") THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_INV, FIELD_INV_EQ_0, DEDEKIND_VALUATION_INV] THEN REWRITE_TAC [(← GSYM FORALL_AND_THM)] THEN AP_TERM_TAC THEN ABS_TAC THEN REWRITE_TAC [r1] THEN AP_TERM_TAC THEN INT_ARITH_TAC)

  let RING_OF_S_INTEGERS_COMPLEMENT_SING ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!r k (h:A->B) P.
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          prime_ideal r P /\ ~(P = {ring_0 r})
          ==> ring_of_s_integers (r,k) h {Q | ~(Q = P)} =
              subring_generated k
                {x | x IN ring_carrier k /\
                     (x = ring_0 k \/ &0 <= dedekind_valuation (r,k) h P x)} /\
              DVR(ring_of_s_integers (r,k) h {Q | ~(Q = P)})"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [REWRITE_TAC [ring_of_s_integers, IN_ELIM_THM] THEN AP_TERM_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC DEDEKIND_VALUATION_RING_DVR THEN ASM_REWRITE_TAC []])

  let RING_OF_S_INTEGERS_VALUATION_IDEAL ← prove
    r"!r k (h:A->B) S n.
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> ring_ideal (ring_of_s_integers (r,k) h S)
             {x | x IN ring_carrier k /\
                  !P. prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN S)
                      ==> x = ring_0 k \/
                          &(n P) <= dedekind_valuation (r,k) h P x}"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN ASM_SIMP_TAC [ring_ideal, RING_OF_S_INTEGERS_CARRIER, RING_OF_S_INTEGERS, SUBSET, IN_ELIM_THM, RING_0, RING_NEG, RING_ADD, RING_MUL] THEN REPEAT CONJ_TAC THENL [X_GEN_TAC (← q r"x:B") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPEC (← q r"(n:(A->bool)->num) P") INT_POS) THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_REWRITE_TAC [] THEN INT_ARITH_TAC, REPEAT STRIP_TAC THEN ASM_SIMP_TAC [DEDEKIND_VALUATION_NEG, RING_NEG_EQ_0], MAP_EVERY X_GEN_TAC [(← q r"x:B"), (← q r"y:B")] THEN STRIP_TAC THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN REPEAT (FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:A->bool")))) THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_SIMP_TAC [RING_ADD_LZERO] THEN ASM_CASES_TAC (← q r"y:B = ring_0 k") THEN ASM_SIMP_TAC [RING_ADD_RZERO] THEN REPEAT DISCH_TAC THEN ASM_CASES_TAC (← q r"ring_add k x y = ring_0 k:B") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"x:B"), (← q r"y:B")] DEDEKIND_VALUATION_ADD) THEN ASM_REWRITE_TAC [] THEN ASM_INT_ARITH_TAC, MAP_EVERY X_GEN_TAC [(← q r"x:B"), (← q r"y:B")] THEN STRIP_TAC THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN REPEAT (FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:A->bool")))) THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_SIMP_TAC [RING_MUL_LZERO] THEN ASM_CASES_TAC (← q r"y:B = ring_0 k") THEN ASM_SIMP_TAC [RING_MUL_RZERO] THEN ASM_SIMP_TAC [DEDEKIND_VALUATION_MUL] THEN INT_ARITH_TAC])

  let RING_OF_S_INTEGERS_IDEAL_EXTENSION ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"!k:B ring u v w.
        u IN ring_carrier k /\ v IN ring_carrier k /\ w IN ring_carrier k
        ==> ring_mul k u (ring_mul k v w) = ring_mul k v (ring_mul k u w)"
    let r2 ← RING_RULE q1
    let q3 ← q r"ring_mul k ((h:A->B) c) (ring_mul k x (ring_inv k (h c))) =
    ring_mul k x (ring_mul k (h c) (ring_inv k (h c)))"
    let q4 ← q r"a = b ==> (a:B) IN s ==> b IN s"
    let r5 ← MESON [] q4
    let q6 ← q r"c:A"
    let v7 ← GSYM RING_MUL_ASSOC
    let q8 ← q r"(h:A->B) x' IN ring_carrier k /\ h y IN ring_carrier k"
    let q9 ← q r"(h:A->B) x' IN ring_carrier k /\ h y IN ring_carrier k"
    let q10 ← q r"(h:A->B) x' IN ring_carrier k"
    let q11 ← q r"ring_neg O = ring_neg(k:B ring)"
    let v12 ← ASSUME q11
    let q13 ← q r"ring_add O = ring_add(k:B ring)"
    let v14 ← ASSUME q13
    let q15 ← q r"ring_mul O = ring_mul(k:B ring)"
    let v16 ← ASSUME q15
    let q17 ← q r"ring_0 O = ring_0(k:B ring)"
    let v18 ← ASSUME q17
    let q21 ← q r"!k:B ring u v z.
            u IN ring_carrier k /\ v IN ring_carrier k /\ z IN ring_carrier k
            ==> ring_mul k (ring_mul k u v) z =
                ring_mul k (ring_mul k v z) u"
    let r22 ← RING_RULE q21
    let q23 ← q r"ring_mul k (ring_mul k ((h:A->B) a) (h b)) z =
        ring_mul O (ring_mul k (h b) z) (h a)"
    let q24 ← q r"(a:A) IN ring_carrier r /\ (b:A) IN ring_carrier r"
    let q25 ← q r"b:A"
    let q26 ← q r"a:A"
    let q27 ← q r"ideal_prod r j m SUBSET
    {t | t IN ring_carrier r /\ ring_mul k ((h:A->B) t) z IN E}"
    let v28 ← GSYM INT_OF_NUM_ADD
    let v29 ← GSYM INT_OF_NUM_LE
    let q30 ← q r"P:A->bool"
    let q32 ← q r"m:A->bool"
    let q33 ← q r"ideal_generated r {b:A}"
    let q34 ← q r"r:A ring"
    let v35 ← ISPECL [q34, q33, q32] DEDEKIND_IDEAL_SUBSET_VALUATION
    let q36 ← q r"m:A->bool"
    let q37 ← q r"j:A->bool"
    let q38 ← q r"P:A->bool"
    let q39 ← q r"r:A ring"
    let v40 ← ISPECL [q39, q38, q37, q36] IDEAL_VALUATION_IDEAL_PROD
    let q41 ← q r"P:A->bool"
    let q42 ← q r"~(z:B = ring_0 k)"
    let q43 ← q r"~((h:A->B) b = ring_0 k)"
    let q44 ← q r"b:A = ring_0 r"
    let q45 ← q r"P:A->bool"
    let q46 ← q r"(h:A->B) b IN ring_carrier k"
    let q47 ← q r"(b:A) IN ring_carrier r"
    let q48 ← q r"b:A"
    let q49 ← q r"!b. b IN m ==> ring_mul k ((h:A->B) b) z IN ring_carrier O"
    let q50 ← q r"(z:B) IN ring_carrier k"
    let q51 ← q r"(h:A->B) c IN ring_carrier k /\ ~(h c = ring_0 k)"
    let q52 ← q r"ring_ideal O (E:B->bool)"
    let q53 ← q r"E = ideal_generated O (IMAGE (h:A->B) j)"
    let q54 ← q r"z = ring_mul k x (ring_inv k ((h:A->B) c))"
    let q55 ← q r"c:A"
    let q56 ← q r"m:A->bool"
    let q57 ← q r"j:A->bool"
    let q58 ← q r"r:A ring"
    let v59 ← ISPECL [q58, q57] DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE
    let q60 ← q r"x:B = ring_0 k"
    let q61 ← q r"x:B"
    let q63 ← q r"j:A->bool"
    let q64 ← q r"ideal_generated r {a:A}"
    let q65 ← q r"r:A ring"
    let v66 ← ISPECL [q65, q64, q63] DEDEKIND_IDEAL_SUBSET_VALUATION
    let q67 ← q r"a:A = ring_0 r"
    let q68 ← q r"P:A->bool"
    let q69 ← q r"(a:A) IN ring_carrier r"
    let q70 ← q r"a:A"
    let q71 ← q r"(j:A->bool) SUBSET ring_carrier r"
    let q72 ← q r"ring_0 O = ring_0 k /\ ring_mul O = ring_mul k /\
                ring_add O = ring_add k /\ ring_neg O = ring_neg (k:B ring)"
    let q73 ← q r"IMAGE (h:A->B) (ring_carrier r) SUBSET ring_carrier O"
    let q74 ← q r"ring_carrier O =
    {x | x IN ring_carrier k /\
         !P. prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN S)
             ==> x = ring_0 k \/ &0 <= dedekind_valuation (r,k) (h:A->B) P x}"
    let q75 ← q r"O = ring_of_s_integers (r:A ring,k:B ring) h S"
    prove
      r"!r k (h:A->B) S j.
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          ring_ideal r j /\ ~(j = {ring_0 r})
          ==> ideal_generated (ring_of_s_integers (r,k) h S) (IMAGE h j) =
              {x | x IN ring_carrier k /\
                   !P. prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN S)
                       ==> x = ring_0 k \/
                           &(ideal_valuation r P j) <=
                           dedekind_valuation (r,k) h P x}"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN ABBREV_TAC q75 THEN SUBGOAL_THEN q74 ASSUME_TAC THENL [EXPAND_TAC "O" THEN ASM_SIMP_TAC [RING_OF_S_INTEGERS_CARRIER], ALL_TAC] THEN SUBGOAL_THEN q73 ASSUME_TAC THENL [EXPAND_TAC "O" THEN ASM_SIMP_TAC [RING_OF_S_INTEGERS_IMAGE], ALL_TAC] THEN SUBGOAL_THEN q72 STRIP_ASSUME_TAC THENL [EXPAND_TAC "O" THEN REWRITE_TAC [RING_OF_S_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN q71 ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN CONJ_TAC THENL [ALL_TAC, EXPAND_TAC "O" THEN MATCH_MP_TAC RING_OF_S_INTEGERS_VALUATION_IDEAL THEN ASM_REWRITE_TAC []] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN X_GEN_TAC q70 THEN DISCH_TAC THEN SUBGOAL_THEN q69 ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN X_GEN_TAC q68 THEN STRIP_TAC THEN ASM_CASES_TAC q67 THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_0], DISJ2_TAC] THEN ASM_SIMP_TAC [DEDEKIND_VALUATION_IMAGE, INT_OF_NUM_LE] THEN MP_TAC v66 THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN DISCH_THEN (fun z62 => tactic_of do pure (MP_TAC (← (do pure (Prod.fst (← (do pure (← EQ_IMP_RULE z62)))))))) THEN ANTS_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC q61 THEN STRIP_TAC THEN ASM_CASES_TAC q60 THENL [ASM_MESON_TAC [IN_RING_IDEAL_0, RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN MP_TAC v59 THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [q56, q55] THEN STRIP_TAC THEN ABBREV_TAC q54 THEN ABBREV_TAC q53 THEN SUBGOAL_THEN q52 ASSUME_TAC THENL [EXPAND_TAC "E" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN SUBGOAL_THEN q51 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_MONOMORPHISM_EQ_0], ALL_TAC] THEN SUBGOAL_THEN q50 ASSUME_TAC THENL [EXPAND_TAC "z" THEN ASM_SIMP_TAC [RING_MUL, RING_INV], ALL_TAC] THEN SUBGOAL_THEN q49 ASSUME_TAC THENL [X_GEN_TAC q48 THEN DISCH_TAC THEN SUBGOAL_THEN q47 ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN q46 ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [RING_MUL] THEN X_GEN_TAC q45 THEN STRIP_TAC THEN ASM_CASES_TAC q44 THENL [DISJ1_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 th)])) THEN ASM_SIMP_TAC [RING_MUL_LZERO], DISJ2_TAC] THEN SUBGOAL_THEN q43 ASSUME_TAC THENL [ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0], ALL_TAC] THEN SUBGOAL_THEN q42 ASSUME_TAC THENL [EXPAND_TAC "z" THEN ASM_SIMP_TAC [FIELD_MUL_EQ_0, RING_INV, FIELD_INV_EQ_0], ALL_TAC] THEN ASM_SIMP_TAC [DEDEKIND_VALUATION_MUL] THEN EXPAND_TAC "z" THEN ASM_SIMP_TAC [DEDEKIND_VALUATION_MUL, DEDEKIND_VALUATION_INV, RING_INV, FIELD_INV_EQ_0, DEDEKIND_VALUATION_IMAGE] THEN FIRST_X_ASSUM (MP_TAC o (SPEC q41)) THEN ASM_REWRITE_TAC [] THEN MP_TAC v40 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC v35 THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN DISCH_THEN (fun z31 => tactic_of do pure (MP_TAC (← (do pure (Prod.fst (← (do pure (← EQ_IMP_RULE z31)))))))) THEN ANTS_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], DISCH_THEN (MP_TAC o (SPEC q30)) THEN ASM_REWRITE_TAC []] THEN REWRITE_TAC [v29, v28] THEN INT_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q27 MP_TAC THENL [REWRITE_TAC [ideal_prod] THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN CONJ_TAC THENL [REWRITE_TAC [ring_setmul, SUBSET, FORALL_IN_GSPEC] THEN REWRITE_TAC [IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [q26, q25] THEN STRIP_TAC THEN SUBGOAL_THEN q24 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th)])) THEN SUBGOAL_THEN q23 SUBST1_TAC THENL [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r22 THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN FIRST_ASSUM (fun z19 => tactic_of do pure (MATCH_MP_TAC (← (do let z20 ← (do pure (CONJUNCTS (← GEN_REWRITE_RULE id [ring_ideal] z19))); liftExcept (last z20))))) THEN ASM_SIMP_TAC [] THEN EXPAND_TAC "E" THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN CONJ_TAC THENL [ASM SET_TAC [], ASM SET_TAC []], ALL_TAC] THEN REWRITE_TAC [ring_ideal, SUBSET, IN_ELIM_THM] THEN SIMP_TAC [RING_0, RING_NEG, RING_ADD, RING_MUL] THEN FIRST_ASSUM (fun th => tactic_of do pure (SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 th), (← MATCH_MP RING_HOMOMORPHISM_NEG th), (← MATCH_MP RING_HOMOMORPHISM_ADD th), (← MATCH_MP RING_HOMOMORPHISM_MUL th)])) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [ring_ideal])) THEN RULE_ASSUM_TAC (REWRITE_RULE [v18, v16, v14, v12]) THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [RING_MUL_LZERO], REPEAT STRIP_TAC THEN SUBGOAL_THEN q10 ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_LNEG], REPEAT STRIP_TAC THEN SUBGOAL_THEN q9 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN ASM_SIMP_TAC [RING_ADD_RDISTRIB], REPEAT STRIP_TAC THEN SUBGOAL_THEN q8 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN ASM_SIMP_TAC [v7] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC []], ALL_TAC] THEN ASM_REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN DISCH_THEN (MP_TAC o (SPEC q6)) THEN ASM_REWRITE_TAC [IN_IDEAL_GENERATED_SELF] THEN MATCH_MP_TAC r5 THEN EXPAND_TAC "z" THEN SUBGOAL_THEN q3 SUBST1_TAC THENL [MATCH_MP_TAC r2 THEN ASM_SIMP_TAC [RING_INV], ASM_SIMP_TAC [FIELD_MUL_RINV, RING_MUL_RID]])

  let RING_OF_S_INTEGERS_IDEAL_CONTRACTION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r2 ← SET_RULE (← q r"(x:A) IN s ==> s INTER {x} = {x}")
    prove
      r"!r k (h:A->B) S J.
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          ring_ideal (ring_of_s_integers (r,k) h S) J
          ==> ring_ideal r {a | a IN ring_carrier r /\ h a IN J} /\
              ({a | a IN ring_carrier r /\ h a IN J} = {ring_0 r} <=>
               J = {ring_0 k}) /\
              ideal_generated (ring_of_s_integers (r,k) h S)
                (IMAGE h {a | a IN ring_carrier r /\ h a IN J}) = J"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN ABBREV_TAC (← q r"O = ring_of_s_integers (r:A ring,k:B ring) h S") THEN SUBGOAL_THEN (← q r"ring_monomorphism(r,O) (h:A->B)") ASSUME_TAC THENL [EXPAND_TAC "O" THEN ASM_SIMP_TAC [RING_MONOMORPHISM_RING_OF_S_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_carrier O =
      {x | x IN ring_carrier k /\
           !P. prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN S)
               ==> x = ring_0 k \/ &0 <= dedekind_valuation (r,k) (h:A->B) P x}") ASSUME_TAC THENL [EXPAND_TAC "O" THEN ASM_SIMP_TAC [RING_OF_S_INTEGERS_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_0 O = ring_0 k /\ ring_mul O = ring_mul (k:B ring)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "O" THEN REWRITE_TAC [RING_OF_S_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y z. y IN ring_carrier O /\ z IN J ==> ring_mul k y z IN (J:B->bool)") ASSUME_TAC THENL [FIRST_ASSUM (fun z9 => tactic_of do pure (MP_TAC (← (do let z10 ← (do pure (CONJUNCTS (← GEN_REWRITE_RULE id [ring_ideal] (← (do let z11 ← (pure z9); checkM (fun th => (do let z14 ← (q r"ring_ideal O (J:B->bool)"); let z13 ← (do let z12 ← (pure th); pure (concl z12)); pure (z13 == z14))) z11))))); liftExcept (last z10))))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE (h:A->B) (ring_carrier r) SUBSET ring_carrier O") ASSUME_TAC THENL [EXPAND_TAC "O" THEN ASM_SIMP_TAC [RING_OF_S_INTEGERS_IMAGE], ALL_TAC] THEN ABBREV_TAC (← q r"j = {a | a IN ring_carrier r /\ (h:A->B) a IN J}") THEN SUBGOAL_THEN (← q r"ring_ideal r (j:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "j" THEN MATCH_MP_TAC RING_IDEAL_HOMOMORPHIC_PREIMAGE THEN EXISTS_TAC (← q r"O:B ring") THEN ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM], ASM_REWRITE_TAC []] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP RING_IDEAL_IMP_SUBSET) o (checkM (fun th => (do let z8 ← (q r"ring_ideal O (J:B->bool)"); let z7 ← (do let z6 ← (pure th); pure (concl z6)); pure (z7 == z8)))))) THEN SUBGOAL_THEN (← q r"(J:B->bool) SUBSET ring_carrier k") ASSUME_TAC THENL [UNDISCH_TAC (← q r"(J:B->bool) SUBSET ring_carrier O") THEN ASM_REWRITE_TAC [] THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(j = {ring_0 r:A}) <=> J = {ring_0 k:B}") ASSUME_TAC THENL [EQ_TAC THENL [DISCH_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:B") THEN REWRITE_TAC [IN_SING] THEN EQ_TAC THENL [DISCH_TAC THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier k") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:B")] FIELD_FRACTION_NONZERO) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") (X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC)) THEN UNDISCH_TAC (← q r"j = {ring_0 r:A}") THEN REWRITE_TAC [EXTENSION, IN_SING] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"a:A"))) THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "j" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC [], DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC [IN_RING_IDEAL_0]], DISCH_TAC THEN EXPAND_TAC "j" THEN REWRITE_TAC [(← ASSUME (← q r"J = {ring_0 k:B}")), IN_SING] THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, IN_SING] THEN X_GEN_TAC (← q r"a:A") THEN ASM_CASES_TAC (← q r"(a:A) IN ring_carrier r") THEN ASM_REWRITE_TAC [] THENL [MATCH_MP_TAC RING_MONOMORPHISM_EQ_0 THEN ASM_REWRITE_TAC [], ASM_MESON_TAC [RING_0]]], ASM_REWRITE_TAC []] THEN ASM_CASES_TAC (← q r"J = {ring_0 k:B}") THENL [SUBGOAL_THEN (← q r"j = {ring_0 r:A}") SUBST1_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"O:B ring"), (← q r"h:A->B"), (← q r"{ring_0 r:A}")] IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0) THEN ASM_REWRITE_TAC [RING_IDEAL_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(j = {ring_0 r:A})") ASSUME_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "j" THEN SET_TAC [], ALL_TAC] THEN EXPAND_TAC "O" THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"j:A->bool")] RING_OF_S_INTEGERS_IDEAL_EXTENSION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier O") MP_TAC THENL [ASM SET_TAC [], ASM_REWRITE_TAC [IN_ELIM_THM]] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"x:B")] DEDEKIND_VALUATION_POS) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(b:A = ring_0 r)") ASSUME_TAC THENL [ASM_MESON_TAC [IN_RING_IDEAL_0, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(a:A = ring_0 r)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ring_mul k ((h:A->B) b) x = h (ring_0 r)") THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 th)])) THEN SUBGOAL_THEN (← q r"(h:A->B) b IN ring_carrier k /\ ~(h b = ring_0 k)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_MONOMORPHISM_EQ_0], ASM_SIMP_TAC [FIELD_MUL_EQ_0]], ALL_TAC] THEN SUBGOAL_THEN (← q r"(a:A) IN j") ASSUME_TAC THENL [EXPAND_TAC "j" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun z3 => (do let z4 ← (do let z5 ← (pure z3); pure (concl z5)); pure (is_eq z4)))))) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_valuation r P (ideal_generated r {b:A}) = 0") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"ideal_generated r {b:A}")] IDEAL_VALUATION_EQ_0) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, IDEAL_GENERATED_MINIMAL_EQ, PRIME_IMP_RING_IDEAL, r2, SING_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"x:B"), (← q r"a:A"), (← q r"b:A")] DEDEKIND_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [INT_SUB_RZERO] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r {a:A}"), (← q r"j:A->bool")] DEDEKIND_IDEAL_SUBSET_VALUATION) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN DISCH_THEN (fun z1 => tactic_of do pure (MP_TAC (← (do pure (Prod.fst (← (do pure (← EQ_IMP_RULE z1)))))))) THEN ANTS_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], DISCH_THEN (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_REWRITE_TAC []] THEN REWRITE_TAC [(← GSYM INT_OF_NUM_LE)] THEN INT_ARITH_TAC)

  let RING_OF_S_INTEGERS_IDEAL_EXTENSION_EQ_CARRIER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(p ==> (q <=> r)) ==> (p ==> q <=> p ==> r)")
    let r2 ← TAUT (← q r"(q <=> r) ==> (p /\ q <=> p /\ r)")
    prove
      r"!r k (h:A->B) S j.
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          ring_ideal r j /\ ~(j = {ring_0 r})
          ==> (ideal_generated (ring_of_s_integers (r,k) h S) (IMAGE h j) =
               ring_carrier(ring_of_s_integers (r,k) h S) <=>
               !P. prime_ideal r P /\ ~(P = {ring_0 r}) /\ j SUBSET P
                   ==> P IN S)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN ASM_SIMP_TAC [RING_OF_S_INTEGERS_IDEAL_EXTENSION, RING_OF_S_INTEGERS_CARRIER] THEN EQ_TAC THENL [DISCH_TAC THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"(P:A->bool) IN S") THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o (AP_TERM (← q r"(IN) (ring_1 k:B)"))) THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [RING_1, DEDEKIND_VALUATION_1, INT_LE_REFL] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_SIMP_TAC [FIELD_NONTRIVIAL, INT_OF_NUM_LE, LE] THEN ASM_SIMP_TAC [IDEAL_VALUATION_EQ_0], DISCH_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:B") THEN REWRITE_TAC [IN_ELIM_THM] THEN MATCH_MP_TAC r2 THEN AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC r1 THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ideal_valuation r P (j:A->bool) = 0") (fun th => REWRITE_TAC [th]) THEN ASM_SIMP_TAC [IDEAL_VALUATION_EQ_0] THEN ASM_MESON_TAC []])

  let RING_OF_S_INTEGERS_IDEAL_EXTENSION_PRIME ← prove
    r"!r k (h:A->B) S P.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r})
        ==> ideal_generated (ring_of_s_integers (r,k) h S) (IMAGE h P) =
            if P IN S then ring_carrier(ring_of_s_integers (r,k) h S)
            else {x | x IN ring_carrier(ring_of_s_integers (r,k) h S) /\
                      (x = ring_0 k \/
                       &1 <= dedekind_valuation (r,k) h P x)}"
    (REPEAT STRIP_TAC THEN COND_CASES_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"P:A->bool")] RING_OF_S_INTEGERS_IDEAL_EXTENSION_EQ_CARRIER) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN X_GEN_TAC (← q r"Q:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"Q:A->bool"), (← q r"P:A->bool")] DEDEKIND_KRULL_DIMENSION_ONE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [RING_OF_S_INTEGERS_IDEAL_EXTENSION, PRIME_IMP_RING_IDEAL, RING_OF_S_INTEGERS_CARRIER] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:B") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"(x:B) IN ring_carrier k") THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [IDEAL_VALUATION_PRIME] THEN EQ_TAC THENL [DISCH_TAC THEN CONJ_TAC THENL [X_GEN_TAC (← q r"Q:A->bool") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"Q:A->bool"))) THEN ASM_REWRITE_TAC [] THEN COND_CASES_TAC THEN INT_ARITH_TAC, FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_REWRITE_TAC []], STRIP_TAC THEN X_GEN_TAC (← q r"Q:A->bool") THEN STRIP_TAC THEN COND_CASES_TAC THENL [FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC [], REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]])

  -- @@RETURN BEGIN
  return { ring_of_s_integers, RING_OF_S_INTEGERS, RING_OF_S_INTEGERS_SUBSET,
           RING_OF_S_INTEGERS_SUBRING_OF, RING_OF_S_INTEGERS_CARRIER,
           RING_OF_S_INTEGERS_SUBRING, INTEGRAL_DOMAIN_RING_OF_S_INTEGERS,
           RING_OF_S_INTEGERS_MONO, RING_OF_S_INTEGERS_IMAGE,
           RING_MONOMORPHISM_RING_OF_S_INTEGERS, FIELD_OF_FRACTIONS_RING_OF_S_INTEGERS,
           RING_OF_S_INTEGERS_EMPTY, RING_UNIT_RING_OF_S_INTEGERS,
           RING_OF_S_INTEGERS_COMPLEMENT_SING, RING_OF_S_INTEGERS_VALUATION_IDEAL,
           RING_OF_S_INTEGERS_IDEAL_EXTENSION, RING_OF_S_INTEGERS_IDEAL_CONTRACTION,
           RING_OF_S_INTEGERS_IDEAL_EXTENSION_EQ_CARRIER,
           RING_OF_S_INTEGERS_IDEAL_EXTENSION_PRIME }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- s_integers.ml phrases from line 771 to 1466                            -/
/- ---------------------------------------------------------------------- -/

structure SIntegers02 where
  -- @@FIELDS
  PRIME_IDEAL_RING_OF_S_INTEGERS_EXTENSION : thm
  DEDEKIND_RING_OF_S_INTEGERS : thm
  RING_OF_S_INTEGERS_PRIME_IDEALS : thm
  IDEAL_VALUATION_RING_OF_S_INTEGERS : thm
  DEDEKIND_VALUATION_RING_OF_S_INTEGERS : thm
  RING_OF_S_INTEGERS_EXTENSION_GENERATOR_VALUATION : thm
  RING_OF_S_INTEGERS_CLASS_GROUP : thm
  RING_OF_S_INTEGERS_CLASS_GROUP_QUOTIENT : thm
  RING_OF_S_INTEGERS_PID_EQ : thm
  RING_OF_S_INTEGERS_EXTENSION_PRINCIPAL : thm
  GROUP_HOMOMORPHISM_RING_OF_S_INTEGERS_VALUATIONS : thm
  GROUP_HOMOMORPHISM_CLASS_GROUP_SUM_PRIME_CLASSES : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupSIntegers02 [HolBase] (D : SIntegersDeps) (BSIntegers01 : SIntegers01) :
    ExceptT String IO SIntegers02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC, INT_ARITH,
        INT_ARITH_TAC, MESON_TAC, RING_RULE, SET_RULE, SET_TAC, .. } := D
  let { ABELIAN_CLASS_GROUP, ABELIAN_GROUP_SUM_MUL, CLASS_GROUP,
        DEDEKIND_CLASS_GROUP_EXTENSION, DEDEKIND_EQ_IDEALS_INVERTIBLE,
        DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE, DEDEKIND_IDEAL_SUBSET_POW_VALUATION,
        DEDEKIND_IN_IDEAL_POW_VALUATION, DEDEKIND_VALUATION, DEDEKIND_VALUATION_1,
        DEDEKIND_VALUATION_FINITE, DEDEKIND_VALUATION_IMAGE, DEDEKIND_VALUATION_INV,
        DEDEKIND_VALUATION_MUL, DEDEKIND_VALUATION_PRIME_IDEAL, EQ_TRANS, EXTENSION,
        FIELD_FRACTION_NONZERO, FIELD_INV_EQ_0, FIELD_MUL_EQ_0, FIELD_MUL_RINV,
        FIELD_NONTRIVIAL, FIELD_OF_FRACTIONS_IMP_MONOMORPHISM, FINITE_RESTRICT,
        FINITE_SUBSET, FINITE_UNION, FIRST_GROUP_EPIMORPHISM_THEOREM, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, GROUP_HOMOMORPHISM, GROUP_ID, GROUP_SUM, GROUP_SUM_EQ,
        GROUP_ZPOW, GROUP_ZPOW_ADD, IDEAL_CLASS_EQ_ID,
        IDEAL_CLASS_EQ_SUM_PRIME_CLASSES, IDEAL_CLASS_IN_CLASS_GROUP,
        IDEAL_GENERATED_0, IDEAL_GENERATED_EQ_0, IDEAL_GENERATED_IMAGE_IDEAL_GENERATED,
        IDEAL_GENERATED_INC, IDEAL_GENERATED_MINIMAL,
        IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0, IDEAL_POW_EQ_ZERO,
        IDEAL_POW_HOMOMORPHIC_IMAGE, IDEAL_PROD_HOMOMORPHIC_IMAGE,
        IDEAL_VALUATION_FINITE_SUPPORT, IDEAL_VALUATION_IDEAL_POW,
        IDEAL_VALUATION_PRIME, IDEAL_VALUATION_UNIQUE, IMAGE_CLAUSES, IMP_CONJ,
        INTEGER_GROUP, INT_LE_REFL, INT_OF_NUM_LE, INT_OF_NUM_SUC, INT_POS,
        IN_ELIM_THM, IN_IDEAL_GENERATED_SING_EQ, IN_IMAGE, IN_RING_IDEAL_0,
        IN_SUBGROUP_SUM, IN_SUBGROUP_ZPOW, IN_UNION, .. } := D.core1
  let { IN_UNIV, ISOMORPHIC_GROUP_SYM, I_THM, LEFT_IMP_EXISTS_THM, LE_REFL,
        MONO_EXISTS, MULT_CLAUSES, PRIME_IDEAL_HOMOMORPHIC_PREIMAGE,
        PRIME_IMP_PROPER_IDEAL, PRIME_IMP_RING_IDEAL, PRODUCT_GROUP, PSUBSET,
        PSUBSET_ALT, RESTRICTION, RESTRICTION_EXTENSION,
        RESTRICTION_IN_CARTESIAN_PRODUCT, RIGHT_FORALL_IMP_THM, RING_1,
        RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_IN_CARRIER, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET, RING_INV, RING_MONOMORPHISM_EQ_0,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_MUL_LZERO, SING_SUBSET,
        SUBGROUP_GENERATED_INC, SUBGROUP_GENERATED_MINIMAL, SUBGROUP_GROUP_KERNEL,
        SUBGROUP_SUBGROUP_GENERATED, SUBSET, SUBSET_ANTISYM, TRIVIAL_CLASS_GROUP,
        UNIT_GROUP, field_of_fractions, group_epimorphism, group_homomorphism,
        group_kernel, ideal_classes, prime_ideal, principal_ideal, proper_ideal,
        ring_divides, trivial_group, .. } := D.core2
  let { FIELD_OF_FRACTIONS_RING_OF_S_INTEGERS, INTEGRAL_DOMAIN_RING_OF_S_INTEGERS,
        RING_MONOMORPHISM_RING_OF_S_INTEGERS, RING_OF_S_INTEGERS,
        RING_OF_S_INTEGERS_CARRIER, RING_OF_S_INTEGERS_IDEAL_CONTRACTION,
        RING_OF_S_INTEGERS_IDEAL_EXTENSION, RING_OF_S_INTEGERS_IDEAL_EXTENSION_PRIME,
        RING_OF_S_INTEGERS_IMAGE, RING_OF_S_INTEGERS_SUBSET,
        RING_OF_S_INTEGERS_VALUATION_IDEAL, RING_UNIT_RING_OF_S_INTEGERS, .. } := BSIntegers01
  -- @@SCOPE END

  let PRIME_IDEAL_RING_OF_S_INTEGERS_EXTENSION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INT_ARITH (← q r"~(&1:int <= &0)")
    prove
      r"!r k (h:A->B) S P.
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN S)
          ==> prime_ideal (ring_of_s_integers (r,k) h S)
                (ideal_generated (ring_of_s_integers (r,k) h S) (IMAGE h P)) /\
              ~(ideal_generated (ring_of_s_integers (r,k) h S) (IMAGE h P) =
                {ring_0 k}) /\
              {a | a IN ring_carrier r /\
                   h a IN ideal_generated (ring_of_s_integers (r,k) h S)
                            (IMAGE h P)} = P"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN ABBREV_TAC (← q r"O = ring_of_s_integers (r:A ring,k:B ring) h S") THEN SUBGOAL_THEN (← q r"ring_monomorphism(r,O) (h:A->B)") ASSUME_TAC THENL [EXPAND_TAC "O" THEN ASM_SIMP_TAC [RING_MONOMORPHISM_RING_OF_S_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_0 O = ring_0 k /\ ring_1 O = ring_1 k /\
                  ring_mul O = ring_mul (k:B ring)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "O" THEN REWRITE_TAC [RING_OF_S_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN ring_carrier O
          ==> x IN ring_carrier k /\
              (x = ring_0 k \/ &0 <= dedekind_valuation (r,k) (h:A->B) P x)") (LABEL_TAC "carr") THENL [EXPAND_TAC "O" THEN ASM_SIMP_TAC [RING_OF_S_INTEGERS_CARRIER] THEN SIMP_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_generated O (IMAGE (h:A->B) P) =
      {x | x IN ring_carrier O /\
           (x = ring_0 k \/ &1 <= dedekind_valuation (r,k) h P x)}") ASSUME_TAC THENL [EXPAND_TAC "O" THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"P:A->bool")] RING_OF_S_INTEGERS_IDEAL_EXTENSION_PRIME) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [prime_ideal, proper_ideal, RING_IDEAL_IDEAL_GENERATED] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [REWRITE_TAC [PSUBSET_ALT] THEN CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN EXISTS_TAC (← q r"ring_1 k:B") THEN REWRITE_TAC [IN_ELIM_THM] THEN SUBGOAL_THEN (← q r"ring_1 k IN ring_carrier(O:B ring)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_1], ASM_REWRITE_TAC []] THEN ASM_SIMP_TAC [RING_1, FIELD_NONTRIVIAL, DEDEKIND_VALUATION_1, r1], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"x:B"), (← q r"y:B")] THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN ASM_REWRITE_TAC [] THEN USE_THEN "carr" (MP_TAC o (SPEC (← q r"x:B"))) THEN USE_THEN "carr" (MP_TAC o (SPEC (← q r"y:B"))) THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"y:B = ring_0 k") THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [IMP_CONJ] THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"&1 <= dedekind_valuation (r,k) (h:A->B) P (ring_mul k x y)") MP_TAC THENL [ASM_MESON_TAC [FIELD_MUL_EQ_0], ASM_SIMP_TAC [DEDEKIND_VALUATION_MUL] THEN ASM_INT_ARITH_TAC], MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"O:B ring"), (← q r"h:A->B"), (← q r"P:A->bool")] IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"a:A") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"(a:A) IN ring_carrier r") THENL [ALL_TAC, ASM_MESON_TAC [PRIME_IMP_RING_IDEAL, RING_IDEAL_IMP_SUBSET, SUBSET]] THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(h:A->B) a IN ring_carrier O") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] RING_OF_S_INTEGERS_IMAGE) THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC [], ASM_REWRITE_TAC []] THEN ASM_CASES_TAC (← q r"a:A = ring_0 r") THENL [ASM_REWRITE_TAC [] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_0 th)])) THEN ASM_MESON_TAC [IN_RING_IDEAL_0, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN ASM_SIMP_TAC [RING_MONOMORPHISM_EQ_0, DEDEKIND_VALUATION_PRIME_IDEAL] THEN INT_ARITH_TAC])

  let DEDEKIND_RING_OF_S_INTEGERS ← prove
    r"!r k (h:A->B) S.
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> dedekind_domain (ring_of_s_integers (r,k) h S)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN REWRITE_TAC [DEDEKIND_EQ_IDEALS_INVERTIBLE] THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_RING_OF_S_INTEGERS] THEN ABBREV_TAC (← q r"O = ring_of_s_integers (r:A ring,k:B ring) h S") THEN SUBGOAL_THEN (← q r"ring_monomorphism(r,O) (h:A->B)") ASSUME_TAC THENL [EXPAND_TAC "O" THEN ASM_SIMP_TAC [RING_MONOMORPHISM_RING_OF_S_INTEGERS], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) o (checkM (fun th => (do let z7 ← (q r"ring_monomorphism(r,O) (h:A->B)"); let z6 ← (do let z5 ← (pure th); pure (concl z5)); pure (z6 == z7)))))) THEN X_GEN_TAC (← q r"J:B->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"J:B->bool")] RING_OF_S_INTEGERS_IDEAL_CONTRACTION) THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_0 O = ring_0 (k:B ring)") SUBST_ALL_TAC THENL [EXPAND_TAC "O" THEN REWRITE_TAC [RING_OF_S_INTEGERS], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"j = {a | a IN ring_carrier r /\ (h:A->B) a IN J}") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"m:A->bool"), (← q r"c:A")] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"ideal_generated O (IMAGE (h:A->B) m)"), (← q r"(h:A->B) c")] THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN REPEAT CONJ_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0], FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z4 ← (q r"J:B->bool"); let z3 ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); liftExcept (rand z1)); pure (z3 == z4)))))) THEN ASM_SIMP_TAC [(← GSYM IDEAL_PROD_HOMOMORPHIC_IMAGE), RING_IDEAL_IMP_SUBSET] THEN ASM_SIMP_TAC [IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, SING_SUBSET] THEN REWRITE_TAC [IMAGE_CLAUSES]])

  let RING_OF_S_INTEGERS_PRIME_IDEALS ← prove
    r"!r k (h:A->B) S.
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> {Q | prime_ideal (ring_of_s_integers (r,k) h S) Q /\
                 ~(Q = {ring_0 k})} =
            IMAGE (\P. ideal_generated (ring_of_s_integers (r,k) h S)
                                       (IMAGE h P))
                  {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN S)} /\
            !P P'. prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN S) /\
                   prime_ideal r P' /\ ~(P' = {ring_0 r}) /\ ~(P' IN S) /\
                   ideal_generated (ring_of_s_integers (r,k) h S)
                     (IMAGE h P) =
                   ideal_generated (ring_of_s_integers (r,k) h S)
                     (IMAGE h P')
                   ==> P = P'"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC, REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"P':A->bool")] PRIME_IDEAL_RING_OF_S_INTEGERS_EXTENSION) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"P:A->bool")] PRIME_IDEAL_RING_OF_S_INTEGERS_EXTENSION) THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC []] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN ABBREV_TAC (← q r"O = ring_of_s_integers (r:A ring,k:B ring) h S") THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"Q:B->bool") THEN REWRITE_TAC [IN_ELIM_THM, IN_IMAGE] THEN EQ_TAC THENL [STRIP_TAC, DISCH_THEN (X_CHOOSE_THEN (← q r"P:A->bool") STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "O" THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"P:A->bool")] PRIME_IDEAL_RING_OF_S_INTEGERS_EXTENSION) THEN ASM_SIMP_TAC []] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"Q:B->bool")] RING_OF_S_INTEGERS_IDEAL_CONTRACTION) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN STRIP_TAC THEN EXISTS_TAC (← q r"{a | a IN ring_carrier r /\ (h:A->B) a IN Q}") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_monomorphism(r,O) (h:A->B)") ASSUME_TAC THENL [EXPAND_TAC "O" THEN ASM_SIMP_TAC [RING_MONOMORPHISM_RING_OF_S_INTEGERS], ALL_TAC] THEN CONJ_TAC THENL [MATCH_MP_TAC PRIME_IDEAL_HOMOMORPHIC_PREIMAGE THEN EXISTS_TAC (← q r"O:B ring") THEN ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"{a | a IN ring_carrier r /\ (h:A->B) a IN Q}")] RING_OF_S_INTEGERS_IDEAL_EXTENSION_PRIME) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC PRIME_IDEAL_HOMOMORPHIC_PREIMAGE THEN EXISTS_TAC (← q r"O:B ring") THEN ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM], ASM_REWRITE_TAC []] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP PRIME_IMP_PROPER_IDEAL)) THEN REWRITE_TAC [proper_ideal, PSUBSET] THEN MESON_TAC [])

  let IDEAL_VALUATION_RING_OF_S_INTEGERS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"~(SUC n <= n)")
    prove
      r"!r k (h:A->B) S P j.
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN S) /\
          ring_ideal r j /\ ~(j = {ring_0 r})
          ==> ideal_valuation (ring_of_s_integers (r,k) h S)
                (ideal_generated (ring_of_s_integers (r,k) h S) (IMAGE h P))
                (ideal_generated (ring_of_s_integers (r,k) h S) (IMAGE h j)) =
              ideal_valuation r P j"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN ABBREV_TAC (← q r"O = ring_of_s_integers (r:A ring,k:B ring) h S") THEN SUBGOAL_THEN (← q r"ring_monomorphism(r,O) (h:A->B)") ASSUME_TAC THENL [EXPAND_TAC "O" THEN ASM_SIMP_TAC [RING_MONOMORPHISM_RING_OF_S_INTEGERS], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) o (checkM (fun th => (do let z4 ← (q r"ring_monomorphism(r,O) (h:A->B)"); let z3 ← (do let z2 ← (pure th); pure (concl z2)); pure (z3 == z4)))))) THEN SUBGOAL_THEN (← q r"!m. ideal_generated O (IMAGE (h:A->B) j) SUBSET
          ideal_pow O (ideal_generated O (IMAGE h P)) m <=>
          m <= ideal_valuation r P j") ASSUME_TAC THENL [X_GEN_TAC (← q r"m:num") THEN ASM_SIMP_TAC [(← GSYM IDEAL_POW_HOMOMORPHIC_IMAGE), RING_IDEAL_IMP_SUBSET, PRIME_IMP_RING_IDEAL] THEN SUBGOAL_THEN (← q r"ring_ideal r (ideal_pow r P m) /\ ~(ideal_pow r P m = {ring_0 r:A})") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, IDEAL_POW_EQ_ZERO, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN EXPAND_TAC "O" THEN ASM_SIMP_TAC [RING_OF_S_INTEGERS_IDEAL_EXTENSION] THEN SUBGOAL_THEN (← q r"!Q:A->bool. prime_ideal r Q /\ ~(Q = {ring_0 r})
                    ==> ideal_valuation r Q (ideal_pow r P m) =
                        if P = Q then m else 0") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_POW, PRIME_IMP_RING_IDEAL, IDEAL_VALUATION_PRIME] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES], ASM_SIMP_TAC []] THEN EQ_TAC THENL [DISCH_TAC, DISCH_TAC THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:B") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"Q:A->bool") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"Q:A->bool"))) THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_REWRITE_TAC [] THEN COND_CASES_TAC THENL [FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN UNDISCH_TAC (← q r"m <= ideal_valuation r P (j:A->bool)") THEN REWRITE_TAC [(← GSYM INT_OF_NUM_LE)] THEN INT_ARITH_TAC, MP_TAC (← ISPEC (← q r"ideal_valuation r Q (j:A->bool)") INT_POS) THEN INT_ARITH_TAC]] THEN SUBGOAL_THEN (← q r"?c:A. c IN j /\ ~(c IN ideal_pow r P (SUC(ideal_valuation r P j)))") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"j:A->bool"), (← q r"SUC(ideal_valuation r P (j:A->bool))")] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN ASM_REWRITE_TAC [r1] THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(c:A) IN ring_carrier r /\ ~(c = ring_0 r)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(ring_0 r IN
              ideal_pow r P (SUC(ideal_valuation r P (j:A->bool))))") THEN REWRITE_TAC [] THEN MATCH_MP_TAC IN_RING_IDEAL_0 THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW]], ALL_TAC] THEN UNDISCH_TAC (← q r"~((c:A) IN ideal_pow r P (SUC(ideal_valuation r P j)))") THEN ASM_SIMP_TAC [DEDEKIND_IN_IDEAL_POW_VALUATION] THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"(h:A->B) c")) o (REWRITE_RULE [SUBSET]))) THEN ANTS_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"j:A->bool")] RING_OF_S_INTEGERS_IDEAL_EXTENSION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] RING_OF_S_INTEGERS_IMAGE) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] RING_IDEAL_IMP_SUBSET) THEN ASM SET_TAC [], ASM SET_TAC []], ALL_TAC] THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"P:A->bool")) o CONJUNCT2)) THEN ASM_SIMP_TAC [RING_MONOMORPHISM_EQ_0, DEDEKIND_VALUATION_IMAGE] THEN UNDISCH_TAC (← q r"~(SUC(ideal_valuation r P j) <=
          ideal_valuation r P (ideal_generated r {c:A}))") THEN REWRITE_TAC [(← GSYM INT_OF_NUM_LE), (← GSYM INT_OF_NUM_SUC)] THEN INT_ARITH_TAC, ALL_TAC] THEN MATCH_MP_TAC IDEAL_VALUATION_UNIQUE THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, LE_REFL] THEN ARITH_TAC)

  let DEDEKIND_VALUATION_RING_OF_S_INTEGERS ← prove
    r"!r k (h:A->B) S P x.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN S) /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> dedekind_valuation (ring_of_s_integers (r,k) h S,k) I
              (ideal_generated (ring_of_s_integers (r,k) h S) (IMAGE h P)) x =
            dedekind_valuation (r,k) h P x"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:B")] FIELD_FRACTION_NONZERO) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") (X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"x:B"), (← q r"a:A"), (← q r"b:A")] DEDEKIND_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ABBREV_TAC (← q r"O = ring_of_s_integers (r:A ring,k:B ring) h S") THEN SUBGOAL_THEN (← q r"ring_monomorphism(r,O) (h:A->B)") ASSUME_TAC THENL [EXPAND_TAC "O" THEN ASM_SIMP_TAC [RING_MONOMORPHISM_RING_OF_S_INTEGERS], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) o (checkM (fun th => (do let z3 ← (q r"ring_monomorphism(r,O) (h:A->B)"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3)))))) THEN SUBGOAL_THEN (← q r"!c. c IN ring_carrier r /\ ~(c = ring_0 r)
        ==> ideal_valuation O (ideal_generated O (IMAGE (h:A->B) P))
              (ideal_generated O {h c}) =
            ideal_valuation r P (ideal_generated r {c})") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"O:B ring"), (← q r"h:A->B"), (← q r"{c:A}")] IDEAL_GENERATED_IMAGE_IDEAL_GENERATED) THEN ASM_REWRITE_TAC [SING_SUBSET, IMAGE_CLAUSES] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN EXPAND_TAC "O" THEN MATCH_MP_TAC IDEAL_VALUATION_RING_OF_S_INTEGERS THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"(h:A->B) a IN ring_carrier O /\ h b IN ring_carrier O") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"~((h:A->B) a = ring_0 k) /\ ~(h b = ring_0 k)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"O:B ring"), (← q r"k:B ring"), (← q r"I:B->B"), (← q r"ideal_generated O (IMAGE (h:A->B) P)"), (← q r"x:B"), (← q r"(h:A->B) a"), (← q r"(h:A->B) b")] DEDEKIND_VALUATION) THEN SUBGOAL_THEN (← q r"ring_0 O = ring_0 (k:B ring)") SUBST1_TAC THENL [EXPAND_TAC "O" THEN REWRITE_TAC [RING_OF_S_INTEGERS], ALL_TAC] THEN ASM_SIMP_TAC [I_THM] THEN DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "O" THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_S_INTEGERS, PRIME_IDEAL_RING_OF_S_INTEGERS_EXTENSION] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] FIELD_OF_FRACTIONS_RING_OF_S_INTEGERS) THEN ASM_SIMP_TAC [field_of_fractions])

  let RING_OF_S_INTEGERS_EXTENSION_GENERATOR_VALUATION ← prove
    r"!r k (h:A->B) S j y.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        ring_ideal r j /\ ~(j = {ring_0 r}) /\
        y IN ring_carrier(ring_of_s_integers (r,k) h S) /\
        ideal_generated (ring_of_s_integers (r,k) h S) (IMAGE h j) =
        ideal_generated (ring_of_s_integers (r,k) h S) {y}
        ==> ~(y = ring_0 k) /\
            !P. prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN S)
                ==> dedekind_valuation (r,k) h P y =
                    &(ideal_valuation r P j)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN ABBREV_TAC (← q r"O = ring_of_s_integers (r:A ring,k:B ring) h S") THEN SUBGOAL_THEN (← q r"ring_monomorphism(r,O) (h:A->B)") ASSUME_TAC THENL [EXPAND_TAC "O" THEN ASM_SIMP_TAC [RING_MONOMORPHISM_RING_OF_S_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_0 O = ring_0 (k:B ring)") ASSUME_TAC THENL [EXPAND_TAC "O" THEN REWRITE_TAC [RING_OF_S_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(y:B = ring_0 k)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"O:B ring"), (← q r"h:A->B"), (← q r"j:A->bool")] IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPEC (← q r"O:B ring") IDEAL_GENERATED_0) THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC []] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier k") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] RING_OF_S_INTEGERS_SUBSET) THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"(y:B) IN ring_carrier O") THEN SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"P:A->bool"), (← q r"y:B")] DEDEKIND_VALUATION_RING_OF_S_INTEGERS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"P:A->bool"), (← q r"j:A->bool")] IDEAL_VALUATION_RING_OF_S_INTEGERS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"O:B ring"), (← q r"k:B ring"), (← q r"I:B->B"), (← q r"ideal_generated O (IMAGE (h:A->B) P)"), (← q r"y:B")] DEDEKIND_VALUATION_IMAGE) THEN ASM_REWRITE_TAC [I_THM] THEN DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "O" THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_S_INTEGERS, PRIME_IDEAL_RING_OF_S_INTEGERS_EXTENSION] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] FIELD_OF_FRACTIONS_RING_OF_S_INTEGERS) THEN ASM_SIMP_TAC [field_of_fractions])

  let RING_OF_S_INTEGERS_CLASS_GROUP ← prove
    r"!r k (h:A->B) S.
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> ?f. group_epimorphism(class_group r,
                                  class_group(ring_of_s_integers (r,k) h S))
                                 f /\
                (!j. ring_ideal r j /\ ~(j = {ring_0 r})
                     ==> f(ideal_class r j) =
                         ideal_class (ring_of_s_integers (r,k) h S)
                          (ideal_generated (ring_of_s_integers (r,k) h S)
                                           (IMAGE h j))) /\
                group_kernel (class_group r,
                              class_group(ring_of_s_integers (r,k) h S)) f =
                group_carrier
                 (subgroup_generated (class_group r)
                   {ideal_class r P | P |
                    P IN S /\ prime_ideal r P /\ ~(P = {ring_0 r})})"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN ABBREV_TAC (← q r"O = ring_of_s_integers (r:A ring,k:B ring) h S") THEN SUBGOAL_THEN (← q r"ring_monomorphism(r,O) (h:A->B)") ASSUME_TAC THENL [EXPAND_TAC "O" THEN ASM_SIMP_TAC [RING_MONOMORPHISM_RING_OF_S_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"dedekind_domain(O:B ring)") ASSUME_TAC THENL [EXPAND_TAC "O" THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_S_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_0 O = ring_0 (k:B ring)") ASSUME_TAC THENL [EXPAND_TAC "O" THEN REWRITE_TAC [RING_OF_S_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"O:B ring"), (← q r"h:A->B")] DEDEKIND_CLASS_GROUP_EXTENSION) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:((A->bool)->bool)->((B->bool)->bool)") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_REWRITE_TAC [group_epimorphism] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"group_homomorphism (class_group r,class_group O)
                     (f:((A->bool)->bool)->((B->bool)->bool))") THEN SIMP_TAC [group_homomorphism], ALL_TAC] THEN ASM_SIMP_TAC [CLASS_GROUP, ideal_classes, SUBSET, FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"J:B->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"J:B->bool")] RING_OF_S_INTEGERS_IDEAL_CONTRACTION) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"j = {a | a IN ring_carrier r /\ (h:A->B) a IN J}") THEN STRIP_TAC THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"ideal_class r (j:A->bool)") THEN ASM_SIMP_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"j:A->bool") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC SUBGROUP_GENERATED_MINIMAL THEN ASM_SIMP_TAC [SUBGROUP_GROUP_KERNEL] THEN REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, group_kernel, IN_ELIM_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_CLASS_IN_CLASS_GROUP, PRIME_IMP_RING_IDEAL] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"P:A->bool")] RING_OF_S_INTEGERS_IDEAL_EXTENSION_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [CLASS_GROUP]] THEN REWRITE_TAC [SUBSET, group_kernel] THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [(← CONJUNCT1 CLASS_GROUP)] THEN REWRITE_TAC [ideal_classes, IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"j:A->bool") THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"~(ideal_generated O (IMAGE (h:A->B) j) = {ring_0 k})") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"O:B ring"), (← q r"h:A->B"), (← q r"j:A->bool")] IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"principal_ideal O (ideal_generated O (IMAGE (h:A->B) j))") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"O:B ring"), (← q r"ideal_generated O (IMAGE (h:A->B) j)")] IDEAL_CLASS_EQ_ID) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z4 ← (q r"group_id(class_group O):(B->bool)->bool"); let z3 ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); liftExcept (rand z1)); pure (z3 == z4)))))) THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [principal_ideal] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"y:B") (STRIP_ASSUME_TAC o GSYM)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"j:A->bool"), (← q r"y:B")] RING_OF_S_INTEGERS_EXTENSION_GENERATOR_VALUATION) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier k") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] RING_OF_S_INTEGERS_SUBSET) THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"(y:B) IN ring_carrier O") THEN SET_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"t = {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
             ~(dedekind_valuation (r,k) (h:A->B) P y =
               &(ideal_valuation r P j))}") THEN SUBGOAL_THEN (← q r"FINITE(t:(A->bool)->bool)") ASSUME_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
           ~(dedekind_valuation (r,k) (h:A->B) P y = &0)} UNION
      {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
           ~(ideal_valuation r P (j:A->bool) = 0)}") THEN ASM_SIMP_TAC [FINITE_UNION, DEDEKIND_VALUATION_FINITE, IDEAL_VALUATION_FINITE_SUPPORT] THEN EXPAND_TAC "t" THEN REWRITE_TAC [SUBSET, IN_UNION, IN_ELIM_THM] THEN GEN_TAC THEN ASM_CASES_TAC (← q r"ideal_valuation r x (j:A->bool) = 0") THEN ASM_REWRITE_TAC [] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(t:(A->bool)->bool) SUBSET S") ASSUME_TAC THENL [EXPAND_TAC "t" THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"t:(A->bool)->bool"), (← q r"j:A->bool"), (← q r"y:B")] IDEAL_CLASS_EQ_SUM_PRIME_CLASSES) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN EXPAND_TAC "t" THEN SIMP_TAC [IN_ELIM_THM] THEN MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC IN_SUBGROUP_SUM THEN REWRITE_TAC [SUBGROUP_SUBGROUP_GENERATED] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN MATCH_MP_TAC IN_SUBGROUP_ZPOW THEN REWRITE_TAC [SUBGROUP_SUBGROUP_GENERATED] THEN MATCH_MP_TAC SUBGROUP_GENERATED_INC THEN SUBGOAL_THEN (← q r"prime_ideal r P /\ ~(P = {ring_0 r:A}) /\ P IN S") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"(P:A->bool) IN t") THEN EXPAND_TAC "t" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM SET_TAC [], ALL_TAC] THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN ASM_SIMP_TAC [IDEAL_CLASS_IN_CLASS_GROUP, PRIME_IMP_RING_IDEAL], REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"P:A->bool") THEN ASM_REWRITE_TAC []])

  let RING_OF_S_INTEGERS_CLASS_GROUP_QUOTIENT ← prove
    r"!r k (h:A->B) S.
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> class_group(ring_of_s_integers (r,k) h S) isomorphic_group
            quotient_group (class_group r)
              (group_carrier
                (subgroup_generated (class_group r)
                  {ideal_class r P | P |
                   P IN S /\ prime_ideal r P /\ ~(P = {ring_0 r})}))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] RING_OF_S_INTEGERS_CLASS_GROUP) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"f:((A->bool)->bool)->((B->bool)->bool)") THEN STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ONCE_REWRITE_TAC [ISOMORPHIC_GROUP_SYM] THEN MATCH_MP_TAC FIRST_GROUP_EPIMORPHISM_THEOREM THEN ASM_REWRITE_TAC [])

  let RING_OF_S_INTEGERS_PID_EQ ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!f s (z:B). (?x:A. x IN s)
                ==> (IMAGE f s = {z} <=> {x | x IN s /\ f x = z} = s)")
    prove
      r"!r k (h:A->B) S.
          dedekind_domain r /\ field_of_fractions (r,k) h
          ==> (PID(ring_of_s_integers (r,k) h S) <=>
               group_carrier
                (subgroup_generated (class_group r)
                  {ideal_class r P | P |
                   P IN S /\ prime_ideal r P /\ ~(P = {ring_0 r})}) =
               group_carrier(class_group r))"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] RING_OF_S_INTEGERS_CLASS_GROUP) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"f:((A->bool)->bool)->((B->bool)->bool)") THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (fun (_ : thm) => ALL_TAC) (SUBST1_TAC o SYM))) THEN REWRITE_TAC [group_epimorphism] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] DEDEKIND_RING_OF_S_INTEGERS) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_SIMP_TAC [(← GSYM TRIVIAL_CLASS_GROUP), trivial_group] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC [group_kernel] THEN MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"group_id(class_group(r:A ring))") THEN REWRITE_TAC [GROUP_ID])

  let RING_OF_S_INTEGERS_EXTENSION_PRINCIPAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"!k:B ring x y w. x IN ring_carrier k /\ y IN ring_carrier k /\
                      w IN ring_carrier k /\ ring_mul k y w = ring_1 k
                      ==> x = ring_mul k y (ring_mul k x w)")
    prove
      r"!r k (h:A->B) S j.
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          ring_ideal r j /\ ~(j = {ring_0 r})
          ==> (principal_ideal (ring_of_s_integers (r,k) h S)
                 (ideal_generated (ring_of_s_integers (r,k) h S) (IMAGE h j)) <=>
               ?y. y IN ring_carrier k /\ ~(y = ring_0 k) /\
                   !P. prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN S)
                       ==> dedekind_valuation (r,k) h P y =
                           &(ideal_valuation r P j))"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN EQ_TAC THENL [REWRITE_TAC [principal_ideal] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"y:B") (STRIP_ASSUME_TAC o GSYM)) THEN EXISTS_TAC (← q r"y:B") THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"j:A->bool"), (← q r"y:B")] RING_OF_S_INTEGERS_EXTENSION_GENERATOR_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] RING_OF_S_INTEGERS_SUBSET) THEN UNDISCH_TAC (← q r"(y:B) IN ring_carrier(ring_of_s_integers (r,k) (h:A->B) S)") THEN SET_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"y:B") STRIP_ASSUME_TAC) THEN REWRITE_TAC [principal_ideal] THEN EXISTS_TAC (← q r"y:B") THEN ABBREV_TAC (← q r"O = ring_of_s_integers (r:A ring,k:B ring) h S") THEN SUBGOAL_THEN (← q r"ring_carrier O =
      {x | x IN ring_carrier k /\
           !P. prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN S)
               ==> x = ring_0 k \/ &0 <= dedekind_valuation (r,k) (h:A->B) P x}") ASSUME_TAC THENL [EXPAND_TAC "O" THEN ASM_SIMP_TAC [RING_OF_S_INTEGERS_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul O = ring_mul (k:B ring)") ASSUME_TAC THENL [EXPAND_TAC "O" THEN REWRITE_TAC [RING_OF_S_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier O") ASSUME_TAC THENL [ASM_REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [INT_POS], ASM_REWRITE_TAC []] THEN EXPAND_TAC "O" THEN ASM_SIMP_TAC [RING_OF_S_INTEGERS_IDEAL_EXTENSION] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN CONJ_TAC THENL [ASM_REWRITE_TAC [SING_SUBSET, IN_ELIM_THM] THEN ASM_SIMP_TAC [INT_LE_REFL], MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"\P. ideal_valuation r P (j:A->bool)")] RING_OF_S_INTEGERS_VALUATION_IDEAL) THEN ASM_REWRITE_TAC []], ALL_TAC] THEN ASM_REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:B") THEN STRIP_TAC THEN ASM_SIMP_TAC [IN_IDEAL_GENERATED_SING_EQ, ring_divides] THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"P:A->bool")) o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); canM (fun z4 => (do let z5 ← (pure z4); find_termM (fun z6 => (do let z8 ← (pure z6); let z7 ← (q r"x:B"); pure (z7 == z8))) z5)) z2) then (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); pure (is_forall z9)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPEC (← q r"ideal_valuation r P (j:A->bool)") INT_POS) THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_REWRITE_TAC [] THEN INT_ARITH_TAC, ALL_TAC] THEN EXISTS_TAC (← q r"ring_mul k x (ring_inv k y):B") THEN ASM_SIMP_TAC [RING_MUL, RING_INV] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_SIMP_TAC [RING_MUL_LZERO, RING_INV] THEN DISJ2_TAC THEN ASM_SIMP_TAC [DEDEKIND_VALUATION_MUL, DEDEKIND_VALUATION_INV, RING_INV, FIELD_INV_EQ_0] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_REWRITE_TAC [] THEN INT_ARITH_TAC, MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_INV, FIELD_MUL_RINV]])

  let GROUP_HOMOMORPHISM_RING_OF_S_INTEGERS_VALUATIONS ← prove
    r"!r k (h:A->B) S.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        (!P. P IN S ==> prime_ideal r P /\ ~(P = {ring_0 r}))
        ==> group_homomorphism
             (unit_group(ring_of_s_integers (r,k) h S),
              product_group S (\P. integer_group))
             (\x. RESTRICTION S (\P. dedekind_valuation (r,k) h P x))"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [GROUP_HOMOMORPHISM, SUBSET, FORALL_IN_IMAGE, PRODUCT_GROUP, RESTRICTION_IN_CARTESIAN_PRODUCT, INTEGER_GROUP, IN_UNIV] THEN REWRITE_TAC [UNIT_GROUP, IN_ELIM_THM, RESTRICTION_EXTENSION] THEN ASM_SIMP_TAC [RING_UNIT_RING_OF_S_INTEGERS, RESTRICTION, RING_OF_S_INTEGERS, FIELD_MUL_EQ_0] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC DEDEKIND_VALUATION_MUL THEN ASM_SIMP_TAC [])

  let GROUP_HOMOMORPHISM_CLASS_GROUP_SUM_PRIME_CLASSES ← prove
    r"!r:A ring S.
        dedekind_domain r /\ FINITE S /\
        (!P. P IN S ==> prime_ideal r P /\ ~(P = {ring_0 r}))
        ==> group_homomorphism
             (product_group S (\P. integer_group),class_group r)
             (\n. group_sum (class_group r) S
                    (\P. group_zpow (class_group r) (ideal_class r P) (n P)))"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [GROUP_HOMOMORPHISM, SUBSET, FORALL_IN_IMAGE, GROUP_SUM] THEN REWRITE_TAC [PRODUCT_GROUP, INTEGER_GROUP] THEN MAP_EVERY X_GEN_TAC [(← q r"m:(A->bool)->int"), (← q r"n:(A->bool)->int")] THEN DISCH_TAC THEN TRANS_TAC EQ_TRANS (← q r"group_sum (class_group r) S
     (\P:A->bool. group_mul (class_group r)
            (group_zpow (class_group r) (ideal_class r P) (m P))
            (group_zpow (class_group r) (ideal_class r P) (n P)))") THEN CONJ_TAC THENL [MATCH_MP_TAC GROUP_SUM_EQ THEN X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN ASM_REWRITE_TAC [RESTRICTION] THEN MATCH_MP_TAC GROUP_ZPOW_ADD THEN ASM_SIMP_TAC [IDEAL_CLASS_IN_CLASS_GROUP, PRIME_IMP_RING_IDEAL], MATCH_MP_TAC ABELIAN_GROUP_SUM_MUL THEN ASM_SIMP_TAC [ABELIAN_CLASS_GROUP, FINITE_RESTRICT] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_ZPOW THEN ASM_SIMP_TAC [IDEAL_CLASS_IN_CLASS_GROUP, PRIME_IMP_RING_IDEAL]])

  -- @@RETURN BEGIN
  return { PRIME_IDEAL_RING_OF_S_INTEGERS_EXTENSION, DEDEKIND_RING_OF_S_INTEGERS,
           RING_OF_S_INTEGERS_PRIME_IDEALS, IDEAL_VALUATION_RING_OF_S_INTEGERS,
           DEDEKIND_VALUATION_RING_OF_S_INTEGERS,
           RING_OF_S_INTEGERS_EXTENSION_GENERATOR_VALUATION,
           RING_OF_S_INTEGERS_CLASS_GROUP, RING_OF_S_INTEGERS_CLASS_GROUP_QUOTIENT,
           RING_OF_S_INTEGERS_PID_EQ, RING_OF_S_INTEGERS_EXTENSION_PRINCIPAL,
           GROUP_HOMOMORPHISM_RING_OF_S_INTEGERS_VALUATIONS,
           GROUP_HOMOMORPHISM_CLASS_GROUP_SUM_PRIME_CLASSES }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- s_integers.ml phrases from line 1493 to 1809                           -/
/- ---------------------------------------------------------------------- -/

structure SIntegers03 where
  -- @@FIELDS
  RING_OF_S_INTEGERS_CLASS_GROUP_EXACT : thm
  RING_OF_S_INTEGERS_CLASS_NUMBER_DIVIDES : thm
  RING_OF_S_INTEGERS_PID : thm
  NUMBER_FIELD_RING_OF_S_INTEGERS_EMPTY : thm
  NUMBER_FIELD_CLASS_GROUP_RING_OF_S_INTEGERS : thm
  NUMBER_FIELD_RING_OF_S_INTEGERS_PID : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupSIntegers03 [HolBase] (D : SIntegersDeps) (BSIntegers01 : SIntegers01) (BSIntegers02 : SIntegers02) :
    ExceptT String IO SIntegers03 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_RULE, .. } := D
  let { CARD_DIVIDES_GROUP_EPIMORPHIC_IMAGE, CLASS_GROUP,
        CLASS_GROUP_SUM_PRIME_CLASSES_EQ_ID, DEDEKIND_VALUATION_UNIT, EQ_TRANS,
        EXISTS_IN_IMAGE, EXTENSION, EXTENSIONAL, FIELD_OF_FRACTIONS_IMP_MONOMORPHISM,
        FINITE_IMAGE, FINITE_SUBSET, FINITE_UNIONS, FORALL_IN_GSPEC, FORALL_IN_IMAGE,
        FORALL_IN_UNIONS, FUN_EQ_THM, GROUP_HOMOMORPHISM_UNIT_GROUP, GROUP_ID,
        GROUP_SUM_EQ, IDEAL_CLASS_EQ_ID, IDEAL_CLASS_EQ_SUM_PRIME_CLASSES,
        IDEAL_CLASS_IN_CLASS_GROUP, IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0,
        IDEAL_VALUATION_EQ_0, IDEAL_VALUATION_FINITE_SUPPORT, IMAGE_I, IMP_CONJ,
        INTEGER_GROUP, IN_ELIM_THM, IN_IMAGE, IN_SUBGROUP_SUM, IN_SUBGROUP_ZPOW, .. } := D.core1
  let { IN_UNIONS, IN_UNIV, LEFT_IMP_EXISTS_THM, MONO_EXISTS,
        NUMBER_FIELD_CLASS_GROUP_FINITE, PRIME_IMP_RING_IDEAL, PRODUCT_GROUP,
        RESTRICTION, RESTRICTION_EXTENSION, RESTRICTION_IN_CARTESIAN_PRODUCT,
        RIGHT_EXISTS_IMP_THM, RIGHT_FORALL_IMP_THM, RING_HOMOMORPHISM_IN_CARRIER,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_INJECTIVE_EQ,
        RING_OF_INTEGERS, RING_OF_INTEGERS_FRACTION_FIELD, RING_OF_INTEGERS_SUBRING,
        RING_UNIT_IN_CARRIER, SKOLEM_THM, SUBGROUP_GENERATED_INC,
        SUBGROUP_SUBGROUP_GENERATED, SUBSET, SUBSET_ANTISYM, TRIVIAL_CLASS_GROUP,
        UNIT_GROUP, cartesian_product, class_number, group_epimorphism,
        group_exactness, group_image, group_kernel, group_monomorphism, ideal_classes,
        trivial_group, .. } := D.core2
  let { RING_MONOMORPHISM_RING_OF_S_INTEGERS, RING_OF_S_INTEGERS,
        RING_OF_S_INTEGERS_EMPTY, RING_OF_S_INTEGERS_IDEAL_EXTENSION_EQ_CARRIER,
        RING_OF_S_INTEGERS_SUBRING, RING_UNIT_RING_OF_S_INTEGERS, .. } := BSIntegers01
  let { DEDEKIND_RING_OF_S_INTEGERS, GROUP_HOMOMORPHISM_CLASS_GROUP_SUM_PRIME_CLASSES,
        GROUP_HOMOMORPHISM_RING_OF_S_INTEGERS_VALUATIONS,
        RING_OF_S_INTEGERS_CLASS_GROUP, RING_OF_S_INTEGERS_EXTENSION_PRINCIPAL, .. } := BSIntegers02
  -- @@SCOPE END

  let RING_OF_S_INTEGERS_CLASS_GROUP_EXACT ← prove
    r"!r k (h:A->B) S.
        dedekind_domain r /\ field_of_fractions (r,k) h /\ FINITE S /\
        (!P. P IN S ==> prime_ideal r P /\ ~(P = {ring_0 r}))
        ==> ?f. group_monomorphism
                 (unit_group r,unit_group(ring_of_s_integers (r,k) h S)) h /\
                group_exactness
                 (unit_group r,unit_group(ring_of_s_integers (r,k) h S),
                  product_group S (\P. integer_group))
                 (h,(\x. RESTRICTION S (\P. dedekind_valuation (r,k) h P x))) /\
                group_exactness
                 (unit_group(ring_of_s_integers (r,k) h S),
                  product_group S (\P. integer_group),class_group r)
                 ((\x. RESTRICTION S (\P. dedekind_valuation (r,k) h P x)),
                  (\n. group_sum (class_group r) S
                         (\P. group_zpow (class_group r) (ideal_class r P)
                                (n P)))) /\
                group_exactness
                 (product_group S (\P. integer_group),class_group r,
                  class_group(ring_of_s_integers (r,k) h S))
                 ((\n. group_sum (class_group r) S
                         (\P. group_zpow (class_group r) (ideal_class r P)
                                (n P))),f) /\
                group_epimorphism
                 (class_group r,class_group(ring_of_s_integers (r,k) h S)) f /\
                !j. ring_ideal r j /\ ~(j = {ring_0 r})
                    ==> f(ideal_class r j) =
                        ideal_class (ring_of_s_integers (r,k) h S)
                          (ideal_generated (ring_of_s_integers (r,k) h S)
                                           (IMAGE h j))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] RING_OF_S_INTEGERS_CLASS_GROUP) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:((A->bool)->bool)->((B->bool)->bool)") THEN STRIP_TAC THEN ASM_REWRITE_TAC [group_exactness] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] GROUP_HOMOMORPHISM_RING_OF_S_INTEGERS_VALUATIONS) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"S:(A->bool)->bool")] GROUP_HOMOMORPHISM_CLASS_GROUP_SUM_PRIME_CLASSES) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] RING_MONOMORPHISM_RING_OF_S_INTEGERS) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"O = ring_of_s_integers (r:A ring,k:B ring) h S") THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"group_homomorphism (class_group r,class_group O)
      (f:((A->bool)->bool)->((B->bool)->bool))") ASSUME_TAC THENL [UNDISCH_TAC (← q r"group_epimorphism (class_group r,class_group O)
                   (f:((A->bool)->bool)->((B->bool)->bool))") THEN SIMP_TAC [group_epimorphism], ALL_TAC] THEN SUBGOAL_THEN (← q r"group_homomorphism (unit_group r,unit_group O) (h:A->B)") ASSUME_TAC THENL [MATCH_MP_TAC GROUP_HOMOMORPHISM_UNIT_GROUP THEN ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM], ASM_REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"!x. ring_unit O x <=>
        x IN ring_carrier k /\ ~(x = ring_0 k) /\
        !P. prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN S)
            ==> dedekind_valuation (r,k) (h:A->B) P x = &0") ASSUME_TAC THENL [EXPAND_TAC "O" THEN ASM_SIMP_TAC [RING_UNIT_RING_OF_S_INTEGERS], ALL_TAC] THEN REPEAT CONJ_TAC THENL [ASM_REWRITE_TAC [group_monomorphism, UNIT_GROUP, IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"a:A"), (← q r"b:A")] RING_MONOMORPHISM_INJECTIVE_EQ) THEN ASM_SIMP_TAC [RING_UNIT_IN_CARRIER], REWRITE_TAC [group_image, group_kernel, UNIT_GROUP, PRODUCT_GROUP, INTEGER_GROUP, RESTRICTION_EXTENSION] THEN ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:B") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"(x:B) IN ring_carrier k") THENL [ASM_SIMP_TAC [DEDEKIND_VALUATION_UNIT], ASM_REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_UNIT_IN_CARRIER, RING_HOMOMORPHISM_IN_CARRIER]] THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_REWRITE_TAC [] THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THENL [CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [], X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"(P:A->bool) IN S") THEN ASM_SIMP_TAC []], REWRITE_TAC [group_image, group_kernel, UNIT_GROUP, PRODUCT_GROUP, INTEGER_GROUP] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"n:(A->bool)->int") THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"x:B") (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN REWRITE_TAC [RESTRICTION_IN_CARTESIAN_PRODUCT, IN_UNIV] THEN TRANS_TAC EQ_TRANS (← q r"group_sum (class_group r) S
         (\P. group_zpow (class_group r) (ideal_class r P)
                (dedekind_valuation (r,k) (h:A->B) P x))") THEN CONJ_TAC THENL [MATCH_MP_TAC GROUP_SUM_EQ THEN SIMP_TAC [RESTRICTION], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"\P. dedekind_valuation (r,k) (h:A->B) P x")] CLASS_GROUP_SUM_PRIME_CLASSES_EQ_ID) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN EXISTS_TAC (← q r"x:B") THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [], STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"n:(A->bool)->int")] CLASS_GROUP_SUM_PRIME_CLASSES_EQ_ID) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"x:B") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"x:B") THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"(n:(A->bool)->int) IN cartesian_product S (\P. (:int))") THEN REWRITE_TAC [cartesian_product, EXTENSIONAL, IN_ELIM_THM] THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN REWRITE_TAC [FUN_EQ_THM, RESTRICTION] THEN X_GEN_TAC (← q r"P:A->bool") THEN COND_CASES_TAC THEN ASM_SIMP_TAC [], X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC []]], MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [REWRITE_TAC [group_image, SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"n:(A->bool)->int") THEN DISCH_TAC THEN MATCH_MP_TAC IN_SUBGROUP_SUM THEN REWRITE_TAC [SUBGROUP_SUBGROUP_GENERATED] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN MATCH_MP_TAC IN_SUBGROUP_ZPOW THEN REWRITE_TAC [SUBGROUP_SUBGROUP_GENERATED] THEN MATCH_MP_TAC SUBGROUP_GENERATED_INC THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_GSPEC] THEN ASM_SIMP_TAC [IDEAL_CLASS_IN_CLASS_GROUP, PRIME_IMP_RING_IDEAL], REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC (← q r"P:A->bool") THEN ASM_SIMP_TAC []], ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); pure (is_eq z5)) then (do let l ← (do pure (Prod.fst (← (do let z7 ← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); liftExcept (lhand z8)); pure (strip_comb z7))))); (do if ← (do let z10 ← (pure l); pure (is_const z10)) then (do let z13 ← (pure "group_kernel"); let z12 ← (do pure (Prod.fst (← (do let z11 ← (pure l); liftExcept (dest_const z11))))); pure (z12 == z13)) else pure false)) else pure false))))) THEN REWRITE_TAC [SUBSET, group_kernel] THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [(← CONJUNCT1 CLASS_GROUP)] THEN REWRITE_TAC [ideal_classes, IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"j:A->bool") THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"~(ideal_generated O (IMAGE (h:A->B) j) = {ring_0 k})") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"O:B ring"), (← q r"h:A->B"), (← q r"j:A->bool")] IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0) THEN SUBGOAL_THEN (← q r"ring_0 O = ring_0 (k:B ring)") SUBST1_TAC THENL [EXPAND_TAC "O" THEN REWRITE_TAC [RING_OF_S_INTEGERS], ALL_TAC] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"principal_ideal O (ideal_generated O (IMAGE (h:A->B) j))") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"O:B ring"), (← q r"ideal_generated O (IMAGE (h:A->B) j)")] IDEAL_CLASS_EQ_ID) THEN SUBGOAL_THEN (← q r"ring_0 O = ring_0 (k:B ring)") SUBST1_TAC THENL [EXPAND_TAC "O" THEN REWRITE_TAC [RING_OF_S_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"dedekind_domain (O:B ring)") ASSUME_TAC THENL [EXPAND_TAC "O" THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_S_INTEGERS], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z4 ← (q r"group_id(class_group O):(B->bool)->bool"); let z3 ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); liftExcept (rand z1)); pure (z3 == z4)))))) THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN EXPAND_TAC "O" THEN ASM_SIMP_TAC [RING_OF_S_INTEGERS_EXTENSION_PRINCIPAL] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"y:B") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool"), (← q r"j:A->bool"), (← q r"y:B")] IDEAL_CLASS_EQ_SUM_PRIME_CLASSES) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [group_image, IN_IMAGE, PRODUCT_GROUP] THEN EXISTS_TAC (← q r"RESTRICTION S (\P. &(ideal_valuation r P (j:A->bool)) -
                          dedekind_valuation (r,k) (h:A->B) P y)") THEN REWRITE_TAC [RESTRICTION_IN_CARTESIAN_PRODUCT, INTEGER_GROUP, IN_UNIV] THEN MATCH_MP_TAC GROUP_SUM_EQ THEN SIMP_TAC [RESTRICTION]])

  let RING_OF_S_INTEGERS_CLASS_NUMBER_DIVIDES ← prove
    r"!r k (h:A->B) S.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        FINITE(ideal_classes r)
        ==> FINITE(ideal_classes(ring_of_s_integers (r,k) h S)) /\
            class_number(ring_of_s_integers (r,k) h S) divides
            class_number r"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] RING_OF_S_INTEGERS_CLASS_GROUP) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] DEDEKIND_RING_OF_S_INTEGERS) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN DISCH_THEN (X_CHOOSE_THEN (← q r"f:((A->bool)->bool)->((B->bool)->bool)") (MP_TAC o CONJUNCT1)) THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← MATCH_MP (← REWRITE_RULE [IMP_CONJ] CARD_DIVIDES_GROUP_EPIMORPHIC_IMAGE) th) THEN MP_TAC (← CONJUNCT2 (← GEN_REWRITE_RULE id [group_epimorphism] th)))) THEN ASM_SIMP_TAC [CLASS_GROUP, class_number] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [FINITE_IMAGE])

  let RING_OF_S_INTEGERS_PID ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r4 ← SET_RULE (← q r"!f s (z:B). (!x:A. x IN s ==> f x = z) /\ (?x. x IN s)
                ==> IMAGE f s = {z}")
    prove
      r"!r k (h:A->B).
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          FINITE(ideal_classes r)
          ==> ?S0. FINITE S0 /\
                   (!P. P IN S0 ==> prime_ideal r P /\ ~(P = {ring_0 r})) /\
                   !S. S0 SUBSET S ==> PID(ring_of_s_integers (r,k) h S)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN SUBGOAL_THEN (← q r"?J. !c. c IN ideal_classes r
              ==> ring_ideal r (J c) /\ ~(J c = {ring_0 r}) /\
                  c = ideal_class r (J c:A->bool)") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← GSYM SKOLEM_THM), RIGHT_EXISTS_IMP_THM] THEN REWRITE_TAC [ideal_classes, IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN EXISTS_TAC (← q r"UNIONS (IMAGE (\c. {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                              (J:((A->bool)->bool)->A->bool) c SUBSET P})
                    (ideal_classes r))") THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [FINITE_UNIONS] THEN ASM_SIMP_TAC [FINITE_IMAGE] THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"c:(A->bool)->bool") THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                       ~(ideal_valuation r P
                          ((J:((A->bool)->bool)->A->bool) c) = 0)}") THEN ASM_SIMP_TAC [IDEAL_VALUATION_FINITE_SUPPORT] THEN GEN_REWRITE_TAC id [SUBSET] THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [IDEAL_VALUATION_EQ_0], REWRITE_TAC [FORALL_IN_UNIONS, IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE, IN_ELIM_THM] THEN SIMP_TAC [], X_GEN_TAC (← q r"S:(A->bool)->bool") THEN DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] DEDEKIND_RING_OF_S_INTEGERS) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_SIMP_TAC [(← GSYM TRIVIAL_CLASS_GROUP), trivial_group] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"S:(A->bool)->bool")] RING_OF_S_INTEGERS_CLASS_GROUP) THEN ASM_REWRITE_TAC [group_epimorphism, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"f:((A->bool)->bool)->((B->bool)->bool)") THEN DISCH_THEN (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) (CONJUNCTS_THEN2 ASSUME_TAC (fun (_ : thm) => ALL_TAC))) THEN MATCH_MP_TAC r4 THEN CONJ_TAC THENL [ALL_TAC, EXISTS_TAC (← q r"group_id(class_group(r:A ring))") THEN REWRITE_TAC [GROUP_ID]] THEN ASM_SIMP_TAC [(← CONJUNCT1 CLASS_GROUP)] THEN X_GEN_TAC (← q r"c:(A->bool)->bool") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"c:(A->bool)->bool"))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_eq z2))))) THEN ASM_SIMP_TAC [] THEN SUBGOAL_THEN (← q r"ideal_generated (ring_of_s_integers (r,k) h S)
        (IMAGE (h:A->B) ((J:((A->bool)->bool)->A->bool) c)) =
      ring_carrier(ring_of_s_integers (r,k) h S)") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_OF_S_INTEGERS_IDEAL_EXTENSION_EQ_CARRIER] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o (GEN_REWRITE_RULE id [SUBSET])) THEN REWRITE_TAC [IN_UNIONS, EXISTS_IN_IMAGE, IN_ELIM_THM] THEN EXISTS_TAC (← q r"c:(A->bool)->bool") THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [CLASS_GROUP]])

  let NUMBER_FIELD_RING_OF_S_INTEGERS_EMPTY ← prove
    r"!k:A ring.
        number_field k
        ==> ring_of_s_integers (ring_of_integers k,k) I {} =
            ring_of_integers k"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"{}:(A->bool)->bool")] RING_OF_S_INTEGERS_SUBRING) THEN ASM_SIMP_TAC [RING_OF_S_INTEGERS_EMPTY, IMAGE_I] THEN DISCH_THEN (SUBST1_TAC o (SYM o CONJUNCT2)) THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING])

  let NUMBER_FIELD_CLASS_GROUP_RING_OF_S_INTEGERS ← prove
    r"!k:A ring S.
        number_field k
        ==> FINITE(group_carrier(class_group
                    (ring_of_s_integers (ring_of_integers k,k) I S))) /\
            class_number(ring_of_s_integers (ring_of_integers k,k) I S)
            divides class_number(ring_of_integers k)"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"S:(A->bool)->bool")] RING_OF_S_INTEGERS_CLASS_NUMBER_DIVIDES) THEN ASM_SIMP_TAC [NUMBER_FIELD_CLASS_GROUP_FINITE, CLASS_GROUP, DEDEKIND_RING_OF_S_INTEGERS])

  let NUMBER_FIELD_RING_OF_S_INTEGERS_PID ← prove
    r"!k:A ring.
        number_field k
        ==> ?S0. FINITE S0 /\
                 (!P. P IN S0
                      ==> prime_ideal (ring_of_integers k) P /\
                          ~(P = {ring_0 k})) /\
                 !S. S0 SUBSET S
                     ==> PID(ring_of_s_integers (ring_of_integers k,k) I S)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_FRACTION_FIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"k:A ring"), (← q r"I:A->A")] RING_OF_S_INTEGERS_PID) THEN ASM_SIMP_TAC [NUMBER_FIELD_CLASS_GROUP_FINITE, RING_OF_INTEGERS])

  -- @@RETURN BEGIN
  return { RING_OF_S_INTEGERS_CLASS_GROUP_EXACT, RING_OF_S_INTEGERS_CLASS_NUMBER_DIVIDES,
           RING_OF_S_INTEGERS_PID, NUMBER_FIELD_RING_OF_S_INTEGERS_EMPTY,
           NUMBER_FIELD_CLASS_GROUP_RING_OF_S_INTEGERS,
           NUMBER_FIELD_RING_OF_S_INTEGERS_PID }
  -- @@RETURN END

end HolANT.SIntegers
