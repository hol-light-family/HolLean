/- ========================================================================= -/
/- ANT: Fractional ideals of a domain r in a field of fractions k ...      -/
/- ========================================================================= -/
/- File: HolANT/FractionalIdeals.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/fractional_ideals.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antfractionalidealsdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/ring_groups.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, Library/isum.ml, ANT/ideal_norm.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/classgroup_group.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.FractionalIdeals fills them).

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
import HolLibrary.RingGroups
import HolANT.IdealArith
import HolLibrary.Products
import HolANT.Algmisc
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

namespace HolANT.FractionalIdeals

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ABELIAN_CLASS_GROUP ABELIAN_INTEGER_GROUP CLASS_GROUP CLASS_GROUP_MUL
   DEDEKIND_IDEAL_INVERTIBLE DEDEKIND_IDEAL_SUBSET_VALUATION
   DEDEKIND_IMP_INTEGRAL_DOMAIN DEDEKIND_VALUATION DEDEKIND_VALUATION_UNIT
   DEST_FRAG_ADD EQ_SYM_EQ EQ_TRANS EXTENSION FIELD_FRACTION_NONZERO
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_INV_EQ_0 FIELD_MUL_LINV FIELD_MUL_RINV
   FIELD_OF_FRACTIONS_IMP_MONOMORPHISM FIELD_UNIT FIELD_UNIT_GROUP
   FINITE_FRAG_SUPPORT FINITE_NUMSEG_LT FINITE_SUBSET FINITE_UNION
   FIRST_GROUP_EPIMORPHISM_THEOREM FORALL_IN_GSPEC FORALL_IN_IMAGE FRAG_EQ
   FREE_ABELIAN_GROUP FUN_EQ_THM FUN_IN_IMAGE GROUP_DIV GROUP_EPIMORPHISM
   GROUP_HOMOMORPHISM GROUP_HOMOMORPHISM_DIV GROUP_HOMOMORPHISM_UNIT_GROUP
   GROUP_HOMOMORPHISM_ZPOW GROUP_INV_ID GROUP_ISOMORPHISM GROUP_MUL_RID
   GROUP_SUM GROUP_SUM_CLAUSES_EXISTS GROUP_SUM_EQ GROUP_SUM_HOMOMORPHIC_IMAGE
   GROUP_SUM_SING GROUP_SUM_SUPERSET GROUP_ZPOW GROUP_ZPOW_INTEGER_GROUP
   IDEAL_CLASS_EQ IDEAL_CLASS_EQ_ID IDEAL_CLASS_IN_CLASS_GROUP IDEAL_GENERATED_0
   IDEAL_GENERATED_EQ_0 IDEAL_GENERATED_SING_EQ_CARRIER IDEAL_OF_VALUATIONS
   IDEAL_PROD_EQ_ZERO IDEAL_PROD_EXPLICIT IDEAL_PROD_SCALE
   IDEAL_VALUATION_CARRIER IDEAL_VALUATION_FINITE_SUPPORT
   IDEAL_VALUATION_IDEAL_PROD IDEAL_VALUATION_PRIME
   IDEAL_VALUATION_PRINCIPAL_MUL IMAGE_CLAUSES IMAGE_HOMOMORPHISM_MUL
   IMAGE_SUBSET IMAGE_o IMP_CONJ IMP_IMP INTEGER_GROUP INTEGRAL_DOMAIN_MUL_EQ_0
   INTEGRAL_DOMAIN_MUL_LCANCEL INTEGRAL_DOMAIN_NONTRIVIAL INTER_SUBSET
   INT_ADD_LID INT_LE_REFL INT_MUL_RID INT_MUL_RZERO INT_OF_NUM_ADD
   INT_OF_NUM_EQ INT_OF_NUM_LE INT_OF_NUM_OF_INT INT_SUB_RZERO IN_DIFF
   IN_ELIM_THM IN_IDEAL_CLASS IN_IMAGE IN_INTER IN_RING_IDEAL_0
   IN_RING_IDEAL_ADD IN_RING_IDEAL_LMUL IN_SING IN_SUBRING_0 IN_SUBRING_ADD
   IN_SUBRING_MUL : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (IN_UNION IN_UNIV ISOMORPHIC_GROUP_SYM LEFT_IMP_EXISTS_THM MONO_EXISTS
   NOT_FORALL_THM PRIME_IMP_PROPER_IDEAL PRIME_IMP_RING_IDEAL
   PRINCIPAL_IDEAL_IDEAL_GENERATED_SING PROPER_IDEAL_ALT RIGHT_EXISTS_IMP_THM
   RIGHT_FORALL_IMP_THM RING_0 RING_1 RING_ADD RING_ADD_LDISTRIB
   RING_ADD_RDISTRIB RING_HOMOMORPHISM_1 RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_NEG RING_HOMOMORPHISM_SUM RING_IDEAL
   RING_IDEAL_CARRIER RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_PROD
   RING_IDEAL_IMP_SUBSET RING_INV RING_MONOMORPHISM_EQ_0
   RING_MONOMORPHISM_INJECTIVE_EQ RING_MUL RING_MUL_ASSOC RING_MUL_IN_IDEAL_PROD
   RING_MUL_LID RING_MUL_LNEG RING_MUL_LZERO RING_MUL_RID RING_MUL_RZERO
   RING_MUL_SYM RING_NEG RING_SETMUL RING_SETMUL_IMAGE_MUL RING_SETMUL_SING
   RING_SPAN_0 RING_SPAN_ADD RING_SPAN_EQ_SELF RING_SPAN_IMAGE_IDEAL_GENERATED
   RING_SPAN_IMAGE_MUL RING_SPAN_INC RING_SPAN_MINIMAL RING_SPAN_MONO
   RING_SPAN_MUL RING_SPAN_SETMUL_ASSOC RING_SPAN_SETMUL_SPAN
   RING_SPAN_SETMUL_SYM RING_SPAN_SING_IMAGE RING_SPAN_SUBSET RING_SPAN_SUM
   RING_SUM_EQ RING_SUM_RMUL RING_UNIT_1 RING_UNIT_IN_CARRIER SELECT_UNIQUE
   SING_SUBSET SKOLEM_THM SUBRING_RING_IMAGE SUBSET SUBSET_ANTISYM
   SUBSET_ANTISYM_EQ SUBSET_UNIV UNIT_GROUP abelian_group frag_support
   frag_tybij group_carrier group_div group_epimorphism group_exactness group_id
   group_image group_inv group_kernel group_monomorphism group_mul group_tybij
   ideal_classes isomorphic_group o_DEF o_THM principal_ideal ring_divides
   ring_homomorphism ring_image ring_setmul ring_sub : thm)
  deriving Inhabited

/-- What fractional_ideals.ml uses from Session besides theorems. -/
structure FractionalIdealsDeps where
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
/- fractional_ideals.ml phrases from line 87 to 823                       -/
/- ---------------------------------------------------------------------- -/

structure FractionalIdeals01 where
  -- @@FIELDS
  fractional_ideal : thm
  fractional_ideal_inv : thm
  FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS : thm
  FRACTIONAL_IDEAL_IMP_SUBSET : thm
  FRACTIONAL_IDEAL_IMP_NONZERO : thm
  IN_FRACTIONAL_IDEAL_0 : thm
  IN_FRACTIONAL_IDEAL_ADD : thm
  IN_FRACTIONAL_IDEAL_LMUL : thm
  IN_FRACTIONAL_IDEAL_NEG : thm
  IN_FRACTIONAL_IDEAL_SUB : thm
  FRACTIONAL_IDEAL_RING_SPAN : thm
  RING_IDEAL_IMP_FRACTIONAL_IDEAL : thm
  FRACTIONAL_IDEAL_CARRIER : thm
  FRACTIONAL_IDEAL_IMAGE_MUL : thm
  FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV : thm
  FRACTIONAL_IDEAL_DENOMINATOR : thm
  RING_SPAN_SETMUL_IMAGE_IDEAL_PROD : thm
  FRACTIONAL_IDEAL_INTEGRAL : thm
  FRACTIONAL_IDEAL_SCALED_IDEAL : thm
  FRACTIONAL_IDEAL_SCALED_IDEAL_EQ : thm
  FRACTIONAL_IDEAL_MUL : thm
  FRACTIONAL_IDEAL_MUL_LID : thm
  DEDEKIND_FRACTIONAL_IDEAL_INVERTIBLE : thm
  DEDEKIND_FRACTIONAL_IDEAL_MUL_INV : thm
  fractional_ideal_group : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFractionalIdeals01 [HolBase] (D : FractionalIdealsDeps) :
    ExceptT String IO FractionalIdeals01 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, RING_RULE, SET_RULE, SET_TAC, TAUT, new_definition, .. } := D
  let { DEDEKIND_IDEAL_INVERTIBLE, EQ_TRANS, EXTENSION, FIELD_FRACTION_NONZERO,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_INV_EQ_0, FIELD_MUL_LINV, FIELD_MUL_RINV,
        FIELD_OF_FRACTIONS_IMP_MONOMORPHISM, FINITE_NUMSEG_LT, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, FUN_IN_IMAGE, IDEAL_PROD_EXPLICIT, IMAGE_SUBSET, IMAGE_o,
        IMP_CONJ, IMP_IMP, INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_NONTRIVIAL,
        IN_ELIM_THM, IN_IMAGE, IN_RING_IDEAL_0, IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL,
        IN_SING, IN_SUBRING_0, IN_SUBRING_ADD, IN_SUBRING_MUL, .. } := D.core1
  let { LEFT_IMP_EXISTS_THM, NOT_FORALL_THM, RIGHT_EXISTS_IMP_THM,
        RIGHT_FORALL_IMP_THM, RING_0, RING_1, RING_ADD, RING_ADD_LDISTRIB,
        RING_ADD_RDISTRIB, RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_NEG, RING_HOMOMORPHISM_SUM,
        RING_IDEAL, RING_IDEAL_CARRIER, RING_IDEAL_IDEAL_PROD, RING_IDEAL_IMP_SUBSET,
        RING_INV, RING_MONOMORPHISM_EQ_0, RING_MUL, RING_MUL_ASSOC,
        RING_MUL_IN_IDEAL_PROD, RING_MUL_LID, RING_MUL_LNEG, RING_MUL_LZERO,
        RING_MUL_RID, RING_MUL_RZERO, RING_MUL_SYM, RING_NEG, RING_SPAN_0,
        RING_SPAN_ADD, RING_SPAN_EQ_SELF, RING_SPAN_INC, RING_SPAN_MINIMAL,
        RING_SPAN_MONO, RING_SPAN_MUL, RING_SPAN_SUBSET, RING_SPAN_SUM, RING_SUM_EQ,
        RING_SUM_RMUL, SKOLEM_THM, SUBRING_RING_IMAGE, SUBSET, SUBSET_ANTISYM, o_DEF,
        ring_divides, ring_homomorphism, ring_image, ring_setmul, ring_sub, .. } := D.core2
  -- @@SCOPE END

  let fractional_ideal ← new_definition
    r"fractional_ideal (r:A ring,k:B ring) (h:A->B) (J:B->bool) <=>
        field_of_fractions (r,k) h /\
        J SUBSET ring_carrier k /\ ~(J = {ring_0 k}) /\ ring_0 k IN J /\
        (!x y. x IN J /\ y IN J ==> ring_add k x y IN J) /\
        (!a x. a IN ring_carrier r /\ x IN J ==> ring_mul k (h a) x IN J) /\
        ?d. d IN ring_carrier r /\ ~(d = ring_0 r) /\
            !x. x IN J ==> ring_mul k (h d) x IN IMAGE h (ring_carrier r)"

  let fractional_ideal_inv ← new_definition
    r"fractional_ideal_inv (r:A ring,k:B ring) (h:A->B) (J:B->bool) =
        {x | x IN ring_carrier k /\
             !y. y IN J ==> ring_mul k x y IN IMAGE h (ring_carrier r)}"

  let FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS ← prove
    r"!r k (h:A->B) J.
        fractional_ideal (r,k) h J ==> field_of_fractions (r,k) h"
    (SIMP_TAC [fractional_ideal])

  let FRACTIONAL_IDEAL_IMP_SUBSET ← prove
    r"!r k (h:A->B) J. fractional_ideal (r,k) h J ==> J SUBSET ring_carrier k"
    (SIMP_TAC [fractional_ideal])

  let FRACTIONAL_IDEAL_IMP_NONZERO ← prove
    r"!r k (h:A->B) J.
        fractional_ideal (r,k) h J ==> ?x. x IN J /\ ~(x = ring_0 k)"
    (REWRITE_TAC [fractional_ideal] THEN SET_TAC [])

  let IN_FRACTIONAL_IDEAL_0 ← prove
    r"!r k (h:A->B) J. fractional_ideal (r,k) h J ==> ring_0 k IN J"
    (SIMP_TAC [fractional_ideal])

  let IN_FRACTIONAL_IDEAL_ADD ← prove
    r"!r k (h:A->B) J x y.
        fractional_ideal (r,k) h J /\ x IN J /\ y IN J
        ==> ring_add k x y IN J"
    (SIMP_TAC [fractional_ideal])

  let IN_FRACTIONAL_IDEAL_LMUL ← prove
    r"!r k (h:A->B) J a x.
        fractional_ideal (r,k) h J /\ a IN ring_carrier r /\ x IN J
        ==> ring_mul k (h a) x IN J"
    (SIMP_TAC [fractional_ideal])

  let IN_FRACTIONAL_IDEAL_NEG ← prove
    r"!r k (h:A->B) J x.
        fractional_ideal (r,k) h J /\ x IN J ==> ring_neg k x IN J"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM) o (MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS))) THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [FRACTIONAL_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"J:B->bool"), (← q r"ring_neg r (ring_1 r):A"), (← q r"x:B")] IN_FRACTIONAL_IDEAL_LMUL) THEN ASM_SIMP_TAC [RING_NEG, RING_1] THEN FIRST_ASSUM (fun th => tactic_of do pure (SIMP_TAC [RING_1, (← MATCH_MP RING_HOMOMORPHISM_NEG th), (← MATCH_MP RING_HOMOMORPHISM_1 th)])) THEN ASM_SIMP_TAC [RING_MUL_LNEG, RING_MUL_LID, RING_1])

  let IN_FRACTIONAL_IDEAL_SUB ← prove
    r"!r k (h:A->B) J x y.
        fractional_ideal (r,k) h J /\ x IN J /\ y IN J
        ==> ring_sub k x y IN J"
    (REWRITE_TAC [ring_sub] THEN MESON_TAC [IN_FRACTIONAL_IDEAL_ADD, IN_FRACTIONAL_IDEAL_NEG])

  let FRACTIONAL_IDEAL_RING_SPAN ← prove
    r"!r k (h:A->B) J.
        fractional_ideal (r,k) h J ==> ring_span (r,k) h J = J"
    (REWRITE_TAC [fractional_ideal] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_SPAN_EQ_SELF THEN ASM_REWRITE_TAC [])

  let RING_IDEAL_IMP_FRACTIONAL_IDEAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r4 ← SET_RULE (← q r"!x:B. x IN s /\ ~(x = z) ==> ~(s = {z})")
    let r5 ← SET_RULE (← q r"(z:A) IN s /\ ~(s = {z}) ==> ?a. a IN s /\ ~(a = z)")
    prove
      r"!r k (h:A->B) j.
          field_of_fractions (r,k) h /\ ring_ideal r j /\ ~(j = {ring_0 r})
          ==> fractional_ideal (r,k) h (IMAGE h j)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_IDEAL_IMP_SUBSET)) THEN SUBGOAL_THEN (← q r"?a:A. a IN j /\ ~(a = ring_0 r)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [IN_RING_IDEAL_0, r5], ALL_TAC] THEN SUBGOAL_THEN (← q r"~((h:A->B) a = ring_0 k)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0, SUBSET], ALL_TAC] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [SUBSET, FORALL_IN_IMAGE]) o (GEN_REWRITE_RULE id [ring_homomorphism]))) THEN ASM_REWRITE_TAC [fractional_ideal] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN REPEAT CONJ_TAC THENL [ASM SET_TAC [], MATCH_MP_TAC r4 THEN EXISTS_TAC (← q r"(h:A->B) a") THEN ASM_SIMP_TAC [FUN_IN_IMAGE], FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z3 ← (q r"(h:A->B)(ring_0 r) = ring_0 k"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3)))))) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC [IN_RING_IDEAL_0], X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_add k ((h:A->B) x) (h y) = h(ring_add r x y)") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC [], MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC [IN_RING_IDEAL_ADD]], X_GEN_TAC (← q r"c:A") THEN DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_mul k ((h:A->B) c) (h x) = h(ring_mul r c x)") SUBST1_TAC THENL [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC [], MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC [IN_RING_IDEAL_LMUL]], EXISTS_TAC (← q r"ring_1 r:A") THEN ASM_SIMP_TAC [RING_1, INTEGRAL_DOMAIN_NONTRIVIAL] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier r") ASSUME_TAC THENL [ASM SET_TAC [], ASM_SIMP_TAC [RING_MUL_LID, FUN_IN_IMAGE]]])

  let FRACTIONAL_IDEAL_CARRIER ← prove
    r"!r k (h:A->B).
        fractional_ideal (r,k) h (IMAGE h (ring_carrier r)) <=>
        field_of_fractions (r,k) h"
    (REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC [FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS], DISCH_TAC] THEN MATCH_MP_TAC RING_IDEAL_IMP_FRACTIONAL_IDEAL THEN ASM_REWRITE_TAC [RING_IDEAL_CARRIER] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN ASM_MESON_TAC [INTEGRAL_DOMAIN_NONTRIVIAL, RING_1, RING_0, IN_SING])

  let FRACTIONAL_IDEAL_IMAGE_MUL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul r (ring_mul r b d) (ring_mul r x y) =
    ring_mul r (ring_mul r b x) (ring_mul r d (y:B))")
    let r10 ← RING_RULE (← q r"ring_mul r a (ring_mul r b c) = ring_mul r b (ring_mul r a (c:B))")
    let r11 ← SET_RULE (← q r"!x:B. x IN s /\ ~(x = z) ==> ~(s = {z})")
    prove
      r"!r k (h:A->B) J x.
          fractional_ideal (r,k) h J /\ x IN ring_carrier k /\ ~(x = ring_0 k)
          ==> fractional_ideal (r,k) h (IMAGE (ring_mul k x) J)"
      (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN REWRITE_TAC [fractional_ideal] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"d:A") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "den"))))))))) THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN (← q r"!y:B. y IN J ==> y IN ring_carrier k") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!c:A. c IN ring_carrier r ==> (h:A->B) c IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [RING_MUL], SUBGOAL_THEN (← q r"?y:B. y IN J /\ ~(y = ring_0 k)") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MATCH_MP_TAC r11 THEN EXISTS_TAC (← q r"ring_mul k x y:B") THEN ASM_SIMP_TAC [FUN_IN_IMAGE, INTEGRAL_DOMAIN_MUL_EQ_0], SUBGOAL_THEN (← q r"ring_0 k:B = ring_mul k x (ring_0 k)") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_MUL_RZERO], ASM_SIMP_TAC [FUN_IN_IMAGE]], X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN X_GEN_TAC (← q r"z:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_add k (ring_mul k x y) (ring_mul k x z) =
        ring_mul k x (ring_add k y (z:B))") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_ADD_LDISTRIB], ASM_SIMP_TAC [FUN_IN_IMAGE]], X_GEN_TAC (← q r"c:A") THEN DISCH_TAC THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_mul k ((h:A->B) c) (ring_mul k x y) =
        ring_mul k x (ring_mul k (h c) y)") SUBST1_TAC THENL [ASM_SIMP_TAC [r10], ASM_SIMP_TAC [FUN_IN_IMAGE]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:B")] FIELD_FRACTION_NONZERO) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN EXISTS_TAC (← q r"ring_mul r b d:A") THEN ASM_SIMP_TAC [RING_MUL, INTEGRAL_DOMAIN_MUL_EQ_0] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN USE_THEN "den" (MP_TAC o (SPEC (← q r"y:B"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], REWRITE_TAC [IN_IMAGE]] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:A") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"ring_mul r a c:A") THEN ASM_SIMP_TAC [RING_MUL] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th)])) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z9 ← (q r"(h:A->B) a"); let z8 ← (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); liftExcept (rand z6)); pure (z8 == z9)))))) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z5 ← (q r"(h:A->B) c"); let z4 ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); liftExcept (rand z2)); pure (z4 == z5)))))) THEN ASM_SIMP_TAC [r1])

  let FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul r (ring_mul r a b) c = ring_mul r a (ring_mul r c (b:B))")
    prove
      r"!r k (h:A->B) J.
          fractional_ideal (r,k) h J
          ==> fractional_ideal (r,k) h (fractional_ideal_inv (r,k) h J)"
      (REPEAT GEN_TAC THEN REWRITE_TAC [fractional_ideal, fractional_ideal_inv] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"d:A") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "den"))))))))) THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN (← q r"!y:B. y IN J ==> y IN ring_carrier k") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE (h:A->B) (ring_carrier r) subring_of k") ASSUME_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [ring_image] SUBRING_RING_IMAGE) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [SUBSET, FORALL_IN_IMAGE]) o (GEN_REWRITE_RULE id [ring_homomorphism]))) THEN REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_SING] THEN REPEAT CONJ_TAC THENL [SIMP_TAC [], REWRITE_TAC [EXTENSION, IN_SING, IN_ELIM_THM, NOT_FORALL_THM] THEN EXISTS_TAC (← q r"(h:A->B) d") THEN ASM_SIMP_TAC [] THEN ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0], REWRITE_TAC [RING_0], ASM_SIMP_TAC [RING_MUL_LZERO, IN_SUBRING_0], REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_ADD, RING_ADD_RDISTRIB, IN_SUBRING_ADD], REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_MUL, (← GSYM RING_MUL_ASSOC)] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [FUN_IN_IMAGE], ALL_TAC] THEN SUBGOAL_THEN (← q r"?y0:B. y0 IN J /\ ~(y0 = ring_0 k)") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"?u:A. u IN ring_carrier r /\ (h:A->B) u = ring_mul k (h d) y0") STRIP_ASSUME_TAC THENL [USE_THEN "den" (MP_TAC o (SPEC (← q r"y0:B"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], REWRITE_TAC [IN_IMAGE]] THEN MESON_TAC [], ALL_TAC] THEN EXISTS_TAC (← q r"u:A") THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"(h:A->B)(ring_0 r) = ring_mul k (h d) y0") THEN DISCH_THEN (MP_TAC o SYM) THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0] THEN ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0], X_GEN_TAC (← q r"x:B") THEN STRIP_TAC THEN ASM_SIMP_TAC [r1] THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [FUN_IN_IMAGE]])

  let FRACTIONAL_IDEAL_DENOMINATOR ← prove
    r"!r k (h:A->B) J.
        fractional_ideal (r,k) h J
        ==> ?d. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                !x. x IN J ==> ring_mul k (h d) x IN IMAGE h (ring_carrier r)"
    (SIMP_TAC [fractional_ideal])

  let RING_SPAN_SETMUL_IMAGE_IDEAL_PROD ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(s:B->bool) SUBSET t ==> u INTER s SUBSET t")
    prove
      r"!(h:A->B) r k i j.
          ring_homomorphism(r,k) h /\ ring_ideal r i /\ ring_ideal r j
          ==> ring_span (r,k) h (ring_setmul k (IMAGE h i) (IMAGE h j)) =
              IMAGE h (ideal_prod r i j)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [SUBSET, FORALL_IN_IMAGE]) o (GEN_REWRITE_RULE id [ring_homomorphism]))) THEN MAP_EVERY (fun t => tactic_of do pure (FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP RING_IDEAL_IMP_SUBSET) o (checkM (fun th => (do let z7 ← (pure t); let z6 ← (do let z5 ← (pure th); pure (concl z5)); pure (z6 == z7)))))))) [(← q r"ring_ideal r (i:A->bool)"), (← q r"ring_ideal r (j:A->bool)")] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SPAN_MINIMAL THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z4 ← (q r"(h:A->B)(ring_0 r) = ring_0 k"); let z3 ← (do let z2 ← (pure th); pure (concl z2)); pure (z3 == z4)))))) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN MESON_TAC [RING_IDEAL_IDEAL_PROD, IN_RING_IDEAL_0], X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier r /\ (y:A) IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_add k ((h:A->B) x) (h y) = h(ring_add r x y)") SUBST1_TAC THENL [ASM_SIMP_TAC [], MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC [IN_RING_IDEAL_ADD, RING_IDEAL_IDEAL_PROD]], X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul k ((h:A->B) a) (h y) = h(ring_mul r a y)") SUBST1_TAC THENL [ASM_SIMP_TAC [], MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC [IN_RING_IDEAL_LMUL, RING_IDEAL_IDEAL_PROD]], MATCH_MP_TAC r1 THEN REWRITE_TAC [SUBSET, ring_setmul, FORALL_IN_GSPEC] THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier r /\ (y:A) IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul k ((h:A->B) x) (h y) = h(ring_mul r x y)") SUBST1_TAC THENL [ASM_SIMP_TAC [], MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC [RING_MUL_IN_IDEAL_PROD]]], ALL_TAC] THEN ASM_SIMP_TAC [IDEAL_PROD_EXPLICIT, SUBSET, FORALL_IN_IMAGE, FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"u:num->A"), (← q r"v:num->A")] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"!i. i < n ==> (u:num->A) i IN ring_carrier r /\
       (v:num->A) i IN ring_carrier r") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"\i. ring_mul r ((u:num->A) i) (v i)"), (← q r"{i:num | i < n}")] (← MATCH_MP RING_HOMOMORPHISM_SUM (← ASSUME (← q r"ring_homomorphism(r,k) (h:A->B)")))) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL, o_DEF] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SPAN_SUM THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MATCH_MP_TAC RING_SPAN_INC THEN ASM_SIMP_TAC [RING_MUL] THEN REWRITE_TAC [ring_setmul, IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [(← q r"(h:A->B)((u:num->A) i)"), (← q r"(h:A->B)((v:num->A) i)")] THEN ASM_SIMP_TAC [FUN_IN_IMAGE])

  let FRACTIONAL_IDEAL_INTEGRAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!a:A. a IN j /\ ~(a = z) ==> ~(j = {z})")
    prove
      r"!r k (h:A->B) J.
          fractional_ideal (r,k) h J /\ J SUBSET IMAGE h (ring_carrier r) <=>
          field_of_fractions (r,k) h /\
          ?j. ring_ideal r j /\ ~(j = {ring_0 r}) /\ J = IMAGE h j"
      (REPEAT GEN_TAC THEN EQ_TAC THENL [STRIP_TAC, MESON_TAC [RING_IDEAL_IMP_FRACTIONAL_IDEAL, IMAGE_SUBSET, RING_IDEAL_IMP_SUBSET]] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [SUBSET, FORALL_IN_IMAGE]) o (GEN_REWRITE_RULE id [ring_homomorphism]))) THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"{a:A | a IN ring_carrier r /\ (h:A->B) a IN J}") THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [RING_IDEAL, SUBSET, IN_ELIM_THM] THEN SIMP_TAC [] THEN ASM_SIMP_TAC [RING_0, RING_ADD, RING_MUL] THEN ASM_MESON_TAC [IN_FRACTIONAL_IDEAL_0, IN_FRACTIONAL_IDEAL_ADD, IN_FRACTIONAL_IDEAL_LMUL], FIRST_ASSUM ((X_CHOOSE_THEN (← q r"x:B") STRIP_ASSUME_TAC) o (MATCH_MP FRACTIONAL_IDEAL_IMP_NONZERO)) THEN SUBGOAL_THEN (← q r"?a:A. a IN ring_carrier r /\ (h:A->B) a = x") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"a:A") THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC [], ASM SET_TAC []])

  let FRACTIONAL_IDEAL_SCALED_IDEAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (q ==> r) ==> (p <=> q) ==> r")
    prove
      r"!r k (h:A->B) J.
          fractional_ideal (r,k) h J
          ==> ?d j. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                    ring_ideal r j /\ ~(j = {ring_0 r}) /\
                    IMAGE (ring_mul k (h d)) J = IMAGE h j"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN FIRST_ASSUM ((X_CHOOSE_THEN (← q r"d:A") STRIP_ASSUME_TAC) o (MATCH_MP FRACTIONAL_IDEAL_DENOMINATOR)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"IMAGE (ring_mul k ((h:A->B) d)) J")] FRACTIONAL_IDEAL_INTEGRAL) THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [ASM_SIMP_TAC [SUBSET, FORALL_IN_IMAGE] THEN MATCH_MP_TAC FRACTIONAL_IDEAL_IMAGE_MUL THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_MONOMORPHISM_EQ_0], DISCH_THEN ((X_CHOOSE_THEN (← q r"j:A->bool") STRIP_ASSUME_TAC) o CONJUNCT2) THEN MAP_EVERY EXISTS_TAC [(← q r"d:A"), (← q r"j:A->bool")] THEN ASM_REWRITE_TAC []])

  let FRACTIONAL_IDEAL_SCALED_IDEAL_EQ ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(!x:B. x IN s ==> f x = x) ==> s = IMAGE f s")
    prove
      r"!r k (h:A->B) J.
          fractional_ideal (r,k) h J <=>
          field_of_fractions (r,k) h /\ J SUBSET ring_carrier k /\
          ?d j. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                ring_ideal r j /\ ~(j = {ring_0 r}) /\
                IMAGE (ring_mul k (h d)) J = IMAGE h j"
      (REPEAT GEN_TAC THEN EQ_TAC THENL [DISCH_TAC THEN REPEAT CONJ_TAC THENL [ASM_MESON_TAC [FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS], ASM_MESON_TAC [FRACTIONAL_IDEAL_IMP_SUBSET], ASM_MESON_TAC [FRACTIONAL_IDEAL_SCALED_IDEAL]], STRIP_TAC] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN SUBGOAL_THEN (← q r"(h:A->B) d IN ring_carrier k /\ ~(h d = ring_0 k)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_MONOMORPHISM_EQ_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"J = IMAGE (ring_mul k (ring_inv k ((h:A->B) d)))
                (IMAGE (ring_mul k (h d)) J)") SUBST1_TAC THENL [REWRITE_TAC [(← GSYM IMAGE_o), o_DEF] THEN MATCH_MP_TAC r1 THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier k") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_ASSOC, RING_INV, FIELD_MUL_LINV, RING_MUL_LID], ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FRACTIONAL_IDEAL_IMAGE_MUL THEN ASM_SIMP_TAC [RING_IDEAL_IMP_FRACTIONAL_IDEAL, RING_INV] THEN ASM_MESON_TAC [FIELD_INV_EQ_0]])

  let FRACTIONAL_IDEAL_MUL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul r (ring_mul r a b) (ring_mul r x y) =
        ring_mul r (ring_mul r a x) (ring_mul r b (y:B))")
    let r2 ← SET_RULE (← q r"(s:B->bool) SUBSET t ==> u INTER s SUBSET t")
    let r3 ← RING_RULE (← q r"ring_mul r a (ring_mul r b c) = ring_mul r b (ring_mul r a (c:B))")
    let r4 ← SET_RULE (← q r"!x:B. x IN s /\ ~(x = z) ==> ~(s = {z})")
    prove
      r"!r k (h:A->B) J1 J2.
          fractional_ideal (r,k) h J1 /\ fractional_ideal (r,k) h J2
          ==> fractional_ideal (r,k) h (ring_span (r,k) h (ring_setmul k J1 J2))"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN (← q r"(J1:B->bool) SUBSET ring_carrier k /\ (J2:B->bool) SUBSET ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [FRACTIONAL_IDEAL_IMP_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE (h:A->B) (ring_carrier r) subring_of k") ASSUME_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [ring_image] SUBRING_RING_IMAGE) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!a:A. a IN ring_carrier r ==> (h:A->B) a IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN ASM_REWRITE_TAC [fractional_ideal, RING_SPAN_SUBSET, RING_SPAN_0] THEN REPEAT CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"J1:B->bool")] FRACTIONAL_IDEAL_IMP_NONZERO) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"J2:B->bool")] FRACTIONAL_IDEAL_IMP_NONZERO) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"y:B") THEN STRIP_TAC THEN X_GEN_TAC (← q r"x:B") THEN STRIP_TAC THEN MATCH_MP_TAC r4 THEN EXISTS_TAC (← q r"ring_mul k x y:B") THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier k /\ (y:B) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_MUL_EQ_0] THEN MATCH_MP_TAC RING_SPAN_INC THEN ASM_SIMP_TAC [RING_MUL] THEN REWRITE_TAC [ring_setmul, IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [(← q r"x:B"), (← q r"y:B")] THEN ASM_REWRITE_TAC [], SIMP_TAC [RING_SPAN_ADD], REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_SPAN_MUL THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"J1:B->bool")] FRACTIONAL_IDEAL_DENOMINATOR) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"J2:B->bool")] FRACTIONAL_IDEAL_DENOMINATOR) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"d2:A") THEN STRIP_TAC THEN X_GEN_TAC (← q r"d1:A") THEN STRIP_TAC THEN EXISTS_TAC (← q r"ring_mul r d1 d2:A") THEN ASM_SIMP_TAC [RING_MUL, INTEGRAL_DOMAIN_MUL_EQ_0] THEN SUBGOAL_THEN (← q r"ring_span (r,k) h (ring_setmul k J1 J2) SUBSET
      {z | z IN ring_carrier k /\
           ring_mul k ((h:A->B)(ring_mul r d1 d2)) z IN
           IMAGE h (ring_carrier r)}") (fun th => MP_TAC th THEN SET_TAC []) THEN MATCH_MP_TAC RING_SPAN_MINIMAL THEN REWRITE_TAC [IN_ELIM_THM] THEN SUBGOAL_THEN (← q r"(h:A->B)(ring_mul r d1 d2) IN ring_carrier k") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_MUL], ALL_TAC] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [RING_0], ASM_SIMP_TAC [RING_MUL_RZERO, IN_SUBRING_0], MAP_EVERY X_GEN_TAC [(← q r"y:B"), (← q r"z:B")] THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_ADD, RING_ADD_LDISTRIB, IN_SUBRING_ADD], MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"y:B")] THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_MUL, r3] THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [FUN_IN_IMAGE], MATCH_MP_TAC r2 THEN REWRITE_TAC [ring_setmul, SUBSET, FORALL_IN_GSPEC] THEN REWRITE_TAC [IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"x:B"), (← q r"y:B")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier k /\ (y:B) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ASM_SIMP_TAC [RING_MUL]] THEN SUBGOAL_THEN (← q r"ring_mul k ((h:A->B)(ring_mul r d1 d2)) (ring_mul k x y) =
        ring_mul k (ring_mul k (h d1) x) (ring_mul k (h d2) y)") SUBST1_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th)])) THEN ASM_SIMP_TAC [r1], MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC []]])

  let FRACTIONAL_IDEAL_MUL_LID ← prove
    r"!r k (h:A->B) J.
        fractional_ideal (r,k) h J
        ==> ring_span (r,k) h (ring_setmul k (IMAGE h (ring_carrier r)) J) =
            J"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FRACTIONAL_IDEAL_IMP_SUBSET)) THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← GSYM (← MATCH_MP FRACTIONAL_IDEAL_RING_SPAN th))])) THEN MATCH_MP_TAC RING_SPAN_MONO THEN REWRITE_TAC [ring_setmul, SUBSET, FORALL_IN_GSPEC, IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_IMAGE] THEN ASM_MESON_TAC [IN_FRACTIONAL_IDEAL_LMUL], REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN MATCH_MP_TAC RING_SPAN_INC THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier k") ASSUME_TAC THENL [ASM SET_TAC [], ASM_REWRITE_TAC []] THEN REWRITE_TAC [ring_setmul, IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [(← q r"(h:A->B)(ring_1 r)"), (← q r"x:B")] THEN ASM_SIMP_TAC [FUN_IN_IMAGE, RING_1] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_1 th)])) THEN ASM_SIMP_TAC [RING_MUL_LID]])

  let DEDEKIND_FRACTIONAL_IDEAL_INVERTIBLE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul k z (ring_mul k (ring_mul k a b) c) =
      ring_mul k (ring_mul k (ring_mul k a z) b) (c:B)")
    let r2 ← RING_RULE (← q r"ring_mul k ((h:A->B) d) w = h a /\
      ring_mul k (h a) (h((v:num->A) i)) = ring_mul k (h c) (h b) /\
      ring_mul k (h c) (ring_inv k (h c)) = ring_1 k
      ==> ring_mul k (ring_mul k (ring_mul k (h d) (h (v i)))
                                   (ring_inv k (h c))) w = h b")
    prove
      r"!r k (h:A->B) J.
          dedekind_domain r /\ fractional_ideal (r,k) h J
          ==> ?n x y. (!i. i < n:num
                           ==> x i IN J /\
                               y i IN fractional_ideal_inv (r,k) h J) /\
                      ring_sum k {i | i < n}
                        (\i. ring_mul k (x i) (y i)) =
                      ring_1 k"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FRACTIONAL_IDEAL_IMP_SUBSET)) THEN FIRST_ASSUM (MP_TAC o (MATCH_MP FRACTIONAL_IDEAL_SCALED_IDEAL)) THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"d:A"), (← q r"j:A->bool")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_INVERTIBLE) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"c:A"), (← q r"n:num"), (← q r"u:num->A"), (← q r"v:num->A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!i. i < n ==> (u:num->A) i IN ring_carrier r /\
                    (v:num->A) i IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN REWRITE_TAC [fractional_ideal_inv, IN_ELIM_THM] THEN SUBGOAL_THEN (← q r"!x. x IN J ==> x IN ring_carrier(k:B ring)") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x:A. x IN ring_carrier r ==> ((h:A->B) x = ring_0 k <=> x = ring_0 r)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0], ALL_TAC] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [SUBSET, FORALL_IN_IMAGE]) o (GEN_REWRITE_RULE id [ring_homomorphism]))) THEN SUBGOAL_THEN (← q r"!i. ?z. i < n
              ==> z IN J /\
                  (h:A->B)((u:num->A) i) = ring_mul k (h d) z") MP_TAC THENL [X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(h:A->B)((u:num->A) i) IN IMAGE (ring_mul k (h d)) J") MP_TAC THENL [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_SIMP_TAC [], REWRITE_TAC [IN_IMAGE] THEN MESON_TAC []], REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"z:num->B") THEN DISCH_TAC] THEN SUBGOAL_THEN (← q r"ring_inv k ((h:A->B) c) IN ring_carrier k /\
      ring_mul k (h c) (ring_inv k (h c)) = ring_1 k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_INV, FIELD_MUL_RINV], ALL_TAC] THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"z:num->B"), (← q r"\i. ring_mul k (ring_mul k ((h:A->B) d) (h((v:num->A) i)))
                       (ring_inv k (h(c:A)))")] THEN REWRITE_TAC [] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(v:num->A) i IN ring_carrier r /\
        (h:A->B) d IN ring_carrier k /\ h(v i) IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ASM_SIMP_TAC [RING_MUL]] THEN X_GEN_TAC (← q r"w:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_mul k ((h:A->B) d) w IN IMAGE h j") MP_TAC THENL [UNDISCH_TAC (← q r"IMAGE (ring_mul k ((h:A->B) d)) J = IMAGE h j") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC [], REWRITE_TAC [IN_IMAGE, LEFT_IMP_EXISTS_THM]] THEN X_GEN_TAC (← q r"a:A") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"?b:A. b IN ring_carrier r /\ ring_mul r a ((v:num->A) i) = ring_mul r c b") STRIP_ASSUME_TAC THENL [MP_TAC (← SPEC (← q r"a:A") (← CONJUNCT2 (← CONJUNCT2 (← MATCH_MP (← ASSUME (← q r"!i. i < n ==> (u:num->A) i IN j /\ v i IN ring_carrier r /\
                        !a. a IN j ==> ring_divides r c (ring_mul r a (v i))")) (← ASSUME (← q r"i:num < n")))))) THEN ASM_REWRITE_TAC [ring_divides] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul k ((h:A->B) a) (h((v:num->A) i)) =
        ring_mul k (h c) (h b)") ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o (AP_TERM (← q r"h:A->B"))) THEN ASM_SIMP_TAC [], ALL_TAC] THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"b:A") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_IMP] r2) THEN ASM_SIMP_TAC [], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"ring_sum k {i | i < n}
        (\i:num. ring_mul k ((h:A->B)(ring_mul r (u i) (v i)))
                         (ring_inv k (h(c:A))))") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(u:num->A) i IN ring_carrier r /\ (v:num->A) i IN ring_carrier r /\
        (h:A->B) d IN ring_carrier k /\ h(v i) IN ring_carrier k /\
        (z:num->B) i IN ring_carrier k /\
        h(u i) = ring_mul k (h d) (z i)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [r1], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:B ring"), (← q r"\i:num. (h:A->B)(ring_mul r (u i) (v i))"), (← q r"ring_inv k ((h:A->B) c)"), (← q r"{i:num | i < n}")] RING_SUM_RMUL) THEN REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"\i. ring_mul r ((u:num->A) i) (v i)"), (← q r"{i:num | i < n}")] (← MATCH_MP RING_HOMOMORPHISM_SUM (← ASSUME (← q r"ring_homomorphism (r,k) (h:A->B)")))) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL, o_DEF] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [])

  let DEDEKIND_FRACTIONAL_IDEAL_MUL_INV ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(s:B->bool) SUBSET t ==> u INTER s SUBSET t")
    prove
      r"!r k (h:A->B) J.
          dedekind_domain r /\ fractional_ideal (r,k) h J
          ==> ring_span (r,k) h
                (ring_setmul k J (fractional_ideal_inv (r,k) h J)) =
              IMAGE h (ring_carrier r)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FRACTIONAL_IDEAL_IMP_SUBSET)) THEN SUBGOAL_THEN (← q r"IMAGE (h:A->B) (ring_carrier r) subring_of k") ASSUME_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [ring_image] SUBRING_RING_IMAGE) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"fractional_ideal_inv (r,k) (h:A->B) J SUBSET ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV, FRACTIONAL_IDEAL_IMP_SUBSET], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SPAN_MINIMAL THEN ASM_SIMP_TAC [IN_SUBRING_0, IN_SUBRING_ADD] THEN CONJ_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [FUN_IN_IMAGE], MATCH_MP_TAC r1 THEN REWRITE_TAC [ring_setmul, SUBSET, FORALL_IN_GSPEC] THEN REWRITE_TAC [fractional_ideal_inv, IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"x:B"), (← q r"y:B")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier k") ASSUME_TAC THENL [ASM SET_TAC [], ASM_MESON_TAC [RING_MUL_SYM]]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"J:B->bool")] DEDEKIND_FRACTIONAL_IDEAL_INVERTIBLE) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"x:num->B"), (← q r"y:num->B")] THEN STRIP_TAC THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"a:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(h:A->B) a IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"(h:A->B) a =
      ring_mul k (h a) (ring_sum k {i | i < n}
                         (\i. ring_mul k ((x:num->B) i) (y i)))") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_MUL_RID], ALL_TAC] THEN MATCH_MP_TAC RING_SPAN_MUL THEN REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN MATCH_MP_TAC RING_SPAN_SUM THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MATCH_MP_TAC RING_SPAN_INC THEN SUBGOAL_THEN (← q r"(x:num->B) i IN ring_carrier k /\ (y:num->B) i IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ASM_SIMP_TAC [RING_MUL]] THEN REWRITE_TAC [ring_setmul, IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [(← q r"(x:num->B) i"), (← q r"(y:num->B) i")] THEN ASM_SIMP_TAC [])

  let fractional_ideal_group ← new_definition
    r"fractional_ideal_group (r:A ring,k:B ring) (h:A->B) =
    group({J | fractional_ideal (r,k) h J},
          IMAGE h (ring_carrier r),
          fractional_ideal_inv (r,k) h,
          (\J1 J2. ring_span (r,k) h (ring_setmul k J1 J2)))"

  -- @@RETURN BEGIN
  return { fractional_ideal, fractional_ideal_inv,
           FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS, FRACTIONAL_IDEAL_IMP_SUBSET,
           FRACTIONAL_IDEAL_IMP_NONZERO, IN_FRACTIONAL_IDEAL_0, IN_FRACTIONAL_IDEAL_ADD,
           IN_FRACTIONAL_IDEAL_LMUL, IN_FRACTIONAL_IDEAL_NEG, IN_FRACTIONAL_IDEAL_SUB,
           FRACTIONAL_IDEAL_RING_SPAN, RING_IDEAL_IMP_FRACTIONAL_IDEAL,
           FRACTIONAL_IDEAL_CARRIER, FRACTIONAL_IDEAL_IMAGE_MUL,
           FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV, FRACTIONAL_IDEAL_DENOMINATOR,
           RING_SPAN_SETMUL_IMAGE_IDEAL_PROD, FRACTIONAL_IDEAL_INTEGRAL,
           FRACTIONAL_IDEAL_SCALED_IDEAL, FRACTIONAL_IDEAL_SCALED_IDEAL_EQ,
           FRACTIONAL_IDEAL_MUL, FRACTIONAL_IDEAL_MUL_LID,
           DEDEKIND_FRACTIONAL_IDEAL_INVERTIBLE, DEDEKIND_FRACTIONAL_IDEAL_MUL_INV,
           fractional_ideal_group }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- fractional_ideals.ml phrases from line 830 to 1517                     -/
/- ---------------------------------------------------------------------- -/

structure FractionalIdeals02 where
  -- @@FIELDS
  FRACTIONAL_IDEAL_GROUP : thm
  ABELIAN_FRACTIONAL_IDEAL_GROUP : thm
  FRACTIONAL_IDEAL_SCALED_IDEAL_COMPARE : thm
  fractional_ideal_valuation : thm
  FRACTIONAL_IDEAL_VALUATION : thm
  FRACTIONAL_IDEAL_VALUATION_IMAGE : thm
  FRACTIONAL_IDEAL_VALUATION_CARRIER : thm
  FRACTIONAL_IDEAL_SCALED_IDEAL_MUL : thm
  FRACTIONAL_IDEAL_COMMON_DENOMINATOR : thm
  FRACTIONAL_IDEAL_PRINCIPAL : thm
  FRACTIONAL_IDEAL_VALUATION_MUL : thm
  FRACTIONAL_IDEAL_VALUATION_INV : thm
  FRACTIONAL_IDEAL_VALUATION_PRINCIPAL : thm
  FRACTIONAL_IDEAL_VALUATION_FINITE : thm
  FRACTIONAL_IDEAL_SUBSET_VALUATION : thm
  FRACTIONAL_IDEAL_EQ_VALUATION : thm
  IN_FRACTIONAL_IDEAL_VALUATION : thm
  FRACTIONAL_IDEAL_INTEGRAL_VALUATION : thm
  FRACTIONAL_IDEAL_PRESCRIBED_VALUATIONS : thm
  GROUP_HOMOMORPHISM_FRACTIONAL_IDEAL_VALUATION : thm
  FRACTIONAL_IDEAL_VALUATION_PRIME : thm
  FRACTIONAL_IDEAL_VALUATION_ZPOW : thm
  FRACTIONAL_IDEAL_VALUATION_PRIME_PRODUCT : thm
  DEDEKIND_FRACTIONAL_IDEAL_FACTORIZATION : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFractionalIdeals02 [HolBase] (D : FractionalIdealsDeps) (BFractionalIdeals01 : FractionalIdeals01) :
    ExceptT String IO FractionalIdeals02 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC, INT_ARITH, INT_ARITH_TAC,
        MESON_TAC, RING_RULE, SET_RULE, SET_TAC, new_definition, .. } := D
  let { ABELIAN_INTEGER_GROUP, DEDEKIND_IDEAL_SUBSET_VALUATION,
        DEDEKIND_IMP_INTEGRAL_DOMAIN, DEDEKIND_VALUATION, EQ_TRANS,
        FIELD_FRACTION_NONZERO, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_OF_FRACTIONS_IMP_MONOMORPHISM, FINITE_SUBSET, FINITE_UNION,
        FORALL_IN_IMAGE, FUN_EQ_THM, FUN_IN_IMAGE, GROUP_HOMOMORPHISM,
        GROUP_HOMOMORPHISM_ZPOW, GROUP_SUM, GROUP_SUM_CLAUSES_EXISTS, GROUP_SUM_EQ,
        GROUP_SUM_HOMOMORPHIC_IMAGE, GROUP_SUM_SING, GROUP_SUM_SUPERSET, GROUP_ZPOW,
        GROUP_ZPOW_INTEGER_GROUP, IDEAL_GENERATED_EQ_0,
        IDEAL_GENERATED_SING_EQ_CARRIER, IDEAL_OF_VALUATIONS, IDEAL_PROD_EQ_ZERO,
        IDEAL_PROD_SCALE, IDEAL_VALUATION_CARRIER, IDEAL_VALUATION_FINITE_SUPPORT,
        IDEAL_VALUATION_IDEAL_PROD, IDEAL_VALUATION_PRIME,
        IDEAL_VALUATION_PRINCIPAL_MUL, IMAGE_CLAUSES, IMAGE_HOMOMORPHISM_MUL, IMAGE_o,
        IMP_CONJ, INTEGER_GROUP, INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_MUL_LCANCEL,
        INTEGRAL_DOMAIN_NONTRIVIAL, INTER_SUBSET, INT_LE_REFL, INT_MUL_RID,
        INT_MUL_RZERO, INT_OF_NUM_ADD, INT_OF_NUM_EQ, INT_OF_NUM_LE, INT_OF_NUM_OF_INT,
        INT_SUB_RZERO, IN_ELIM_THM, IN_INTER, IN_SING, IN_SUBRING_MUL, .. } := D.core1
  let { IN_UNION, IN_UNIV, LEFT_IMP_EXISTS_THM, MONO_EXISTS, PRIME_IMP_PROPER_IDEAL,
        PRIME_IMP_RING_IDEAL, PROPER_IDEAL_ALT, RING_0, RING_1, RING_HOMOMORPHISM_1,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_MUL, RING_IDEAL_CARRIER,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_PROD, RING_IDEAL_IMP_SUBSET,
        RING_MONOMORPHISM_EQ_0, RING_MONOMORPHISM_INJECTIVE_EQ, RING_MUL, RING_MUL_LID,
        RING_MUL_SYM, RING_SETMUL, RING_SETMUL_IMAGE_MUL,
        RING_SPAN_IMAGE_IDEAL_GENERATED, RING_SPAN_IMAGE_MUL, RING_SPAN_INC,
        RING_SPAN_MONO, RING_SPAN_SETMUL_ASSOC, RING_SPAN_SETMUL_SYM,
        RING_SPAN_SING_IMAGE, RING_UNIT_1, SELECT_UNIQUE, SING_SUBSET,
        SUBRING_RING_IMAGE, SUBSET, SUBSET_ANTISYM_EQ, SUBSET_UNIV, abelian_group,
        group_carrier, group_id, group_inv, group_mul, group_tybij, o_DEF, o_THM,
        ring_image, .. } := D.core2
  let { DEDEKIND_FRACTIONAL_IDEAL_MUL_INV, FRACTIONAL_IDEAL_CARRIER,
        FRACTIONAL_IDEAL_DENOMINATOR, FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV,
        FRACTIONAL_IDEAL_IMAGE_MUL, FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS,
        FRACTIONAL_IDEAL_IMP_SUBSET, FRACTIONAL_IDEAL_INTEGRAL, FRACTIONAL_IDEAL_MUL,
        FRACTIONAL_IDEAL_MUL_LID, FRACTIONAL_IDEAL_RING_SPAN,
        FRACTIONAL_IDEAL_SCALED_IDEAL, RING_IDEAL_IMP_FRACTIONAL_IDEAL,
        RING_SPAN_SETMUL_IMAGE_IDEAL_PROD, fractional_ideal_group, .. } := BFractionalIdeals01
  -- @@SCOPE END

  let FRACTIONAL_IDEAL_GROUP ← prove
    r"!r k (h:A->B).
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> group_carrier(fractional_ideal_group (r,k) h) =
              {J | fractional_ideal (r,k) h J} /\
            group_id(fractional_ideal_group (r,k) h) =
              IMAGE h (ring_carrier r) /\
            group_inv(fractional_ideal_group (r,k) h) =
              fractional_ideal_inv (r,k) h /\
            group_mul(fractional_ideal_group (r,k) h) =
              (\J1 J2. ring_span (r,k) h (ring_setmul k J1 J2))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN MP_TAC (← (do pure (Prod.fst (← (do pure (← EQ_IMP_RULE (← ISPEC (← (do let z1 ← (do let z2 ← (do pure (Prod.snd (← (do let z3 ← (do let z4 ← (pure fractional_ideal_group); pure (concl z4)); pure (strip_forall z3))))); liftExcept (rand z2)); liftExcept (rand z1))) (← CONJUNCT2 group_tybij)))))))) THEN REWRITE_TAC [(← GSYM fractional_ideal_group)] THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC [group_carrier, group_id, group_inv, group_mul]] THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_CARRIER, FRACTIONAL_IDEAL_MUL, FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV] THEN REPEAT CONJ_TAC THENL [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SPAN_SETMUL_ASSOC THEN ASM_MESON_TAC [FRACTIONAL_IDEAL_IMP_SUBSET], X_GEN_TAC (← q r"J:B->bool") THEN DISCH_TAC THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_MUL_LID] THEN wPart lhand (lhand o rand) RING_SPAN_SETMUL_SYM THEN ANTS_TAC THENL [ASM_MESON_TAC [FRACTIONAL_IDEAL_IMP_SUBSET, FRACTIONAL_IDEAL_CARRIER], DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_MUL_LID]], X_GEN_TAC (← q r"J:B->bool") THEN DISCH_TAC THEN ASM_SIMP_TAC [DEDEKIND_FRACTIONAL_IDEAL_MUL_INV] THEN wPart lhand (lhand o rand) RING_SPAN_SETMUL_SYM THEN ANTS_TAC THENL [ASM_MESON_TAC [FRACTIONAL_IDEAL_IMP_SUBSET, FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV], DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [DEDEKIND_FRACTIONAL_IDEAL_MUL_INV]]])

  let ABELIAN_FRACTIONAL_IDEAL_GROUP ← prove
    r"!r k (h:A->B).
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> abelian_group(fractional_ideal_group (r,k) h)"
    (SIMP_TAC [abelian_group, FRACTIONAL_IDEAL_GROUP, IN_ELIM_THM] THEN MESON_TAC [RING_SPAN_SETMUL_SYM, FRACTIONAL_IDEAL_IMP_SUBSET])

  let FRACTIONAL_IDEAL_SCALED_IDEAL_COMPARE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul r a (ring_mul r b c) = ring_mul r b (ring_mul r a (c:B))")
    let r2 ← SET_RULE (← q r"(!x:B. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE (g:B->B) s")
    let r11 ← SET_RULE (← q r"!(f:A->B) u. (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\
                 s SUBSET u /\ t SUBSET u /\ IMAGE f s = IMAGE f t
                 ==> s = t")
    prove
      r"!r k (h:A->B) J d j d' j'.
          field_of_fractions (r,k) h /\ J SUBSET ring_carrier k /\
          d IN ring_carrier r /\ d' IN ring_carrier r /\
          ring_ideal r j /\ ring_ideal r j' /\
          IMAGE (ring_mul k (h d)) J = IMAGE h j /\
          IMAGE (ring_mul k (h d')) J = IMAGE h j'
          ==> ideal_prod r (ideal_generated r {d'}) j =
              ideal_prod r (ideal_generated r {d}) j'"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN ASM_SIMP_TAC [IDEAL_PROD_SCALE] THEN MAP_EVERY (fun t => tactic_of do pure (FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP RING_IDEAL_IMP_SUBSET) o (checkM (fun th => (do let z14 ← (pure t); let z13 ← (do let z12 ← (pure th); pure (concl z12)); pure (z13 == z14)))))))) [(← q r"ring_ideal r (j:A->bool)"), (← q r"ring_ideal r (j':A->bool)")] THEN SUBGOAL_THEN (← q r"IMAGE (ring_mul r d') j SUBSET ring_carrier r /\
      IMAGE (ring_mul r (d:A)) j' SUBSET ring_carrier r") STRIP_ASSUME_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN ASM_MESON_TAC [RING_MUL, SUBSET], ALL_TAC] THEN MATCH_MP_TAC r11 THEN MAP_EVERY EXISTS_TAC [(← q r"h:A->B"), (← q r"ring_carrier r:A->bool")] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_MONOMORPHISM_INJECTIVE_EQ], ALL_TAC] THEN ASM_SIMP_TAC [IMAGE_HOMOMORPHISM_MUL] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z10 ← (q r"IMAGE (h:A->B) j'"); let z9 ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); liftExcept (rand z7)); pure (z9 == z10)))))) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z6 ← (q r"IMAGE (h:A->B) j"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (rand z3)); pure (z5 == z6)))))) THEN REWRITE_TAC [(← GSYM IMAGE_o), o_DEF] THEN MATCH_MP_TAC r2 THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier k /\ (h:A->B) d IN ring_carrier k /\
      h d' IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [SUBSET, RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN ASM_SIMP_TAC [r1])

  let fractional_ideal_valuation ← new_definition
    r"fractional_ideal_valuation (r:A ring,k:B ring) (h:A->B) (P:A->bool) J =
  @v:int. !d j. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                ring_ideal r j /\ ~(j = {ring_0 r}) /\
                IMAGE (ring_mul k (h d)) J = IMAGE h j
                ==> v = &(ideal_valuation r P j) -
                        &(ideal_valuation r P (ideal_generated r {d}))"

  let FRACTIONAL_IDEAL_VALUATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INT_ARITH (← q r"(a:int) - b = c - d <=> d + a = b + c")
    prove
      r"!r k (h:A->B) P J d j.
          dedekind_domain r /\ fractional_ideal (r,k) h J /\
          prime_ideal r P /\ ~(P = {ring_0 r}) /\
          d IN ring_carrier r /\ ~(d = ring_0 r) /\
          ring_ideal r j /\ ~(j = {ring_0 r}) /\
          IMAGE (ring_mul k (h d)) J = IMAGE h j
          ==> fractional_ideal_valuation (r,k) h P J =
              &(ideal_valuation r P j) -
              &(ideal_valuation r P (ideal_generated r {d}))"
      (REPEAT STRIP_TAC THEN REWRITE_TAC [fractional_ideal_valuation] THEN MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC (← q r"v:int") THEN BETA_TAC THEN EQ_TAC THENL [DISCH_THEN (MP_TAC o (SPECL [(← q r"d:A"), (← q r"j:A->bool")])) THEN ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"d':A"), (← q r"j':A->bool")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"J:B->bool"), (← q r"d:A"), (← q r"j:A->bool"), (← q r"d':A"), (← q r"j':A->bool")] FRACTIONAL_IDEAL_SCALED_IDEAL_COMPARE) THEN ANTS_TAC THENL [ASM_MESON_TAC [FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS, FRACTIONAL_IDEAL_IMP_SUBSET], DISCH_THEN (MP_TAC o (AP_TERM (← q r"ideal_valuation r (P:A->bool)")))] THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_PROD, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN REWRITE_TAC [r1] THEN REWRITE_TAC [INT_OF_NUM_ADD, INT_OF_NUM_EQ] THEN ARITH_TAC)

  let FRACTIONAL_IDEAL_VALUATION_IMAGE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(!x:A. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE (g:A->B) s")
    prove
      r"!r k (h:A->B) P j.
          dedekind_domain r /\ field_of_fractions (r,k) h /\
          prime_ideal r P /\ ~(P = {ring_0 r}) /\
          ring_ideal r j /\ ~(j = {ring_0 r})
          ==> fractional_ideal_valuation (r,k) h P (IMAGE h j) =
              &(ideal_valuation r P j)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"IMAGE (h:A->B) j"), (← q r"ring_1 r:A"), (← q r"j:A->bool")] FRACTIONAL_IDEAL_VALUATION) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_FRACTIONAL_IDEAL, RING_1, INTEGRAL_DOMAIN_NONTRIVIAL] THEN ANTS_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_1 th)])) THEN REWRITE_TAC [(← GSYM IMAGE_o), o_DEF] THEN MATCH_MP_TAC r1 THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC RING_MUL_LID THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_IDEAL_IMP_SUBSET, SUBSET], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_1 r:A")] IDEAL_GENERATED_SING_EQ_CARRIER) THEN REWRITE_TAC [RING_1, RING_UNIT_1] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool")] IDEAL_VALUATION_CARRIER) THEN ANTS_TAC THENL [ASM_MESON_TAC [PRIME_IMP_PROPER_IDEAL, PROPER_IDEAL_ALT], DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [INT_SUB_RZERO]])

  let FRACTIONAL_IDEAL_VALUATION_CARRIER ← prove
    r"!r k (h:A->B) P.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r})
        ==> fractional_ideal_valuation (r,k) h P (IMAGE h (ring_carrier r)) =
            &0"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"ring_carrier r:A->bool")] FRACTIONAL_IDEAL_VALUATION_IMAGE) THEN ASM_REWRITE_TAC [RING_IDEAL_CARRIER] THEN ANTS_TAC THENL [ASM_MESON_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN, INTEGRAL_DOMAIN_NONTRIVIAL, RING_1, RING_0, IN_SING], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [INT_OF_NUM_EQ] THEN MATCH_MP_TAC IDEAL_VALUATION_CARRIER THEN ASM_MESON_TAC [PRIME_IMP_PROPER_IDEAL, PROPER_IDEAL_ALT])

  let FRACTIONAL_IDEAL_SCALED_IDEAL_MUL ← prove
    r"!r k (h:A->B) J1 J2 d1 j1 d2 j2.
        fractional_ideal (r,k) h J1 /\ fractional_ideal (r,k) h J2 /\
        d1 IN ring_carrier r /\ d2 IN ring_carrier r /\
        ring_ideal r j1 /\ ring_ideal r j2 /\
        IMAGE (ring_mul k (h d1)) J1 = IMAGE h j1 /\
        IMAGE (ring_mul k (h d2)) J2 = IMAGE h j2
        ==> IMAGE (ring_mul k (h(ring_mul r d1 d2)))
                  (ring_span (r,k) h (ring_setmul k J1 J2)) =
            IMAGE h (ideal_prod r j1 j2)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN SUBGOAL_THEN (← q r"(J1:B->bool) SUBSET ring_carrier k /\ (J2:B->bool) SUBSET ring_carrier k /\
    (h:A->B) d1 IN ring_carrier k /\ h d2 IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [FRACTIONAL_IDEAL_IMP_SUBSET, RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th)])) THEN ASM_SIMP_TAC [(← GSYM RING_SPAN_IMAGE_MUL), RING_MUL, RING_SETMUL] THEN ASM_SIMP_TAC [(← GSYM RING_SETMUL_IMAGE_MUL)] THEN ASM_SIMP_TAC [RING_SPAN_SETMUL_IMAGE_IDEAL_PROD])

  let FRACTIONAL_IDEAL_COMMON_DENOMINATOR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul r (ring_mul r a b) c = ring_mul r b (ring_mul r a (c:B))")
    prove
      r"!r k (h:A->B) J1 J2.
          fractional_ideal (r,k) h J1 /\ fractional_ideal (r,k) h J2
          ==> ?d j1 j2. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                        ring_ideal r j1 /\ ~(j1 = {ring_0 r}) /\
                        ring_ideal r j2 /\ ~(j2 = {ring_0 r}) /\
                        IMAGE (ring_mul k (h d)) J1 = IMAGE h j1 /\
                        IMAGE (ring_mul k (h d)) J2 = IMAGE h j2"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN SUBGOAL_THEN (← q r"IMAGE (h:A->B) (ring_carrier r) subring_of k") ASSUME_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [ring_image] SUBRING_RING_IMAGE) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"J1:B->bool")] FRACTIONAL_IDEAL_DENOMINATOR) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"J2:B->bool")] FRACTIONAL_IDEAL_DENOMINATOR) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"d2:A") THEN STRIP_TAC THEN X_GEN_TAC (← q r"d1:A") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!J d d'. fractional_ideal (r,k) h J /\
               d IN ring_carrier r /\ ~(d = ring_0 r) /\
               d' IN ring_carrier r /\ ~(d' = ring_0 r) /\
               (!x. x IN J ==>
                 ring_mul k ((h:A->B) d) x IN IMAGE h (ring_carrier r))
               ==> ?j. ring_ideal r j /\ ~(j = {ring_0 r}) /\
                       IMAGE (ring_mul k (h(ring_mul r d d'))) J = IMAGE h j") MP_TAC THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"IMAGE (ring_mul k ((h:A->B)(ring_mul r d d'))) J")] FRACTIONAL_IDEAL_INTEGRAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"(h:A->B)(ring_mul r d d') IN ring_carrier k /\
        ~(h(ring_mul r d d') = ring_0 k)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [ASM_MESON_TAC [RING_MUL, RING_HOMOMORPHISM_IN_CARRIER], ASM_SIMP_TAC [RING_MUL, RING_MONOMORPHISM_EQ_0, INTEGRAL_DOMAIN_MUL_EQ_0]], ASM_SIMP_TAC [FRACTIONAL_IDEAL_IMAGE_MUL]] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FRACTIONAL_IDEAL_IMP_SUBSET)) THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_mul k ((h:A->B)(ring_mul r d d')) x =
        ring_mul k (h d') (ring_mul k (h d) x)") SUBST1_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th)])) THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier k /\ (h:A->B) d IN ring_carrier k /\
          h d' IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [SUBSET, RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN ASM_SIMP_TAC [r1], MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [FUN_IN_IMAGE]], DISCH_TAC] THEN EXISTS_TAC (← q r"ring_mul r d1 d2:A") THEN ASM_SIMP_TAC [RING_MUL, INTEGRAL_DOMAIN_MUL_EQ_0] THEN FIRST_ASSUM (MP_TAC o (SPECL [(← q r"J1:B->bool"), (← q r"d1:A"), (← q r"d2:A")])) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"j1:A->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o (SPECL [(← q r"J2:B->bool"), (← q r"d2:A"), (← q r"d1:A")])) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul r d2 d1:A = ring_mul r d1 d2") SUBST1_TAC THENL [ASM_MESON_TAC [RING_MUL_SYM], REWRITE_TAC []])

  let FRACTIONAL_IDEAL_PRINCIPAL ← prove
    r"!r k (h:A->B) x.
        field_of_fractions (r,k) h /\ x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> fractional_ideal (r,k) h (ring_span (r,k) h {x})"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN ASM_SIMP_TAC [RING_SPAN_SING_IMAGE] THEN MATCH_MP_TAC FRACTIONAL_IDEAL_IMAGE_MUL THEN ASM_REWRITE_TAC [FRACTIONAL_IDEAL_CARRIER])

  let FRACTIONAL_IDEAL_VALUATION_MUL ← prove
    r"!r k (h:A->B) P J1 J2.
        dedekind_domain r /\
        fractional_ideal (r,k) h J1 /\ fractional_ideal (r,k) h J2 /\
        prime_ideal r P /\ ~(P = {ring_0 r})
        ==> fractional_ideal_valuation (r,k) h P
              (ring_span (r,k) h (ring_setmul k J1 J2)) =
            fractional_ideal_valuation (r,k) h P J1 +
            fractional_ideal_valuation (r,k) h P J2"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"J1:B->bool")] FRACTIONAL_IDEAL_SCALED_IDEAL) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"J2:B->bool")] FRACTIONAL_IDEAL_SCALED_IDEAL) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"d2:A"), (← q r"j2:A->bool")] THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"d1:A"), (← q r"j1:A->bool")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"J1:B->bool"), (← q r"J2:B->bool"), (← q r"d1:A"), (← q r"j1:A->bool"), (← q r"d2:A"), (← q r"j2:A->bool")] FRACTIONAL_IDEAL_SCALED_IDEAL_MUL) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"ring_span (r,k) (h:A->B) (ring_setmul k J1 J2)"), (← q r"ring_mul r d1 d2:A"), (← q r"ideal_prod r j1 j2:A->bool")] FRACTIONAL_IDEAL_VALUATION) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"J1:B->bool"), (← q r"d1:A"), (← q r"j1:A->bool")] FRACTIONAL_IDEAL_VALUATION) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"J2:B->bool"), (← q r"d2:A"), (← q r"j2:A->bool")] FRACTIONAL_IDEAL_VALUATION) THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_MUL, RING_MUL, INTEGRAL_DOMAIN_MUL_EQ_0, RING_IDEAL_IDEAL_PROD, IDEAL_PROD_EQ_ZERO] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_PROD, IDEAL_VALUATION_PRINCIPAL_MUL] THEN REWRITE_TAC [(← GSYM INT_OF_NUM_ADD)] THEN INT_ARITH_TAC)

  let FRACTIONAL_IDEAL_VALUATION_INV ← prove
    r"!r k (h:A->B) P J.
        dedekind_domain r /\ fractional_ideal (r,k) h J /\
        prime_ideal r P /\ ~(P = {ring_0 r})
        ==> fractional_ideal_valuation (r,k) h P
              (fractional_ideal_inv (r,k) h J) =
            --(fractional_ideal_valuation (r,k) h P J)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"J:B->bool"), (← q r"fractional_ideal_inv (r,k) (h:A->B) J")] FRACTIONAL_IDEAL_VALUATION_MUL) THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV, DEDEKIND_FRACTIONAL_IDEAL_MUL_INV] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool")] FRACTIONAL_IDEAL_VALUATION_CARRIER) THEN ANTS_TAC THENL [ASM_MESON_TAC [FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS], DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC])

  let FRACTIONAL_IDEAL_VALUATION_PRINCIPAL ← prove
    r"!r k (h:A->B) P x.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> fractional_ideal_valuation (r,k) h P (ring_span (r,k) h {x}) =
            dedekind_valuation (r,k) h P x"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:B")] FIELD_FRACTION_NONZERO) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"x:B"), (← q r"a:A"), (← q r"b:A")] DEDEKIND_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC FRACTIONAL_IDEAL_VALUATION THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_PRINCIPAL, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN SUBGOAL_THEN (← q r"(h:A->B) b IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM RING_SPAN_IMAGE_MUL), SING_SUBSET, IMAGE_CLAUSES] THEN ASM_SIMP_TAC [(← GSYM RING_SPAN_IMAGE_IDEAL_GENERATED), SING_SUBSET, IMAGE_CLAUSES])

  let FRACTIONAL_IDEAL_VALUATION_FINITE ← prove
    r"!r k (h:A->B) J.
        dedekind_domain r /\ fractional_ideal (r,k) h J
        ==> FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                        ~(fractional_ideal_valuation (r,k) h P J = &0)}"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP FRACTIONAL_IDEAL_SCALED_IDEAL)) THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"d:A"), (← q r"j:A->bool")] THEN STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
         ~(ideal_valuation r P (j:A->bool) = 0)} UNION
    {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
         ~(ideal_valuation r P (ideal_generated r {d:A}) = 0)}") THEN ASM_SIMP_TAC [FINITE_UNION, IDEAL_VALUATION_FINITE_SUPPORT, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN REWRITE_TAC [SUBSET, IN_UNION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"~(fractional_ideal_valuation (r,k) (h:A->B) P J = &0)") THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"J:B->bool"), (← q r"d:A"), (← q r"j:A->bool")] FRACTIONAL_IDEAL_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [(← GSYM INT_OF_NUM_EQ)] THEN INT_ARITH_TAC)

  let FRACTIONAL_IDEAL_SUBSET_VALUATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INT_ARITH (← q r"(a:int) - c <= b - c <=> a <= b")
    let r2 ← SET_RULE (← q r"!u. (!x y. x IN u /\ y IN u /\ (f:A->B) x = f y ==> x = y) /\
        s SUBSET u /\ t SUBSET u
        ==> (IMAGE f s SUBSET IMAGE f t <=> s SUBSET t)")
    let r3 ← SET_RULE (← q r"!u. (!x y. x IN u /\ y IN u /\ (f:B->B) x = f y ==> x = y) /\
        s SUBSET u /\ t SUBSET u
        ==> (s SUBSET t <=> IMAGE f s SUBSET IMAGE f t)")
    prove
      r"!r k (h:A->B) J1 J2.
          dedekind_domain r /\
          fractional_ideal (r,k) h J1 /\ fractional_ideal (r,k) h J2
          ==> (J1 SUBSET J2 <=>
               !P. prime_ideal r P /\ ~(P = {ring_0 r})
                   ==> fractional_ideal_valuation (r,k) h P J2 <=
                       fractional_ideal_valuation (r,k) h P J1)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"J1:B->bool"), (← q r"J2:B->bool")] FRACTIONAL_IDEAL_COMMON_DENOMINATOR) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"d:A"), (← q r"j1:A->bool"), (← q r"j2:A->bool")] THEN STRIP_TAC THEN TRANS_TAC EQ_TRANS (← q r"(j1:A->bool) SUBSET j2") THEN CONJ_TAC THENL [SUBGOAL_THEN (← q r"(J1:B->bool) SUBSET ring_carrier k /\
         (J2:B->bool) SUBSET ring_carrier k /\
        (h:A->B) d IN ring_carrier k /\ ~(h d = ring_0 k) /\
        (j1:A->bool) SUBSET ring_carrier r /\ (j2:A->bool) SUBSET ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [FRACTIONAL_IDEAL_IMP_SUBSET, RING_HOMOMORPHISM_IN_CARRIER, RING_MONOMORPHISM_EQ_0, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"IMAGE (ring_mul k ((h:A->B) d)) J1 SUBSET
        IMAGE (ring_mul k (h d)) J2") THEN CONJ_TAC THENL [MATCH_MP_TAC r3 THEN EXISTS_TAC (← q r"ring_carrier k:B->bool") THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [INTEGRAL_DOMAIN_MUL_LCANCEL], ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r2 THEN EXISTS_TAC (← q r"ring_carrier r:A->bool") THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [RING_MONOMORPHISM_INJECTIVE_EQ]], ALL_TAC] THEN ASM_SIMP_TAC [DEDEKIND_IDEAL_SUBSET_VALUATION] THEN AP_TERM_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN ASM_CASES_TAC (← q r"prime_ideal r (P:A->bool) /\ ~(P = {ring_0 r})") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"J1:B->bool"), (← q r"d:A"), (← q r"j1:A->bool")] FRACTIONAL_IDEAL_VALUATION) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool"), (← q r"J2:B->bool"), (← q r"d:A"), (← q r"j2:A->bool")] FRACTIONAL_IDEAL_VALUATION) THEN ASM_REWRITE_TAC [] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC [r1, INT_OF_NUM_LE])

  let FRACTIONAL_IDEAL_EQ_VALUATION ← prove
    r"!r k (h:A->B) J1 J2.
        dedekind_domain r /\
        fractional_ideal (r,k) h J1 /\ fractional_ideal (r,k) h J2
        ==> (J1 = J2 <=>
             !P. prime_ideal r P /\ ~(P = {ring_0 r})
                 ==> fractional_ideal_valuation (r,k) h P J1 =
                     fractional_ideal_valuation (r,k) h P J2)"
    (REPEAT STRIP_TAC THEN EQ_TAC THENL [SIMP_TAC [], DISCH_TAC] THEN REWRITE_TAC [(← GSYM SUBSET_ANTISYM_EQ)] THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_SUBSET_VALUATION, INT_LE_REFL])

  let IN_FRACTIONAL_IDEAL_VALUATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(x:B) IN s ==> s SUBSET t ==> x IN t")
    prove
      r"!r k (h:A->B) J x.
          dedekind_domain r /\ fractional_ideal (r,k) h J /\
          x IN ring_carrier k /\ ~(x = ring_0 k)
          ==> (x IN J <=>
               !P. prime_ideal r P /\ ~(P = {ring_0 r})
                   ==> fractional_ideal_valuation (r,k) h P J <=
                       dedekind_valuation (r,k) h P x)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN TRANS_TAC EQ_TRANS (← q r"ring_span (r,k) (h:A->B) {x} SUBSET J") THEN CONJ_TAC THENL [EQ_TAC THENL [DISCH_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← GSYM (← MATCH_MP FRACTIONAL_IDEAL_RING_SPAN th))])) THEN MATCH_MP_TAC RING_SPAN_MONO THEN ASM SET_TAC [], MATCH_MP_TAC r1 THEN MATCH_MP_TAC RING_SPAN_INC THEN ASM_REWRITE_TAC [IN_SING]], ASM_SIMP_TAC [FRACTIONAL_IDEAL_SUBSET_VALUATION, FRACTIONAL_IDEAL_PRINCIPAL, FRACTIONAL_IDEAL_VALUATION_PRINCIPAL]])

  let FRACTIONAL_IDEAL_INTEGRAL_VALUATION ← prove
    r"!r k (h:A->B) J.
        dedekind_domain r /\ fractional_ideal (r,k) h J
        ==> (J SUBSET IMAGE h (ring_carrier r) <=>
             !P. prime_ideal r P /\ ~(P = {ring_0 r})
                 ==> &0 <= fractional_ideal_valuation (r,k) h P J)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS)) THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_SUBSET_VALUATION, FRACTIONAL_IDEAL_CARRIER, FRACTIONAL_IDEAL_VALUATION_CARRIER])

  let FRACTIONAL_IDEAL_PRESCRIBED_VALUATIONS ← prove
    r"!r k (h:A->B) (e:(A->bool)->int).
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(e P = &0)}
        ==> ?J. fractional_ideal (r,k) h J /\
                !P. prime_ideal r P /\ ~(P = {ring_0 r})
                    ==> fractional_ideal_valuation (r,k) h P J = e P"
    (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"ep = \P:A->bool. num_of_int(max (&0) (e P))") THEN ABBREV_TAC (← q r"em = \P:A->bool. num_of_int(max (&0) (--(e P)))") THEN SUBGOAL_THEN (← q r"!P:A->bool. &(ep P):int = max (&0) (e P) /\
                &(em P):int = max (&0) (--(e P))") ASSUME_TAC THENL [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["ep", "em"] THEN CONJ_TAC THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN INT_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(ep P = 0)} /\
    FINITE {P:A->bool | prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(em P = 0)}") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN FIRST_ASSUM (MATCH_MP_TAC o (MATCH_MP (← REWRITE_RULE [IMP_CONJ] FINITE_SUBSET))) THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN REWRITE_TAC [(← GSYM INT_OF_NUM_EQ)] THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_INT_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ep:(A->bool)->num")] IDEAL_OF_VALUATIONS) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"em:(A->bool)->num")] IDEAL_OF_VALUATIONS) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"jp = ideal_of_valuations r (ep:(A->bool)->num)") THEN ABBREV_TAC (← q r"jm = ideal_of_valuations r (em:(A->bool)->num)") THEN REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"ring_span (r,k) (h:A->B)
      (ring_setmul k (IMAGE h jp)
                     (fractional_ideal_inv (r,k) h (IMAGE h jm)))") THEN SUBGOAL_THEN (← q r"fractional_ideal (r,k) (h:A->B) (IMAGE h jp) /\
    fractional_ideal (r,k) (h:A->B) (IMAGE h jm)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IMP_FRACTIONAL_IDEAL], ALL_TAC] THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_MUL, FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_VALUATION_MUL, FRACTIONAL_IDEAL_VALUATION_INV, FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV, FRACTIONAL_IDEAL_VALUATION_IMAGE] THEN INT_ARITH_TAC)

  let GROUP_HOMOMORPHISM_FRACTIONAL_IDEAL_VALUATION ← prove
    r"!r k (h:A->B) P.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r})
        ==> group_homomorphism (fractional_ideal_group (r,k) h,integer_group)
                               (fractional_ideal_valuation (r,k) h P)"
    (SIMP_TAC [GROUP_HOMOMORPHISM, INTEGER_GROUP, SUBSET_UNIV, FRACTIONAL_IDEAL_GROUP, IN_ELIM_THM, FRACTIONAL_IDEAL_VALUATION_MUL])

  let FRACTIONAL_IDEAL_VALUATION_PRIME ← prove
    r"!r k (h:A->B) P Q.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        prime_ideal r Q /\ ~(Q = {ring_0 r})
        ==> fractional_ideal_valuation (r,k) h Q (IMAGE h P) =
            if P = Q then &1 else &0"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_VALUATION_IMAGE, PRIME_IMP_RING_IDEAL, IDEAL_VALUATION_PRIME] THEN COND_CASES_TAC THEN REWRITE_TAC [])

  let FRACTIONAL_IDEAL_VALUATION_ZPOW ← prove
    r"!r k (h:A->B) P J n.
        dedekind_domain r /\ fractional_ideal (r,k) h J /\
        prime_ideal r P /\ ~(P = {ring_0 r})
        ==> fractional_ideal_valuation (r,k) h P
              (group_zpow (fractional_ideal_group (r,k) h) J n) =
            n * fractional_ideal_valuation (r,k) h P J"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"P:A->bool")] GROUP_HOMOMORPHISM_FRACTIONAL_IDEAL_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (MATCH_MP GROUP_HOMOMORPHISM_ZPOW)) THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_GROUP, IN_ELIM_THM, GROUP_ZPOW_INTEGER_GROUP])

  let FRACTIONAL_IDEAL_VALUATION_PRIME_PRODUCT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"~((a:A) IN s) ==> s INTER {a} = {}")
    let r2 ← SET_RULE (← q r"(a:A) IN s ==> s INTER {a} = {a}")
    prove
      r"!r k (h:A->B) s (e:(A->bool)->int) Q.
          dedekind_domain r /\ field_of_fractions (r,k) h /\ FINITE s /\
          (!P. P IN s ==> prime_ideal r P /\ ~(P = {ring_0 r})) /\
          prime_ideal r Q /\ ~(Q = {ring_0 r})
          ==> fractional_ideal_valuation (r,k) h Q
                (group_sum (fractional_ideal_group (r,k) h) s
                   (\P. group_zpow (fractional_ideal_group (r,k) h)
                          (IMAGE h P) (e P))) =
              if Q IN s then e Q else &0"
      (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"G = fractional_ideal_group (r,k) (h:A->B)") THEN SUBGOAL_THEN (← q r"!P. P IN s ==> IMAGE (h:A->B) P IN group_carrier G") ASSUME_TAC THENL [EXPAND_TAC "G" THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_GROUP, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_IDEAL_IMP_FRACTIONAL_IDEAL THEN ASM_MESON_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"G:(B->bool)group"), (← q r"integer_group"), (← q r"fractional_ideal_valuation (r,k) (h:A->B) Q"), (← q r"s:(A->bool)->bool"), (← q r"\P. group_zpow G (IMAGE (h:A->B) P) ((e:(A->bool)->int) P)")] GROUP_SUM_HOMOMORPHIC_IMAGE) THEN ANTS_TAC THENL [EXPAND_TAC "G" THEN ASM_SIMP_TAC [ABELIAN_FRACTIONAL_IDEAL_GROUP, ABELIAN_INTEGER_GROUP, GROUP_HOMOMORPHISM_FRACTIONAL_IDEAL_VALUATION] THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"s:(A->bool)->bool") THEN ASM_REWRITE_TAC [] THEN SET_TAC [], REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_ZPOW THEN UNDISCH_TAC (← q r"!P. P IN s ==> IMAGE (h:A->B) P IN group_carrier G") THEN EXPAND_TAC "G" THEN ASM_SIMP_TAC []], DISCH_THEN SUBST1_TAC] THEN TRANS_TAC EQ_TRANS (← q r"group_sum integer_group s
        (\P:A->bool. if P = Q then (e:(A->bool)->int) P else &0)") THEN CONJ_TAC THENL [MATCH_MP_TAC GROUP_SUM_EQ THEN X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN REWRITE_TAC [o_THM] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"Q:A->bool"), (← q r"IMAGE (h:A->B) P"), (← q r"(e:(A->bool)->int) P")] FRACTIONAL_IDEAL_VALUATION_ZPOW) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_IDEAL_IMP_FRACTIONAL_IDEAL THEN ASM_MESON_TAC [PRIME_IMP_RING_IDEAL], ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_VALUATION_PRIME] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [INT_MUL_RID, INT_MUL_RZERO], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"group_sum integer_group (s INTER {Q:A->bool})
        (\P:A->bool. if P = Q then (e:(A->bool)->int) P else &0)") THEN CONJ_TAC THENL [MATCH_MP_TAC GROUP_SUM_SUPERSET THEN REWRITE_TAC [INTER_SUBSET, INTEGER_GROUP, IN_INTER, IN_SING] THEN MESON_TAC [], ALL_TAC] THEN COND_CASES_TAC THENL [ASM_SIMP_TAC [r2] THEN REWRITE_TAC [GROUP_SUM_SING, INTEGER_GROUP, IN_UNIV], ASM_SIMP_TAC [r1] THEN REWRITE_TAC [GROUP_SUM_CLAUSES_EXISTS, INTEGER_GROUP]])

  let DEDEKIND_FRACTIONAL_IDEAL_FACTORIZATION ← prove
    r"!r k (h:A->B) J.
        dedekind_domain r /\ fractional_ideal (r,k) h J
        ==> group_sum (fractional_ideal_group (r,k) h)
              {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                   ~(fractional_ideal_valuation (r,k) h P J = &0)}
              (\P. group_zpow (fractional_ideal_group (r,k) h) (IMAGE h P)
                     (fractional_ideal_valuation (r,k) h P J)) =
            J"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FRACTIONAL_IDEAL_IMP_FIELD_OF_FRACTIONS)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B")] FRACTIONAL_IDEAL_EQ_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => wPart Except.ok (lhand o rand) th) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"!X. X IN group_carrier(fractional_ideal_group (r,k) (h:A->B))
          ==> fractional_ideal (r,k) h X") MATCH_MP_TAC THENL [ASM_SIMP_TAC [FRACTIONAL_IDEAL_GROUP, IN_ELIM_THM], REWRITE_TAC [GROUP_SUM]], DISCH_THEN SUBST1_TAC] THEN X_GEN_TAC (← q r"Q:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_VALUATION_PRIME_PRODUCT, FRACTIONAL_IDEAL_VALUATION_FINITE, IN_ELIM_THM] THEN MESON_TAC [])

  -- @@RETURN BEGIN
  return { FRACTIONAL_IDEAL_GROUP, ABELIAN_FRACTIONAL_IDEAL_GROUP,
           FRACTIONAL_IDEAL_SCALED_IDEAL_COMPARE, fractional_ideal_valuation,
           FRACTIONAL_IDEAL_VALUATION, FRACTIONAL_IDEAL_VALUATION_IMAGE,
           FRACTIONAL_IDEAL_VALUATION_CARRIER, FRACTIONAL_IDEAL_SCALED_IDEAL_MUL,
           FRACTIONAL_IDEAL_COMMON_DENOMINATOR, FRACTIONAL_IDEAL_PRINCIPAL,
           FRACTIONAL_IDEAL_VALUATION_MUL, FRACTIONAL_IDEAL_VALUATION_INV,
           FRACTIONAL_IDEAL_VALUATION_PRINCIPAL, FRACTIONAL_IDEAL_VALUATION_FINITE,
           FRACTIONAL_IDEAL_SUBSET_VALUATION, FRACTIONAL_IDEAL_EQ_VALUATION,
           IN_FRACTIONAL_IDEAL_VALUATION, FRACTIONAL_IDEAL_INTEGRAL_VALUATION,
           FRACTIONAL_IDEAL_PRESCRIBED_VALUATIONS,
           GROUP_HOMOMORPHISM_FRACTIONAL_IDEAL_VALUATION,
           FRACTIONAL_IDEAL_VALUATION_PRIME, FRACTIONAL_IDEAL_VALUATION_ZPOW,
           FRACTIONAL_IDEAL_VALUATION_PRIME_PRODUCT,
           DEDEKIND_FRACTIONAL_IDEAL_FACTORIZATION }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- fractional_ideals.ml phrases from line 1550 to 2058                    -/
/- ---------------------------------------------------------------------- -/

structure FractionalIdeals03 where
  -- @@FIELDS
  FRACTIONAL_IDEAL_GROUP_FREE_ABELIAN_EXPLICIT : thm
  FRACTIONAL_IDEAL_GROUP_FREE_ABELIAN : thm
  GROUP_HOMOMORPHISM_PRINCIPAL_FRACTIONAL_IDEAL : thm
  GROUP_KERNEL_PRINCIPAL_FRACTIONAL_IDEAL : thm
  FRACTIONAL_IDEAL_PRINCIPAL_SCALED : thm
  FRACTIONAL_IDEAL_CLASS_EXISTS : thm
  FRACTIONAL_IDEAL_CLASS_GROUP_EXACT : thm
  FRACTIONAL_IDEAL_CLASS_GROUP : thm
  FRACTIONAL_IDEAL_CLASS_PRIME_SUM : thm
  CLASS_GROUP_SUM_PRIME_CLASSES_EQ_ID : thm
  IDEAL_CLASS_EQ_SUM_PRIME_CLASSES : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFractionalIdeals03 [HolBase] (D : FractionalIdealsDeps) (BFractionalIdeals01 : FractionalIdeals01) (BFractionalIdeals02 : FractionalIdeals02) :
    ExceptT String IO FractionalIdeals03 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INT_ARITH_TAC, MESON_TAC, SET_RULE, SET_TAC, .. } := D
  let { ABELIAN_CLASS_GROUP, CLASS_GROUP, CLASS_GROUP_MUL,
        DEDEKIND_IMP_INTEGRAL_DOMAIN, DEDEKIND_VALUATION_UNIT, DEST_FRAG_ADD,
        EQ_SYM_EQ, EQ_TRANS, EXTENSION, FIELD_FRACTION_NONZERO,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_INV_EQ_0, FIELD_MUL_RINV,
        FIELD_OF_FRACTIONS_IMP_MONOMORPHISM, FIELD_UNIT, FIELD_UNIT_GROUP,
        FINITE_FRAG_SUPPORT, FINITE_SUBSET, FIRST_GROUP_EPIMORPHISM_THEOREM,
        FORALL_IN_GSPEC, FORALL_IN_IMAGE, FRAG_EQ, FREE_ABELIAN_GROUP, FUN_EQ_THM,
        GROUP_DIV, GROUP_EPIMORPHISM, GROUP_HOMOMORPHISM, GROUP_HOMOMORPHISM_DIV,
        GROUP_HOMOMORPHISM_UNIT_GROUP, GROUP_HOMOMORPHISM_ZPOW, GROUP_INV_ID,
        GROUP_ISOMORPHISM, GROUP_MUL_RID, GROUP_SUM, GROUP_SUM_EQ,
        GROUP_SUM_HOMOMORPHIC_IMAGE, GROUP_ZPOW, IDEAL_CLASS_EQ, IDEAL_CLASS_EQ_ID,
        IDEAL_CLASS_IN_CLASS_GROUP, IDEAL_GENERATED_0, IDEAL_GENERATED_EQ_0,
        IDEAL_PROD_EQ_ZERO, IMAGE_CLAUSES, IMAGE_o, INTEGER_GROUP,
        INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_MUL_LCANCEL,
        INTEGRAL_DOMAIN_NONTRIVIAL, INT_ADD_LID, IN_DIFF, IN_ELIM_THM, IN_IDEAL_CLASS,
        IN_IMAGE, IN_SING, .. } := D.core1
  let { ISOMORPHIC_GROUP_SYM, LEFT_IMP_EXISTS_THM, MONO_EXISTS, PRIME_IMP_RING_IDEAL,
        PRINCIPAL_IDEAL_IDEAL_GENERATED_SING, RING_1, RING_HOMOMORPHISM_1,
        RING_HOMOMORPHISM_IN_CARRIER, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IDEAL_PROD, RING_IDEAL_IMP_SUBSET, RING_INV, RING_MONOMORPHISM_EQ_0,
        RING_MONOMORPHISM_INJECTIVE_EQ, RING_MUL, RING_MUL_ASSOC, RING_MUL_LID,
        RING_SETMUL_SING, RING_SPAN_IMAGE_IDEAL_GENERATED, RING_SPAN_IMAGE_MUL,
        RING_SPAN_SETMUL_SPAN, RING_SPAN_SUBSET, RING_UNIT_IN_CARRIER, SING_SUBSET,
        SUBSET, SUBSET_ANTISYM, UNIT_GROUP, frag_support, frag_tybij, group_div,
        group_epimorphism, group_exactness, group_image, group_kernel,
        group_monomorphism, ideal_classes, isomorphic_group, o_DEF, o_THM,
        principal_ideal, .. } := D.core2
  let { FRACTIONAL_IDEAL_CARRIER, FRACTIONAL_IDEAL_IMP_SUBSET, FRACTIONAL_IDEAL_MUL,
        FRACTIONAL_IDEAL_SCALED_IDEAL, RING_IDEAL_IMP_FRACTIONAL_IDEAL, .. } := BFractionalIdeals01
  let { ABELIAN_FRACTIONAL_IDEAL_GROUP, FRACTIONAL_IDEAL_EQ_VALUATION,
        FRACTIONAL_IDEAL_GROUP, FRACTIONAL_IDEAL_PRESCRIBED_VALUATIONS,
        FRACTIONAL_IDEAL_PRINCIPAL, FRACTIONAL_IDEAL_SCALED_IDEAL_COMPARE,
        FRACTIONAL_IDEAL_SCALED_IDEAL_MUL, FRACTIONAL_IDEAL_VALUATION_CARRIER,
        FRACTIONAL_IDEAL_VALUATION_FINITE, FRACTIONAL_IDEAL_VALUATION_IMAGE,
        FRACTIONAL_IDEAL_VALUATION_MUL, FRACTIONAL_IDEAL_VALUATION_PRIME_PRODUCT,
        FRACTIONAL_IDEAL_VALUATION_PRINCIPAL,
        GROUP_HOMOMORPHISM_FRACTIONAL_IDEAL_VALUATION, .. } := BFractionalIdeals02
  -- @@SCOPE END

  let FRACTIONAL_IDEAL_GROUP_FREE_ABELIAN_EXPLICIT ← prove
    r"!r k (h:A->B).
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> ?f. group_isomorphism
                  (fractional_ideal_group (r,k) h,
                   free_abelian_group
                     {P | prime_ideal r P /\ ~(P = {ring_0 r})})
                  f /\
                !J P. fractional_ideal (r,k) h J /\
                      prime_ideal r P /\ ~(P = {ring_0 r})
                      ==> dest_frag (f J) P =
                          fractional_ideal_valuation (r,k) h P J"
    (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"v = \J P. if prime_ideal r P /\ ~(P = {ring_0 r})
              then fractional_ideal_valuation (r,k) (h:A->B) P J else &0") THEN SUBGOAL_THEN (← q r"!J. fractional_ideal (r,k) (h:A->B) J
        ==> dest_frag (mk_frag ((v:(B->bool)->(A->bool)->int) J)) = v J") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN REWRITE_TAC [(← GSYM (← CONJUNCT2 frag_tybij))] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
           ~(fractional_ideal_valuation (r,k) (h:A->B) P J = &0)}") THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_VALUATION_FINITE] THEN EXPAND_TAC "v" THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN EXISTS_TAC (← q r"\J. mk_frag((v:(B->bool)->(A->bool)->int) J)") THEN CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC [] THEN EXPAND_TAC "v" THEN SIMP_TAC []] THEN REWRITE_TAC [GROUP_ISOMORPHISM, GROUP_HOMOMORPHISM] THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_GROUP, FREE_ABELIAN_GROUP] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL [X_GEN_TAC (← q r"J:B->bool") THEN DISCH_TAC THEN ASM_SIMP_TAC [frag_support, IN_ELIM_THM] THEN EXPAND_TAC "v" THEN X_GEN_TAC (← q r"P:A->bool") THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [], MAP_EVERY X_GEN_TAC [(← q r"J1:B->bool"), (← q r"J2:B->bool")] THEN STRIP_TAC THEN REWRITE_TAC [FRAG_EQ, DEST_FRAG_ADD] THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_MUL] THEN EXPAND_TAC "v" THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN BETA_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_VALUATION_MUL, INT_ADD_LID], GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN X_GEN_TAC (← q r"c:(A->bool)frag") THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"J:B->bool") STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC [frag_support, IN_ELIM_THM] THEN EXPAND_TAC "v" THEN X_GEN_TAC (← q r"P:A->bool") THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"dest_frag(c:(A->bool)frag)")] FRACTIONAL_IDEAL_PRESCRIBED_VALUATIONS) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"frag_support(c:(A->bool)frag)") THEN REWRITE_TAC [FINITE_FRAG_SUPPORT, frag_support] THEN SET_TAC [], MATCH_MP_TAC MONO_EXISTS] THEN X_GEN_TAC (← q r"J:B->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [FRAG_EQ] THEN ASM_SIMP_TAC [] THEN EXPAND_TAC "v" THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN BETA_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN UNDISCH_TAC (← q r"!x. x IN frag_support(c:(A->bool)frag)
                     ==> prime_ideal r x /\ ~(x = {ring_0 r})") THEN DISCH_THEN (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN REWRITE_TAC [frag_support, IN_ELIM_THM] THEN ASM_MESON_TAC [], MAP_EVERY X_GEN_TAC [(← q r"J1:B->bool"), (← q r"J2:B->bool")] THEN REWRITE_TAC [FRAG_EQ] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN ASM_SIMP_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"J1:B->bool"), (← q r"J2:B->bool")] FRACTIONAL_IDEAL_EQ_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (← do let c := (← q r"P:A->bool"); pure (fun th => AP_THM th c))) THEN EXPAND_TAC "v" THEN ASM_REWRITE_TAC []])

  let FRACTIONAL_IDEAL_GROUP_FREE_ABELIAN ← prove
    r"!r k (h:A->B).
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> fractional_ideal_group (r,k) h isomorphic_group
            free_abelian_group {P | prime_ideal r P /\ ~(P = {ring_0 r})}"
    (REWRITE_TAC [isomorphic_group] THEN MESON_TAC [FRACTIONAL_IDEAL_GROUP_FREE_ABELIAN_EXPLICIT])

  let GROUP_HOMOMORPHISM_PRINCIPAL_FRACTIONAL_IDEAL ← prove
    r"!r k (h:A->B).
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> group_homomorphism (unit_group k,fractional_ideal_group (r,k) h)
                               (\x. ring_span (r,k) h {x})"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN ASM_SIMP_TAC [GROUP_HOMOMORPHISM, FRACTIONAL_IDEAL_GROUP, FIELD_UNIT_GROUP, SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, IN_DIFF, IN_SING, FRACTIONAL_IDEAL_PRINCIPAL] THEN REWRITE_TAC [UNIT_GROUP] THEN MAP_EVERY X_GEN_TAC [(← q r"x:B"), (← q r"y:B")] THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_SPAN_SETMUL_SPAN, SING_SUBSET, RING_SETMUL_SING, RING_SPAN_SUBSET])

  let GROUP_KERNEL_PRINCIPAL_FRACTIONAL_IDEAL ← prove
    r"!r k (h:A->B).
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> group_kernel (unit_group k,fractional_ideal_group (r,k) h)
                         (\x. ring_span (r,k) h {x}) =
            IMAGE h {u | ring_unit r u}"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN ASM_SIMP_TAC [group_kernel, FRACTIONAL_IDEAL_GROUP, FIELD_UNIT_GROUP] THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, IN_DIFF, IN_SING] THEN X_GEN_TAC (← q r"x:B") THEN ASM_CASES_TAC (← q r"(x:B) IN ring_carrier k") THENL [ALL_TAC, ASM_REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_UNIT_IN_CARRIER, RING_HOMOMORPHISM_IN_CARRIER]] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:B")] DEDEKIND_VALUATION_UNIT) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"ring_span (r,k) (h:A->B) {x}"), (← q r"IMAGE (h:A->B) (ring_carrier r)")] FRACTIONAL_IDEAL_EQ_VALUATION) THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_PRINCIPAL, FRACTIONAL_IDEAL_CARRIER, FRACTIONAL_IDEAL_VALUATION_PRINCIPAL, FRACTIONAL_IDEAL_VALUATION_CARRIER])

  let FRACTIONAL_IDEAL_PRINCIPAL_SCALED ← prove
    r"!r k (h:A->B) x a b.
        field_of_fractions (r,k) h /\ x IN ring_carrier k /\
        a IN ring_carrier r /\ b IN ring_carrier r /\ ring_mul k (h b) x = h a
        ==> IMAGE (ring_mul k (h b)) (ring_span (r,k) h {x}) =
            IMAGE h (ideal_generated r {a})"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN SUBGOAL_THEN (← q r"(h:A->B) b IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM RING_SPAN_IMAGE_MUL), SING_SUBSET, IMAGE_CLAUSES] THEN ASM_SIMP_TAC [(← GSYM RING_SPAN_IMAGE_IDEAL_GENERATED), SING_SUBSET, IMAGE_CLAUSES])

  let FRACTIONAL_IDEAL_CLASS_EXISTS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!(f:B->B) u. (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\
                   s SUBSET u /\ t SUBSET u /\ IMAGE f s = IMAGE f t
                   ==> s = t")
    let r6 ← SET_RULE (← q r"(!x:A. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE (g:A->B) s")
    prove
      r"!r k (h:A->B).
          dedekind_domain r /\ field_of_fractions (r,k) h
          ==> ?f. group_epimorphism (fractional_ideal_group (r,k) h,class_group r)
                                    f /\
                  (!J d j. fractional_ideal (r,k) h J /\
                           d IN ring_carrier r /\ ~(d = ring_0 r) /\
                           ring_ideal r j /\ ~(j = {ring_0 r}) /\
                           IMAGE (ring_mul k (h d)) J = IMAGE h j
                           ==> f J = ideal_class r j) /\
                  group_kernel (fractional_ideal_group (r,k) h,class_group r) f =
                  {ring_span (r,k) h {x} | x | x IN ring_carrier k /\
                                               ~(x = ring_0 k)}"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN (← q r"?f. !J d j. fractional_ideal (r,k) h J /\
                  d IN ring_carrier r /\ ~(d = ring_0 r) /\
                  ring_ideal r j /\ ~(j = {ring_0 r}) /\
                  IMAGE (ring_mul k ((h:A->B) d)) J = IMAGE h j
                  ==> (f:(B->bool)->(A->bool)->bool) J = ideal_class r j") MP_TAC THENL [EXISTS_TAC (← q r"\J. ideal_class r
              (@j. ring_ideal r j /\ ~(j = {ring_0 r}) /\
                   ?d. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                       IMAGE (ring_mul k ((h:A->B) d)) J = IMAGE h j)") THEN REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"?j. ring_ideal r j /\ ~(j = {ring_0 r}) /\
            ?d. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                IMAGE (ring_mul k ((h:A->B) d)) J = IMAGE h j") MP_TAC THENL [EXISTS_TAC (← q r"j:A->bool") THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"d:A") THEN ASM_REWRITE_TAC [], DISCH_THEN (MP_TAC o SELECT_RULE)] THEN ABBREV_TAC (← q r"j0 = @j. ring_ideal r j /\ ~(j = {ring_0 r}) /\
                 ?d. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                     IMAGE (ring_mul k ((h:A->B) d)) J = IMAGE h j") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"d0:A") STRIP_ASSUME_TAC))) THEN ASM_SIMP_TAC [IDEAL_CLASS_EQ] THEN REWRITE_TAC [IN_IDEAL_CLASS] THEN ASM_REWRITE_TAC [] THEN MAP_EVERY EXISTS_TAC [(← q r"d:A"), (← q r"d0:A")] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC FRACTIONAL_IDEAL_SCALED_IDEAL_COMPARE THEN MAP_EVERY EXISTS_TAC [(← q r"k:B ring"), (← q r"h:A->B"), (← q r"J:B->bool")] THEN ASM_MESON_TAC [FRACTIONAL_IDEAL_IMP_SUBSET], MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:(B->bool)->(A->bool)->bool") THEN DISCH_TAC] THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [GROUP_EPIMORPHISM, GROUP_HOMOMORPHISM, group_image] THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_GROUP] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN SUBGOAL_THEN (← q r"!J. fractional_ideal (r,k) (h:A->B) J
          ==> ?d j. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                    ring_ideal r j /\ ~(j = {ring_0 r}) /\
                    IMAGE (ring_mul k (h d)) J = IMAGE h j /\
                    (f:(B->bool)->(A->bool)->bool) J = ideal_class r j") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (MATCH_MP FRACTIONAL_IDEAL_SCALED_IDEAL)) THEN REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC [], ALL_TAC] THEN REPEAT CONJ_TAC THENL [X_GEN_TAC (← q r"J:B->bool") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"J:B->bool"))) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"d:A"), (← q r"j:A->bool")] THEN STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_CLASS_IN_CLASS_GROUP], MAP_EVERY X_GEN_TAC [(← q r"J1:B->bool"), (← q r"J2:B->bool")] THEN STRIP_TAC THEN FIRST_ASSUM (MP_TAC o (SPEC (← q r"J1:B->bool"))) THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"J2:B->bool"))) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"d2:A"), (← q r"j2:A->bool")] THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"d1:A"), (← q r"j1:A->bool")] THEN STRIP_TAC THEN ASM_SIMP_TAC [CLASS_GROUP_MUL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC (← q r"ring_mul r d1 d2:A") THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_MUL, RING_MUL, INTEGRAL_DOMAIN_MUL_EQ_0, RING_IDEAL_IDEAL_PROD, IDEAL_PROD_EQ_ZERO] THEN MATCH_MP_TAC FRACTIONAL_IDEAL_SCALED_IDEAL_MUL THEN ASM_REWRITE_TAC [], MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN X_GEN_TAC (← q r"J:B->bool") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"J:B->bool"))) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"d:A"), (← q r"j:A->bool")] THEN STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_CLASS_IN_CLASS_GROUP], ASM_SIMP_TAC [CLASS_GROUP] THEN REWRITE_TAC [ideal_classes, SUBSET, FORALL_IN_GSPEC] THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN X_GEN_TAC (← q r"j:A->bool") THEN STRIP_TAC THEN EXISTS_TAC (← q r"IMAGE (h:A->B) j") THEN ASM_SIMP_TAC [RING_IDEAL_IMP_FRACTIONAL_IDEAL] THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC (← q r"ring_1 r:A") THEN ASM_SIMP_TAC [RING_IDEAL_IMP_FRACTIONAL_IDEAL, RING_1, INTEGRAL_DOMAIN_NONTRIVIAL] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_1 th)])) THEN REWRITE_TAC [(← GSYM IMAGE_o), o_DEF] THEN MATCH_MP_TAC r6 THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC RING_MUL_LID THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_IDEAL_IMP_SUBSET, SUBSET]], ALL_TAC] THEN REWRITE_TAC [group_kernel] THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_GROUP] THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"J:B->bool") THEN EQ_TAC THENL [STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"J:B->bool"))) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"d:A"), (← q r"j:A->bool")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"principal_ideal r (j:A->bool)") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] IDEAL_CLASS_EQ_ID) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_MESON_TAC [], REWRITE_TAC [principal_ideal, LEFT_IMP_EXISTS_THM]] THEN X_GEN_TAC (← q r"a:A") THEN STRIP_TAC THEN FIRST_X_ASSUM (SUBST_ALL_TAC o (SYM o (checkM (fun th => (do let z5 ← (q r"j:A->bool"); let z4 ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); liftExcept (rand z2)); pure (z4 == z5)))))) THEN SUBGOAL_THEN (← q r"~(a:A = ring_0 r)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC [IDEAL_GENERATED_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"(h:A->B) a IN ring_carrier k /\ h d IN ring_carrier k /\
        ~(h d = ring_0 k) /\ ~(h a = ring_0 k)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_MONOMORPHISM_EQ_0], ALL_TAC] THEN EXISTS_TAC (← q r"ring_mul k (ring_inv k ((h:A->B) d)) (h a)") THEN ASM_SIMP_TAC [RING_MUL, RING_INV, INTEGRAL_DOMAIN_MUL_EQ_0, FIELD_INV_EQ_0] THEN MATCH_MP_TAC r1 THEN MAP_EVERY EXISTS_TAC [(← q r"ring_mul k ((h:A->B) d)"), (← q r"ring_carrier k:B->bool")] THEN REWRITE_TAC [RING_SPAN_SUBSET] THEN REPEAT CONJ_TAC THENL [ASM_MESON_TAC [INTEGRAL_DOMAIN_MUL_LCANCEL], ASM_MESON_TAC [FRACTIONAL_IDEAL_IMP_SUBSET], ASM_REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRACTIONAL_IDEAL_PRINCIPAL_SCALED THEN ASM_SIMP_TAC [RING_MUL, RING_INV] THEN ASM_SIMP_TAC [RING_MUL_ASSOC, RING_INV, FIELD_MUL_RINV, RING_MUL_LID]], DISCH_THEN (X_CHOOSE_THEN (← q r"x:B") STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_PRINCIPAL] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:B")] FIELD_FRACTION_NONZERO) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_span (r,k) (h:A->B) {x}"), (← q r"b:A"), (← q r"ideal_generated r {a:A}")] (← ASSUME (← q r"!J d j. fractional_ideal (r,k) h J /\
                d IN ring_carrier r /\ ~(d = ring_0 r) /\
                ring_ideal r j /\ ~(j = {ring_0 r}) /\
                IMAGE (ring_mul k ((h:A->B) d)) J = IMAGE h j
                ==> (f:(B->bool)->(A->bool)->bool) J = ideal_class r j"))) THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_PRINCIPAL, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, FRACTIONAL_IDEAL_PRINCIPAL_SCALED] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [IDEAL_CLASS_EQ_ID, IDEAL_GENERATED_EQ_0] THEN ASM_MESON_TAC [PRINCIPAL_IDEAL_IDEAL_GENERATED_SING]])

  let FRACTIONAL_IDEAL_CLASS_GROUP_EXACT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(!x:A. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE (g:A->B) s")
    prove
      r"!r k (h:A->B).
          dedekind_domain r /\ field_of_fractions (r,k) h
          ==> ?f. group_monomorphism (unit_group r,unit_group k) h /\
                  group_exactness
                   (unit_group r,unit_group k,fractional_ideal_group (r,k) h)
                   (h,(\x. ring_span (r,k) h {x})) /\
                  group_exactness
                   (unit_group k,fractional_ideal_group (r,k) h,class_group r)
                   ((\x. ring_span (r,k) h {x}),f) /\
                  group_epimorphism (fractional_ideal_group (r,k) h,
                                     class_group r) f /\
                  !j. ring_ideal r j /\ ~(j = {ring_0 r})
                      ==> f(IMAGE h j) = ideal_class r j"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B")] FRACTIONAL_IDEAL_CLASS_EXISTS) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:(B->bool)->(A->bool)->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [group_exactness, GROUP_HOMOMORPHISM_PRINCIPAL_FRACTIONAL_IDEAL, GROUP_KERNEL_PRINCIPAL_FRACTIONAL_IDEAL] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP GROUP_HOMOMORPHISM_UNIT_GROUP)) THEN ASM_REWRITE_TAC [group_monomorphism] THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [group_epimorphism]))) THEN ASM_REWRITE_TAC [group_image, UNIT_GROUP, FIELD_UNIT_GROUP] THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"x:A"), (← q r"y:A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"x:A"), (← q r"y:A")] RING_MONOMORPHISM_INJECTIVE_EQ) THEN ASM_SIMP_TAC [RING_UNIT_IN_CARRIER], GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN ASM_SIMP_TAC [FIELD_UNIT] THEN MESON_TAC [], X_GEN_TAC (← q r"j:A->bool") THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC (← q r"ring_1 r:A") THEN ASM_SIMP_TAC [RING_IDEAL_IMP_FRACTIONAL_IDEAL, RING_1, INTEGRAL_DOMAIN_NONTRIVIAL] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_1 th)])) THEN REWRITE_TAC [(← GSYM IMAGE_o), o_DEF] THEN MATCH_MP_TAC r1 THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC RING_MUL_LID THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_IDEAL_IMP_SUBSET, SUBSET]])

  let FRACTIONAL_IDEAL_CLASS_GROUP ← prove
    r"!r k (h:A->B).
        dedekind_domain r /\ field_of_fractions (r,k) h
        ==> class_group r isomorphic_group
            quotient_group (fractional_ideal_group (r,k) h)
              {ring_span (r,k) h {x} | x | x IN ring_carrier k /\
                                           ~(x = ring_0 k)}"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B")] FRACTIONAL_IDEAL_CLASS_EXISTS) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"f:(B->bool)->(A->bool)->bool") THEN STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ONCE_REWRITE_TAC [ISOMORPHIC_GROUP_SYM] THEN MATCH_MP_TAC FIRST_GROUP_EPIMORPHISM_THEOREM THEN ASM_REWRITE_TAC [])

  let FRACTIONAL_IDEAL_CLASS_PRIME_SUM ← prove
    r"!r k (h:A->B) f t e.
        dedekind_domain r /\ field_of_fractions (r,k) h /\ FINITE t /\
        (!P. P IN t ==> prime_ideal r P /\ ~(P = {ring_0 r})) /\
        group_homomorphism(fractional_ideal_group (r,k) h,class_group r) f /\
        (!j. ring_ideal r j /\ ~(j = {ring_0 r})
             ==> f(IMAGE h j) = ideal_class r j)
        ==> f(group_sum (fractional_ideal_group (r,k) h) t
               (\P. group_zpow (fractional_ideal_group (r,k) h)
                      (IMAGE h P) (e P))) =
            group_sum (class_group r) t
              (\P. group_zpow (class_group r) (ideal_class r P) (e P))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"fractional_ideal_group (r,k) (h:A->B)"), (← q r"class_group (r:A ring)"), (← q r"f:(B->bool)->(A->bool)->bool"), (← q r"t:(A->bool)->bool"), (← q r"\P:A->bool. group_zpow (fractional_ideal_group (r,k) (h:A->B))
                            (IMAGE h P) (e P)")] GROUP_SUM_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [ABELIAN_FRACTIONAL_IDEAL_GROUP, ABELIAN_CLASS_GROUP, DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN SUBGOAL_THEN (← q r"!P. P IN t
        ==> IMAGE (h:A->B) P IN group_carrier(fractional_ideal_group (r,k) h)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_GROUP, IN_ELIM_THM] THEN MATCH_MP_TAC RING_IDEAL_IMP_FRACTIONAL_IDEAL THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN ANTS_TAC THENL [ASM_SIMP_TAC [GROUP_ZPOW] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"t:(A->bool)->bool") THEN ASM_REWRITE_TAC [] THEN SET_TAC [], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC GROUP_SUM_EQ THEN X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN REWRITE_TAC [o_THM] THEN FIRST_ASSUM (fun th => tactic_of do pure (wPart lhand (lhand o rand) (← MATCH_MP GROUP_HOMOMORPHISM_ZPOW th))) THEN ASM_SIMP_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL])

  let CLASS_GROUP_SUM_PRIME_CLASSES_EQ_ID ← prove
    r"!r k (h:A->B) t e.
        dedekind_domain r /\ field_of_fractions (r,k) h /\ FINITE t /\
        (!P. P IN t ==> prime_ideal r P /\ ~(P = {ring_0 r}))
        ==> (group_sum (class_group r) t
               (\P. group_zpow (class_group r) (ideal_class r P) (e P)) =
             group_id (class_group r) <=>
             ?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\
                 !P. prime_ideal r P /\ ~(P = {ring_0 r})
                     ==> dedekind_valuation (r,k) h P x =
                         if P IN t then e P else &0)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B")] FRACTIONAL_IDEAL_CLASS_GROUP_EXACT) THEN ASM_REWRITE_TAC [group_exactness, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"f:(B->bool)->(A->bool)->bool") THEN STRIP_TAC THEN ABBREV_TAC (← q r"D = group_sum (fractional_ideal_group (r,k) (h:A->B)) t
          (\P. group_zpow (fractional_ideal_group (r,k) h)
                 (IMAGE h P) (e P))") THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"f:(B->bool)->(A->bool)->bool"), (← q r"t:(A->bool)->bool"), (← q r"e:(A->bool)->int")] FRACTIONAL_IDEAL_CLASS_PRIME_SUM) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"group_epimorphism (fractional_ideal_group (r,k) (h:A->B),
                                    class_group r) f") THEN SIMP_TAC [group_epimorphism], ASM_REWRITE_TAC []] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"(D:B->bool) IN group_carrier(fractional_ideal_group (r,k) (h:A->B))") ASSUME_TAC THENL [EXPAND_TAC "D" THEN REWRITE_TAC [GROUP_SUM], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"(D:B->bool) IN group_kernel (fractional_ideal_group (r,k) (h:A->B),
                                 class_group r) f") THEN CONJ_TAC THENL [REWRITE_TAC [group_kernel, IN_ELIM_THM] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let l ← (do pure (Prod.fst (← (do let z3 ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (lhand z4)); pure (strip_comb z3))))); (do if ← (do let z6 ← (pure l); pure (is_const z6)) then (do let z9 ← (pure "group_image"); let z8 ← (do pure (Prod.fst (← (do let z7 ← (pure l); liftExcept (dest_const z7))))); pure (z8 == z9)) else pure false)) else pure false))))) THEN ASM_SIMP_TAC [group_image, FIELD_UNIT_GROUP, IN_IMAGE, IN_DIFF, IN_SING] THEN AP_TERM_TAC THEN ABS_TAC THEN ASM_CASES_TAC (← q r"(x:B) IN ring_carrier k") THEN ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"x:B = ring_0 k") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"D:B->bool"), (← q r"ring_span (r,k) (h:A->B) {x}")] FRACTIONAL_IDEAL_EQ_VALUATION) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FRACTIONAL_IDEAL_PRINCIPAL] THEN UNDISCH_TAC (← q r"(D:B->bool) IN group_carrier(fractional_ideal_group (r,k) (h:A->B))") THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_GROUP, IN_ELIM_THM], DISCH_THEN SUBST1_TAC] THEN EXPAND_TAC "D" THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_VALUATION_PRIME_PRODUCT, FRACTIONAL_IDEAL_VALUATION_PRINCIPAL] THEN AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC EQ_SYM_EQ)

  let IDEAL_CLASS_EQ_SUM_PRIME_CLASSES ← prove
    r"!r k (h:A->B) t j x.
        dedekind_domain r /\ field_of_fractions (r,k) h /\ FINITE t /\
        (!P. P IN t ==> prime_ideal r P /\ ~(P = {ring_0 r})) /\
        ring_ideal r j /\ ~(j = {ring_0 r}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k) /\
        (!P. prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN t)
             ==> dedekind_valuation (r,k) h P x = &(ideal_valuation r P j))
        ==> ideal_class r j =
            group_sum (class_group r) t
              (\P. group_zpow (class_group r) (ideal_class r P)
                     (&(ideal_valuation r P j) -
                      dedekind_valuation (r,k) h P x))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B")] FRACTIONAL_IDEAL_CLASS_GROUP_EXACT) THEN ASM_REWRITE_TAC [group_exactness, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"f:(B->bool)->(A->bool)->bool") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"group_homomorphism (fractional_ideal_group (r,k) (h:A->B),
                        class_group r) f") ASSUME_TAC THENL [UNDISCH_TAC (← q r"group_epimorphism (fractional_ideal_group (r,k) (h:A->B),
                                    class_group r) f") THEN SIMP_TAC [group_epimorphism], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"f:(B->bool)->(A->bool)->bool"), (← q r"t:(A->bool)->bool"), (← q r"\P. &(ideal_valuation r P (j:A->bool)) -
                      dedekind_valuation (r,k) (h:A->B) P x")] FRACTIONAL_IDEAL_CLASS_PRIME_SUM) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ABBREV_TAC (← q r"G = fractional_ideal_group (r,k) (h:A->B)") THEN SUBGOAL_THEN (← q r"IMAGE (h:A->B) j IN group_carrier G /\
    ring_span (r,k) h {x} IN group_carrier G") STRIP_ASSUME_TAC THENL [EXPAND_TAC "G" THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_GROUP, IN_ELIM_THM, FRACTIONAL_IDEAL_PRINCIPAL, RING_IDEAL_IMP_FRACTIONAL_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"f(ring_span (r,k) (h:A->B) {x}) = group_id (class_group r)") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"ring_span (r,k) (h:A->B) {x} IN
      group_kernel (G,class_group r) f") MP_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let l ← (do pure (Prod.fst (← (do let z3 ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (lhand z4)); pure (strip_comb z3))))); (do if ← (do let z6 ← (pure l); pure (is_const z6)) then (do let z9 ← (pure "group_image"); let z8 ← (do pure (Prod.fst (← (do let z7 ← (pure l); liftExcept (dest_const z7))))); pure (z8 == z9)) else pure false)) else pure false))))) THEN ASM_SIMP_TAC [group_image, FIELD_UNIT_GROUP, IN_IMAGE, IN_DIFF, IN_SING] THEN EXISTS_TAC (← q r"x:B") THEN ASM_REWRITE_TAC [], SIMP_TAC [group_kernel, IN_ELIM_THM]], ALL_TAC] THEN SUBGOAL_THEN (← q r"group_sum G t
     (\P. group_zpow G (IMAGE (h:A->B) P)
            (&(ideal_valuation r P j) - dedekind_valuation (r,k) h P x)) =
    group_div G (IMAGE h j) (ring_span (r,k) h {x})") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"group_sum G t
                     (\P. group_zpow G (IMAGE (h:A->B) P)
                            (&(ideal_valuation r P j) -
                             dedekind_valuation (r,k) h P x))"), (← q r"group_div G (IMAGE (h:A->B) j) (ring_span (r,k) h {x})")] FRACTIONAL_IDEAL_EQ_VALUATION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"group_sum G t
         (\P. group_zpow G (IMAGE (h:A->B) P)
                (&(ideal_valuation r P j) -
                 dedekind_valuation (r,k) h P x)) IN group_carrier G /\
        group_div G (IMAGE (h:A->B) j) (ring_span (r,k) h {x}) IN
        group_carrier G") MP_TAC THENL [ASM_SIMP_TAC [GROUP_SUM, GROUP_DIV], EXPAND_TAC "G" THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_GROUP] THEN REWRITE_TAC [IN_ELIM_THM]], DISCH_THEN SUBST1_TAC] THEN X_GEN_TAC (← q r"Q:A->bool") THEN STRIP_TAC THEN EXPAND_TAC "G" THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_VALUATION_PRIME_PRODUCT] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"Q:A->bool")] GROUP_HOMOMORPHISM_FRACTIONAL_IDEAL_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (MATCH_MP GROUP_HOMOMORPHISM_DIV)) THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"IMAGE (h:A->B) j"), (← q r"ring_span (r,k) (h:A->B) {x}")])) THEN ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC [group_div, INTEGER_GROUP, FRACTIONAL_IDEAL_VALUATION_IMAGE, FRACTIONAL_IDEAL_VALUATION_PRINCIPAL] THEN COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN INT_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"G:(B->bool)group"), (← q r"class_group (r:A ring)"), (← q r"f:(B->bool)->(A->bool)->bool")] GROUP_HOMOMORPHISM_DIV) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => ASM_SIMP_TAC [th]) THEN REWRITE_TAC [group_div, GROUP_INV_ID] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC GROUP_MUL_RID THEN ASM_SIMP_TAC [IDEAL_CLASS_IN_CLASS_GROUP])

  -- @@RETURN BEGIN
  return { FRACTIONAL_IDEAL_GROUP_FREE_ABELIAN_EXPLICIT,
           FRACTIONAL_IDEAL_GROUP_FREE_ABELIAN,
           GROUP_HOMOMORPHISM_PRINCIPAL_FRACTIONAL_IDEAL,
           GROUP_KERNEL_PRINCIPAL_FRACTIONAL_IDEAL, FRACTIONAL_IDEAL_PRINCIPAL_SCALED,
           FRACTIONAL_IDEAL_CLASS_EXISTS, FRACTIONAL_IDEAL_CLASS_GROUP_EXACT,
           FRACTIONAL_IDEAL_CLASS_GROUP, FRACTIONAL_IDEAL_CLASS_PRIME_SUM,
           CLASS_GROUP_SUM_PRIME_CLASSES_EQ_ID, IDEAL_CLASS_EQ_SUM_PRIME_CLASSES }
  -- @@RETURN END

end HolANT.FractionalIdeals
