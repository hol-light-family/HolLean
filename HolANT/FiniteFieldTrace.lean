/- ========================================================================= -/
/- ANT: Traces of finite fields and separability of free algebras ...      -/
/- ========================================================================= -/
/- File: HolANT/FiniteFieldTrace.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/finite_field_trace.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antfinitefieldtracediff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, Library/isum.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/trace_form.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.FiniteFieldTrace fills them).

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
import HolLibrary.Isum
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
import HolANT.TraceForm

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
open HolANT.TraceForm

namespace HolANT.FiniteFieldTrace

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRA_TRACE_0 ALGEBRA_TRACE_ISOMORPHIC_IMAGE ALGEBRA_TRACE_NORM_IN_CARRIER
   ALGEBRA_TRACE_PROD_RING ALGEBRA_TRACE_SURJECTIVE BASIS_DISCRIMINANT_EQ_0
   BASIS_DISCRIMINANT_NILPOTENT COMAXIMAL_IDEAL_PRODUCT CONTRAPOS_THM EQ_TRANS
   ETA_AX EXISTS_IN_IMAGE EXTENSION FIELD_IMP_INTEGRAL_DOMAIN
   FIELD_IMP_NONTRIVIAL_RING FIELD_NONTRIVIAL FIELD_QUOTIENT_RING
   FIELD_RING_HOMOMORPHISM_MONOMORPHISM FINITE_FIELD_IMP_PERFECT FINITE_IMAGE
   FINITE_IMP_ALGEBRAIC_EXTENSION FINITE_INTEGRAL_DOMAIN_IMP_FIELD
   FINITE_POWERSET FINITE_RING_MONOMORPHIC_PREIMAGE FINITE_SUBSET
   FORALL_IN_IMAGE FREE_BASIS_EXISTS FREE_BASIS_EXTENSION_DEGREE
   FREE_BASIS_HAS_SIZE FREE_BASIS_IMP_FINITE_EXTENSION
   FREE_BASIS_ISOMORPHIC_IMAGE FREE_BASIS_PROD_RING FUN_EQ_THM HAS_SIZE
   IDEAL_PRODUCT_SUBSET INTEGRAL_DOMAIN_QUOTIENT_RING INTER_SUBSET IN_ELIM_THM
   IN_IMAGE IN_INTER IN_INTERS IN_RING_IDEAL_0 IN_RING_IDEAL_ADD
   IN_RING_IDEAL_LMUL IN_SING LEFT_IMP_EXISTS_THM MAXIMAL_IDEAL_COMAXIMAL
   MAXIMAL_IDEAL_COMAXIMAL_MUL MAXIMAL_IDEAL_CORRESPONDENCE
   MAXIMAL_IDEAL_IMP_SUBSET MAXIMAL_IMP_PROPER_IDEAL MAXIMAL_IMP_RING_IDEAL
   MONO_EXISTS NOT_FORALL_THM NOT_IMP PERFECT_FIELD_IMP_SEPARABLE_EXTENSION
   PRIME_IMP_PROPER_IDEAL PRIME_IMP_RING_IDEAL PROPER_IDEAL PSUBSET
   QUOTIENT_RING_0 QUOTIENT_RING_CARRIER RIGHT_AND_EXISTS_THM RING_0 RING_1
   RING_ADD_RZERO RING_COSET_EQ RING_COSET_EQ_IDEAL RING_EPIMORPHISM_RING_COSET
   RING_HOMOMORPHISM_COMPOSE RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_PAIRED RING_HOMOMORPHISM_RING_COSET
   RING_IDEAL_EPIMORPHIC_IMAGE RING_IDEAL_IDEAL_PRODUCT RING_IDEAL_IMP_SUBSET
   RING_IDEAL_INTER RING_ISOMORPHISM_PROD_QUOTIENT_RING RING_MUL RING_MUL_LID
   RING_NILRADICAL RING_SPAN_SELF SIMPLE_IMAGE SUBSET SUBSET_REFL
   field_extension maximal_ideal o_THM radical ring_nilpotent ring_spanning
   trivial_ring : thm)
  deriving Inhabited

/-- What finite_field_trace.ml uses from Session besides theorems. -/
structure FiniteFieldTraceDeps where
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

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)



/- ---------------------------------------------------------------------- -/
/- finite_field_trace.ml phrases from line 48 to 462                      -/
/- ---------------------------------------------------------------------- -/

structure FiniteFieldTrace where
  -- @@FIELDS
  ALGEBRA_TRACE_FINITE_FIELD_NONZERO : thm
  ALGEBRA_TRACE_CHINESE_REMAINDER : thm
  ALGEBRA_TRACE_COMAXIMAL_NONZERO : thm
  ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO : thm
  FINITE_REDUCED_RING_SPLIT : thm
  TRACE_FORM_NONDEGENERATE_FINITE : thm
  BASIS_DISCRIMINANT_EQ_0_FINITE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupFiniteFieldTrace [HolBase] (D : FiniteFieldTraceDeps) :
    ExceptT String IO FiniteFieldTrace := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, RING_RULE, TAUT, .. } := D
  let { ALGEBRA_TRACE_0, ALGEBRA_TRACE_ISOMORPHIC_IMAGE, ALGEBRA_TRACE_NORM_IN_CARRIER,
        ALGEBRA_TRACE_PROD_RING, ALGEBRA_TRACE_SURJECTIVE, BASIS_DISCRIMINANT_EQ_0,
        BASIS_DISCRIMINANT_NILPOTENT, COMAXIMAL_IDEAL_PRODUCT, CONTRAPOS_THM, EQ_TRANS,
        ETA_AX, EXISTS_IN_IMAGE, EXTENSION, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_IMP_NONTRIVIAL_RING, FIELD_NONTRIVIAL, FIELD_QUOTIENT_RING,
        FIELD_RING_HOMOMORPHISM_MONOMORPHISM, FINITE_FIELD_IMP_PERFECT, FINITE_IMAGE,
        FINITE_IMP_ALGEBRAIC_EXTENSION, FINITE_INTEGRAL_DOMAIN_IMP_FIELD,
        FINITE_POWERSET, FINITE_RING_MONOMORPHIC_PREIMAGE, FINITE_SUBSET,
        FORALL_IN_IMAGE, FREE_BASIS_EXISTS, FREE_BASIS_EXTENSION_DEGREE,
        FREE_BASIS_HAS_SIZE, FREE_BASIS_IMP_FINITE_EXTENSION,
        FREE_BASIS_ISOMORPHIC_IMAGE, FREE_BASIS_PROD_RING, FUN_EQ_THM, HAS_SIZE,
        IDEAL_PRODUCT_SUBSET, INTEGRAL_DOMAIN_QUOTIENT_RING, INTER_SUBSET, IN_ELIM_THM,
        IN_IMAGE, IN_INTER, IN_INTERS, IN_RING_IDEAL_0, IN_RING_IDEAL_ADD,
        IN_RING_IDEAL_LMUL, IN_SING, LEFT_IMP_EXISTS_THM, MAXIMAL_IDEAL_COMAXIMAL,
        MAXIMAL_IDEAL_COMAXIMAL_MUL, MAXIMAL_IDEAL_CORRESPONDENCE,
        MAXIMAL_IDEAL_IMP_SUBSET, MAXIMAL_IMP_PROPER_IDEAL, MAXIMAL_IMP_RING_IDEAL,
        MONO_EXISTS, NOT_FORALL_THM, NOT_IMP, PERFECT_FIELD_IMP_SEPARABLE_EXTENSION,
        PRIME_IMP_PROPER_IDEAL, PRIME_IMP_RING_IDEAL, PROPER_IDEAL, PSUBSET,
        QUOTIENT_RING_0, QUOTIENT_RING_CARRIER, RIGHT_AND_EXISTS_THM, RING_0, RING_1,
        RING_ADD_RZERO, RING_COSET_EQ, RING_COSET_EQ_IDEAL,
        RING_EPIMORPHISM_RING_COSET, RING_HOMOMORPHISM_COMPOSE,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_PAIRED,
        RING_HOMOMORPHISM_RING_COSET, RING_IDEAL_EPIMORPHIC_IMAGE,
        RING_IDEAL_IDEAL_PRODUCT, RING_IDEAL_IMP_SUBSET, RING_IDEAL_INTER,
        RING_ISOMORPHISM_PROD_QUOTIENT_RING, RING_MUL, RING_MUL_LID, RING_NILRADICAL,
        RING_SPAN_SELF, SIMPLE_IMAGE, SUBSET, SUBSET_REFL, field_extension,
        maximal_ideal, o_THM, radical, ring_nilpotent, ring_spanning, trivial_ring, .. } := D.core1
  -- @@SCOPE END

  let ALGEBRA_TRACE_FINITE_FIELD_NONZERO ← prove
    r"!k:A ring l:B ring h n g.
        field k /\ field l /\ FINITE(ring_carrier l) /\
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g
        ==> ?x. x IN ring_carrier l /\
                ~(algebra_trace (k,l) h x = ring_0 k)"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"field_extension(k,l) (h:A->B)") ASSUME_TAC THENL [ASM_SIMP_TAC [field_extension, FIELD_RING_HOMOMORPHISM_MONOMORPHISM, FIELD_IMP_NONTRIVIAL_RING], ALL_TAC] THEN SUBGOAL_THEN (← q r"finite_extension(k,l) (h:A->B) /\ FINITE(ring_carrier(k:A ring))") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [FREE_BASIS_IMP_FINITE_EXTENSION, FINITE_RING_MONOMORPHIC_PREIMAGE, field_extension], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring")] ALGEBRA_TRACE_SURJECTIVE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC PERFECT_FIELD_IMP_SEPARABLE_EXTENSION THEN ASM_SIMP_TAC [FINITE_FIELD_IMP_PERFECT, FINITE_IMP_ALGEBRAIC_EXTENSION], ALL_TAC] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"ring_1 k:A")) o (REWRITE_RULE [EXTENSION, IN_IMAGE]))) THEN REWRITE_TAC [RING_1] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC [FIELD_NONTRIVIAL])

  let ALGEBRA_TRACE_CHINESE_REMAINDER ← prove
    r"!k:A ring l:B ring h n g j1 j2 n1 g1 n2 g2 z.
        field k /\ ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
        ring_ideal l j1 /\ ring_ideal l j2 /\
        ring_setadd l j1 j2 = ring_carrier l /\ j1 INTER j2 = {ring_0 l} /\
        free_basis (k,quotient_ring l j1) (ring_coset l j1 o h) n1 g1 /\
        free_basis (k,quotient_ring l j2) (ring_coset l j2 o h) n2 g2 /\
        z IN ring_carrier l
        ==> algebra_trace (k,l) h z =
            ring_add k
             (algebra_trace (k,quotient_ring l j1) (ring_coset l j1 o h)
                (ring_coset l j1 z))
             (algebra_trace (k,quotient_ring l j2) (ring_coset l j2 o h)
                (ring_coset l j2 z))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"j1:B->bool"), (← q r"j2:B->bool")] RING_ISOMORPHISM_PROD_QUOTIENT_RING) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ABBREV_TAC (← q r"f = \x:B. ring_coset l j1 x,ring_coset l j2 x") THEN SUBGOAL_THEN (← q r"ring_homomorphism(k,quotient_ring l j1) (ring_coset l j1 o (h:A->B)) /\
    ring_homomorphism(k,quotient_ring l j2) (ring_coset l j2 o h)") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"l:B ring") THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"(f:B->(B->bool)#(B->bool)) o (h:A->B) =
    (\a. (ring_coset l j1 o h) a,(ring_coset l j2 o h) a)") ASSUME_TAC THENL [EXPAND_TAC "f" THEN REWRITE_TAC [FUN_EQ_THM, o_THM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"quotient_ring l (j1:B->bool)"), (← q r"quotient_ring l (j2:B->bool)"), (← q r"ring_coset l j1 o (h:A->B)"), (← q r"ring_coset l j2 o (h:A->B)"), (← q r"n1:num"), (← q r"n2:num"), (← q r"g1:num->B->bool"), (← q r"g2:num->B->bool")] FREE_BASIS_PROD_RING) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"prod_ring (quotient_ring l j1) (quotient_ring (l:B ring) j2)"), (← q r"h:A->B"), (← q r"f:B->(B->bool)#(B->bool)"), (← q r"n:num"), (← q r"g:num->B")] FREE_BASIS_ISOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_homomorphism
     (k,prod_ring (quotient_ring l j1) (quotient_ring l j2))
     (\a. (ring_coset l j1 o (h:A->B)) a,(ring_coset l j2 o h) a)") ASSUME_TAC THENL [ASM_REWRITE_TAC [RING_HOMOMORPHISM_PAIRED, ETA_AX], ALL_TAC] THEN SUBGOAL_THEN (← q r"n:num = n1 + n2") SUBST_ALL_TAC THENL [TRANS_TAC EQ_TRANS (← q r"extension_degree
       (k:A ring,prod_ring (quotient_ring l j1) (quotient_ring l j2))
       (\a. (ring_coset l j1 o (h:A->B)) a,(ring_coset l j2 o h) a)") THEN CONJ_TAC THENL [ALL_TAC, CONV_TAC SYM_CONV] THEN MATCH_MP_TAC FREE_BASIS_EXTENSION_DEGREE THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (fun th => tactic_of do pure (EXISTS_TAC (← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); liftExcept (rand z1))) THEN ACCEPT_TAC th)), ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"prod_ring (quotient_ring l j1) (quotient_ring (l:B ring) j2)"), (← q r"h:A->B"), (← q r"f:B->(B->bool)#(B->bool)"), (← q r"n1 + n2:num"), (← q r"g:num->B"), (← q r"z:B")] ALGEBRA_TRACE_ISOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN EXPAND_TAC "f" THEN BETA_TAC THEN MATCH_MP_TAC ALGEBRA_TRACE_PROD_RING THEN MAP_EVERY EXISTS_TAC [(← q r"n1:num"), (← q r"n2:num"), (← q r"g1:num->B->bool"), (← q r"g2:num->B->bool")] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THEN MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC (← q r"l:B ring") THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET])

  let ALGEBRA_TRACE_COMAXIMAL_NONZERO ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r")
    prove
      r"!k:A ring l:B ring h n g m j.
          field k /\ FINITE(ring_carrier k) /\
          ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
          maximal_ideal l m /\ ring_ideal l j /\
          ring_setadd l m j = ring_carrier l /\ m INTER j = {ring_0 l}
          ==> ?y. y IN j /\ ~(algebra_trace (k,l) h y = ring_0 k)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"FINITE(ring_carrier(l:B ring))") ASSUME_TAC THENL [ASM_MESON_TAC [FREE_BASIS_HAS_SIZE, HAS_SIZE], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i:B->bool.
          ring_ideal l i
          ==> FINITE(ring_carrier(quotient_ring l i)) /\
              ring_homomorphism(k,quotient_ring l i)
                               (ring_coset l i o (h:A->B)) /\
              ?n' g'. free_basis (k,quotient_ring l i) (ring_coset l i o h) n' g'") (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"m:B->bool") th) THEN MP_TAC (← SPEC (← q r"j:B->bool") th))) THENL [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC r1 THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, SIMPLE_IMAGE, FINITE_IMAGE], MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"l:B ring") THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET], STRIP_TAC THEN EXISTS_TAC (← q r"extension_degree (k,quotient_ring l i) (ring_coset l i o (h:A->B))") THEN MATCH_MP_TAC FREE_BASIS_EXISTS THEN EXISTS_TAC (← q r"ring_carrier(quotient_ring l (i:B->bool))") THEN ASM_REWRITE_TAC [ring_spanning, RING_SPAN_SELF, SUBSET_REFL]], ASM_REWRITE_TAC [RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM]] THEN MAP_EVERY X_GEN_TAC [(← q r"n2:num"), (← q r"g2:num->B->bool")] THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"n1:num"), (← q r"g1:num->B->bool")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"quotient_ring l (m:B->bool)"), (← q r"ring_coset l m o (h:A->B)"), (← q r"n1:num"), (← q r"g1:num->B->bool")] ALGEBRA_TRACE_FINITE_FIELD_NONZERO) THEN ASM_SIMP_TAC [FIELD_QUOTIENT_RING, QUOTIENT_RING_CARRIER, SIMPLE_IMAGE] THEN REWRITE_TAC [EXISTS_IN_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"w:B") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:B->bool"), (← q r"j:B->bool"), (← q r"ring_1 l:B"), (← q r"w:B")] MAXIMAL_IDEAL_COMAXIMAL_MUL) THEN ASM_REWRITE_TAC [RING_1] THEN ANTS_TAC THENL [ASM_MESON_TAC [MAXIMAL_IMP_PROPER_IDEAL, PROPER_IDEAL], ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"y:B") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"n:num"), (← q r"g:num->B"), (← q r"m:B->bool"), (← q r"j:B->bool"), (← q r"n1:num"), (← q r"g1:num->B->bool"), (← q r"n2:num"), (← q r"g2:num->B->bool"), (← q r"y:B")] ALGEBRA_TRACE_CHINESE_REMAINDER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"ring_coset l m y = ring_coset l m (w:B) /\
      ring_coset l j y = ring_0(quotient_ring l (j:B->bool))") (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_SIMP_TAC [RING_COSET_EQ, QUOTIENT_RING_0, RING_COSET_EQ_IDEAL] THEN ASM_MESON_TAC [RING_MUL_LID], ALL_TAC] THEN SUBGOAL_THEN (← q r"algebra_trace (k,quotient_ring l j) (ring_coset l j o (h:A->B))
                      (ring_0(quotient_ring l j)) = ring_0 k") SUBST1_TAC THENL [ASM_SIMP_TAC [ALGEBRA_TRACE_0], ASM_SIMP_TAC [RING_ADD_RZERO, ALGEBRA_TRACE_NORM_IN_CARRIER]])

  let ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q /\ r) ==> p /\ q /\ r")
    let r5 ← RING_RULE (← q r"x = ring_add (r:A ring) (ring_sub r x u) u")
    prove
      r"!(f:K ring) (r:A ring) g n G P Q.
          field f /\ FINITE(ring_carrier f) /\
          ring_homomorphism(f,quotient_ring r (P INTER Q)) g /\
          free_basis (f,quotient_ring r (P INTER Q)) g n G /\
          maximal_ideal r P /\ ring_ideal r Q /\
          ring_setadd r P Q = ring_carrier r
          ==> ?x. x IN Q /\
                  ~(algebra_trace (f,quotient_ring r (P INTER Q)) g
                      (ring_coset r (P INTER Q) x) = ring_0 f)"
      (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"j = (P:A->bool) INTER Q") THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"ring_ideal r (j:A->bool) /\ j SUBSET P /\ j SUBSET Q") STRIP_ASSUME_TAC THENL [EXPAND_TAC "j" THEN ASM_SIMP_TAC [RING_IDEAL_INTER, INTER_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. ring_ideal r i /\ j SUBSET i
          ==> {x | x IN ring_carrier r /\
                   ring_coset r j x IN IMAGE (ring_coset r j) i} = (i:A->bool)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:A") THEN REWRITE_TAC [IN_ELIM_THM, IN_IMAGE] THEN EQ_TAC THENL [ALL_TAC, ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET]] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"u:A") STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"(u:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sub r x u IN (i:A->bool)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_COSET_EQ, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"x = ring_add r (ring_sub r x u) (u:A)") SUBST1_TAC THENL [MATCH_MP_TAC r5 THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [IN_RING_IDEAL_ADD]], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP RING_EPIMORPHISM_RING_COSET) o (checkM (fun th => (do let z4 ← (q r"ring_ideal r (j:A->bool)"); let z3 ← (do let z2 ← (pure th); pure (concl z2)); pure (z3 == z4)))))) THEN SUBGOAL_THEN (← q r"ring_ideal (quotient_ring r j) (IMAGE (ring_coset r j) (P:A->bool)) /\
      ring_ideal (quotient_ring r j) (IMAGE (ring_coset r j) (Q:A->bool))") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC RING_IDEAL_EPIMORPHIC_IMAGE THEN EXISTS_TAC (← q r"r:A ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"f:K ring"), (← q r"quotient_ring r (j:A->bool)"), (← q r"g:K->(A->bool)"), (← q r"n:num"), (← q r"G:num->(A->bool)"), (← q r"IMAGE (ring_coset r j) (P:A->bool)"), (← q r"IMAGE (ring_coset r j) (Q:A->bool)")] ALGEBRA_TRACE_COMAXIMAL_NONZERO) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [MATCH_MP_TAC r1 THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"quotient_ring r (j:A->bool)"), (← q r"ring_coset r (j:A->bool)"), (← q r"P:A->bool"), (← q r"IMAGE (ring_coset r j) (P:A->bool)")] MAXIMAL_IDEAL_CORRESPONDENCE) THEN ASM_SIMP_TAC [], DISCH_TAC] THEN ASM_SIMP_TAC [MAXIMAL_IDEAL_COMAXIMAL] THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"ring_setadd r P Q = ring_carrier(r:A ring)") THEN ASM_SIMP_TAC [MAXIMAL_IDEAL_COMAXIMAL] THEN REWRITE_TAC [CONTRAPOS_THM, SUBSET, FORALL_IN_IMAGE] THEN DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) THEN ASM_SIMP_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"z:A->bool") THEN REWRITE_TAC [IN_INTER, IN_SING] THEN ASM_SIMP_TAC [QUOTIENT_RING_0] THEN EQ_TAC THENL [REWRITE_TAC [IN_IMAGE] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"x:A") STRIP_ASSUME_TAC) (X_CHOOSE_THEN (← q r"y:A") STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"(x:A) IN Q") ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"Q:A->bool"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) THEN REWRITE_TAC [IN_ELIM_THM, IN_IMAGE] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], EXISTS_TAC (← q r"y:A") THEN ASM_MESON_TAC []], UNDISCH_THEN (← q r"z = ring_coset r j (x:A)") SUBST1_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ASM_SIMP_TAC [RING_COSET_EQ_IDEAL] THEN EXPAND_TAC "j" THEN ASM_REWRITE_TAC [IN_INTER]]], DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IN_IMAGE] THEN CONJ_TAC THEN EXISTS_TAC (← q r"ring_0 r:A") THEN ASM_SIMP_TAC [IN_RING_IDEAL_0] THEN CONV_TAC SYM_CONV THEN ASM_SIMP_TAC [RING_COSET_EQ_IDEAL, RING_0, IN_RING_IDEAL_0]], ALL_TAC] THEN REWRITE_TAC [EXISTS_IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [])

  let FINITE_REDUCED_RING_SPLIT ← prove
    r"!l:B ring x.
        FINITE(ring_carrier l) /\
        (!z. ring_nilpotent l z ==> z = ring_0 l) /\
        x IN ring_carrier l /\ ~(x = ring_0 l)
        ==> ?m j. maximal_ideal l m /\ ~(x IN m) /\ ring_ideal l j /\
                  ring_setadd l m j = ring_carrier l /\
                  m INTER j = {ring_0 l}"
    (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN DISCH_THEN (fun red => tactic_of do pure (SUBGOAL_THEN (← q r"!z:B. z IN INTERS {p | prime_ideal l p} ==> z = ring_0 l") (LABEL_TAC "nil") THENL [MP_TAC (← ISPEC (← q r"l:B ring") RING_NILRADICAL) THEN COND_CASES_TAC THENL [ASM_MESON_TAC [trivial_ring, IN_SING], ALL_TAC] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [radical, IN_ELIM_THM, IN_SING] THEN MESON_TAC [red, ring_nilpotent], ALL_TAC])) THEN SUBGOAL_THEN (← q r"!p. prime_ideal l p ==> maximal_ideal (l:B ring) p") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← MATCH_MP FIELD_QUOTIENT_RING th))])) THEN MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_IMP_FIELD THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_QUOTIENT_RING, QUOTIENT_RING_CARRIER, SIMPLE_IMAGE, FINITE_IMAGE], ALL_TAC] THEN SUBGOAL_THEN (← q r"?p. prime_ideal l p /\ ~((x:B) IN p)") STRIP_ASSUME_TAC THENL [USE_THEN "nil" (MP_TAC o (SPEC (← q r"x:B"))) THEN REWRITE_TAC [IN_INTERS, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"s = {q | maximal_ideal l q /\ ~(q = (p:B->bool))}") THEN SUBGOAL_THEN (← q r"FINITE(s:(B->bool)->bool) /\
    !q. q IN s ==> ring_ideal l q /\ ring_setadd l p q = ring_carrier l") STRIP_ASSUME_TAC THENL [EXPAND_TAC "s" THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{t:B->bool | t SUBSET ring_carrier l}") THEN ASM_SIMP_TAC [FINITE_POWERSET, SUBSET, IN_ELIM_THM, MAXIMAL_IDEAL_IMP_SUBSET], ALL_TAC] THEN X_GEN_TAC (← q r"q:B->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC [MAXIMAL_IMP_RING_IDEAL, MAXIMAL_IDEAL_COMAXIMAL] THEN ASM_MESON_TAC [maximal_ideal, PSUBSET, PRIME_IMP_PROPER_IDEAL], ALL_TAC] THEN MAP_EVERY EXISTS_TAC [(← q r"p:B->bool"), (← q r"ideal_product l s (\q:B->bool. q)")] THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_PRODUCT, COMAXIMAL_IDEAL_PRODUCT, PRIME_IMP_RING_IDEAL] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"z:B") THEN REWRITE_TAC [IN_INTER, IN_SING] THEN EQ_TAC THENL [STRIP_TAC THEN USE_THEN "nil" MATCH_MP_TAC THEN REWRITE_TAC [IN_INTERS, IN_ELIM_THM] THEN X_GEN_TAC (← q r"q:B->bool") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"q:B->bool = p") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"s:(B->bool)->bool"), (← q r"\q:B->bool. q"), (← q r"q:B->bool")] IDEAL_PRODUCT_SUBSET) THEN ANTS_TAC THENL [ASM_SIMP_TAC [] THEN EXPAND_TAC "s" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [], REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC []], DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [IN_RING_IDEAL_0, RING_IDEAL_IDEAL_PRODUCT, PRIME_IMP_RING_IDEAL]])

  let TRACE_FORM_NONDEGENERATE_FINITE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r")
    prove
      r"!k:A ring l:B ring h n g x.
          field k /\ FINITE(ring_carrier k) /\
          ring_homomorphism(k,l) h /\ free_basis (k,l) h n g /\
          (!z. ring_nilpotent l z ==> z = ring_0 l) /\
          x IN ring_carrier l /\ ~(x = ring_0 l)
          ==> ?y. y IN ring_carrier l /\
                  ~(algebra_trace (k,l) h (ring_mul l x y) = ring_0 k)"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"FINITE(ring_carrier(l:B ring))") ASSUME_TAC THENL [ASM_MESON_TAC [FREE_BASIS_HAS_SIZE, HAS_SIZE], ALL_TAC] THEN UNDISCH_TAC (← q r"!z:B. ring_nilpotent l z ==> z = ring_0 l") THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← MATCH_MP FINITE_REDUCED_RING_SPLIT (← CONJ (← ASSUME (← q r"FINITE(ring_carrier(l:B ring))")) (← CONJ th (← CONJ (← ASSUME (← q r"(x:B) IN ring_carrier l")) (← ASSUME (← q r"~(x:B = ring_0 l)")))))))) THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"m:B->bool"), (← q r"j:B->bool")] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"!i:B->bool.
          ring_ideal l i
          ==> FINITE(ring_carrier(quotient_ring l i)) /\
              ring_homomorphism(k,quotient_ring l i)
                               (ring_coset l i o (h:A->B)) /\
              ?n' g'. free_basis (k,quotient_ring l i) (ring_coset l i o h) n' g'") (fun th => tactic_of do pure (MP_TAC (← SPEC (← q r"m:B->bool") th) THEN MP_TAC (← SPEC (← q r"j:B->bool") th))) THENL [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC r1 THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, SIMPLE_IMAGE, FINITE_IMAGE], MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"l:B ring") THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET], STRIP_TAC THEN EXISTS_TAC (← q r"extension_degree (k,quotient_ring l i) (ring_coset l i o (h:A->B))") THEN MATCH_MP_TAC FREE_BASIS_EXISTS THEN EXISTS_TAC (← q r"ring_carrier(quotient_ring l (i:B->bool))") THEN ASM_REWRITE_TAC [ring_spanning, RING_SPAN_SELF, SUBSET_REFL]], ASM_REWRITE_TAC [RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM]] THEN MAP_EVERY X_GEN_TAC [(← q r"n2:num"), (← q r"g2:num->B->bool")] THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"n1:num"), (← q r"g1:num->B->bool")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"quotient_ring l (m:B->bool)"), (← q r"ring_coset l m o (h:A->B)"), (← q r"n1:num"), (← q r"g1:num->B->bool")] ALGEBRA_TRACE_FINITE_FIELD_NONZERO) THEN ASM_SIMP_TAC [FIELD_QUOTIENT_RING, QUOTIENT_RING_CARRIER, SIMPLE_IMAGE] THEN REWRITE_TAC [EXISTS_IN_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"w:B") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:B->bool"), (← q r"j:B->bool"), (← q r"x:B"), (← q r"w:B")] MAXIMAL_IDEAL_COMAXIMAL_MUL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"y:B") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(y:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN EXISTS_TAC (← q r"y:B") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"n:num"), (← q r"g:num->B"), (← q r"m:B->bool"), (← q r"j:B->bool"), (← q r"n1:num"), (← q r"g1:num->B->bool"), (← q r"n2:num"), (← q r"g2:num->B->bool"), (← q r"ring_mul l x y:B")] ALGEBRA_TRACE_CHINESE_REMAINDER) THEN ASM_SIMP_TAC [RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"ring_coset l m (ring_mul l x y) = ring_coset l m (w:B) /\
      ring_coset l j (ring_mul l x y) = ring_0(quotient_ring l (j:B->bool))") (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_SIMP_TAC [RING_COSET_EQ, QUOTIENT_RING_0, RING_COSET_EQ_IDEAL, RING_MUL, IN_RING_IDEAL_LMUL], ALL_TAC] THEN SUBGOAL_THEN (← q r"algebra_trace (k,quotient_ring l j) (ring_coset l j o (h:A->B))
                      (ring_0(quotient_ring l j)) = ring_0 k") SUBST1_TAC THENL [ASM_SIMP_TAC [ALGEBRA_TRACE_0], ASM_SIMP_TAC [RING_ADD_RZERO, ALGEBRA_TRACE_NORM_IN_CARRIER]])

  let BASIS_DISCRIMINANT_EQ_0_FINITE ← prove
    r"!k:A ring l:B ring h n g.
        field k /\ FINITE(ring_carrier k) /\
        ring_homomorphism(k,l) h /\ free_basis (k,l) h n g
        ==> (basis_discriminant (k,l) h n g = ring_0 k <=>
             ?x. ring_nilpotent l x /\ ~(x = ring_0 l))"
    (REPEAT STRIP_TAC THEN EQ_TAC THENL [ASM_SIMP_TAC [BASIS_DISCRIMINANT_EQ_0] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"x:B") STRIP_ASSUME_TAC) THEN REWRITE_TAC [(← GSYM NOT_IMP), (← GSYM NOT_FORALL_THM)] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"n:num"), (← q r"g:num->B"), (← q r"x:B")] TRACE_FORM_NONDEGENERATE_FINITE) THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], STRIP_TAC THEN MATCH_MP_TAC BASIS_DISCRIMINANT_NILPOTENT THEN EXISTS_TAC (← q r"x:B") THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]])

  -- @@RETURN BEGIN
  return { ALGEBRA_TRACE_FINITE_FIELD_NONZERO, ALGEBRA_TRACE_CHINESE_REMAINDER,
           ALGEBRA_TRACE_COMAXIMAL_NONZERO, ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO,
           FINITE_REDUCED_RING_SPLIT, TRACE_FORM_NONDEGENERATE_FINITE,
           BASIS_DISCRIMINANT_EQ_0_FINITE }
  -- @@RETURN END

end HolANT.FiniteFieldTrace
