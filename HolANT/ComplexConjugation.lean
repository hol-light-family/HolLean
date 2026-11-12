/- ========================================================================= -/
/- ANT: Complex conjugation as an element of order 2 of the absolute ...   -/
/- ========================================================================= -/
/- File: HolANT/ComplexConjugation.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/complex_conjugation.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antcomplexconjugationdiff; the rest is by hand.  Its `needs` closure is
  Library/wo.ml, Library/card.ml, Library/matroids.ml, Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/ringtheory.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/nf_valuation.ml, ANT/prime_split.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/integrality.ml, Library/ring_groups.ml, ANT/fingen_group.ml, Multivariate/misc.ml, Multivariate/metric.ml, Multivariate/homology.ml, Multivariate/vectors.ml, Multivariate/determinants.ml, Multivariate/topology.ml, Multivariate/convex.ml, Multivariate/paths.ml, Multivariate/polytope.ml, Multivariate/degree.ml, Multivariate/derivatives.ml, Multivariate/integration.ml, Multivariate/measure.ml, Multivariate/complex_algebra.ml, Multivariate/complexes.ml, Multivariate/canal.ml, Multivariate/transcendentals.ml, Multivariate/realanalysis.ml, Multivariate/moretop.ml, Multivariate/cauchy.ml, Multivariate/complex_ring.ml, Multivariate/complex_field.ml, ANT/complex_embeddings.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.ComplexConjugation fills them).

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
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.Products
import HolANT.Algmisc
import HolANT.Integral
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.IdealArith
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.NfValuation
import HolANT.PrimeSplit
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.Integrality
import HolLibrary.RingGroups
import HolANT.FingenGroup
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
import HolMultiLib.RealAnalysis
import HolMultiLib.MoreTop
import HolMultiLib.Cauchy
import HolMultiLib.ComplexRing
import HolMultiLib.ComplexField
import HolANT.ComplexEmbeddings

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc
open HolANT.Integral
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.IdealArith
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.NfValuation
open HolANT.PrimeSplit
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.Integrality
open HolANT.FingenGroup
open HolANT.ComplexEmbeddings

namespace HolANT.ComplexConjugation

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD
   ALGEBRAICALLY_CLOSED_FIELD_NTH_ROOT ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION
   ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM ARITH_EQ ARTIN_FIXED_FIELD CARD_CLAUSES
   CNJ_ADD CNJ_CNJ CNJ_CX CNJ_MUL CNJ_NEG COMPLEX_RING_CLAUSES COMPLEX_RING_POW
   CX_INJ CX_NEG CX_POW EXTENSION FIELD_COMPLEX_RING
   FIELD_HOMOMORPHISM_IMP_MONOMORPHISM FIELD_IMP_INTEGRAL_DOMAIN FINITE_EMPTY
   FINITE_INSERT FORALL_IN_IMAGE FORALL_IN_INSERT FUN_EQ_THM GALOIS_GROUP
   GALOIS_GROUP_PERMUTES GALOIS_GROUP_RING_AUTOMORPHISM
   GALOIS_GROUP_RING_HOMOMORPHISM GROUP_ELEMENT_ORDER_EQ_2 GROUP_POW_2 INVERSE_I
   INVERSE_UNIQUE_o IN_ELIM_THM IN_FIXED_FIELD IN_IMAGE IN_INSERT I_O_ID I_THM
   MONO_EXISTS NORMAL_EXTENSION_IMAGES_EQ NORMAL_IMP_FIELD_EXTENSION
   NOT_FORALL_THM NOT_IMP NOT_IN_EMPTY PERMUTES_I PERMUTES_INVOLUTION
   PERMUTES_IN_IMAGE PRIME_SUBFIELD_HOMOMORPHISM_EXISTS PRIME_SUBFIELD_MINIMAL
   REAL_CNJ REAL_EXISTS REAL_LE_SQUARE REAL_POW_2 RING_0 RING_1 RING_ADD
   RING_AUTOMORPHISM_I RING_CARRIER_SUBFIELD_GENERATED_SUBSET
   RING_CHAR_COMPLEX_RING RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_1
   RING_HOMOMORPHISM_ADD RING_HOMOMORPHISM_CNJ RING_HOMOMORPHISM_COMPOSE
   RING_HOMOMORPHISM_I RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_NEG
   RING_HOMOMORPHISM_POW RING_MONOMORPHISM_INJECTIVE_EQ RING_MUL RING_NEG
   SUBFIELD_OF_FIXED_FIELD SUBFIELD_OF_HOMOMORPHIC_EQUALITIES SUBSET
   SYMMETRIC_GROUP field_extension o_THM permutes ring_automorphism
   ring_endomorphism ring_homomorphism ring_isomorphism ring_isomorphisms
   subgroup_of : thm)
  deriving Inhabited

/-- What complex_conjugation.ml uses from Session besides theorems. -/
structure ComplexConjugationDeps where
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
  SELECT_CONV : ioconv
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
/- complex_conjugation.ml phrases from line 47 to 245                     -/
/- ---------------------------------------------------------------------- -/

structure ComplexConjugation where
  -- @@FIELDS
  GALOIS_GROUP_COMPLEX_CONJUGATION : thm
  COMPLEX_CONJUGATION_REAL_SUBFIELD : thm
  ALGEBRAIC_CLOSURE_COMPLEX_CONJUGATION : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupComplexConjugation [HolBase] (D : ComplexConjugationDeps) :
    ExceptT String IO ComplexConjugation := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, NUM_REDUCE_CONV, REAL_ARITH_TAC,
        REAL_RAT_REDUCE_CONV, SELECT_CONV, TAUT, .. } := D
  let { ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING, ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD,
        ALGEBRAICALLY_CLOSED_FIELD_NTH_ROOT, ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION,
        ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM, ARITH_EQ, ARTIN_FIXED_FIELD,
        CARD_CLAUSES, CNJ_ADD, CNJ_CNJ, CNJ_CX, CNJ_MUL, CNJ_NEG, COMPLEX_RING_CLAUSES,
        COMPLEX_RING_POW, CX_INJ, CX_NEG, CX_POW, EXTENSION, FIELD_COMPLEX_RING,
        FIELD_HOMOMORPHISM_IMP_MONOMORPHISM, FIELD_IMP_INTEGRAL_DOMAIN, FINITE_EMPTY,
        FINITE_INSERT, FORALL_IN_IMAGE, FORALL_IN_INSERT, FUN_EQ_THM, GALOIS_GROUP,
        GALOIS_GROUP_PERMUTES, GALOIS_GROUP_RING_AUTOMORPHISM,
        GALOIS_GROUP_RING_HOMOMORPHISM, GROUP_ELEMENT_ORDER_EQ_2, GROUP_POW_2,
        INVERSE_I, INVERSE_UNIQUE_o, IN_ELIM_THM, IN_FIXED_FIELD, IN_IMAGE, IN_INSERT,
        I_O_ID, I_THM, MONO_EXISTS, NORMAL_EXTENSION_IMAGES_EQ,
        NORMAL_IMP_FIELD_EXTENSION, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, PERMUTES_I,
        PERMUTES_INVOLUTION, PERMUTES_IN_IMAGE, PRIME_SUBFIELD_HOMOMORPHISM_EXISTS,
        PRIME_SUBFIELD_MINIMAL, REAL_CNJ, REAL_EXISTS, REAL_LE_SQUARE, REAL_POW_2,
        RING_0, RING_1, RING_ADD, RING_AUTOMORPHISM_I,
        RING_CARRIER_SUBFIELD_GENERATED_SUBSET, RING_CHAR_COMPLEX_RING,
        RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_ADD,
        RING_HOMOMORPHISM_CNJ, RING_HOMOMORPHISM_COMPOSE, RING_HOMOMORPHISM_I,
        RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_NEG, RING_HOMOMORPHISM_POW,
        RING_MONOMORPHISM_INJECTIVE_EQ, RING_MUL, RING_NEG, SUBFIELD_OF_FIXED_FIELD,
        SUBFIELD_OF_HOMOMORPHIC_EQUALITIES, SUBSET, SYMMETRIC_GROUP, field_extension,
        o_THM, permutes, ring_automorphism, ring_endomorphism, ring_homomorphism,
        ring_isomorphism, ring_isomorphisms, subgroup_of, .. } := D.core1
  -- @@SCOPE END

  let GALOIS_GROUP_COMPLEX_CONJUGATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r20 ← TAUT (← q r"~p ==> p \/ q ==> q")
    prove
      r"!(k:A ring) e.
          normal_extension(subfield_generated k {ring_0 k},k) I /\
          ring_homomorphism(k,complex_ring) e
          ==> ?c. c IN group_carrier
                        (galois_group(subfield_generated k {ring_0 k},k) I) /\
                  (!x. x IN ring_carrier k ==> e(c x) = cnj(e x)) /\
                  group_mul (galois_group(subfield_generated k {ring_0 k},k) I)
                            c c =
                  group_id(galois_group(subfield_generated k {ring_0 k},k) I) /\
                  (c = group_id
                         (galois_group(subfield_generated k {ring_0 k},k) I) <=>
                   !x. x IN ring_carrier k ==> real(e x))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field(k:A ring)") ASSUME_TAC THENL [ASM_MESON_TAC [NORMAL_IMP_FIELD_EXTENSION, field_extension], ALL_TAC] THEN REWRITE_TAC [GALOIS_GROUP, IN_ELIM_THM, I_THM] THEN SUBGOAL_THEN (← q r"ring_monomorphism(k,complex_ring) (e:A->complex)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"e:A->complex")] FIELD_HOMOMORPHISM_IMP_MONOMORPHISM) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r20 THEN DISCH_THEN (MP_TAC o (SPEC (← q r"ring_1 k:A"))) THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_1 th)])) THEN REWRITE_TAC [RING_1, COMPLEX_RING_CLAUSES, CX_INJ] THEN CONV_TAC REAL_RAT_REDUCE_CONV, ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(k,complex_ring) (cnj o (e:A->complex))") ASSUME_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"complex_ring") THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_CNJ], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y:A. y IN ring_carrier(subfield_generated k {ring_0 k})
            ==> cnj((e:A->complex) y) = e y") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"e:A->complex"), (← q r"cnj o (e:A->complex)")] SUBFIELD_OF_HOMOMORPHIC_EQUALITIES) THEN ASM_REWRITE_TAC [FIELD_COMPLEX_RING] THEN DISCH_THEN (MP_TAC o (MATCH_MP PRIME_SUBFIELD_MINIMAL)) THEN REWRITE_TAC [SUBSET, IN_ELIM_THM, o_THM] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE (e:A->complex) (ring_carrier k) =
      IMAGE (cnj o e) (ring_carrier k)") ASSUME_TAC THENL [MATCH_MP_TAC NORMAL_EXTENSION_IMAGES_EQ THEN MAP_EVERY EXISTS_TAC [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 (k:A ring)}"), (← q r"complex_ring")] THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, FIELD_COMPLEX_RING, I_THM, o_THM], ALL_TAC] THEN ABBREV_TAC (← q r"c = \x:A. if x IN ring_carrier k
                then @y. y IN ring_carrier k /\ (e:A->complex) y = cnj(e x)
                else x") THEN SUBGOAL_THEN (← q r"!x:A. x IN ring_carrier k
            ==> c x IN ring_carrier k /\ (e:A->complex)(c x) = cnj(e x)") ASSUME_TAC THENL [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN EXPAND_TAC "c" THEN ASM_REWRITE_TAC [] THEN CONV_TAC SELECT_CONV THEN UNDISCH_TAC (← q r"IMAGE (e:A->complex) (ring_carrier k) =
        IMAGE (cnj o e) (ring_carrier k)") THEN REWRITE_TAC [EXTENSION, IN_IMAGE, o_THM] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"cnj((e:A->complex) x)"))) THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x:A. ~(x IN ring_carrier k) ==> c x = x") ASSUME_TAC THENL [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN EXPAND_TAC "c" THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x:A. c(c x) = x") ASSUME_TAC THENL [X_GEN_TAC (← q r"x:A") THEN ASM_CASES_TAC (← q r"(x:A) IN ring_carrier k") THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"e:A->complex"), (← q r"(c:A->A)(c x)"), (← q r"x:A")] RING_MONOMORPHISM_INJECTIVE_EQ) THEN ASM_SIMP_TAC [CNJ_CNJ], ASM_SIMP_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(k,k) (c:A->A)") ASSUME_TAC THENL [REWRITE_TAC [ring_homomorphism, SUBSET, FORALL_IN_IMAGE] THEN ASM_SIMP_TAC [] THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN W (fun (_asl, w) => tactic_of do pure ((← do let (l, r) ← (do let z19 ← (pure w); liftExcept (dest_eq z19)); pure (MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"e:A->complex"), l, r] RING_MONOMORPHISM_INJECTIVE_EQ))))) THEN FIRST_ASSUM ((fun th => tactic_of do pure (ASM_SIMP_TAC [RING_0, RING_1, RING_NEG, RING_ADD, RING_MUL, (← MATCH_MP RING_HOMOMORPHISM_0 th), (← MATCH_MP RING_HOMOMORPHISM_1 th), (← MATCH_MP RING_HOMOMORPHISM_NEG th), (← MATCH_MP RING_HOMOMORPHISM_ADD th), (← MATCH_MP RING_HOMOMORPHISM_MUL th)])) o (checkM (fun th => (do let z18 ← (q r"ring_homomorphism(k,complex_ring)                                     (e:A->complex)"); let z17 ← (do let z16 ← (pure th); pure (concl z16)); pure (z17 == z18))))) THEN REWRITE_TAC [COMPLEX_RING_CLAUSES, CNJ_ADD, CNJ_MUL, CNJ_NEG, CNJ_CX], ALL_TAC] THEN EXISTS_TAC (← q r"c:A->A") THEN ASM_SIMP_TAC [] THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC PERMUTES_INVOLUTION THEN ASM_REWRITE_TAC [], REWRITE_TAC [ring_automorphism, ring_isomorphism] THEN EXISTS_TAC (← q r"c:A->A") THEN ASM_SIMP_TAC [ring_isomorphisms], X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [SUBSET, RING_CARRIER_SUBFIELD_GENERATED_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"e:A->complex"), (← q r"(c:A->A) y"), (← q r"y:A")] RING_MONOMORPHISM_INJECTIVE_EQ) THEN ASM_SIMP_TAC [], REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN ASM_REWRITE_TAC [], REWRITE_TAC [FUN_EQ_THM, I_THM, REAL_CNJ] THEN EQ_TAC THENL [DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"x:A")) o (checkM (fun th => (do if ← (do if ← (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do pure (Prod.snd (← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (dest_forall z4))))); pure (is_eq z3)) else pure false) then (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); canM (fun z8 => (do let z9 ← (pure z8); find_termM (fun z10 => (do let z12 ← (pure z10); let z11 ← (q r"c:A->A"); pure (z11 == z12))) z9)) z6) else pure false) then (do pure !(← (do let z13 ← (do pure (Prod.snd (← (do let z14 ← (do let z15 ← (pure th); pure (concl z15)); liftExcept (dest_forall z14))))); pure (is_imp z13)))) else pure false))))) THEN DISCH_TAC THEN ASM_MESON_TAC [], DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN ASM_CASES_TAC (← q r"(x:A) IN ring_carrier k") THEN ASM_SIMP_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"e:A->complex"), (← q r"(c:A->A) x"), (← q r"x:A")] RING_MONOMORPHISM_INJECTIVE_EQ) THEN ASM_SIMP_TAC []]])

  let COMPLEX_CONJUGATION_REAL_SUBFIELD ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"~p ==> p \/ q ==> q")
    prove
      r"!(k:A ring) e c.
          field k /\ ring_homomorphism(k,complex_ring) e /\
          c IN group_carrier(galois_group(subfield_generated k {ring_0 k},k) I) /\
          (!x. x IN ring_carrier k ==> e(c x) = cnj(e x)) /\ ~(c = I)
          ==> {x | x IN ring_carrier k /\ real(e x)} subfield_of k /\
              finite_extension
               (subfield_generated k {x | x IN ring_carrier k /\ real(e x)},k)
               I /\
              galois_extension
               (subfield_generated k {x | x IN ring_carrier k /\ real(e x)},k)
               I /\
              extension_degree
               (subfield_generated k {x | x IN ring_carrier k /\ real(e x)},k)
               I = 2"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_monomorphism(k,complex_ring) (e:A->complex)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"e:A->complex")] FIELD_HOMOMORPHISM_IMP_MONOMORPHISM) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r1 THEN DISCH_THEN (MP_TAC o (SPEC (← q r"ring_1 k:A"))) THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_1 th)])) THEN REWRITE_TAC [RING_1, COMPLEX_RING_CLAUSES, CX_INJ] THEN CONV_TAC REAL_RAT_REDUCE_CONV, ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP GALOIS_GROUP_PERMUTES)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP GALOIS_GROUP_RING_AUTOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"!x:A. x IN ring_carrier k ==> c x IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [PERMUTES_IN_IMAGE], ALL_TAC] THEN SUBGOAL_THEN (← q r"(c:A->A) o c = I") ASSUME_TAC THENL [REWRITE_TAC [FUN_EQ_THM, o_THM, I_THM] THEN X_GEN_TAC (← q r"x:A") THEN ASM_CASES_TAC (← q r"(x:A) IN ring_carrier k") THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"e:A->complex"), (← q r"(c:A->A)(c x)"), (← q r"x:A")] RING_MONOMORPHISM_INJECTIVE_EQ) THEN ASM_SIMP_TAC [CNJ_CNJ], ASM_MESON_TAC [permutes]], ALL_TAC] THEN SUBGOAL_THEN (← q r"fixed_field k {I,c:A->A} = {x | x IN ring_carrier k /\ real(e x)}") (SUBST1_TAC o SYM) THENL [REWRITE_TAC [EXTENSION, IN_FIXED_FIELD, IN_ELIM_THM, FORALL_IN_INSERT, NOT_IN_EMPTY, I_THM, REAL_CNJ] THEN X_GEN_TAC (← q r"x:A") THEN ASM_CASES_TAC (← q r"(x:A) IN ring_carrier k") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"e:A->complex"), (← q r"(c:A->A) x"), (← q r"x:A")] RING_MONOMORPHISM_INJECTIVE_EQ) THEN ASM_SIMP_TAC [] THEN MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"{I,c:A->A}")] ARTIN_FIXED_FIELD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY, FORALL_IN_INSERT, NOT_IN_EMPTY, RING_AUTOMORPHISM_I] THEN REWRITE_TAC [subgroup_of, SYMMETRIC_GROUP, SUBSET, FORALL_IN_INSERT, NOT_IN_EMPTY, IN_ELIM_THM, IN_INSERT] THEN ASM_REWRITE_TAC [PERMUTES_I, INVERSE_I, I_O_ID] THEN SUBGOAL_THEN (← q r"inverse(c:A->A) = c") SUBST1_TAC THENL [MATCH_MP_TAC INVERSE_UNIQUE_o THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [] THEN REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN (DISJ_CASES_THEN SUBST1_TAC)) THEN ASM_REWRITE_TAC [I_O_ID], ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MATCH_MP_TAC SUBFIELD_OF_FIXED_FIELD THEN ASM_REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY, ring_endomorphism, RING_HOMOMORPHISM_I], SUBGOAL_THEN (← q r"~(I:A->A = c)") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY, IN_INSERT, NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV])

  let ALGEBRAIC_CLOSURE_COMPLEX_CONJUGATION ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r4 ← TAUT (← q r"~p ==> p \/ q ==> q")
    prove
      r"!k:A ring.
          algebraically_closed_field k /\ ring_char k = 0 /\
          algebraic_extension(subfield_generated k {ring_0 k},k) I
          ==> ?e c. ring_monomorphism(k,complex_ring) e /\
                    c IN group_carrier
                          (galois_group(subfield_generated k {ring_0 k},k) I) /\
                    group_element_order
                     (galois_group(subfield_generated k {ring_0 k},k) I) c = 2 /\
                    (!x. x IN ring_carrier k ==> e(c x) = cnj(e x)) /\
                    extension_degree
                     (subfield_generated k
                        {x | x IN ring_carrier k /\ real(e x)},k) I = 2"
      (GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring")] PRIME_SUBFIELD_HOMOMORPHISM_EXISTS) THEN ASM_REWRITE_TAC [FIELD_COMPLEX_RING, RING_CHAR_COMPLEX_RING] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"h0:A->complex")) THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 (k:A ring)}"), (← q r"k:A ring"), (← q r"complex_ring"), (← q r"I:A->A"), (← q r"h0:A->complex")] ALGEBRAIC_CLOSURE_EXTEND_HOMOMORPHISM) THEN ASM_REWRITE_TAC [ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING, I_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:A->complex") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"ring_monomorphism(k,complex_ring) (e:A->complex)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"complex_ring"), (← q r"e:A->complex")] FIELD_HOMOMORPHISM_IMP_MONOMORPHISM) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r4 THEN DISCH_THEN (MP_TAC o (SPEC (← q r"ring_1 k:A"))) THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_1 th)])) THEN REWRITE_TAC [RING_1, COMPLEX_RING_CLAUSES, CX_INJ] THEN CONV_TAC REAL_RAT_REDUCE_CONV, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"e:A->complex")] GALOIS_GROUP_COMPLEX_CONJUGATION) THEN ASM_SIMP_TAC [ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:A->A") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "iff"))))) THEN SUBGOAL_THEN (← q r"~(c = group_id(galois_group(subfield_generated k {ring_0 k},k)
                                 (I:A->A)))") ASSUME_TAC THENL [REMOVE_THEN "iff" SUBST1_TAC THEN REWRITE_TAC [NOT_FORALL_THM, NOT_IMP] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_neg k (ring_1 k):A"), (← q r"2")] ALGEBRAICALLY_CLOSED_FIELD_NTH_ROOT) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_NEG, RING_1, ARITH_EQ], ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"i:A") THEN STRIP_TAC THEN ASM_REWRITE_TAC [REAL_EXISTS] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"r:real")) THEN UNDISCH_TAC (← q r"ring_pow k i 2 = ring_neg k (ring_1 (k:A ring))") THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"e:A->complex"))) THEN FIRST_ASSUM ((fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_POW th), (← MATCH_MP RING_HOMOMORPHISM_NEG th), (← MATCH_MP RING_HOMOMORPHISM_1 th), RING_1])) o (checkM (fun th => (do let z3 ← (q r"ring_homomorphism(k,complex_ring)                                     (e:A->complex)"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3))))) THEN REWRITE_TAC [COMPLEX_RING_POW, COMPLEX_RING_CLAUSES] THEN REWRITE_TAC [(← GSYM CX_POW), (← GSYM CX_NEG), CX_INJ] THEN MP_TAC (← SPEC (← q r"r:real") REAL_LE_SQUARE) THEN REWRITE_TAC [REAL_POW_2] THEN REAL_ARITH_TAC, REMOVE_THEN "iff" (fun (_ : thm) => ALL_TAC)] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"e:A->complex"), (← q r"c:A->A")] COMPLEX_CONJUGATION_REAL_SUBFIELD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"~(c = group_id(galois_group(subfield_generated k {ring_0 k},k)
                                   (I:A->A)))") THEN REWRITE_TAC [GALOIS_GROUP], STRIP_TAC] THEN MAP_EVERY EXISTS_TAC [(← q r"e:A->complex"), (← q r"c:A->A")] THEN ASM_SIMP_TAC [GROUP_ELEMENT_ORDER_EQ_2, GROUP_POW_2])

  -- @@RETURN BEGIN
  return { GALOIS_GROUP_COMPLEX_CONJUGATION, COMPLEX_CONJUGATION_REAL_SUBFIELD,
           ALGEBRAIC_CLOSURE_COMPLEX_CONJUGATION }
  -- @@RETURN END

end HolANT.ComplexConjugation
