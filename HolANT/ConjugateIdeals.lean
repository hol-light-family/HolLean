/- ========================================================================= -/
/- ANT: Galois conjugates of ideals in Galois extensions of number ...     -/
/- ========================================================================= -/
/- File: HolANT/ConjugateIdeals.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/conjugate_ideals.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antconjugateidealsdiff; the rest is by hand.  Its `needs` closure is
  Library/wo.ml, Library/card.ml, Library/matroids.ml, Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/ringtheory.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/prime_split.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/relative_split.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/decomposition.ml, ANT/nf_valuation.ml, ANT/relative_degree.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/splitting_types.ml, ANT/nf_decomposition.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.ConjugateIdeals fills them).

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
import HolANT.IdealArith
import HolLibrary.Products
import HolANT.Algmisc
import HolANT.Integral
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.PrimeSplit
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.Discriminant
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
open HolANT.IdealNorm
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.PrimeSplit
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
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

namespace HolANT.ConjugateIdeals

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CARD_CLAUSES CARD_EQ_NSUM CARD_GALOIS_GROUP_IMAGE_FIBER CONTRAPOS_THM
   DEDEKIND_IDEAL_EQ_VALUATION DEDEKIND_IDEAL_INDUCT
   DEDEKIND_IMP_INTEGRAL_DOMAIN DEDEKIND_RING_OF_INTEGERS EQ_TRANS
   EXISTS_UNIQUE_THM EXTENSION FIELD_SUBFIELD_GENERATED FINITE_GALOIS_GROUP
   FINITE_RESTRICT FORALL_IN_IMAGE GALOIS_GROUP_FIXES
   GALOIS_GROUP_PRIME_IDEAL_IMAGE GALOIS_GROUP_RING_OF_INTEGERS
   GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM
   GALOIS_GROUP_RING_OF_INTEGERS_IDEAL GALOIS_IMP_FIELD_EXTENSION
   IDEAL_GENERATED_IMAGE_IDEAL_GENERATED IDEAL_GENERATED_INC
   IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0 IDEAL_GENERATED_SING_EQ_CARRIER
   IDEAL_NORM_CARRIER IDEAL_POW_EQ_ZERO IDEAL_POW_PRINCIPAL IDEAL_PRODUCT_EQ
   IDEAL_PRODUCT_EQ_ZERO IDEAL_PRODUCT_MUL IDEAL_PRODUCT_PRINCIPAL
   IDEAL_PROD_PRINCIPAL IDEAL_VALUATION_EQ_0 IDEAL_VALUATION_IDEAL_POW
   IDEAL_VALUATION_IDEAL_PRODUCT IDEAL_VALUATION_PRIME IMAGE_I IN_ELIM_THM
   IN_IMAGE MULT_CLAUSES MULT_SYM NOT_EXISTS_THM NOT_IN_EMPTY NSUM_EQ
   NSUM_RESTRICT_SET NUMBER_FIELD_DECOMPOSITION_GROUP
   NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE NUMBER_FIELD_IDEAL_NORM_MUL_Q
   NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_PRIME_IDEAL_ABOVE
   NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE NUMBER_FIELD_TOWER_LAW
   PRIME_IDEAL_IMP_SUBSET PRIME_IMP_RING_IDEAL RESIDUE_DEGREE_PRIME_SUBFIELD
   RING_1 RING_HOMOMORPHISM_RING_OF_INTEGERS
   RING_HOMOMORPHISM_SUBFIELD_INCLUSION RING_IDEAL_IDEAL_GENERATED
   RING_IDEAL_IDEAL_POW RING_IDEAL_IDEAL_PRODUCT RING_IDEAL_IMP_SUBSET
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MONOMORPHISM_RING_OF_INTEGERS
   RING_OF_INTEGERS RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q
   RING_OF_INTEGERS_PRIME_IDEAL_ABOVE RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL
   RING_OF_INTEGERS_SUBRING RING_OF_INTEGERS_SUBSET RING_OF_NUM RING_OF_NUM_1
   RING_OF_NUM_EXP RING_OF_NUM_MUL RING_OF_NUM_SUBFIELD_GENERATED RING_PRODUCT_1
   RING_UNIT_1 SING_SUBSET SUBFIELD_GENERATED SUBSET SUBSET_TRANS
   field_extension finite_extension number_field ramification_index : thm)
  deriving Inhabited

/-- What conjugate_ideals.ml uses from Session besides theorems. -/
structure ConjugateIdealsDeps where
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
/- conjugate_ideals.ml phrases from line 53 to 227                        -/
/- ---------------------------------------------------------------------- -/

structure ConjugateIdeals where
  -- @@FIELDS
  NUMBER_FIELD_GALOIS_PRODUCT_PRIME : thm
  NUMBER_FIELD_GALOIS_PRODUCT_IDEAL : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupConjugateIdeals [HolBase] (D : ConjugateIdealsDeps) :
    ExceptT String IO ConjugateIdeals := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, SET_TAC, TAUT, .. } := D
  let { CARD_CLAUSES, CARD_EQ_NSUM, CARD_GALOIS_GROUP_IMAGE_FIBER, CONTRAPOS_THM,
        DEDEKIND_IDEAL_EQ_VALUATION, DEDEKIND_IDEAL_INDUCT,
        DEDEKIND_IMP_INTEGRAL_DOMAIN, DEDEKIND_RING_OF_INTEGERS, EQ_TRANS,
        EXISTS_UNIQUE_THM, EXTENSION, FIELD_SUBFIELD_GENERATED, FINITE_GALOIS_GROUP,
        FINITE_RESTRICT, FORALL_IN_IMAGE, GALOIS_GROUP_FIXES,
        GALOIS_GROUP_PRIME_IDEAL_IMAGE, GALOIS_GROUP_RING_OF_INTEGERS,
        GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM,
        GALOIS_GROUP_RING_OF_INTEGERS_IDEAL, GALOIS_IMP_FIELD_EXTENSION,
        IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, IDEAL_GENERATED_INC,
        IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0, IDEAL_GENERATED_SING_EQ_CARRIER,
        IDEAL_NORM_CARRIER, IDEAL_POW_EQ_ZERO, IDEAL_POW_PRINCIPAL, IDEAL_PRODUCT_EQ,
        IDEAL_PRODUCT_EQ_ZERO, IDEAL_PRODUCT_MUL, IDEAL_PRODUCT_PRINCIPAL,
        IDEAL_PROD_PRINCIPAL, IDEAL_VALUATION_EQ_0, IDEAL_VALUATION_IDEAL_POW,
        IDEAL_VALUATION_IDEAL_PRODUCT, IDEAL_VALUATION_PRIME, IMAGE_I, IN_ELIM_THM,
        IN_IMAGE, MULT_CLAUSES, MULT_SYM, NOT_EXISTS_THM, NOT_IN_EMPTY, NSUM_EQ,
        NSUM_RESTRICT_SET, NUMBER_FIELD_DECOMPOSITION_GROUP,
        NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE, NUMBER_FIELD_IDEAL_NORM_MUL_Q,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_PRIME_IDEAL_ABOVE,
        NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE, NUMBER_FIELD_TOWER_LAW,
        PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_RING_IDEAL, RESIDUE_DEGREE_PRIME_SUBFIELD,
        RING_1, RING_HOMOMORPHISM_RING_OF_INTEGERS,
        RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_PRODUCT, RING_IDEAL_IMP_SUBSET,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_RING_OF_INTEGERS,
        RING_OF_INTEGERS, RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q,
        RING_OF_INTEGERS_PRIME_IDEAL_ABOVE, RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET, RING_OF_NUM, RING_OF_NUM_1,
        RING_OF_NUM_EXP, RING_OF_NUM_MUL, RING_OF_NUM_SUBFIELD_GENERATED,
        RING_PRODUCT_1, RING_UNIT_1, SING_SUBSET, SUBFIELD_GENERATED, SUBSET,
        SUBSET_TRANS, field_extension, finite_extension, number_field,
        ramification_index, .. } := D.core1
  -- @@SCOPE END

  let NUMBER_FIELD_GALOIS_PRODUCT_PRIME ← prove
    r"!(h:A->B) k l p P.
        number_field l /\ galois_extension(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P
        ==> ideal_product (ring_of_integers l)
              (group_carrier(galois_group(k,l) h)) (\f. IMAGE f P) =
            ideal_pow (ring_of_integers l)
              (ideal_generated (ring_of_integers l) (IMAGE h p))
              (residue_degree (ring_of_integers k,ring_of_integers l) h P)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"field k /\ ring_homomorphism(k,l) (h:A->B)") STRIP_ASSUME_TAC THENL [FIRST_ASSUM (MP_TAC o (MATCH_MP GALOIS_IMP_FIELD_EXTENSION)) THEN SIMP_TAC [field_extension, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN SUBGOAL_THEN (← q r"FINITE(group_carrier(galois_group(k:A ring,l:B ring) h))") ASSUME_TAC THENL [MATCH_MP_TAC FINITE_GALOIS_GROUP THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_monomorphism(k:A ring,l:B ring) h") ASSUME_TAC THENL [ASM_MESON_TAC [finite_extension, field_extension], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_RING_OF_INTEGERS)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN SUBGOAL_THEN (← q r"(p:A->bool) SUBSET ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [PRIME_IDEAL_IMP_SUBSET, RING_OF_INTEGERS_SUBSET, SUBSET_TRANS], ALL_TAC] THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(galois_group(k:A ring,l:B ring) h)
        ==> IMAGE f (ring_carrier(ring_of_integers l)) SUBSET
            ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [MESON_TAC [GALOIS_GROUP_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(galois_group(k:A ring,l:B ring) h)
        ==> prime_ideal (ring_of_integers l) (IMAGE f P) /\
            IMAGE h p SUBSET IMAGE f P /\
            ~(IMAGE f P = {ring_0 l})") ASSUME_TAC THENL [X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_integers l:B ring"), (← q r"f:B->B"), (← q r"P:B->bool")] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING, PRIME_IDEAL_IMP_SUBSET] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"IMAGE (h:A->B) p SUBSET IMAGE (f:B->B) P") ASSUME_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_IMAGE] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN EXISTS_TAC (← q r"(h:A->B) x") THEN CONJ_TAC THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC GALOIS_GROUP_FIXES THEN ASM SET_TAC [], ASM SET_TAC []], ASM_REWRITE_TAC []] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"IMAGE (f:B->B) P")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN ASM_SIMP_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"E = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)") THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers l) (E:B->bool) /\
                ~(E = {ring_0 l})") STRIP_ASSUME_TAC THENL [EXPAND_TAC "E" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0) THEN ASM_SIMP_TAC [RING_MONOMORPHISM_RING_OF_INTEGERS, PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"ideal_product (ring_of_integers l)
                    (group_carrier(galois_group(k:A ring,l:B ring) h))
                    (\f:B->B. IMAGE f P)"), (← q r"ideal_pow (ring_of_integers l) (E:B->bool)
                    (residue_degree (ring_of_integers k,ring_of_integers l)
                                    (h:A->B) P)")] DEDEKIND_IDEAL_EQ_VALUATION) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_PRODUCT, RING_IDEAL_IDEAL_POW, IDEAL_POW_EQ_ZERO, RING_OF_INTEGERS] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"group_carrier(galois_group(k:A ring,l:B ring) h)"), (← q r"\f:B->B. IMAGE f P")] IDEAL_PRODUCT_EQ_ZERO) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"f:B->B") THEN FIRST_ASSUM (MP_TAC o (SPEC (← q r"f:B->B"))) THEN CONV_TAC TAUT, DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [RING_OF_INTEGERS] THEN X_GEN_TAC (← q r"Q:B->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"group_carrier(galois_group(k:A ring,l:B ring) h)"), (← q r"\f:B->B. IMAGE f P")] IDEAL_VALUATION_IDEAL_PRODUCT) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, PRIME_IMP_RING_IDEAL] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_POW, RING_OF_INTEGERS] THEN SUBGOAL_THEN (← q r"nsum (group_carrier(galois_group(k:A ring,l:B ring) h))
         (\f:B->B. ideal_valuation (ring_of_integers l) Q (IMAGE f P)) =
    CARD {f | f IN group_carrier(galois_group(k,l) h) /\ IMAGE f P = Q}") SUBST1_TAC THENL [ASM_SIMP_TAC [CARD_EQ_NSUM, FINITE_RESTRICT, NSUM_RESTRICT_SET] THEN MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"IMAGE (f:B->B) P")] IDEAL_VALUATION_PRIME) THEN ASM_SIMP_TAC [RING_OF_INTEGERS], ALL_TAC] THEN ASM_CASES_TAC (← q r"IMAGE (h:A->B) p SUBSET Q") THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"P:B->bool"), (← q r"Q:B->bool")] NUMBER_FIELD_GALOIS_GROUP_TRANSITIVE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:B->B") (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM))) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"P:B->bool"), (← q r"g:B->B")] CARD_GALOIS_GROUP_IMAGE_FIBER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_DECOMPOSITION_GROUP) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN SUBGOAL_THEN (← q r"!R. prime_ideal (ring_of_integers l) R /\ IMAGE (h:A->B) p SUBSET R
          ==> {x | x IN ring_carrier(ring_of_integers k) /\ h x IN R} = p") ASSUME_TAC THENL [X_GEN_TAC (← q r"R:B->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"R:B->bool")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (CONJUNCT2 o (CONJUNCT2 o CONJUNCT2))) THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool")] PRIME_IDEAL_IMP_SUBSET) THEN ASM_REWRITE_TAC [] THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_valuation (ring_of_integers l) (IMAGE (g:B->B) P) E =
      ramification_index (ring_of_integers k,ring_of_integers l) (h:A->B)
        (IMAGE g P)") SUBST1_TAC THENL [REWRITE_TAC [ramification_index] THEN EXPAND_TAC "E" THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"g:B->B"), (← q r"P:B->bool")] NUMBER_FIELD_RAMIFICATION_INDEX_CONJUGATE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:B->bool"))) THEN ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [MULT_SYM]], SUBGOAL_THEN (← q r"{f | f IN group_carrier(galois_group(k:A ring,l:B ring) h) /\
           IMAGE f P = Q} = {}") SUBST1_TAC THENL [ONCE_REWRITE_TAC [EXTENSION] THEN REWRITE_TAC [NOT_IN_EMPTY] THEN X_GEN_TAC (← q r"f:B->B") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN UNDISCH_TAC (← q r"~(IMAGE (h:A->B) p SUBSET Q)") THEN REWRITE_TAC [] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [], REWRITE_TAC [CARD_CLAUSES]] THEN SUBGOAL_THEN (← q r"ideal_valuation (ring_of_integers l) Q (E:B->bool) = 0") (fun th => REWRITE_TAC [th, MULT_CLAUSES]) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool"), (← q r"E:B->bool")] IDEAL_VALUATION_EQ_0) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN UNDISCH_TAC (← q r"~(IMAGE (h:A->B) p SUBSET Q)") THEN REWRITE_TAC [CONTRAPOS_THM] THEN DISCH_TAC THEN TRANS_TAC SUBSET_TRANS (← q r"E:B->bool") THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "E" THEN REWRITE_TAC [SUBSET] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM_REWRITE_TAC [] THEN TRANS_TAC SUBSET_TRANS (← q r"P:B->bool") THEN ASM_SIMP_TAC [PRIME_IDEAL_IMP_SUBSET]])

  let NUMBER_FIELD_GALOIS_PRODUCT_IDEAL ← prove
    r"!k:A ring j.
        number_field k /\
        galois_extension (subfield_generated k {ring_0 k},k) I /\
        ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
        ==> ideal_product (ring_of_integers k)
              (group_carrier(galois_group(subfield_generated k {ring_0 k},k) I))
              (\f. IMAGE f j) =
            ideal_generated (ring_of_integers k)
              {ring_of_num k (ideal_norm (ring_of_integers k) j)}"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_RING_OF_INTEGERS)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"FINITE(group_carrier(galois_group
      (subfield_generated k {ring_0 k},k) (I:A->A)))") ASSUME_TAC THENL [MATCH_MP_TAC FINITE_GALOIS_GROUP THEN FIRST_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [number_field])) THEN SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!q. prime_ideal (ring_of_integers (k:A ring)) q /\ ~(q = {ring_0 k})
        ==> ideal_product (ring_of_integers k)
              (group_carrier(galois_group
                 (subfield_generated k {ring_0 k},k) I))
              (\f. IMAGE f q) =
            ideal_generated (ring_of_integers k)
              {ring_of_num k (ideal_norm (ring_of_integers k) q)}") ASSUME_TAC THENL [X_GEN_TAC (← q r"q:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"q:A->bool")] RING_OF_INTEGERS_PRIME_IDEAL_ABOVE) THEN ASM_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"p:num") STRIP_ASSUME_TAC) o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"q:A->bool"), (← q r"p:num")] RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"q:A->bool")] RESIDUE_DEGREE_PRIME_SUBFIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"ring_homomorphism(subfield_generated k {ring_0 k},k) (I:A->A) /\
      ring_homomorphism(ring_of_integers(subfield_generated k {ring_0 k}),
                        ring_of_integers k) (I:A->A)") STRIP_ASSUME_TAC THENL [REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN MATCH_MP_TAC RING_HOMOMORPHISM_RING_OF_INTEGERS THEN REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_num k p IN
      ring_carrier(ring_of_integers(subfield_generated k {ring_0 k:A}))") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers(subfield_generated k {ring_0 k:A})"), (← q r"p:num")] RING_OF_NUM) THEN REWRITE_TAC [RING_OF_INTEGERS, RING_OF_NUM_SUBFIELD_GENERATED], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"ideal_generated (ring_of_integers(subfield_generated k {ring_0 k}))
                       {ring_of_num k p:A}"), (← q r"q:A->bool")] NUMBER_FIELD_GALOIS_PRODUCT_PRIME) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, (← CONJUNCT2 SUBFIELD_GENERATED)] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers(subfield_generated k {ring_0 k}):A ring"), (← q r"ring_of_integers k:A ring"), (← q r"I:A->A"), (← q r"{ring_of_num k p:A}")] IDEAL_GENERATED_IMAGE_IDEAL_GENERATED) THEN ASM_REWRITE_TAC [SING_SUBSET, IMAGE_I] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:num")] RING_OF_NUM) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_TAC THEN ASM_SIMP_TAC [IDEAL_POW_PRINCIPAL] THEN REWRITE_TAC [RING_OF_INTEGERS, RING_OF_NUM_EXP], ALL_TAC] THEN SUBGOAL_THEN (← q r"!j. ring_ideal (ring_of_integers (k:A ring)) j /\
        ~(j = {ring_0(ring_of_integers k)})
        ==> ideal_product (ring_of_integers k)
              (group_carrier(galois_group
                 (subfield_generated k {ring_0 k},k) I))
              (\f. IMAGE f j) =
            ideal_generated (ring_of_integers k)
              {ring_of_num k (ideal_norm (ring_of_integers k) j)}") (fun th => ASM_SIMP_TAC [th, RING_OF_INTEGERS]) THEN MATCH_MP_TAC DEDEKIND_IDEAL_INDUCT THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN CONJ_TAC THENL [REWRITE_TAC [IDEAL_NORM_CARRIER, RING_OF_NUM_1] THEN SUBGOAL_THEN (← q r"ideal_generated (ring_of_integers k) {ring_1 k} =
      ring_carrier(ring_of_integers(k:A ring))") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_1 k:A")] IDEAL_GENERATED_SING_EQ_CARRIER) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_1) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_UNIT_1) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_product (ring_of_integers k)
        (group_carrier(galois_group
           (subfield_generated k {ring_0 k},k) (I:A->A)))
        (\f. ring_carrier(ring_of_integers k)) =
      ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [(← SYM th)] THEN GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"group_carrier(galois_group
                        (subfield_generated k {ring_0 k},k) (I:A->A))"), (← q r"\f:A->A. ring_1 k:A")] IDEAL_PRODUCT_PRINCIPAL) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_1) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"group_carrier(galois_group
                        (subfield_generated k {ring_0 k},k) (I:A->A))")] RING_PRODUCT_1) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC, ALL_TAC] THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) THEN MATCH_MP_TAC IDEAL_PRODUCT_EQ THEN X_GEN_TAC (← q r"f:A->A") THEN DISCH_TAC THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"f:A->A")] GALOIS_GROUP_RING_OF_INTEGERS_AUTOMORPHISM) THEN ASM_SIMP_TAC [], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"q:A->bool"), (← q r"i:A->bool")] THEN STRIP_TAC THEN TRANS_TAC EQ_TRANS (← q r"ideal_product (ring_of_integers k)
      (group_carrier(galois_group
         (subfield_generated k {ring_0 k},k) (I:A->A)))
      (\f. ideal_prod (ring_of_integers k) (IMAGE f q) (IMAGE f i))") THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_PRODUCT_EQ THEN X_GEN_TAC (← q r"f:A->A") THEN DISCH_TAC THEN REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"f:A->A"), (← q r"q:A->bool")] GALOIS_GROUP_RING_OF_INTEGERS_IDEAL) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN wPart lhand (lhand o rand) IDEAL_PRODUCT_MUL THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"f:A->A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"f:A->A"), (← q r"q:A->bool")] GALOIS_GROUP_RING_OF_INTEGERS_IDEAL) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"f:A->A"), (← q r"i:A->bool")] GALOIS_GROUP_RING_OF_INTEGERS_IDEAL) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_num k (ideal_norm (ring_of_integers k) q):A"), (← q r"ring_of_num k (ideal_norm (ring_of_integers k) i):A")] IDEAL_PROD_PRINCIPAL) THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_OF_NUM) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [(← GSYM RING_OF_NUM_MUL), NUMBER_FIELD_IDEAL_NORM_MUL_Q, PRIME_IMP_RING_IDEAL])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_GALOIS_PRODUCT_PRIME, NUMBER_FIELD_GALOIS_PRODUCT_IDEAL }
  -- @@RETURN END

end HolANT.ConjugateIdeals
