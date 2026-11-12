/- ========================================================================= -/
/- ANT: Splitting types of primes                                          -/
/- ========================================================================= -/
/- File: HolANT/SplittingTypes.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/splitting_types.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antsplittingtypesdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/ideal_arith.ml, Library/isum.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/relative_split.ml, ANT/relative_degree.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.SplittingTypes fills them).

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
import HolANT.PrimeSplit
import HolANT.NormIndex
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.RelativeSplit
import HolANT.RelativeDegree

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
open HolANT.PrimeSplit
open HolANT.NormIndex
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.RelativeSplit
open HolANT.RelativeDegree

namespace HolANT.SplittingTypes

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ARITH_EQ CARD_EQ_0 CARD_EQ_NSUM CARD_SING CONJ_ASSOC DE_MORGAN_THM
   DIVIDES_ZERO EQ_MULT_LCANCEL EQ_MULT_RCANCEL EQ_TRANS EXISTS_IN_IMAGE
   EXISTS_UNIQUE_THM EXTENSION FIELD_EXTENSION_SUBRING_GENERATED_FINITE
   FIELD_IMP_NONTRIVIAL_RING FIELD_RING_HOMOMORPHISM_MONOMORPHISM
   FINITE_EQ_FIELD_EXTENSION FINITE_FIELD_IMP_PERFECT FINITE_IMAGE
   FINITE_IMP_ALGEBRAIC_EXTENSION FINITE_INTEGRAL_DOMAIN_IMP_FIELD FINITE_SING
   FINITE_SUBRING_GENERATED FINITE_SUBSET FINITE_UNIONS
   FIRST_RING_ISOMORPHISM_THEOREM FORALL_IN_IMAGE FORALL_IN_INSERT
   IDEAL_GENERATED_IMAGE_IDEAL_GENERATED IDEAL_GENERATED_INC
   IDEAL_GENERATED_MINIMAL_EQ IDEAL_GENERATED_SUBSET IDEAL_POW_1
   IDEAL_PRODUCT_EQ IDEAL_PRODUCT_SING IMAGE_CLAUSES IMAGE_I IMP_CONJ IMP_IMP
   INTEGER_RING INTEGRAL_DOMAIN_QUOTIENT_RING IN_ELIM_THM IN_RING_IDEAL_0
   IN_SING IN_UNIONS ISOMORPHIC_RING_PERFECT_FIELD MULT_CLAUSES MULT_EQ_0
   MULT_EQ_1 NOT_EXISTS_THM NOT_FORALL_THM NOT_IMP NOT_IN_EMPTY NOT_LT NSUM_ADD
   NSUM_EQ NSUM_EQ_0_IFF NSUM_SING NUMBER_FIELD_FINITE_RAMIFIED_PRIMES
   NUMBER_FIELD_FUNDAMENTAL_IDENTITY NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q
   NUMBER_FIELD_HOMOMORPHIC_PREIMAGE NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_PRIME_FACTORIZATION NUMBER_FIELD_PRIME_FACTORIZATION_Q
   NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE
   NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_Q NUMBER_FIELD_PRIME_IDEALS_ABOVE
   NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q
   NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS
   NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q NUMBER_FIELD_RAMIFIED_DISCRIMINANT
   NUMBER_FIELD_SUBFIELD_GENERATED PERFECT_FIELD_IMP_SEPARABLE_EXTENSION
   PRIME_IMP_NZ PRIME_IMP_RING_IDEAL PRIME_SUBFIELD_SUBFIELD_GENERATED
   PROPER_IDEAL PROPER_IMP_RING_IDEAL QUOTIENT_RING_0
   RAMIFICATION_INDEX_PRIME_SUBFIELD RESIDUE_DEGREE_PRIME_SUBFIELD RING_0 RING_1
   RING_COSET_EQ_IDEAL RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_1
   RING_HOMOMORPHISM_COMPOSE RING_HOMOMORPHISM_INTEGER_RING_OF_INT
   RING_HOMOMORPHISM_IN_CARRIER RING_HOMOMORPHISM_RING_COSET
   RING_HOMOMORPHISM_RING_OF_INTEGERS RING_HOMOMORPHISM_RING_OF_NUM
   RING_HOMOMORPHISM_SUBFIELD_INCLUSION RING_IDEAL_HOMOMORPHIC_PREIMAGE
   RING_IDEAL_IDEAL_POW RING_IDEAL_IMP_SUBSET RING_OF_INT RING_OF_INTEGERS
   RING_OF_INTEGERS_FINITE_QUOTIENT RING_OF_INTEGERS_PRIME_IDEAL_ABOVE
   RING_OF_INTEGERS_PRIME_IDEAL_BELOW RING_OF_INTEGERS_SUBSET RING_OF_INT_OF_NUM
   RING_OF_NUM RING_OF_NUM_EQ_0 RING_OF_NUM_SUBFIELD_GENERATED SING_SUBSET
   SUBSET SUBSET_ANTISYM SUBSET_TRANS SUBSET_UNIV field_extension maximal_ideal
   number_field o_THM prime_ideal ring_homomorphism ring_image ring_kernel
   ring_monomorphism : thm)
  deriving Inhabited

/-- What splitting_types.ml uses from Session besides theorems. -/
structure SplittingTypesDeps where
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
  SIMP_RULE : List thm → thm → ExceptT String IO thm
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
/- splitting_types.ml phrases from line 99 to 795                         -/
/- ---------------------------------------------------------------------- -/

structure SplittingTypes01 where
  -- @@FIELDS
  weakly_unramified : thm
  unramified : thm
  totally_split : thm
  inert : thm
  totally_ramified : thm
  UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED : thm
  UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_FINITE : thm
  UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_PERFECT : thm
  RING_OF_INTEGERS_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED : thm
  NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_Q : thm
  NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED : thm
  SPLITTING_TYPES_PRINCIPAL : thm
  SPLITTING_TYPES_INTEGER_RING : thm
  IDEAL_PRODUCT_SPLITTING_TYPES : thm
  NUMBER_FIELD_PRIME_DECOMPOSITION_Q : thm
  NUMBER_FIELD_UNRAMIFIED_DISCRIMINANT : thm
  NUMBER_FIELD_UNRAMIFIED_FACTORIZATION : thm
  NUMBER_FIELD_TOTALLY_SPLIT_CARD : thm
  NUMBER_FIELD_INERT_RESIDUE_DEGREE : thm
  NUMBER_FIELD_TOTALLY_RAMIFIED_RAMIFICATION_INDEX : thm
  NUMBER_FIELD_TOTALLY_RAMIFIED_IDEAL_POW : thm
  NUMBER_FIELD_INERT_IMP_UNRAMIFIED : thm
  NUMBER_FIELD_SPLITTING_TYPES_EXCLUSIVE : thm
  NUMBER_FIELD_PRIME_DECOMPOSITION : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupSplittingTypes01 [HolBase] (D : SplittingTypesDeps) :
    ExceptT String IO SplittingTypes01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, SET_RULE, SET_TAC,
        SIMP_RULE, TAUT, new_definition, .. } := D
  let { ARITH_EQ, CARD_EQ_0, CARD_EQ_NSUM, CARD_SING, CONJ_ASSOC, DE_MORGAN_THM,
        DIVIDES_ZERO, EQ_MULT_LCANCEL, EQ_MULT_RCANCEL, EQ_TRANS, EXTENSION,
        FIELD_EXTENSION_SUBRING_GENERATED_FINITE, FIELD_IMP_NONTRIVIAL_RING,
        FIELD_RING_HOMOMORPHISM_MONOMORPHISM, FINITE_EQ_FIELD_EXTENSION,
        FINITE_FIELD_IMP_PERFECT, FINITE_IMP_ALGEBRAIC_EXTENSION,
        FINITE_INTEGRAL_DOMAIN_IMP_FIELD, FINITE_SING, FINITE_SUBRING_GENERATED,
        FIRST_RING_ISOMORPHISM_THEOREM, FORALL_IN_IMAGE, FORALL_IN_INSERT,
        IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, IDEAL_GENERATED_INC,
        IDEAL_GENERATED_MINIMAL_EQ, IDEAL_POW_1, IDEAL_PRODUCT_EQ, IDEAL_PRODUCT_SING,
        IMAGE_CLAUSES, IMP_CONJ, INTEGER_RING, INTEGRAL_DOMAIN_QUOTIENT_RING,
        IN_ELIM_THM, IN_RING_IDEAL_0, IN_SING, ISOMORPHIC_RING_PERFECT_FIELD,
        MULT_CLAUSES, MULT_EQ_0, MULT_EQ_1, NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP,
        NOT_IN_EMPTY, NSUM_ADD, NSUM_EQ, NSUM_EQ_0_IFF, NSUM_SING,
        NUMBER_FIELD_FUNDAMENTAL_IDENTITY, NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_PRIME_FACTORIZATION,
        NUMBER_FIELD_PRIME_FACTORIZATION_Q, NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE,
        NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_Q, NUMBER_FIELD_PRIME_IDEALS_ABOVE,
        NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q, NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS,
        NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q, NUMBER_FIELD_RAMIFIED_DISCRIMINANT,
        PERFECT_FIELD_IMP_SEPARABLE_EXTENSION, PRIME_IMP_NZ, PRIME_IMP_RING_IDEAL,
        PROPER_IDEAL, PROPER_IMP_RING_IDEAL, QUOTIENT_RING_0, RING_0, RING_1,
        RING_COSET_EQ_IDEAL, RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_1,
        RING_HOMOMORPHISM_COMPOSE, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_RING_COSET,
        RING_IDEAL_HOMOMORPHIC_PREIMAGE, RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET,
        RING_OF_INT, RING_OF_INTEGERS, RING_OF_INTEGERS_FINITE_QUOTIENT,
        RING_OF_INTEGERS_SUBSET, RING_OF_INT_OF_NUM, RING_OF_NUM, RING_OF_NUM_EQ_0,
        SING_SUBSET, SUBSET, SUBSET_ANTISYM, SUBSET_UNIV, field_extension,
        maximal_ideal, number_field, o_THM, prime_ideal, ring_image, ring_kernel,
        ring_monomorphism, .. } := D.core1
  -- @@SCOPE END

  let weakly_unramified ← new_definition
    r"weakly_unramified (r:A ring,s:B ring) (h:A->B) p <=>
  !P. prime_ideal s P /\ IMAGE h p SUBSET P
      ==> ramification_index (r,s) h P = 1"

  let unramified ← new_definition
    r"unramified (r:A ring,s:B ring) (h:A->B) p <=>
  !P. prime_ideal s P /\ IMAGE h p SUBSET P
      ==> ramification_index (r,s) h P = 1 /\
          separable_extension
           (subring_generated (quotient_ring s P)
              (IMAGE (ring_coset s P o h) (ring_carrier r)),
            quotient_ring s P) I"

  let totally_split ← new_definition
    r"totally_split (r:A ring,s:B ring) (h:A->B) p <=>
  !P. prime_ideal s P /\ IMAGE h p SUBSET P
      ==> ramification_index (r,s) h P = 1 /\
          residue_degree (r,s) h P = 1"

  let inert ← new_definition
    r"inert (r:A ring,s:B ring) (h:A->B) p <=>
  prime_ideal s (ideal_generated s (IMAGE h p))"

  let totally_ramified ← new_definition
    r"totally_ramified (r:A ring,s:B ring) (h:A->B) p <=>
  ?P. {Q | prime_ideal s Q /\ IMAGE h p SUBSET Q} = {P} /\
      residue_degree (r,s) h P = 1"

  let UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED ← prove
    r"!r:A ring s:B ring h p.
        unramified (r,s) h p ==> weakly_unramified (r,s) h p"
    (SIMP_TAC [unramified, weakly_unramified])

  let UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_FINITE ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"X:(B->bool)->bool"
    let q2 ← q r"quotient_ring s (P:B->bool)"
    let v3 ← ISPECL [q2, q1] FIELD_EXTENSION_SUBRING_GENERATED_FINITE
    let q4 ← q r"field(quotient_ring s (P:B->bool))"
    let q5 ← q r"X = IMAGE (ring_coset s P o (h:A->B)) (ring_carrier r)"
    let q6 ← q r"P:B->bool"
    let q7 ← q r"P:B->bool"
    let q8 ← q r"!a b c. (!P:B->bool. a P ==> c P)
            ==> ((!P. a P ==> b P /\ c P) <=> (!P. a P ==> b P))"
    let r9 ← MESON [] q8
    prove
      r"!r:A ring s:B ring h p.
          (!P. prime_ideal s P /\ IMAGE h p SUBSET P
               ==> FINITE(ring_carrier(quotient_ring s P)))
          ==> (unramified (r,s) h p <=> weakly_unramified (r,s) h p)"
      (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [unramified, weakly_unramified] THEN MATCH_MP_TAC r9 THEN X_GEN_TAC q7 THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC q6)) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC q5 THEN DISCH_TAC THEN SUBGOAL_THEN q4 ASSUME_TAC THENL [MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_IMP_FIELD THEN ASM_MESON_TAC [INTEGRAL_DOMAIN_QUOTIENT_RING, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN MP_TAC v3 THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MATCH_MP_TAC PERFECT_FIELD_IMP_SEPARABLE_EXTENSION THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_FIELD_IMP_PERFECT THEN ASM_SIMP_TAC [FINITE_SUBRING_GENERATED] THEN ASM_MESON_TAC [field_extension], MATCH_MP_TAC FINITE_IMP_ALGEBRAIC_EXTENSION THEN ASM_SIMP_TAC [FINITE_EQ_FIELD_EXTENSION]])

  let UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_PERFECT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"ring_coset s P o (h:A->B)"
    let q2 ← q r"quotient_ring s (P:B->bool)"
    let q3 ← q r"r:A ring"
    let v4 ← ISPECL [q3, q2, q1] FIRST_RING_ISOMORPHISM_THEOREM
    let q5 ← q r"prime_ideal s (P:B->bool)"
    let q6 ← q r"h:A->B"
    let q7 ← q r"s:B ring"
    let q8 ← q r"r:A ring"
    let v9 ← ISPECL [q8, q7, q6] RING_HOMOMORPHISM_1
    let q10 ← q r"s:B ring"
    let q11 ← q r"p:A->bool"
    let q12 ← q r"r:A ring"
    let v13 ← ISPECL [q12, q11] RING_IDEAL_IMP_SUBSET
    let q14 ← q r"(a:A->bool) SUBSET b /\ c ==> ~(c /\ a PSUBSET b) ==> b = a"
    let r15 ← SET_RULE q14
    let q16 ← q r"{x | x IN ring_carrier r /\ (h:A->B) x IN P}"
    let q17 ← q r"(x:A) IN ring_carrier r"
    let q18 ← q r"x:A"
    let q19 ← q r"ring_kernel (r,quotient_ring s P) (ring_coset s P o (h:A->B)) =
      {x | x IN ring_carrier r /\ h x IN P}"
    let q20 ← q r"ring_kernel (r,quotient_ring s P) (ring_coset s P o (h:A->B)) = p"
    let q21 ← q r"s:B ring"
    let q22 ← q r"ring_homomorphism(r,quotient_ring s P) (ring_coset s P o (h:A->B))"
    let q23 ← q r"P:B->bool"
    let q24 ← q r"!a b c. (!P:B->bool. a P ==> c P)
            ==> ((!P. a P ==> b P /\ c P) <=> (!P. a P ==> b P))"
    let r25 ← MESON [] q24
    prove
      r"!r:A ring s:B ring h p.
          ring_homomorphism(r,s) h /\ maximal_ideal r p /\
          perfect_field(quotient_ring r p) /\
          (!P. prime_ideal s P /\ IMAGE h p SUBSET P
               ==> algebraic_extension
                    (subring_generated (quotient_ring s P)
                       (IMAGE (ring_coset s P o h) (ring_carrier r)),
                     quotient_ring s P) I)
          ==> (unramified (r,s) h p <=> weakly_unramified (r,s) h p)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [unramified, weakly_unramified] THEN MATCH_MP_TAC r25 THEN X_GEN_TAC q23 THEN STRIP_TAC THEN MATCH_MP_TAC PERFECT_FIELD_IMP_SEPARABLE_EXTENSION THEN ASM_SIMP_TAC [] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN q22 ASSUME_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC q21 THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET], ALL_TAC] THEN SUBGOAL_THEN q20 ASSUME_TAC THENL [FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [maximal_ideal])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PROPER_IMP_RING_IDEAL)) THEN SUBGOAL_THEN q19 SUBST1_TAC THENL [REWRITE_TAC [ring_kernel] THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, o_THM] THEN X_GEN_TAC q18 THEN ASM_CASES_TAC q17 THEN ASM_SIMP_TAC [QUOTIENT_RING_0] THEN MATCH_MP_TAC RING_COSET_EQ_IDEAL THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q16) o (REWRITE_RULE [NOT_EXISTS_THM]))) THEN MATCH_MP_TAC r15 THEN CONJ_TAC THENL [MP_TAC v13 THEN ASM SET_TAC [], ALL_TAC] THEN REWRITE_TAC [PROPER_IDEAL] THEN CONJ_TAC THENL [MATCH_MP_TAC RING_IDEAL_HOMOMORPHIC_PREIMAGE THEN EXISTS_TAC q10 THEN ASM_REWRITE_TAC [], REWRITE_TAC [IN_ELIM_THM, RING_1] THEN MP_TAC v9 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN UNDISCH_TAC q5 THEN SIMP_TAC [prime_ideal, PROPER_IDEAL]], ALL_TAC] THEN MP_TAC v4 THEN ASM_REWRITE_TAC [ring_image] THEN DISCH_THEN (SUBST1_TAC o (SYM o (MATCH_MP ISOMORPHIC_RING_PERFECT_FIELD))) THEN ASM_REWRITE_TAC [])

  let RING_OF_INTEGERS_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED ← prove
    r"!r:A ring k:B ring h p.
        number_field k /\ ~(IMAGE h p SUBSET {ring_0 k})
        ==> (unramified (r,ring_of_integers k) h p <=>
             weakly_unramified (r,ring_of_integers k) h p)"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_FINITE THEN X_GEN_TAC (← q r"P:B->bool") THEN STRIP_TAC THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC [])

  let NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_Q ← prove
    r"!k:A ring p.
        number_field k /\ ~(p = 0)
        ==> (unramified (integer_ring,ring_of_integers k) (ring_of_int k)
               (ideal_generated integer_ring {&p}) <=>
             weakly_unramified (integer_ring,ring_of_integers k)
               (ring_of_int k) (ideal_generated integer_ring {&p}))"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_OF_INTEGERS_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED THEN ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_SING, NOT_FORALL_THM, NOT_IMP] THEN EXISTS_TAC (← q r"&p:int") THEN SIMP_TAC [IDEAL_GENERATED_INC, INTEGER_RING, SUBSET_UNIV, IN_SING] THEN REWRITE_TAC [RING_OF_INT_OF_NUM, RING_OF_NUM_EQ_0] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← CONJUNCT1 (← REWRITE_RULE [number_field] th))])) THEN ASM_REWRITE_TAC [DIVIDES_ZERO])

  let NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED ← prove
    r"!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        ring_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> (unramified (ring_of_integers k,ring_of_integers l) h p <=>
             weakly_unramified (ring_of_integers k,ring_of_integers l) h p)"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_OF_INTEGERS_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED THEN ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_SING] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~(p = {ring_0(k:A ring)})") THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [SING_SUBSET] THEN ASM_MESON_TAC [IN_RING_IDEAL_0, RING_OF_INTEGERS]] THEN REWRITE_TAC [SUBSET, IN_SING] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] FIELD_RING_HOMOMORPHISM_MONOMORPHISM) THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING, NUMBER_FIELD_IMP_FIELD] THEN REWRITE_TAC [ring_monomorphism] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_0) THEN ASM_SIMP_TAC [RING_0])

  let SPLITTING_TYPES_PRINCIPAL ← prove
    r"!r:A ring s:B ring h p c e f.
        IMAGE h p SUBSET ring_carrier s /\ c IN ring_carrier s /\
        ideal_generated s (IMAGE h p) = ideal_generated s {c} /\
        (!P. prime_ideal s P /\ c IN P
             ==> ramification_index (r,s) h P = e P /\
                 residue_degree (r,s) h P = f P)
        ==> (weakly_unramified (r,s) h p <=>
             !P. prime_ideal s P /\ c IN P ==> e P = 1) /\
            (totally_split (r,s) h p <=>
             !P. prime_ideal s P /\ c IN P ==> e P = 1 /\ f P = 1) /\
            (inert (r,s) h p <=>
             prime_ideal s (ideal_generated s {c})) /\
            (totally_ramified (r,s) h p <=>
             ?P. {Q | prime_ideal s Q /\ c IN Q} = {P} /\ f P = 1)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!P. prime_ideal s P ==> (IMAGE (h:A->B) p SUBSET P <=> c IN P)") ASSUME_TAC THENL [X_GEN_TAC (← q r"P:B->bool") THEN DISCH_THEN (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN TRANS_TAC EQ_TRANS (← q r"ideal_generated s (IMAGE (h:A->B) p) SUBSET P") THEN CONJ_TAC THENL [ALL_TAC, ASM_REWRITE_TAC []] THEN ASM_SIMP_TAC [IDEAL_GENERATED_MINIMAL_EQ] THEN ASM SET_TAC [], ALL_TAC] THEN REWRITE_TAC [weakly_unramified, totally_split, inert, totally_ramified] THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"{Q | prime_ideal s Q /\ IMAGE (h:A->B) p SUBSET Q} =
    {Q | prime_ideal s Q /\ c IN Q}") SUBST1_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN REPEAT CONJ_TAC THEN AP_TERM_TAC THEN ABS_TAC THENL [ASM_CASES_TAC (← q r"prime_ideal s (P:B->bool)") THEN ASM_SIMP_TAC [], ASM_CASES_TAC (← q r"prime_ideal s (P:B->bool)") THEN ASM_SIMP_TAC [], ASM_CASES_TAC (← q r"{Q | prime_ideal s Q /\ c IN Q} = {P:B->bool}") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(P:B->bool) IN {Q | prime_ideal s Q /\ c IN Q}") MP_TAC THENL [ASM_REWRITE_TAC [IN_SING], REWRITE_TAC [IN_ELIM_THM]] THEN DISCH_THEN (fun th => ASM_SIMP_TAC [th])])

  let SPLITTING_TYPES_INTEGER_RING ← prove
    r"!r:A ring p.
        prime p
        ==> (weakly_unramified (integer_ring,r) (ring_of_int r)
               (ideal_generated integer_ring {&p}) <=>
             !P. prime_ideal r P /\ ring_of_num r p IN P
                 ==> ramification_index (integer_ring,r) (ring_of_int r) P =
                     1) /\
            (totally_split (integer_ring,r) (ring_of_int r)
               (ideal_generated integer_ring {&p}) <=>
             !P. prime_ideal r P /\ ring_of_num r p IN P
                 ==> ramification_index (integer_ring,r) (ring_of_int r) P =
                     1 /\
                     residue_degree (integer_ring,r) (ring_of_int r) P = 1) /\
            (inert (integer_ring,r) (ring_of_int r)
               (ideal_generated integer_ring {&p}) <=>
             prime_ideal r (ideal_generated r {ring_of_num r p})) /\
            (totally_ramified (integer_ring,r) (ring_of_int r)
               (ideal_generated integer_ring {&p}) <=>
             ?P. {Q | prime_ideal r Q /\ ring_of_num r p IN Q} = {P} /\
                 residue_degree (integer_ring,r) (ring_of_int r) P = 1)"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SPLITTING_TYPES_PRINCIPAL THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, RING_OF_INT, RING_OF_NUM] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"r:A ring"), (← q r"ring_of_int r:int->A"), (← q r"{&p:int}")] IDEAL_GENERATED_IMAGE_IDEAL_GENERATED) THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, INTEGER_RING, SUBSET_UNIV, IMAGE_CLAUSES, RING_OF_INT_OF_NUM])

  let IDEAL_PRODUCT_SPLITTING_TYPES ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r6 ← TAUT (← q r"(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)")
    let r7 ← ARITH_RULE (← q r"a = a * b <=> a * b = a * 1")
    let r12 ← ARITH_RULE (← q r"a * b = b <=> a * b = 1 * b")
    let r17 ← ARITH_RULE (← q r"x - 1 = 0 <=> x = 0 \/ x = 1")
    let r18 ← ARITH_RULE (← q r"a = a + b <=> b = 0")
    let r19 ← ARITH_RULE (← q r"a + b = 0 <=> a = 0 /\ b = 0")
    let r20 ← ARITH_RULE (← q r"~(x = 0) ==> x = 1 + (x - 1)")
    prove
      r"!s:B ring S j e f n.
          FINITE S /\ ~(S = {}) /\
          (!P. P IN S ==> prime_ideal s P /\ 1 <= e P /\ 1 <= f P) /\
          j = ideal_product s S (\P. ideal_pow s P (e P)) /\
          (!t d. FINITE t /\ (!P. P IN t ==> prime_ideal s P /\ ~(d P = 0)) /\
                 j = ideal_product s t (\P. ideal_pow s P (d P))
                 ==> t = S /\ !P. P IN t ==> e P = d P) /\
          nsum S (\P. e P * f P) = n
          ==> ((!P. P IN S ==> e P = 1) <=> j = ideal_product s S (\P. P)) /\
              ((!P. P IN S ==> e P = 1 /\ f P = 1) <=> CARD S = n) /\
              (prime_ideal s j <=> ?P. S = {P} /\ f P = n) /\
              ((?P. S = {P} /\ f P = 1) <=> ?P. S = {P} /\ e P = n) /\
              ((?P. S = {P} /\ f P = 1) <=>
               ?P. prime_ideal s P /\ j = ideal_pow s P n) /\
              (prime_ideal s j ==> !P. P IN S ==> e P = 1) /\
              (1 < n
               ==> ((?P. S = {P} /\ f P = 1) ==> ~(!P. P IN S ==> e P = 1)) /\
                   ~((!P. P IN S ==> e P = 1 /\ f P = 1) /\ prime_ideal s j) /\
                   ~((!P. P IN S ==> e P = 1 /\ f P = 1) /\
                     (?P. S = {P} /\ f P = 1)) /\
                   ~(prime_ideal s j /\ (?P. S = {P} /\ f P = 1)))"
      (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))))) THEN SUBGOAL_THEN (← q r"~(n = 0) /\
      ((!P. P IN S ==> (e:(B->bool)->num) P = 1 /\ (f:(B->bool)->num) P = 1) <=>
       CARD(S:(B->bool)->bool) = n)") STRIP_ASSUME_TAC THENL [SUBGOAL_THEN (← q r"n = CARD(S:(B->bool)->bool) +
                        nsum S (\P. (e:(B->bool)->num) P * f P - 1)") SUBST1_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z24 ← (q r"n:num"); let z23 ← (do let z21 ← (do let z22 ← (pure th); pure (concl z22)); liftExcept (rhs z21)); pure (z23 == z24)))))) THEN ASM_SIMP_TAC [CARD_EQ_NSUM, (← GSYM NSUM_ADD)] THEN MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"P:B->bool") THEN DISCH_THEN (fun th => tactic_of do pure (FIRST_ASSUM (MP_TAC o (← do let c := th; pure (fun th => MATCH_MP th c))))) THEN REWRITE_TAC [] THEN STRIP_TAC THEN MATCH_MP_TAC r20 THEN REWRITE_TAC [MULT_EQ_0, DE_MORGAN_THM] THEN UNDISCH_TAC (← q r"1 <= (e:(B->bool)->num) P") THEN UNDISCH_TAC (← q r"1 <= (f:(B->bool)->num) P") THEN ARITH_TAC, ASM_SIMP_TAC [r19, CARD_EQ_0, r18, NSUM_EQ_0_IFF] THEN AP_TERM_TAC THEN ABS_TAC THEN ASM_CASES_TAC (← q r"(P:B->bool) IN S") THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MP_TAC o (← do let c := (← ASSUME (← q r"(P:B->bool) IN S")); pure (fun th => MATCH_MP th c))) THEN REWRITE_TAC [r17, MULT_EQ_0, MULT_EQ_1] THEN ARITH_TAC], ALL_TAC] THEN DISCH_THEN (fun th => tactic_of do pure (MP_TAC (← SPECL [(← q r"S:(B->bool)->bool"), (← q r"\P:B->bool. 1")] th) THEN MP_TAC (← GEN (← q r"P:B->bool") (← GEN (← q r"m:num") (← SPECL [(← q r"{P:B->bool}"), (← q r"\Q:B->bool. (m:num)")] th))))) THEN REWRITE_TAC [FINITE_SING, FORALL_IN_INSERT, NOT_IN_EMPTY] THEN SIMP_TAC [IDEAL_PRODUCT_SING, RING_IDEAL_IDEAL_POW] THEN DISCH_TAC THEN REWRITE_TAC [ARITH_EQ, IMP_CONJ, (← ASSUME (← q r"FINITE(S:(B->bool)->bool)"))] THEN ANTS_TAC THENL [X_GEN_TAC (← q r"P:B->bool") THEN DISCH_THEN (fun th => tactic_of do pure (FIRST_ASSUM (MP_TAC o (← do let c := th; pure (fun th => MATCH_MP th c))))) THEN SIMP_TAC [], DISCH_TAC] THEN SUBGOAL_THEN (← q r"(!P. P IN S ==> (e:(B->bool)->num) P = 1) <=>
      j = ideal_product (s:B ring) S (\P. P)") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"ideal_product s S (\P. P) =
        ideal_product (s:B ring) S (\P. ideal_pow s P 1)") SUBST1_TAC THENL [MATCH_MP_TAC IDEAL_PRODUCT_EQ THEN X_GEN_TAC (← q r"P:B->bool") THEN DISCH_THEN (fun th => tactic_of do pure (FIRST_ASSUM (MP_TAC o (← do let c := th; pure (fun th => MATCH_MP th c))))) THEN SIMP_TAC [IDEAL_POW_1, PRIME_IMP_RING_IDEAL], EQ_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z16 ← (q r"j:B->bool"); let z15 ← (do let z13 ← (do let z14 ← (pure th); pure (concl z14)); liftExcept (rhs z13)); pure (z15 == z16)))))) THEN MATCH_MP_TAC IDEAL_PRODUCT_EQ THEN X_GEN_TAC (← q r"P:B->bool") THEN DISCH_THEN (fun th => tactic_of do pure (FIRST_X_ASSUM (MP_TAC o (← do let c := th; pure (fun th => MATCH_MP th c))))) THEN SIMP_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P. S = {P}
          ==> prime_ideal (s:B ring) P /\ j = ideal_pow s P (e P) /\
              e P * (f:(B->bool)->num) P = n /\ 1 <= e P /\ 1 <= f P") ASSUME_TAC THENL [X_GEN_TAC (← q r"P:B->bool") THEN DISCH_THEN SUBST_ALL_TAC THEN RULE_ASSUM_TAC (SIMP_RULE [NSUM_SING, FORALL_IN_INSERT, NOT_IN_EMPTY, IDEAL_PRODUCT_SING, RING_IDEAL_IDEAL_POW]) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"prime_ideal (s:B ring) j
      ==> (S:(B->bool)->bool) = {j} /\ (e:(B->bool)->num) j = 1") ASSUME_TAC THENL [DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (SPECL [(← q r"j:B->bool"), (← q r"1")])) THEN SIMP_TAC [ARITH_EQ, IDEAL_POW_1, PRIME_IMP_RING_IDEAL, (← ASSUME (← q r"prime_ideal (s:B ring) j"))] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"prime_ideal (s:B ring) j <=>
      ?P. (S:(B->bool)->bool) = {P} /\ (f:(B->bool)->num) P = n") ASSUME_TAC THENL [EQ_TAC THENL [DISCH_THEN (fun th => tactic_of do pure (FIRST_ASSUM (MP_TAC o (← do let c := th; pure (fun th => MATCH_MP th c))))) THEN DISCH_THEN (fun th => tactic_of do pure (EXISTS_TAC (← q r"j:B->bool") THEN REWRITE_TAC [(← CONJUNCT1 th)] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (CONJUNCT2 o (CONJUNCT2 o (← do let c := (← CONJUNCT1 th); pure (fun th => MATCH_MP th c)))))) THEN REWRITE_TAC [(← CONJUNCT2 th), MULT_CLAUSES])), DISCH_THEN (X_CHOOSE_THEN (← q r"P:B->bool") STRIP_ASSUME_TAC) THEN FIRST_ASSUM (MP_TAC o (← do let c := (← ASSUME (← q r"S = {P:B->bool}")); pure (fun th => MATCH_MP th c))) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [r12, EQ_MULT_RCANCEL] THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [IDEAL_POW_1, PRIME_IMP_RING_IDEAL]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P. S = {P} ==> ((f:(B->bool)->num) P = 1 <=> (e:(B->bool)->num) P = n)") ASSUME_TAC THENL [X_GEN_TAC (← q r"P:B->bool") THEN DISCH_THEN (fun th => tactic_of do pure (FIRST_ASSUM (MP_TAC o (← do let c := th; pure (fun th => MATCH_MP th c))))) THEN STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z11 ← (q r"n:num"); let z10 ← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); liftExcept (rhs z8)); pure (z10 == z11)))))) THEN REWRITE_TAC [r7, EQ_MULT_LCANCEL] THEN UNDISCH_TAC (← q r"1 <= (e:(B->bool)->num) P") THEN ARITH_TAC, ALL_TAC] THEN REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL [AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC r6 THEN FIRST_ASSUM MATCH_ACCEPT_TAC, EQ_TAC THEN DISCH_THEN (X_CHOOSE_THEN (← q r"P:B->bool") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"P:B->bool") THENL [FIRST_ASSUM (MP_TAC o ((← do let c := (← ASSUME (← q r"S = {P:B->bool}")); pure (fun th => MATCH_MP th c)) o (checkM (fun z1 => (do let z2 ← (do let z3 ← (do pure (Prod.snd (← (do let z4 ← (do let z5 ← (pure z1); pure (concl z5)); pure (strip_forall z4))))); liftExcept (rand z3)); pure (is_conj z2)))))) THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN STRIP_TAC THEN ASM_REWRITE_TAC [], FIRST_ASSUM (MP_TAC o (SPECL [(← q r"P:B->bool"), (← q r"n:num")])) THEN REWRITE_TAC [(← ASSUME (← q r"prime_ideal (s:B ring) P")), (← ASSUME (← q r"~(n = 0)")), (← ASSUME (← q r"j = ideal_pow (s:B ring) P n"))] THEN DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MP_TAC o (← do let c := (← ASSUME (← q r"S = {P:B->bool}")); pure (fun th => MATCH_MP th c))) THEN ASM_REWRITE_TAC []], DISCH_THEN (fun th => tactic_of do pure (FIRST_ASSUM (MP_TAC o (← do let c := th; pure (fun th => MATCH_MP th c))))) THEN DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN REWRITE_TAC [IN_SING] THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [], DISCH_TAC THEN REPEAT CONJ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"P:B->bool") STRIP_ASSUME_TAC) THEN DISCH_THEN (MP_TAC o (SPEC (← q r"P:B->bool"))) THEN FIRST_ASSUM (MP_TAC o (← do let c := (← ASSUME (← q r"S = {P:B->bool}")); pure (fun th => MATCH_MP th c))) THEN ASM_REWRITE_TAC [IN_SING] THEN UNDISCH_TAC (← q r"1 < n") THEN ARITH_TAC, ASM_REWRITE_TAC [] THEN STRIP_TAC THEN UNDISCH_TAC (← q r"CARD(S:(B->bool)->bool) = n") THEN ASM_REWRITE_TAC [CARD_SING] THEN UNDISCH_TAC (← q r"1 < n") THEN ARITH_TAC, ASM_REWRITE_TAC [] THEN STRIP_TAC THEN UNDISCH_TAC (← q r"CARD(S:(B->bool)->bool) = n") THEN ASM_REWRITE_TAC [CARD_SING] THEN UNDISCH_TAC (← q r"1 < n") THEN ARITH_TAC, ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"P:B->bool") STRIP_ASSUME_TAC) (X_CHOOSE_THEN (← q r"Q:B->bool") STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"(P:B->bool) IN S") MP_TAC THENL [REWRITE_TAC [(← ASSUME (← q r"S = {P:B->bool}")), IN_SING], ALL_TAC] THEN REWRITE_TAC [(← ASSUME (← q r"S = {Q:B->bool}")), IN_SING] THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"(f:(B->bool)->num) Q = n") THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"1 < n") THEN ARITH_TAC]])

  let NUMBER_FIELD_PRIME_DECOMPOSITION_Q ← prove
    r"!k:A ring p.
        number_field k /\ prime p
        ==> FINITE {P | prime_ideal (ring_of_integers k) P /\
                        ring_of_num k p IN P} /\
            ~({P | prime_ideal (ring_of_integers k) P /\
                   ring_of_num k p IN P} = {}) /\
            (!P. P IN {P | prime_ideal (ring_of_integers k) P /\
                           ring_of_num k p IN P}
                 ==> prime_ideal (ring_of_integers k) P /\
                     1 <= ramification_index (integer_ring,ring_of_integers k)
                            (ring_of_int k) P /\
                     1 <= residue_degree (integer_ring,ring_of_integers k)
                            (ring_of_int k) P) /\
            ideal_generated (ring_of_integers k) {ring_of_num k p} =
            ideal_product (ring_of_integers k)
              {P | prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P}
              (\P. ideal_pow (ring_of_integers k) P
                     (ramification_index (integer_ring,ring_of_integers k)
                        (ring_of_int k) P)) /\
            (!t d. FINITE t /\
                   (!P. P IN t ==> prime_ideal (ring_of_integers k) P /\
                                   ~(d P = 0)) /\
                   ideal_generated (ring_of_integers k) {ring_of_num k p} =
                   ideal_product (ring_of_integers k) t
                     (\P. ideal_pow (ring_of_integers k) P (d P))
                   ==> t = {P | prime_ideal (ring_of_integers k) P /\
                                ring_of_num k p IN P} /\
                       !P. P IN t
                           ==> ramification_index
                               (integer_ring,ring_of_integers k) (ring_of_int
                                   k) P =
                               d P) /\
            nsum {P | prime_ideal (ring_of_integers k) P /\
                      ring_of_num k p IN P}
                 (\P. ramification_index (integer_ring,ring_of_integers k)
                        (ring_of_int k) P *
                      residue_degree (integer_ring,ring_of_integers k)
                        (ring_of_int k) P) =
            extension_degree (subfield_generated k {ring_0 k},k) I"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q, IN_ELIM_THM, NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q] THEN REPEAT CONJ_TAC THENL [X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q) THEN ASM_SIMP_TAC [], ASM_SIMP_TAC [NUMBER_FIELD_PRIME_FACTORIZATION_Q], REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_Q THEN ASM_REWRITE_TAC []])

  let NUMBER_FIELD_UNRAMIFIED_DISCRIMINANT ← prove
    r"!k:A ring p.
        number_field k /\ prime p
        ==> (unramified (integer_ring,ring_of_integers k)
               (ring_of_int k) (ideal_generated integer_ring {&p}) <=>
             ~(&p divides number_field_discriminant k))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_Q, PRIME_IMP_NZ] THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") SPLITTING_TYPES_INTEGER_RING)), (← GSYM NUMBER_FIELD_RAMIFIED_DISCRIMINANT), NOT_EXISTS_THM, CONJ_ASSOC] THEN AP_TERM_TAC THEN ABS_TAC THEN ASM_CASES_TAC (← q r"prime_ideal (ring_of_integers k) P /\ ring_of_num (k:A ring) p IN P") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC)

  let NUMBER_FIELD_UNRAMIFIED_FACTORIZATION ← prove
    r"!k:A ring p.
        number_field k /\ prime p
        ==> (unramified (integer_ring,ring_of_integers k)
               (ring_of_int k) (ideal_generated integer_ring {&p}) <=>
             ideal_generated (ring_of_integers k) {ring_of_num k p} =
             ideal_product (ring_of_integers k)
               {P | prime_ideal (ring_of_integers k) P /\
                    ring_of_num k p IN P}
               (\P. P))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_Q, PRIME_IMP_NZ] THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") SPLITTING_TYPES_INTEGER_RING))] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] NUMBER_FIELD_PRIME_DECOMPOSITION_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun z1 => tactic_of do pure (MP_TAC (← (do let z2 ← (do pure (CONJUNCTS (← MATCH_MP IDEAL_PRODUCT_SPLITTING_TYPES z1))); let z3 ← (pure 0); liftExcept (el z3 z2))))) THEN SIMP_TAC [IN_ELIM_THM])

  let NUMBER_FIELD_TOTALLY_SPLIT_CARD ← prove
    r"!k:A ring p.
        number_field k /\ prime p
        ==> (totally_split (integer_ring,ring_of_integers k)
               (ring_of_int k) (ideal_generated integer_ring {&p}) <=>
             CARD {P | prime_ideal (ring_of_integers k) P /\
                       ring_of_num k p IN P} =
             extension_degree (subfield_generated k {ring_0 k},k) I)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") SPLITTING_TYPES_INTEGER_RING))] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] NUMBER_FIELD_PRIME_DECOMPOSITION_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun z1 => tactic_of do pure (MP_TAC (← (do let z2 ← (do pure (CONJUNCTS (← MATCH_MP IDEAL_PRODUCT_SPLITTING_TYPES z1))); let z3 ← (pure 1); liftExcept (el z3 z2))))) THEN SIMP_TAC [IN_ELIM_THM])

  let NUMBER_FIELD_INERT_RESIDUE_DEGREE ← prove
    r"!k:A ring p.
        number_field k /\ prime p
        ==> (inert (integer_ring,ring_of_integers k)
               (ring_of_int k) (ideal_generated integer_ring {&p}) <=>
             ?P. {Q | prime_ideal (ring_of_integers k) Q /\
                      ring_of_num k p IN Q} = {P} /\
                 residue_degree (integer_ring,ring_of_integers k)
                   (ring_of_int k) P =
                 extension_degree (subfield_generated k {ring_0 k},k) I)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") SPLITTING_TYPES_INTEGER_RING))] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] NUMBER_FIELD_PRIME_DECOMPOSITION_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun z1 => tactic_of do pure (MP_TAC (← (do let z2 ← (do pure (CONJUNCTS (← MATCH_MP IDEAL_PRODUCT_SPLITTING_TYPES z1))); let z3 ← (pure 2); liftExcept (el z3 z2))))) THEN SIMP_TAC [IN_ELIM_THM])

  let NUMBER_FIELD_TOTALLY_RAMIFIED_RAMIFICATION_INDEX ← prove
    r"!k:A ring p.
        number_field k /\ prime p
        ==> (totally_ramified (integer_ring,ring_of_integers k)
               (ring_of_int k) (ideal_generated integer_ring {&p}) <=>
             ?P. {Q | prime_ideal (ring_of_integers k) Q /\
                      ring_of_num k p IN Q} = {P} /\
                 ramification_index (integer_ring,ring_of_integers k)
                   (ring_of_int k) P =
                 extension_degree (subfield_generated k {ring_0 k},k) I)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") SPLITTING_TYPES_INTEGER_RING))] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] NUMBER_FIELD_PRIME_DECOMPOSITION_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun z1 => tactic_of do pure (MP_TAC (← (do let z2 ← (do pure (CONJUNCTS (← MATCH_MP IDEAL_PRODUCT_SPLITTING_TYPES z1))); let z3 ← (pure 3); liftExcept (el z3 z2))))) THEN SIMP_TAC [IN_ELIM_THM])

  let NUMBER_FIELD_TOTALLY_RAMIFIED_IDEAL_POW ← prove
    r"!k:A ring p.
        number_field k /\ prime p
        ==> (totally_ramified (integer_ring,ring_of_integers k)
               (ring_of_int k) (ideal_generated integer_ring {&p}) <=>
             ?P. prime_ideal (ring_of_integers k) P /\
                 ideal_generated (ring_of_integers k) {ring_of_num k p} =
                 ideal_pow (ring_of_integers k) P
                   (extension_degree (subfield_generated k {ring_0 k},k) I))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") SPLITTING_TYPES_INTEGER_RING))] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] NUMBER_FIELD_PRIME_DECOMPOSITION_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun z1 => tactic_of do pure (MP_TAC (← (do let z2 ← (do pure (CONJUNCTS (← MATCH_MP IDEAL_PRODUCT_SPLITTING_TYPES z1))); let z3 ← (pure 4); liftExcept (el z3 z2))))) THEN SIMP_TAC [IN_ELIM_THM])

  let NUMBER_FIELD_INERT_IMP_UNRAMIFIED ← prove
    r"!k:A ring p.
        number_field k /\ prime p /\
        inert (integer_ring,ring_of_integers k) (ring_of_int k)
          (ideal_generated integer_ring {&p})
        ==> unramified (integer_ring,ring_of_integers k)
              (ring_of_int k) (ideal_generated integer_ring {&p})"
    (REPEAT GEN_TAC THEN REWRITE_TAC [CONJ_ASSOC] THEN DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN ASM_SIMP_TAC [NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_Q, PRIME_IMP_NZ] THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") SPLITTING_TYPES_INTEGER_RING))] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] NUMBER_FIELD_PRIME_DECOMPOSITION_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun z1 => tactic_of do pure (MP_TAC (← (do let z2 ← (do pure (CONJUNCTS (← MATCH_MP IDEAL_PRODUCT_SPLITTING_TYPES z1))); let z3 ← (pure 5); liftExcept (el z3 z2))))) THEN SIMP_TAC [IN_ELIM_THM])

  let NUMBER_FIELD_SPLITTING_TYPES_EXCLUSIVE ← prove
    r"!k:A ring p.
        number_field k /\ prime p /\
        1 < extension_degree (subfield_generated k {ring_0 k},k) I
        ==> (totally_ramified (integer_ring,ring_of_integers k)
               (ring_of_int k) (ideal_generated integer_ring {&p})
             ==> ~(unramified (integer_ring,ring_of_integers k)
                     (ring_of_int k) (ideal_generated integer_ring {&p}))) /\
            ~(totally_split (integer_ring,ring_of_integers k)
                (ring_of_int k) (ideal_generated integer_ring {&p}) /\
              inert (integer_ring,ring_of_integers k)
                (ring_of_int k) (ideal_generated integer_ring {&p})) /\
            ~(totally_split (integer_ring,ring_of_integers k)
                (ring_of_int k) (ideal_generated integer_ring {&p}) /\
              totally_ramified (integer_ring,ring_of_integers k)
                (ring_of_int k) (ideal_generated integer_ring {&p})) /\
            ~(inert (integer_ring,ring_of_integers k)
                (ring_of_int k) (ideal_generated integer_ring {&p}) /\
              totally_ramified (integer_ring,ring_of_integers k)
                (ring_of_int k) (ideal_generated integer_ring {&p}))"
    (REPEAT GEN_TAC THEN REWRITE_TAC [CONJ_ASSOC] THEN DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN ASM_SIMP_TAC [NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_Q, PRIME_IMP_NZ] THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") SPLITTING_TYPES_INTEGER_RING))] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] NUMBER_FIELD_PRIME_DECOMPOSITION_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun z1 => tactic_of do pure (MP_TAC (← (do let z2 ← (do pure (CONJUNCTS (← MATCH_MP IDEAL_PRODUCT_SPLITTING_TYPES z1))); let z3 ← (pure 6); liftExcept (el z3 z2))))) THEN SIMP_TAC [IN_ELIM_THM])

  let NUMBER_FIELD_PRIME_DECOMPOSITION ← prove
    r"!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> FINITE {P | prime_ideal (ring_of_integers l) P /\
                        IMAGE h p SUBSET P} /\
            ~({P | prime_ideal (ring_of_integers l) P /\
                   IMAGE h p SUBSET P} = {}) /\
            (!P. P IN {P | prime_ideal (ring_of_integers l) P /\
                           IMAGE h p SUBSET P}
                 ==> prime_ideal (ring_of_integers l) P /\
                     1 <= ramification_index
                            (ring_of_integers k,ring_of_integers l) h P /\
                     1 <= residue_degree
                            (ring_of_integers k,ring_of_integers l) h P) /\
            ideal_generated (ring_of_integers l) (IMAGE h p) =
            ideal_product (ring_of_integers l)
              {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
              (\P. ideal_pow (ring_of_integers l) P
                     (ramification_index
                        (ring_of_integers k,ring_of_integers l) h P)) /\
            (!t d. FINITE t /\
                   (!P. P IN t ==> prime_ideal (ring_of_integers l) P /\
                                   ~(d P = 0)) /\
                   ideal_generated (ring_of_integers l) (IMAGE h p) =
                   ideal_product (ring_of_integers l) t
                     (\P. ideal_pow (ring_of_integers l) P (d P))
                   ==> t = {P | prime_ideal (ring_of_integers l) P /\
                                IMAGE h p SUBSET P} /\
                       !P. P IN t
                           ==> ramification_index
                                 (ring_of_integers k,ring_of_integers l) h P =
                               d P) /\
            nsum {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
                 (\P. ramification_index
                        (ring_of_integers k,ring_of_integers l) h P *
                      residue_degree
                        (ring_of_integers k,ring_of_integers l) h P) =
            extension_degree (k,l) h"
    (REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [IN_ELIM_THM, (← MATCH_MP NUMBER_FIELD_PRIME_IDEALS_ABOVE th), (← MATCH_MP NUMBER_FIELD_FUNDAMENTAL_IDENTITY th)])) THEN REPEAT CONJ_TAC THENL [X_GEN_TAC (← q r"P:B->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS) THEN ASM_SIMP_TAC [], FIRST_ASSUM (ACCEPT_TAC o (MATCH_MP NUMBER_FIELD_PRIME_FACTORIZATION)), REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE THEN ASM_REWRITE_TAC []])

  -- @@RETURN BEGIN
  return { weakly_unramified, unramified, totally_split, inert, totally_ramified,
           UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED, UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_FINITE,
           UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_PERFECT,
           RING_OF_INTEGERS_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED,
           NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_Q,
           NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED, SPLITTING_TYPES_PRINCIPAL,
           SPLITTING_TYPES_INTEGER_RING, IDEAL_PRODUCT_SPLITTING_TYPES,
           NUMBER_FIELD_PRIME_DECOMPOSITION_Q, NUMBER_FIELD_UNRAMIFIED_DISCRIMINANT,
           NUMBER_FIELD_UNRAMIFIED_FACTORIZATION, NUMBER_FIELD_TOTALLY_SPLIT_CARD,
           NUMBER_FIELD_INERT_RESIDUE_DEGREE,
           NUMBER_FIELD_TOTALLY_RAMIFIED_RAMIFICATION_INDEX,
           NUMBER_FIELD_TOTALLY_RAMIFIED_IDEAL_POW, NUMBER_FIELD_INERT_IMP_UNRAMIFIED,
           NUMBER_FIELD_SPLITTING_TYPES_EXCLUSIVE, NUMBER_FIELD_PRIME_DECOMPOSITION }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- splitting_types.ml phrases from line 850 to 1175                       -/
/- ---------------------------------------------------------------------- -/

structure SplittingTypes02 where
  -- @@FIELDS
  UNRAMIFIED_FACTORIZATION : thm
  TOTALLY_SPLIT_CARD : thm
  INERT_RESIDUE_DEGREE : thm
  TOTALLY_RAMIFIED_RAMIFICATION_INDEX : thm
  TOTALLY_RAMIFIED_IDEAL_POW : thm
  INERT_IMP_UNRAMIFIED : thm
  SPLITTING_TYPES_EXCLUSIVE : thm
  UNRAMIFIED_DISCRIMINANT : thm
  FINITE_RAMIFIED : thm
  SPLITTING_TYPES_PRIME_SUBFIELD : thm
  NUMBER_FIELD_SUBFIELD_UNRAMIFIED_DISCRIMINANT : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupSplittingTypes02 [HolBase] (D : SplittingTypesDeps) (BSplittingTypes01 : SplittingTypes01) :
    ExceptT String IO SplittingTypes02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON, MESON_TAC, SET_TAC, .. } := D
  let { DIVIDES_ZERO, EXISTS_IN_IMAGE, EXISTS_UNIQUE_THM, EXTENSION, FINITE_IMAGE,
        FINITE_SUBSET, FINITE_UNIONS, FORALL_IN_IMAGE,
        IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, IDEAL_GENERATED_INC,
        IDEAL_GENERATED_SUBSET, IMAGE_I, IMP_IMP, IN_ELIM_THM, IN_SING, IN_UNIONS,
        MULT_EQ_1, NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP, NOT_LT,
        NUMBER_FIELD_FINITE_RAMIFIED_PRIMES, NUMBER_FIELD_HOMOMORPHIC_PREIMAGE,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q,
        NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q,
        NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q, NUMBER_FIELD_RAMIFIED_DISCRIMINANT,
        NUMBER_FIELD_SUBFIELD_GENERATED, PRIME_IMP_NZ, PRIME_IMP_RING_IDEAL,
        PRIME_SUBFIELD_SUBFIELD_GENERATED, RAMIFICATION_INDEX_PRIME_SUBFIELD,
        RESIDUE_DEGREE_PRIME_SUBFIELD, RING_HOMOMORPHISM_RING_OF_INTEGERS,
        RING_HOMOMORPHISM_RING_OF_NUM, RING_HOMOMORPHISM_SUBFIELD_INCLUSION,
        RING_OF_INTEGERS, RING_OF_INTEGERS_PRIME_IDEAL_ABOVE,
        RING_OF_INTEGERS_PRIME_IDEAL_BELOW, RING_OF_NUM, RING_OF_NUM_EQ_0,
        RING_OF_NUM_SUBFIELD_GENERATED, SING_SUBSET, SUBSET, SUBSET_TRANS,
        number_field, ring_homomorphism, .. } := D.core1
  let { IDEAL_PRODUCT_SPLITTING_TYPES, NUMBER_FIELD_PRIME_DECOMPOSITION,
        NUMBER_FIELD_UNRAMIFIED_DISCRIMINANT,
        NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED,
        NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_Q,
        RING_OF_INTEGERS_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED, SPLITTING_TYPES_INTEGER_RING,
        SPLITTING_TYPES_PRINCIPAL, inert, totally_ramified, totally_split,
        weakly_unramified, .. } := BSplittingTypes01
  -- @@SCOPE END

  let UNRAMIFIED_FACTORIZATION ← prove
    r"!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> (unramified (ring_of_integers k,ring_of_integers l)
               h p <=>
             ideal_generated (ring_of_integers l) (IMAGE h p) =
             ideal_product (ring_of_integers l)
               {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
               (\P. P))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED, PRIME_IMP_RING_IDEAL] THEN REWRITE_TAC [weakly_unramified] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_DECOMPOSITION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun z1 => tactic_of do pure (MP_TAC (← (do let z2 ← (do pure (CONJUNCTS (← MATCH_MP IDEAL_PRODUCT_SPLITTING_TYPES z1))); let z3 ← (pure 0); liftExcept (el z3 z2))))) THEN SIMP_TAC [IN_ELIM_THM])

  let TOTALLY_SPLIT_CARD ← prove
    r"!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> (totally_split (ring_of_integers k,ring_of_integers l)
               h p <=>
             CARD {P | prime_ideal (ring_of_integers l) P /\
                       IMAGE h p SUBSET P} =
             extension_degree (k,l) h)"
    (REPEAT GEN_TAC THEN REWRITE_TAC [totally_split] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_DECOMPOSITION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun z1 => tactic_of do pure (MP_TAC (← (do let z2 ← (do pure (CONJUNCTS (← MATCH_MP IDEAL_PRODUCT_SPLITTING_TYPES z1))); let z3 ← (pure 1); liftExcept (el z3 z2))))) THEN SIMP_TAC [IN_ELIM_THM])

  let INERT_RESIDUE_DEGREE ← prove
    r"!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> (inert (ring_of_integers k,ring_of_integers l) h p <=>
             ?P. {Q | prime_ideal (ring_of_integers l) Q /\
                      IMAGE h p SUBSET Q} = {P} /\
                 residue_degree
                   (ring_of_integers k,ring_of_integers l) h P =
                 extension_degree (k,l) h)"
    (REPEAT GEN_TAC THEN REWRITE_TAC [inert] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_DECOMPOSITION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun z1 => tactic_of do pure (MP_TAC (← (do let z2 ← (do pure (CONJUNCTS (← MATCH_MP IDEAL_PRODUCT_SPLITTING_TYPES z1))); let z3 ← (pure 2); liftExcept (el z3 z2))))) THEN SIMP_TAC [IN_ELIM_THM])

  let TOTALLY_RAMIFIED_RAMIFICATION_INDEX ← prove
    r"!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> (totally_ramified
               (ring_of_integers k,ring_of_integers l) h p <=>
             ?P. {Q | prime_ideal (ring_of_integers l) Q /\
                      IMAGE h p SUBSET Q} = {P} /\
                 ramification_index
                   (ring_of_integers k,ring_of_integers l) h P =
                 extension_degree (k,l) h)"
    (REPEAT GEN_TAC THEN REWRITE_TAC [totally_ramified] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_DECOMPOSITION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun z1 => tactic_of do pure (MP_TAC (← (do let z2 ← (do pure (CONJUNCTS (← MATCH_MP IDEAL_PRODUCT_SPLITTING_TYPES z1))); let z3 ← (pure 3); liftExcept (el z3 z2))))) THEN SIMP_TAC [IN_ELIM_THM])

  let TOTALLY_RAMIFIED_IDEAL_POW ← prove
    r"!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> (totally_ramified
               (ring_of_integers k,ring_of_integers l) h p <=>
             ?P. prime_ideal (ring_of_integers l) P /\
                 ideal_generated (ring_of_integers l) (IMAGE h p) =
                 ideal_pow (ring_of_integers l) P (extension_degree (k,l) h))"
    (REPEAT GEN_TAC THEN REWRITE_TAC [totally_ramified] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_DECOMPOSITION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun z1 => tactic_of do pure (MP_TAC (← (do let z2 ← (do pure (CONJUNCTS (← MATCH_MP IDEAL_PRODUCT_SPLITTING_TYPES z1))); let z3 ← (pure 4); liftExcept (el z3 z2))))) THEN SIMP_TAC [IN_ELIM_THM])

  let INERT_IMP_UNRAMIFIED ← prove
    r"!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        inert (ring_of_integers k,ring_of_integers l) h p
        ==> unramified (ring_of_integers k,ring_of_integers l) h p"
    (REPEAT GEN_TAC THEN REWRITE_TAC [inert] THEN STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED, PRIME_IMP_RING_IDEAL] THEN REWRITE_TAC [weakly_unramified] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_DECOMPOSITION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun z1 => tactic_of do pure (MP_TAC (← (do let z2 ← (do pure (CONJUNCTS (← MATCH_MP IDEAL_PRODUCT_SPLITTING_TYPES z1))); let z3 ← (pure 5); liftExcept (el z3 z2))))) THEN ASM_SIMP_TAC [IN_ELIM_THM])

  let SPLITTING_TYPES_EXCLUSIVE ← prove
    r"!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        1 < extension_degree (k,l) h
        ==> (totally_ramified
               (ring_of_integers k,ring_of_integers l) h p
             ==> ~(unramified
                     (ring_of_integers k,ring_of_integers l) h p)) /\
            ~(totally_split
                (ring_of_integers k,ring_of_integers l) h p /\
              inert (ring_of_integers k,ring_of_integers l) h p) /\
            ~(totally_split
                (ring_of_integers k,ring_of_integers l) h p /\
              totally_ramified
                (ring_of_integers k,ring_of_integers l) h p) /\
            ~(inert (ring_of_integers k,ring_of_integers l) h p /\
              totally_ramified
                (ring_of_integers k,ring_of_integers l) h p)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED, PRIME_IMP_RING_IDEAL] THEN REWRITE_TAC [weakly_unramified, totally_split, inert, totally_ramified] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_DECOMPOSITION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun z1 => tactic_of do pure (MP_TAC (← (do let z2 ← (do pure (CONJUNCTS (← MATCH_MP IDEAL_PRODUCT_SPLITTING_TYPES z1))); let z3 ← (pure 6); liftExcept (el z3 z2))))) THEN ASM_SIMP_TAC [IN_ELIM_THM])

  let UNRAMIFIED_DISCRIMINANT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"(a <= 1 /\ 1 <= a /\ c) /\ a = b ==> b = 1")
    prove
      r"!k:A ring l:B ring h p q.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime q /\ ring_of_num k q IN p /\
          ~(&q divides number_field_discriminant l)
          ==> unramified (ring_of_integers k,ring_of_integers l) h p"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_SING, NOT_FORALL_THM, NOT_IMP] THEN EXISTS_TAC (← q r"ring_of_num k q:A") THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (SUBST1_TAC o ((SPEC (← q r"q:num")) o (MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM))) THEN REWRITE_TAC [RING_OF_NUM_EQ_0] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← CONJUNCT1 (← REWRITE_RULE [number_field] th))])) THEN ASM_SIMP_TAC [DIVIDES_ZERO, PRIME_IMP_NZ], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [weakly_unramified] THEN X_GEN_TAC (← q r"P:B->bool") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_of_num l q IN (P:B->bool)") ASSUME_TAC THENL [FIRST_ASSUM (SUBST1_TAC o (SYM o ((SPEC (← q r"q:num")) o (MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM)))) THEN UNDISCH_TAC (← q r"IMAGE (h:A->B) p SUBSET P") THEN UNDISCH_TAC (← q r"ring_of_num k q IN (p:A->bool)") THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(P = {ring_0 l:B})") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ring_of_num l q IN {ring_0 l:B}") THEN REWRITE_TAC [IN_SING, RING_OF_NUM_EQ_0] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← CONJUNCT1 (← REWRITE_RULE [number_field] th))])) THEN ASM_SIMP_TAC [DIVIDES_ZERO, PRIME_IMP_NZ], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"P:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_BELOW) THEN ASM_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"p':A->bool") STRIP_ASSUME_TAC) o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p':A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q) THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"P:B->bool"), (← q r"q:num")] NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q) THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"q:num")] NUMBER_FIELD_RAMIFIED_DISCRIMINANT) THEN ASM_REWRITE_TAC [NOT_EXISTS_THM] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"P:B->bool"))) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [NOT_LT, IMP_IMP] THEN DISCH_THEN (MP_TAC o (MATCH_MP r1)) THEN REWRITE_TAC [MULT_EQ_1] THEN SIMP_TAC [])

  let FINITE_RAMIFIED ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"q:num"
    let q2 ← q r"q:num"
    let q3 ← q r"p:A->bool"
    let q4 ← q r"k:A ring"
    let v5 ← ISPECL [q4, q3] RING_OF_INTEGERS_PRIME_IDEAL_ABOVE
    let q6 ← q r"p:A->bool"
    let q7 ← q r"UNIONS (IMAGE (\q. {p | prime_ideal (ring_of_integers k) p /\
                            ring_of_num (k:A ring) q IN p})
                  {q | prime q /\ &q divides
                       number_field_discriminant(l:B ring)})"
    let q8 ← q r"s:num->bool = t ==> FINITE s ==> FINITE t"
    let r9 ← MESON [] q8
    let q10 ← q r"l:B ring"
    let v11 ← ISPEC q10 NUMBER_FIELD_FINITE_RAMIFIED_PRIMES
    let q12 ← q r"FINITE {q | prime q /\ &q divides number_field_discriminant(l:B ring)}"
    let q13 ← q r"number_field(k:A ring)"
    prove
      r"!k:A ring l:B ring h.
          field k /\ number_field l /\ ring_homomorphism(k,l) h
          ==> FINITE {p | prime_ideal (ring_of_integers k) p /\
                          ~(p = {ring_0 k}) /\
                          ~(unramified
                              (ring_of_integers k,ring_of_integers l) h p)}"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN q13 ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_HOMOMORPHIC_PREIMAGE], ALL_TAC] THEN SUBGOAL_THEN q12 ASSUME_TAC THENL [MP_TAC v11 THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r9 THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN ASM_MESON_TAC [NUMBER_FIELD_RAMIFIED_DISCRIMINANT], ALL_TAC] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC q7 THEN ASM_SIMP_TAC [FINITE_UNIONS, FINITE_IMAGE, FORALL_IN_IMAGE, IN_ELIM_THM, NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_UNIONS, EXISTS_IN_IMAGE] THEN X_GEN_TAC q6 THEN STRIP_TAC THEN MP_TAC v5 THEN ASM_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN ((X_CHOOSE_THEN q2 STRIP_ASSUME_TAC) o CONJUNCT1) THEN EXISTS_TAC q1 THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [UNRAMIFIED_DISCRIMINANT])

  let SPLITTING_TYPES_PRIME_SUBFIELD ← prove
    r"!k:A ring p.
        number_field k /\ prime p
        ==> (unramified
               (ring_of_integers(subfield_generated k {ring_0 k}),
                ring_of_integers k) I
               (ideal_generated
                  (ring_of_integers(subfield_generated k {ring_0 k}))
                  {ring_of_num k p}) <=>
             unramified (integer_ring,ring_of_integers k)
               (ring_of_int k) (ideal_generated integer_ring {&p})) /\
            (totally_split
               (ring_of_integers(subfield_generated k {ring_0 k}),
                ring_of_integers k) I
               (ideal_generated
                  (ring_of_integers(subfield_generated k {ring_0 k}))
                  {ring_of_num k p}) <=>
             totally_split (integer_ring,ring_of_integers k)
               (ring_of_int k) (ideal_generated integer_ring {&p})) /\
            (inert
               (ring_of_integers(subfield_generated k {ring_0 k}),
                ring_of_integers k) I
               (ideal_generated
                  (ring_of_integers(subfield_generated k {ring_0 k}))
                  {ring_of_num k p}) <=>
             inert (integer_ring,ring_of_integers k)
               (ring_of_int k) (ideal_generated integer_ring {&p})) /\
            (totally_ramified
               (ring_of_integers(subfield_generated k {ring_0 k}),
                ring_of_integers k) I
               (ideal_generated
                  (ring_of_integers(subfield_generated k {ring_0 k}))
                  {ring_of_num k p}) <=>
             totally_ramified (integer_ring,ring_of_integers k)
               (ring_of_int k) (ideal_generated integer_ring {&p}))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"q = ring_of_integers(subfield_generated k {ring_0 k:A})") THEN SUBGOAL_THEN (← q r"ring_homomorphism(q,ring_of_integers k) (I:A->A) /\
    ring_of_num k p IN ring_carrier q") STRIP_ASSUME_TAC THENL [EXPAND_TAC "q" THEN REWRITE_TAC [(← REWRITE_RULE [RING_OF_INTEGERS, RING_OF_NUM_SUBFIELD_GENERATED] (← ISPEC (← q r"ring_of_integers(subfield_generated k {ring_0 k:A})") RING_OF_NUM))] THEN MATCH_MP_TAC RING_HOMOMORPHISM_RING_OF_INTEGERS THEN REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_of_num k p = ring_0 k:A)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_NUM_EQ_0] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← CONJUNCT1 (← REWRITE_RULE [number_field] th))])) THEN ASM_SIMP_TAC [DIVIDES_ZERO, PRIME_IMP_NZ], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"q:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"ideal_generated q {ring_of_num k p:A}")] RING_OF_INTEGERS_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [IMAGE_I, SUBSET, IN_SING, NOT_FORALL_THM, NOT_IMP] THEN EXISTS_TAC (← q r"ring_of_num k p:A") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM_REWRITE_TAC [SING_SUBSET, IN_SING], DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC [NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_Q, PRIME_IMP_NZ, (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") SPLITTING_TYPES_INTEGER_RING))] THEN MATCH_MP_TAC SPLITTING_TYPES_PRINCIPAL THEN ASM_SIMP_TAC [IMAGE_I, IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, SING_SUBSET, (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers k:A ring") RING_OF_NUM))] THEN CONJ_TAC THENL [MP_TAC (← CONJUNCT1 (← REWRITE_RULE [ring_homomorphism] (← ASSUME (← q r"ring_homomorphism(q,ring_of_integers k) (I:A->A)")))) THEN REWRITE_TAC [IMAGE_I] THEN MESON_TAC [IDEAL_GENERATED_SUBSET, SUBSET_TRANS], X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(P = {ring_0 k:A})") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ring_of_num k p IN {ring_0 k:A}") THEN REWRITE_TAC [IN_SING, RING_OF_NUM_EQ_0] THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← CONJUNCT1 (← REWRITE_RULE [number_field] th))])) THEN ASM_SIMP_TAC [DIVIDES_ZERO, PRIME_IMP_NZ], EXPAND_TAC "q" THEN ASM_SIMP_TAC [RAMIFICATION_INDEX_PRIME_SUBFIELD, RESIDUE_DEGREE_PRIME_SUBFIELD, NUMBER_FIELD_IMP_FIELD, PRIME_IMP_RING_IDEAL]]])

  let NUMBER_FIELD_SUBFIELD_UNRAMIFIED_DISCRIMINANT ← prove
    r"!(m:A ring) X q.
        number_field m /\ prime q /\
        ~(&q divides number_field_discriminant(subfield_generated m X))
        ==> unramified (ring_of_integers(subfield_generated m {ring_0 m}),
                        ring_of_integers(subfield_generated m X)) I
              (ideal_generated
                 (ring_of_integers(subfield_generated m {ring_0 m}))
                 {ring_of_num m q})"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated m (X:A->bool)"), (← q r"q:num")] SPLITTING_TYPES_PRIME_SUBFIELD) THEN MP_TAC (← ISPECL [(← q r"subfield_generated m (X:A->bool)"), (← q r"q:num")] NUMBER_FIELD_UNRAMIFIED_DISCRIMINANT) THEN ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED, PRIME_SUBFIELD_SUBFIELD_GENERATED, RING_OF_NUM_SUBFIELD_GENERATED])

  -- @@RETURN BEGIN
  return { UNRAMIFIED_FACTORIZATION, TOTALLY_SPLIT_CARD, INERT_RESIDUE_DEGREE,
           TOTALLY_RAMIFIED_RAMIFICATION_INDEX, TOTALLY_RAMIFIED_IDEAL_POW,
           INERT_IMP_UNRAMIFIED, SPLITTING_TYPES_EXCLUSIVE, UNRAMIFIED_DISCRIMINANT,
           FINITE_RAMIFIED, SPLITTING_TYPES_PRIME_SUBFIELD,
           NUMBER_FIELD_SUBFIELD_UNRAMIFIED_DISCRIMINANT }
  -- @@RETURN END

end HolANT.SplittingTypes
