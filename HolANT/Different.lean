/- ========================================================================= -/
/- ANT: The codifferent and the different of an extension of number ...    -/
/- ========================================================================= -/
/- File: HolANT/Different.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/different.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antdifferentdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, ANT/algmisc.ml, ANT/ideal_arith.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/prime_split.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/nf_valuation.ml, ANT/integrality.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Different fills them).

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
import HolANT.IdealArith
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
import HolANT.Discriminant
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.PrimeSplit
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.NfValuation
import HolANT.Integrality

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Algmisc
open HolANT.IdealArith
open HolANT.Integral
open HolANT.Dedekind
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.Discriminant
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.PrimeSplit
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.NfValuation
open HolANT.Integrality

namespace HolANT.Different

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRA_TRACE_ADD ALGEBRA_TRACE_NORM_EQ_IMAGE ALGEBRA_TRACE_NORM_IN_CARRIER
   BASIS_COORDINATES_EXPAND BASIS_COORDINATES_IN_CARRIER
   BASIS_DISCRIMINANT_NONZERO BASIS_DISCRIMINANT_TIMES_COORD CARD_NUMSEG_LT
   DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT DEDEKIND_RING_OF_INTEGERS DIVIDES_ZERO
   EQ_MULT_RCANCEL EQ_TRANS EXP EXP_EQ_0 EXTENSION EXTENSION_DEGREE_EQ_0
   EXTENSION_LINCOMB_LMUL FIELD_EXTENSION_IMP_MONOMORPHISM
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_NONTRIVIAL FIELD_SUBFIELD_GENERATED
   FIELD_UNIT FINITE_EXTENSION_FREE_BASIS FINITE_IMP_FIELD_EXTENSION
   FINITE_NUMSEG_LT FORALL_IN_GSPEC FORALL_IN_IMAGE FREE_BASIS_EXTENSION_DEGREE
   FREE_BASIS_INTEGER_RING_SPAN_INDEX FREE_BASIS_IN_CARRIER FREE_BASIS_SCALE
   HAS_SIZE IDEAL_GENERATED_MINIMAL IDEAL_NORM_CARRIER IDEAL_NORM_GT_1
   IDEAL_PROD_COMM IDEAL_PROD_MINIMAL IMP_CONJ INTEGER_RING INTEGER_RING_POW
   INTEGER_RING_SUM INTEGRAL_DOMAIN_INTEGER_RING INTEGRAL_DOMAIN_MUL_LCANCEL
   INT_ABS_POS INT_ABS_POW INT_ABS_ZERO INT_MUL_SYM INT_OF_NUM_EQ
   INT_OF_NUM_OF_INT INT_POW_EQ_0 IN_ELIM_THM IN_IDEAL_GENERATED_SELF IN_IMAGE
   IN_INTER IN_RING_IDEAL_LMUL IN_SING IN_SUBRING_0 IN_SUBRING_1 IN_SUBRING_ADD
   IN_SUBRING_MUL IN_SUBRING_NEG IN_SUBRING_SUM IN_UNIV I_THM NOT_EXISTS_THM
   NUMBER_FIELD_DEGREE_POS NUMBER_FIELD_DISCRIMINANT_BASIS
   NUMBER_FIELD_DISCRIMINANT_NONZERO NUMBER_FIELD_HOMOMORPHIC_PREIMAGE
   NUMBER_FIELD_IDEAL_NORM_MUL_Q NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_INTEGRAL_MULTIPLE NUMBER_FIELD_TOWER_LAW
   NUMBER_FIELD_TRACE_FORM_INJECTIVE NUMBER_FIELD_TRACE_INTEGRAL
   NUMBER_FIELD_TRACE_INTEGRAL_BASIS NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS
   NUMBER_FIELD_TRACE_MUL_LINCOMB NUMBER_FIELD_TRACE_SCALAR_MUL
   NUM_OF_INT_ABS_POW NUM_OF_INT_OF_NUM QUOTIENT_RING_CARRIER
   RIGHT_EXISTS_IMP_THM RING_1 RING_ADD RING_ADD_LDISTRIB RING_ADD_RDISTRIB
   RING_CARRIER_SUBFIELD_GENERATED_SUBSET RING_DET_ADJUGATE_ROWS
   RING_DET_COFACTOR RING_DET_SUBRING RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_RING_OF_INT RING_HOMOMORPHISM_RING_OF_INTEGERS
   RING_HOMOMORPHISM_SUBFIELD_INCLUSION RING_IDEAL_IDEAL_GENERATED
   RING_IDEAL_IMP_SUBSET RING_INV RING_INV_IN_SUBFIELD_GENERATED
   RING_MONOMORPHISM_EQ_0 RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL
   RING_MUL_ASSOC RING_MUL_LID RING_MUL_LINV RING_MUL_LNEG RING_MUL_LZERO
   RING_MUL_RID RING_MUL_RNEG RING_MUL_RZERO RING_MUL_SYM RING_OF_INT
   RING_OF_INTEGERS RING_OF_INTEGERS_FINITE_QUOTIENT RING_OF_INTEGERS_FREE
   RING_OF_INTEGERS_FREE_BASIS_FIELD RING_OF_INTEGERS_IDEAL_NORM_INTEGER
   RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING
   RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE RING_OF_INTEGERS_SUBFIELD_GENERATED
   RING_OF_INTEGERS_SUBRING RING_OF_INTEGERS_SUBSET RING_OF_INT_0
   RING_OF_INT_EQ_0_CHAR_0 RING_OF_INT_EQ_CHAR_0 RING_OF_INT_IN_RING_OF_INTEGERS
   RING_OF_INT_IN_SUBFIELD_GENERATED RING_OF_INT_ISUM RING_OF_INT_MUL
   RING_OF_INT_OF_NUM RING_OF_NUM RING_OF_NUM_EQ_0 RING_SUM RING_SUM_DELTA
   RING_SUM_EQ RING_SUM_RING_OF_INTEGERS SING_SUBSET SKOLEM_THM
   SUBFIELD_GENERATED SUBSET basis_discriminant field_extension free_basis
   ideal_norm ideal_quotient int_divides number_field ring_ideal subring_of : thm)
  deriving Inhabited

/-- What different.ml uses from Session besides theorems. -/
structure DifferentDeps where
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
/- different.ml phrases from line 95 to 710                               -/
/- ---------------------------------------------------------------------- -/

structure Different01 where
  -- @@FIELDS
  number_field_codifferent : thm
  number_field_different : thm
  RING_IDEAL_NUMBER_FIELD_DIFFERENT : thm
  NUMBER_FIELD_CODIFFERENT_PRIME_SUBFIELD : thm
  RING_OF_INTEGERS_SUBSET_CODIFFERENT : thm
  NUMBER_FIELD_CODIFFERENT_MUL : thm
  NUMBER_FIELD_CODIFFERENT_ADD : thm
  NUMBER_FIELD_FREE_BASIS_INTEGRAL : thm
  NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT : thm
  NUMBER_FIELD_CODIFFERENT_FRACTIONAL : thm
  NUMBER_FIELD_DIFFERENT_CODIFFERENT : thm
  NUMBER_FIELD_DIFFERENT_NONZERO : thm
  NUMBER_FIELD_CODIFFERENT_DIFFERENT : thm
  NUMBER_FIELD_CODIFFERENT_DIV : thm
  NUMBER_FIELD_CODIFFERENT_EQ_IMAGE : thm
  NUMBER_FIELD_CODIFFERENT_INTEGRAL_BASIS : thm
  NUMBER_FIELD_CODIFFERENT_DUAL_SPAN : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDifferent01 [HolBase] (D : DifferentDeps) :
    ExceptT String IO Different01 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, RING_RULE, SET_TAC, TAUT, new_definition, .. } := D
  let { ALGEBRA_TRACE_ADD, ALGEBRA_TRACE_NORM_EQ_IMAGE, ALGEBRA_TRACE_NORM_IN_CARRIER,
        BASIS_COORDINATES_EXPAND, BASIS_COORDINATES_IN_CARRIER,
        BASIS_DISCRIMINANT_NONZERO, BASIS_DISCRIMINANT_TIMES_COORD,
        DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT, DEDEKIND_RING_OF_INTEGERS, DIVIDES_ZERO,
        EQ_TRANS, EXTENSION, EXTENSION_DEGREE_EQ_0, EXTENSION_LINCOMB_LMUL,
        FIELD_EXTENSION_IMP_MONOMORPHISM, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_SUBFIELD_GENERATED, FIELD_UNIT, FINITE_EXTENSION_FREE_BASIS,
        FINITE_IMP_FIELD_EXTENSION, FINITE_NUMSEG_LT, FORALL_IN_IMAGE,
        FREE_BASIS_EXTENSION_DEGREE, FREE_BASIS_IN_CARRIER, FREE_BASIS_SCALE,
        IDEAL_GENERATED_MINIMAL, IDEAL_PROD_COMM, IDEAL_PROD_MINIMAL, IMP_CONJ,
        INTEGER_RING, INTEGRAL_DOMAIN_MUL_LCANCEL, IN_ELIM_THM,
        IN_IDEAL_GENERATED_SELF, IN_IMAGE, IN_INTER, IN_RING_IDEAL_LMUL, IN_SING,
        IN_SUBRING_0, IN_SUBRING_1, IN_SUBRING_ADD, IN_SUBRING_MUL, IN_SUBRING_NEG,
        IN_SUBRING_SUM, IN_UNIV, NOT_EXISTS_THM, NUMBER_FIELD_HOMOMORPHIC_PREIMAGE,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_INTEGRAL_MULTIPLE, NUMBER_FIELD_TOWER_LAW,
        NUMBER_FIELD_TRACE_FORM_INJECTIVE, NUMBER_FIELD_TRACE_INTEGRAL,
        NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS, NUMBER_FIELD_TRACE_MUL_LINCOMB,
        NUMBER_FIELD_TRACE_SCALAR_MUL, RIGHT_EXISTS_IMP_THM, RING_ADD,
        RING_ADD_LDISTRIB, RING_ADD_RDISTRIB, RING_CARRIER_SUBFIELD_GENERATED_SUBSET,
        RING_DET_SUBRING, RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_RING_OF_INT,
        RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IMP_SUBSET, RING_INV, RING_INV_IN_SUBFIELD_GENERATED,
        RING_MONOMORPHISM_EQ_0, RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL,
        RING_MUL_ASSOC, RING_MUL_LINV, RING_MUL_LNEG, RING_MUL_LZERO, RING_MUL_RID,
        RING_MUL_RNEG, RING_MUL_RZERO, RING_MUL_SYM, RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FREE_BASIS_FIELD, RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING,
        RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE, RING_OF_INTEGERS_SUBFIELD_GENERATED,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET, RING_OF_INT_EQ_0_CHAR_0,
        RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_IN_SUBFIELD_GENERATED,
        RING_OF_NUM_EQ_0, RING_SUM, RING_SUM_DELTA, RING_SUM_EQ,
        RING_SUM_RING_OF_INTEGERS, SING_SUBSET, SKOLEM_THM, SUBSET, basis_discriminant,
        field_extension, free_basis, ideal_quotient, number_field, ring_ideal,
        subring_of, .. } := D.core1
  -- @@SCOPE END

  let number_field_codifferent ← new_definition
    r"number_field_codifferent (k:A ring,l:B ring) (h:A->B) =
  {x | x IN ring_carrier l /\
       !y. y IN ring_carrier(ring_of_integers l)
           ==> algebra_trace (k,l) h (ring_mul l x y) IN
               ring_carrier(ring_of_integers k)}"

  let number_field_different ← new_definition
    r"number_field_different (k:A ring,l:B ring) (h:A->B) =
  {x | x IN ring_carrier(ring_of_integers l) /\
       !y. y IN number_field_codifferent (k,l) h
           ==> ring_mul l x y IN ring_carrier(ring_of_integers l)}"

  let RING_IDEAL_NUMBER_FIELD_DIFFERENT ← prove
    r"!(k:A ring) (l:B ring) h.
        ring_ideal (ring_of_integers l) (number_field_different (k,l) h)"
    (REPEAT GEN_TAC THEN MP_TAC (← ISPEC (← q r"l:B ring") (← CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN REWRITE_TAC [subring_of, SUBSET] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!y:B. y IN number_field_codifferent (k,l) (h:A->B)
          ==> y IN ring_carrier l") ASSUME_TAC THENL [SIMP_TAC [number_field_codifferent, IN_ELIM_THM], ALL_TAC] THEN REWRITE_TAC [ring_ideal, number_field_different, RING_OF_INTEGERS, SUBSET, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [RING_MUL_LZERO, RING_MUL_LNEG, RING_ADD_RDISTRIB, (← GSYM RING_MUL_ASSOC)])

  let NUMBER_FIELD_CODIFFERENT_PRIME_SUBFIELD ← prove
    r"!k:A ring.
        number_field_codifferent (subfield_generated k {ring_0 k},k) I =
        {x | x IN ring_carrier k /\
             !y. y IN ring_carrier(ring_of_integers k)
                 ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                       (ring_mul k x y) IN
                     ring_carrier(ring_of_integers k)}"
    (REWRITE_TAC [number_field_codifferent, RING_OF_INTEGERS_SUBFIELD_GENERATED, IN_INTER, ALGEBRA_TRACE_NORM_IN_CARRIER])

  let RING_OF_INTEGERS_SUBSET_CODIFFERENT ← prove
    r"!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> ring_carrier(ring_of_integers l) SUBSET
            number_field_codifferent (k,l) h"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [SUBSET, number_field_codifferent, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN MATCH_MP_TAC NUMBER_FIELD_TRACE_INTEGRAL THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL))])

  let (NUMBER_FIELD_CODIFFERENT_MUL, NUMBER_FIELD_CODIFFERENT_ADD) ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let v1 ← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET
    let v2 ← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET
    let q3 ← q r"ring_mul (r:B ring) (ring_mul r a x) y =
        ring_mul r x (ring_mul r a y)"
    let r4 ← RING_RULE q3
    let q5 ← q r"ring_mul l (ring_mul l a x) z = ring_mul (l:B ring) x (ring_mul l a z)"
    let q6 ← q r"z:B"
    let v7 ← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET
    let p8 ← prove r"(!k:A ring l:B ring h a x.
        a IN ring_carrier(ring_of_integers l) /\
        x IN number_field_codifferent (k,l) h
        ==> ring_mul l a x IN number_field_codifferent (k,l) h) /\
   (!k:A ring l:B ring h x y.
        ring_homomorphism(k,l) h /\
        x IN number_field_codifferent (k,l) h /\
        y IN number_field_codifferent (k,l) h
        ==> ring_add l x y IN number_field_codifferent (k,l) h)" (REWRITE_TAC [number_field_codifferent, IN_ELIM_THM] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [RING_MUL, RING_ADD, v7] THEN X_GEN_TAC q6 THEN DISCH_TAC THENL [SUBGOAL_THEN q5 SUBST1_TAC THENL [MATCH_MP_TAC r4 THEN ASM_SIMP_TAC [v2], FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [IN_SUBRING_MUL, RING_OF_INTEGERS_SUBRING]], ASM_SIMP_TAC [RING_ADD_RDISTRIB, ALGEBRA_TRACE_ADD, RING_MUL, IN_SUBRING_ADD, RING_OF_INTEGERS_SUBRING, v1]])
    CONJ_PAIR p8

  let NUMBER_FIELD_FREE_BASIS_INTEGRAL ← prove
    r"!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> ?w. free_basis (k,l) h (extension_degree(k,l) h) w /\
                !i. i < extension_degree(k,l) h
                    ==> w i IN ring_carrier(ring_of_integers l)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"g:num->B")) o (MATCH_MP FINITE_EXTENSION_FREE_BASIS)) THEN ABBREV_TAC (← q r"n = extension_degree(k:A ring,l:B ring) h") THEN SUBGOAL_THEN (← q r"?d. !i. i < n
            ==> ~(d i = &0) /\
                ring_mul l (ring_of_int l (d i)) ((g:num->B) i) IN
                ring_carrier(ring_of_integers l)") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← GSYM SKOLEM_THM), RIGHT_EXISTS_IMP_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_INTEGRAL_MULTIPLE THEN ASM_MESON_TAC [FREE_BASIS_IN_CARRIER], ALL_TAC] THEN EXISTS_TAC (← q r"\i. ring_mul l ((h:A->B)(ring_of_int k ((d:num->int) i)))
                             ((g:num->B) i)") THEN CONJ_TAC THENL [MATCH_MP_TAC FREE_BASIS_SCALE THEN ASM_REWRITE_TAC [RING_OF_INT] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o ((GEN_REWRITE_RULE id [number_field]) o (checkM (fun th => (do let z3 ← (q r"number_field(k:A ring)"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3))))))) THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0], ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT (← ASSUME (← q r"ring_homomorphism(k:A ring,l:B ring) h")))]])

  let NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r4 ← TAUT (← q r"p /\ q /\ (p ==> r) ==> p /\ q /\ r")
    prove
      r"!k:A ring l:B ring h n w x.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          free_basis (k,l) h n w /\
          (!i. i < n ==> w i IN ring_carrier(ring_of_integers l)) /\
          x IN number_field_codifferent (k,l) h
          ==> basis_discriminant (k,l) h n w IN
              ring_carrier(ring_of_integers k) /\
              ~(basis_discriminant (k,l) h n w = ring_0 k) /\
              ring_mul l (h(basis_discriminant (k,l) h n w)) x IN
              ring_carrier(ring_of_integers l)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z7 ← (q r"number_field(l:B ring)"); let z6 ← (do let z5 ← (pure th); pure (concl z5)); pure (z6 == z7)))))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier l /\
                  !y. y IN ring_carrier(ring_of_integers l)
                      ==> algebra_trace (k,l) h (ring_mul l x y) IN
                          ring_carrier(ring_of_integers (k:A ring))") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"(x:B) IN number_field_codifferent (k,l) (h:A->B)") THEN REWRITE_TAC [number_field_codifferent, IN_ELIM_THM], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"l:B ring") (← CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN MP_TAC (← ISPEC (← q r"k:A ring") (← CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"!i j. i < n /\ j < n
            ==> algebra_trace (k,l) h (ring_mul l ((w:num->B) i) (w j)) IN
                ring_carrier(ring_of_integers (k:A ring))") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_TRACE_INTEGRAL THEN ASM_SIMP_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") RING_MUL))], ALL_TAC] THEN MATCH_MP_TAC r4 THEN REPEAT CONJ_TAC THENL [REWRITE_TAC [basis_discriminant] THEN MATCH_MP_TAC RING_DET_SUBRING THEN ASM_SIMP_TAC [IN_ELIM_THM, FINITE_NUMSEG_LT], MATCH_MP_TAC BASIS_DISCRIMINANT_NONZERO THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o ((GEN_REWRITE_RULE id [number_field]) o (checkM (fun th => (do let z3 ← (q r"number_field(k:A ring)"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3))))))) THEN SIMP_TAC [RING_OF_NUM_EQ_0, DIVIDES_ZERO] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"n:num"), (← q r"w:num->B")] FREE_BASIS_EXTENSION_DEGREE) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [EXTENSION_DEGREE_EQ_0, FINITE_IMP_FIELD_EXTENSION], DISCH_TAC] THEN ABBREV_TAC (← q r"d = basis_discriminant (k:A ring,l:B ring) h n w") THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"n:num"), (← q r"w:num->B"), (← q r"ring_carrier(ring_of_integers k:A ring)"), (← q r"x:B")] BASIS_DISCRIMINANT_TIMES_COORD) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_mul l ((w:num->B) j) x = ring_mul l x (w j)") SUBST1_TAC THENL [ASM_MESON_TAC [RING_MUL_SYM], ALL_TAC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"n:num"), (← q r"w:num->B"), (← q r"x:B")] BASIS_COORDINATES_EXPAND) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← SYM th)])) THEN SUBGOAL_THEN (← q r"(d:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"{i:num | i < n}"), (← q r"d:A"), (← q r"\i. basis_coordinates (k,l) (h:A->B) n w x i"), (← q r"w:num->B")] EXTENSION_LINCOMB_LMUL) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, BASIS_COORDINATES_IN_CARRIER] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IN_SUBRING_SUM THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MATCH_MP_TAC o (MATCH_MP (← REWRITE_RULE [IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER))) THEN ASM_SIMP_TAC [])

  let NUMBER_FIELD_CODIFFERENT_FRACTIONAL ← prove
    r"!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> ?d. d IN ring_carrier(ring_of_integers k) /\ ~(d = ring_0 k) /\
                IMAGE (ring_mul l (h d)) (number_field_codifferent (k,l) h)
                SUBSET ring_carrier(ring_of_integers l)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_FREE_BASIS_INTEGRAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"w:num->B") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"basis_discriminant (k,l) (h:A->B) (extension_degree(k,l) h) w") THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"extension_degree(k:A ring,l:B ring) h"), (← q r"w:num->B")] NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o (SPEC (← q r"ring_1 l:B"))) THEN ANTS_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_OF_INTEGERS_SUBSET_CODIFFERENT) THEN ASM_REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC [IN_SUBRING_1, RING_OF_INTEGERS_SUBRING], STRIP_TAC THEN ASM_SIMP_TAC []])

  let NUMBER_FIELD_DIFFERENT_CODIFFERENT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul (r:B ring) f e = ring_1 r
      ==> ring_mul r x y = ring_mul r f (ring_mul r x (ring_mul r e y))")
    let r2 ← TAUT (← q r"(p ==> (q <=> r)) ==> (p ==> q <=> p ==> r)")
    let r3 ← RING_RULE (← q r"ring_mul (r:B ring) a (ring_mul r d x) =
        ring_mul r d (ring_mul r a x)")
    let r4 ← RING_RULE (← q r"ring_neg (r:B ring) (ring_mul r d x) =
          ring_mul r d (ring_mul r (ring_neg r (ring_1 r)) x)")
    prove
      r"!k:A ring l:B ring h d.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          d IN ring_carrier(ring_of_integers k) /\ ~(d = ring_0 k) /\
          IMAGE (ring_mul l (h d)) (number_field_codifferent (k,l) h) SUBSET
          ring_carrier(ring_of_integers l)
          ==> ring_ideal (ring_of_integers l)
                (IMAGE (ring_mul l (h d)) (number_field_codifferent (k,l) h)) /\
              ideal_prod (ring_of_integers l) (number_field_different (k,l) h)
                (IMAGE (ring_mul l (h d)) (number_field_codifferent (k,l) h)) =
              ideal_generated (ring_of_integers l) {h d}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z7 ← (q r"number_field(l:B ring)"); let z6 ← (do let z5 ← (pure th); pure (concl z5)); pure (z6 == z7)))))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((MATCH_MP FINITE_IMP_FIELD_EXTENSION) o CONJUNCT1)) THEN REWRITE_TAC [field_extension] THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN ABBREV_TAC (← q r"e = (h:A->B) d") THEN SUBGOAL_THEN (← q r"e IN ring_carrier(ring_of_integers l) /\ e IN ring_carrier l /\
      ~(e = ring_0 (l:B ring))") STRIP_ASSUME_TAC THENL [EXPAND_TAC "e" THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (MATCH_MP (← REWRITE_RULE [IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER))) THEN DISCH_THEN (MP_TAC o (SPEC (← q r"d:A"))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0, RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ABBREV_TAC (← q r"J = IMAGE (ring_mul l e) (number_field_codifferent (k,l) (h:A->B))") THEN SUBGOAL_THEN (← q r"!x:B. x IN number_field_codifferent (k,l) (h:A->B) ==> x IN ring_carrier l") ASSUME_TAC THENL [SIMP_TAC [number_field_codifferent, IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers l) (J:B->bool)") ASSUME_TAC THENL [ASM_REWRITE_TAC [ring_ideal, RING_OF_INTEGERS] THEN EXPAND_TAC "J" THEN REWRITE_TAC [FORALL_IN_IMAGE, IN_IMAGE] THEN REPEAT CONJ_TAC THENL [EXISTS_TAC (← q r"ring_0 l:B") THEN ASM_SIMP_TAC [RING_MUL_RZERO] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_OF_INTEGERS_SUBSET_CODIFFERENT) THEN ASM_REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC [IN_SUBRING_0, RING_OF_INTEGERS_SUBRING], X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN EXISTS_TAC (← q r"ring_mul l (ring_neg l (ring_1 l)) x:B") THEN CONJ_TAC THENL [MATCH_MP_TAC r4 THEN ASM_SIMP_TAC [], MATCH_MP_TAC NUMBER_FIELD_CODIFFERENT_MUL THEN ASM_SIMP_TAC [IN_SUBRING_NEG, IN_SUBRING_1, RING_OF_INTEGERS_SUBRING]], MAP_EVERY X_GEN_TAC [(← q r"u:B"), (← q r"v:B")] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"x:B") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) (X_CHOOSE_THEN (← q r"y:B") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN EXISTS_TAC (← q r"ring_add l x y:B") THEN ASM_SIMP_TAC [NUMBER_FIELD_CODIFFERENT_ADD, RING_ADD_LDISTRIB], MAP_EVERY X_GEN_TAC [(← q r"a:B"), (← q r"y:B")] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"x:B") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN EXISTS_TAC (← q r"ring_mul l a x:B") THEN ASM_SIMP_TAC [NUMBER_FIELD_CODIFFERENT_MUL] THEN MATCH_MP_TAC r3 THEN ASM_SIMP_TAC [(← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET)]], ASM_REWRITE_TAC []] THEN SUBGOAL_THEN (← q r"number_field_different (k,l) (h:A->B) =
      ideal_quotient (ring_of_integers l)
        (ideal_generated (ring_of_integers l) {e}) (J:B->bool)") SUBST1_TAC THENL [GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:B") THEN REWRITE_TAC [number_field_different, ideal_quotient, IN_ELIM_THM] THEN EXPAND_TAC "J" THEN REWRITE_TAC [FORALL_IN_IMAGE, RING_OF_INTEGERS] THEN ASM_CASES_TAC (← q r"(x:B) IN ring_carrier(ring_of_integers l)") THEN ASM_REWRITE_TAC [] THEN AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC r2 THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier l /\ y IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING, RING_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"e:B")] RING_MUL_LINV) THEN ASM_SIMP_TAC [FIELD_UNIT] THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_INV], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"ideal_generated (ring_of_integers l) {e:B}"), (← q r"J:B->bool")] DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED] THEN ANTS_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET] THEN EXPAND_TAC "J" THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"ring_1 l:B") THEN ASM_SIMP_TAC [RING_MUL_RID] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_OF_INTEGERS_SUBSET_CODIFFERENT) THEN ASM_REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC [IN_SUBRING_1, RING_OF_INTEGERS_SUBRING], DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)]))] THEN MATCH_MP_TAC IDEAL_PROD_COMM THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN REWRITE_TAC [ideal_quotient] THEN SET_TAC [])

  let NUMBER_FIELD_DIFFERENT_NONZERO ← prove
    r"!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> ~(number_field_different (k,l) h = {ring_0 l})"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_CODIFFERENT_FRACTIONAL) THEN ASM_REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"d:A") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((MATCH_MP FINITE_IMP_FIELD_EXTENSION) o CONJUNCT1)) THEN REWRITE_TAC [field_extension] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(h:A->B) d IN number_field_different (k,l) h") MP_TAC THENL [REWRITE_TAC [number_field_different, IN_ELIM_THM] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN DISCH_THEN (MATCH_MP_TAC o (MATCH_MP (← REWRITE_RULE [IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER))) THEN ASM_REWRITE_TAC [], UNDISCH_TAC (← q r"IMAGE (ring_mul l ((h:A->B) d)) (number_field_codifferent (k,l) h)
        SUBSET ring_carrier(ring_of_integers l)") THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE]], ASM_REWRITE_TAC [IN_SING] THEN ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0, RING_OF_INTEGERS_SUBSET, SUBSET]])

  let NUMBER_FIELD_CODIFFERENT_DIFFERENT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul (r:B ring) x (ring_mul r a z) =
          ring_mul r a (ring_mul r x z)")
    prove
      r"!k:A ring l:B ring h.
          field k /\ number_field l /\ ring_homomorphism(k,l) h
          ==> number_field_codifferent (k,l) h =
              {x | x IN ring_carrier l /\
                   !y. y IN number_field_different (k,l) h
                       ==> ring_mul l x y IN ring_carrier(ring_of_integers l)}"
      (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"x:B") THEN REWRITE_TAC [IN_ELIM_THM] THEN EQ_TAC THENL [DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:B) IN ring_carrier l") ASSUME_TAC THENL [UNDISCH_TAC (← q r"(x:B) IN number_field_codifferent (k,l) (h:A->B)") THEN SIMP_TAC [number_field_codifferent, IN_ELIM_THM], ASM_REWRITE_TAC [number_field_different, IN_ELIM_THM]] THEN X_GEN_TAC (← q r"y:B") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_mul l x y = ring_mul l y (x:B)") SUBST1_TAC THENL [MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC [(← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET)], ASM_SIMP_TAC []], STRIP_TAC] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z4 ← (q r"number_field(l:B ring)"); let z3 ← (do let z2 ← (pure th); pure (concl z2)); pure (z3 == z4)))))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_CODIFFERENT_FRACTIONAL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"d:A") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"d:A")] NUMBER_FIELD_DIFFERENT_CODIFFERENT) THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((MATCH_MP FINITE_IMP_FIELD_EXTENSION) o CONJUNCT1)) THEN REWRITE_TAC [field_extension] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(h:A->B) d IN ring_carrier(ring_of_integers l) /\ h d IN ring_carrier l /\
      ~(h d = ring_0 l)") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"d:A")) o (MATCH_MP (← REWRITE_RULE [IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER)))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0, RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ABBREV_TAC (← q r"e = (h:A->B) d") THEN ABBREV_TAC (← q r"J = IMAGE (ring_mul l e) (number_field_codifferent (k,l) (h:A->B))") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_mul l x e IN (J:B->bool)") MP_TAC THENL [SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers l)
          {z | z IN ring_carrier(ring_of_integers l) /\
               ring_mul l x z IN (J:B->bool)}") MP_TAC THENL [UNDISCH_TAC (← q r"ring_ideal (ring_of_integers l) (J:B->bool)") THEN REWRITE_TAC [ring_ideal, RING_OF_INTEGERS, SUBSET, IN_ELIM_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC [IN_SUBRING_0, IN_SUBRING_NEG, IN_SUBRING_ADD, IN_SUBRING_MUL, RING_OF_INTEGERS_SUBRING, (← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET), RING_MUL_RZERO, RING_MUL_RNEG, RING_ADD_LDISTRIB] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_mul l x (ring_mul l x' y) =
                      ring_mul l x' (ring_mul (l:B ring) x y)") SUBST1_TAC THENL [MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [(← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET)], ASM_SIMP_TAC []], DISCH_THEN (MP_TAC o ((SPECL [(← q r"number_field_different (k,l) (h:A->B)"), (← q r"J:B->bool")]) o (MATCH_MP (← REWRITE_RULE [IMP_CONJ] IDEAL_PROD_MINIMAL))))] THEN ANTS_TAC THENL [REWRITE_TAC [IN_ELIM_THM, RING_OF_INTEGERS] THEN MAP_EVERY X_GEN_TAC [(← q r"a:B"), (← q r"b:B")] THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"(a:B) IN ring_carrier(ring_of_integers l) /\
          (b:B) IN ring_carrier(ring_of_integers l)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [UNDISCH_TAC (← q r"(a:B) IN number_field_different (k,l) (h:A->B)") THEN SIMP_TAC [number_field_different, IN_ELIM_THM], UNDISCH_TAC (← q r"(b:B) IN J") THEN UNDISCH_TAC (← q r"ring_ideal (ring_of_integers l) (J:B->bool)") THEN SIMP_TAC [ring_ideal, SUBSET]], ASM_SIMP_TAC [IN_SUBRING_MUL, RING_OF_INTEGERS_SUBRING]] THEN SUBGOAL_THEN (← q r"ring_mul l x (ring_mul l a b) =
                      ring_mul l (ring_mul l x a) (b:B)") SUBST1_TAC THENL [MATCH_MP_TAC RING_MUL_ASSOC THEN ASM_SIMP_TAC [(← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET)], MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool"), (← q r"ring_mul l x a:B"), (← q r"b:B")] IN_RING_IDEAL_LMUL) THEN ASM_SIMP_TAC [RING_OF_INTEGERS]], ASM_REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"e:B"))) THEN ASM_SIMP_TAC [IN_IDEAL_GENERATED_SELF]], EXPAND_TAC "J" THEN REWRITE_TAC [IN_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:B") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(c:B) IN ring_carrier l") ASSUME_TAC THENL [UNDISCH_TAC (← q r"(c:B) IN number_field_codifferent (k,l) (h:A->B)") THEN SIMP_TAC [number_field_codifferent, IN_ELIM_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"x:B = c") (fun th => ASM_REWRITE_TAC [th]) THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"l:B ring"), (← q r"e:B")] THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN SUBGOAL_THEN (← q r"ring_mul l e x = ring_mul l x (e:B)") SUBST1_TAC THENL [MATCH_MP_TAC RING_MUL_SYM THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC []]])

  let NUMBER_FIELD_CODIFFERENT_DIV ← prove
    r"!k:A ring l:B ring h a x.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        a IN ring_carrier(ring_of_integers l) /\ ~(a = ring_0 l) /\
        x IN ring_carrier l
        ==> (ring_mul l (ring_inv l a) x IN number_field_codifferent (k,l) h <=>
             !d. d IN number_field_different (k,l) h
                 ==> ring_mul l x d IN
                     ideal_generated (ring_of_integers l) {a})"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP NUMBER_FIELD_IMP_FIELD) o (checkM (fun th => (do let z3 ← (q r"number_field(l:B ring)"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3)))))) THEN SUBGOAL_THEN (← q r"(a:B) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!d. d IN number_field_different (k,l) (h:A->B)
        ==> d IN ring_carrier(l:B ring)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_IDEAL_NUMBER_FIELD_DIFFERENT) THEN DISCH_THEN (MP_TAC o (MATCH_MP RING_IDEAL_IMP_SUBSET)) THEN MP_TAC (← ISPEC (← q r"l:B ring") RING_OF_INTEGERS_SUBSET) THEN SET_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [NUMBER_FIELD_CODIFFERENT_DIFFERENT, IN_ELIM_THM, RING_MUL, RING_INV, FIELD_UNIT] THEN ASM_SIMP_TAC [RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING, RING_MUL, RING_MUL_ASSOC, RING_INV, FIELD_UNIT])

  let NUMBER_FIELD_CODIFFERENT_EQ_IMAGE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(p ==> (q <=> r)) ==> (p ==> q <=> p ==> r)")
    let r2 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k1:A ring k2:C ring l:B ring h1 h2.
          field k1 /\ field k2 /\ number_field l /\
          ring_homomorphism(k1,l) h1 /\ ring_homomorphism(k2,l) h2 /\
          IMAGE h1 (ring_carrier k1) = IMAGE h2 (ring_carrier k2)
          ==> number_field_codifferent (k1,l) h1 =
              number_field_codifferent (k2,l) h2 /\
              number_field_different (k1,l) h1 =
              number_field_different (k2,l) h2"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC r2 THEN CONJ_TAC THENL [ALL_TAC, SIMP_TAC [number_field_different]] THEN SUBGOAL_THEN (← q r"ring_monomorphism(k1:A ring,l:B ring) h1 /\
      ring_monomorphism(k2:C ring,l:B ring) h2") STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC FIELD_EXTENSION_IMP_MONOMORPHISM THEN MATCH_MP_TAC FINITE_IMP_FIELD_EXTENSION THEN ASM_MESON_TAC [NUMBER_FIELD_TOWER_LAW], ALL_TAC] THEN REWRITE_TAC [number_field_codifferent, EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:B") THEN ASM_CASES_TAC (← q r"(x:B) IN ring_carrier l") THEN ASM_REWRITE_TAC [] THEN AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC r1 THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_mul l x y IN ring_carrier(l:B ring)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_MUL, RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k1:A ring"), (← q r"l:B ring"), (← q r"h1:A->B"), (← q r"algebra_trace (k1,l) (h1:A->B) (ring_mul l x y)")] RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE) THEN MP_TAC (← ISPECL [(← q r"k2:C ring"), (← q r"l:B ring"), (← q r"h2:C->B"), (← q r"algebra_trace (k2,l) (h2:C->B) (ring_mul l x y)")] RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER] THEN REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN MP_TAC (← ISPECL [(← q r"h1:A->B"), (← q r"h2:C->B"), (← q r"k1:A ring"), (← q r"k2:C ring"), (← q r"l:B ring"), (← q r"ring_mul l x y:B")] ALGEBRA_TRACE_NORM_EQ_IMAGE) THEN ASM_SIMP_TAC [])

  let NUMBER_FIELD_CODIFFERENT_INTEGRAL_BASIS ← prove
    r"!k:A ring n w x.
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w
        ==> (x IN
             number_field_codifferent (subfield_generated k {ring_0 k},k) I <=>
             x IN ring_carrier k /\
             !i. i < n
                 ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                       (ring_mul k x (w i)) IN
                     ring_carrier(ring_of_integers k))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN REWRITE_TAC [NUMBER_FIELD_CODIFFERENT_PRIME_SUBFIELD, IN_ELIM_THM] THEN EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN MP_TAC (← ISPEC (← q r"ring_of_integers k:A ring") RING_MUL) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"y:A")) o (CONJUNCT1 o (CONJUNCT2 o (GEN_REWRITE_RULE id [free_basis]))))) THEN ASM_REWRITE_TAC [INTEGER_RING, IN_UNIV, RING_OF_INTEGERS] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->int") SUBST1_TAC) THEN SUBGOAL_THEN (← q r"!i. i < n ==> (w:num->A) i IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_SUM_RING_OF_INTEGERS, IN_ELIM_THM, RING_OF_INT_IN_RING_OF_INTEGERS] THEN ASM_SIMP_TAC [NUMBER_FIELD_TRACE_MUL_LINCOMB, FINITE_NUMSEG_LT, IN_ELIM_THM, RING_OF_INT_IN_SUBFIELD_GENERATED] THEN wPart lhand (rand o rand) (← ISPEC (← q r"k:A ring") RING_SUM_RING_OF_INTEGERS) THEN ASM_SIMP_TAC [IN_ELIM_THM, RING_OF_INT_IN_RING_OF_INTEGERS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [RING_SUM])

  let NUMBER_FIELD_CODIFFERENT_DUAL_SPAN ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul (r:A ring) b a = ring_1 r
        ==> ring_mul r b (ring_mul r c a) = c")
    let r2 ← RING_RULE (← q r"ring_mul (r:A ring) (ring_mul r a b) c =
        ring_mul r a (ring_mul r c b)")
    let r3 ← RING_RULE (← q r"ring_mul (r:A ring) b a = ring_1 r
        ==> c = ring_mul r a (ring_mul r b c)")
    let r4 ← RING_RULE (← q r"ring_mul (r:A ring) a (ring_mul r b c) =
        ring_mul r b (ring_mul r c a)")
    let r5 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k:A ring n w g a.
          number_field k /\
          free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
          a IN ring_carrier(subfield_generated k {ring_0 k}) /\
          ~(a = ring_0 k) /\
          (!j. j < n ==> g j IN ring_carrier k) /\
          (!i j. i < n /\ j < n
                 ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                       (ring_mul k (w i) (g j)) =
                     if i = j then a else ring_0 k)
          ==> IMAGE (ring_mul k a)
               (number_field_codifferent (subfield_generated k {ring_0 k},k) I) =
              {ring_sum k {i | i < n}
                        (\i. ring_mul k (ring_of_int k (c i)) (g i)) |
               c IN (:num->int)}"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT2) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier k /\
      ring_inv k a IN ring_carrier(subfield_generated k {ring_0 k}) /\
      ring_inv k a IN ring_carrier k /\ ring_mul k (ring_inv k a) a = ring_1 k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_INV_IN_SUBFIELD_GENERATED, FIELD_SUBFIELD_GENERATED] THEN MATCH_MP_TAC r5 THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ASM_SIMP_TAC [RING_INV] THEN DISCH_TAC THEN MATCH_MP_TAC RING_MUL_LINV THEN ASM_SIMP_TAC [FIELD_UNIT]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!c m. m < n
            ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                  (ring_mul k (w m)
                    (ring_sum k {i | i < n}
                       (\i. ring_mul k (ring_of_int k (c i)) ((g:num->A) i)))) =
                ring_mul k (ring_of_int k (c m)) a") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_TRACE_MUL_LINCOMB, FINITE_NUMSEG_LT, IN_ELIM_THM, RING_OF_INT_IN_SUBFIELD_GENERATED] THEN TRANS_TAC EQ_TRANS (← q r"ring_sum (k:A ring) {i | i < n}
          (\i. if i = m then ring_mul k (ring_of_int k ((c:num->int) m)) a
               else ring_0 k)") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN ASM_SIMP_TAC [] THEN ASM_CASES_TAC (← q r"i:num = m") THEN ASM_SIMP_TAC [RING_MUL_RZERO, RING_OF_INT], REWRITE_TAC [RING_SUM_DELTA, IN_ELIM_THM] THEN ASM_SIMP_TAC [RING_MUL, RING_OF_INT]], ALL_TAC] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"z:A") THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM, IN_UNIV] THEN EQ_TAC THENL [DISCH_THEN (X_CHOOSE_THEN (← q r"x:A") (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN ASM_SIMP_TAC [NUMBER_FIELD_CODIFFERENT_INTEGRAL_BASIS] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"?c. !i:num. i < n ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                            (ring_mul k x (w i)) =
                          ring_of_int (k:A ring) (c i)") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← GSYM SKOLEM_THM), RIGHT_EXISTS_IMP_THM] THEN ASM_MESON_TAC [NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS, RING_MUL, RING_OF_INTEGERS_SUBSET, SUBSET], EXISTS_TAC (← q r"c:num->int")] THEN MATCH_MP_TAC NUMBER_FIELD_TRACE_FORM_INJECTIVE THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] THEN ASM_SIMP_TAC [RING_SUM, RING_MUL, RING_OF_INT] THEN X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(w:num->A) m IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul k (w m) (ring_mul k a x) =
        ring_mul k a (ring_mul k x ((w:num->A) m))") SUBST1_TAC THENL [MATCH_MP_TAC r4 THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [NUMBER_FIELD_TRACE_SCALAR_MUL, RING_MUL] THEN MATCH_MP_TAC RING_MUL_SYM THEN ASM_REWRITE_TAC [RING_OF_INT]], DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->int") SUBST1_TAC) THEN ABBREV_TAC (← q r"y = ring_sum k {i | i < n}
                   (\i. ring_mul k (ring_of_int k (c i)) ((g:num->A) i))") THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier k") ASSUME_TAC THENL [EXPAND_TAC "y" THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN EXISTS_TAC (← q r"ring_mul k (ring_inv k a) y:A") THEN ASM_SIMP_TAC [NUMBER_FIELD_CODIFFERENT_INTEGRAL_BASIS, RING_MUL] THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"ring_mul k (ring_inv k a) a = ring_1 (k:A ring)") THEN MATCH_MP_TAC r3 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(w:num->A) m IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul k (ring_mul k (ring_inv k a) y) (w m) =
        ring_mul k (ring_inv k a) (ring_mul k ((w:num->A) m) y)") SUBST1_TAC THENL [MATCH_MP_TAC r2 THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [NUMBER_FIELD_TRACE_SCALAR_MUL, RING_MUL]] THEN EXPAND_TAC "y" THEN ASM_SIMP_TAC [] THEN SUBGOAL_THEN (← q r"ring_mul k (ring_inv k a) (ring_mul k (ring_of_int k (c m)) a) =
        ring_of_int (k:A ring) ((c:num->int) m)") SUBST1_TAC THENL [UNDISCH_TAC (← q r"ring_mul k (ring_inv k a) a = ring_1 (k:A ring)") THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [RING_OF_INT], REWRITE_TAC [RING_OF_INT_IN_RING_OF_INTEGERS]]])

  -- @@RETURN BEGIN
  return { number_field_codifferent, number_field_different,
           RING_IDEAL_NUMBER_FIELD_DIFFERENT, NUMBER_FIELD_CODIFFERENT_PRIME_SUBFIELD,
           RING_OF_INTEGERS_SUBSET_CODIFFERENT, NUMBER_FIELD_CODIFFERENT_MUL,
           NUMBER_FIELD_CODIFFERENT_ADD, NUMBER_FIELD_FREE_BASIS_INTEGRAL,
           NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT,
           NUMBER_FIELD_CODIFFERENT_FRACTIONAL, NUMBER_FIELD_DIFFERENT_CODIFFERENT,
           NUMBER_FIELD_DIFFERENT_NONZERO, NUMBER_FIELD_CODIFFERENT_DIFFERENT,
           NUMBER_FIELD_CODIFFERENT_DIV, NUMBER_FIELD_CODIFFERENT_EQ_IMAGE,
           NUMBER_FIELD_CODIFFERENT_INTEGRAL_BASIS, NUMBER_FIELD_CODIFFERENT_DUAL_SPAN }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- different.ml phrases from line 836 to 1268                             -/
/- ---------------------------------------------------------------------- -/

structure Different02 where
  -- @@FIELDS
  NUMBER_FIELD_CODIFFERENT_ADJUGATE : thm
  NUMBER_FIELD_CODIFFERENT_DUAL_BASIS : thm
  NUMBER_FIELD_CODIFFERENT_IDEAL : thm
  NUMBER_FIELD_DISCRIMINANT_IN_DIFFERENT : thm
  NUMBER_FIELD_DIFFERENT_CODIFFERENT_Q : thm
  NUMBER_FIELD_IDEAL_NORM_DIFFERENT : thm
  NUMBER_FIELD_DIFFERENT_EQ_CARRIER : thm
  NUMBER_FIELD_CODIFFERENT_DIV_NUM : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDifferent02 [HolBase] (D : DifferentDeps) (BDifferent01 : Different01) :
    ExceptT String IO Different02 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_MESON_TAC, MESON_TAC, RING_RULE, SET_RULE, TAUT, .. } := D
  let { CARD_NUMSEG_LT, DIVIDES_ZERO, EQ_MULT_RCANCEL, EQ_TRANS, EXP, EXP_EQ_0,
        FIELD_NONTRIVIAL, FIELD_SUBFIELD_GENERATED, FIELD_UNIT, FINITE_NUMSEG_LT,
        FORALL_IN_GSPEC, FORALL_IN_IMAGE, FREE_BASIS_INTEGER_RING_SPAN_INDEX,
        FREE_BASIS_IN_CARRIER, HAS_SIZE, IDEAL_NORM_CARRIER, IDEAL_NORM_GT_1,
        INTEGER_RING, INTEGER_RING_POW, INTEGER_RING_SUM, INTEGRAL_DOMAIN_INTEGER_RING,
        INT_ABS_POS, INT_ABS_POW, INT_ABS_ZERO, INT_MUL_SYM, INT_OF_NUM_EQ,
        INT_OF_NUM_OF_INT, INT_POW_EQ_0, IN_ELIM_THM, IN_IMAGE, IN_INTER, IN_SING,
        IN_SUBRING_0, IN_SUBRING_1, IN_SUBRING_MUL, IN_SUBRING_NEG, IN_SUBRING_SUM,
        IN_UNIV, I_THM, NUMBER_FIELD_DEGREE_POS, NUMBER_FIELD_DISCRIMINANT_BASIS,
        NUMBER_FIELD_DISCRIMINANT_NONZERO, NUMBER_FIELD_IDEAL_NORM_MUL_Q,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_TRACE_INTEGRAL_BASIS,
        NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS, NUMBER_FIELD_TRACE_MUL_LINCOMB,
        NUMBER_FIELD_TRACE_SCALAR_MUL, NUM_OF_INT_ABS_POW, NUM_OF_INT_OF_NUM,
        QUOTIENT_RING_CARRIER, RING_1, RING_ADD_LDISTRIB,
        RING_CARRIER_SUBFIELD_GENERATED_SUBSET, RING_DET_ADJUGATE_ROWS,
        RING_DET_COFACTOR, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_IDEAL_IMP_SUBSET,
        RING_INV, RING_INV_IN_SUBFIELD_GENERATED, RING_MUL, RING_MUL_ASSOC,
        RING_MUL_LID, RING_MUL_LINV, RING_MUL_RID, RING_MUL_RZERO, RING_OF_INT,
        RING_OF_INTEGERS, RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_FREE,
        RING_OF_INTEGERS_IDEAL_NORM_INTEGER, RING_OF_INTEGERS_SUBFIELD_GENERATED,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET, RING_OF_INT_0,
        RING_OF_INT_EQ_0_CHAR_0, RING_OF_INT_EQ_CHAR_0,
        RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_IN_SUBFIELD_GENERATED,
        RING_OF_INT_ISUM, RING_OF_INT_MUL, RING_OF_INT_OF_NUM, RING_OF_NUM,
        RING_OF_NUM_EQ_0, RING_SUM, RING_SUM_EQ, RING_SUM_RING_OF_INTEGERS,
        SUBFIELD_GENERATED, SUBSET, basis_discriminant, ideal_norm, int_divides,
        number_field, ring_ideal, .. } := D.core1
  let { NUMBER_FIELD_CODIFFERENT_ADD, NUMBER_FIELD_CODIFFERENT_DUAL_SPAN,
        NUMBER_FIELD_CODIFFERENT_MUL, NUMBER_FIELD_CODIFFERENT_PRIME_SUBFIELD,
        NUMBER_FIELD_DIFFERENT_CODIFFERENT, NUMBER_FIELD_DIFFERENT_NONZERO,
        RING_IDEAL_NUMBER_FIELD_DIFFERENT, RING_OF_INTEGERS_SUBSET_CODIFFERENT,
        number_field_different, .. } := BDifferent01
  -- @@SCOPE END

  let NUMBER_FIELD_CODIFFERENT_ADJUGATE ← prove
    r"!k:A ring n w.
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w
        ==> ?M. ring_det integer_ring {i | i < n} M =
                number_field_discriminant k pow (n - 1) /\
                !i j. i < n /\ j < n
                      ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                            (ring_mul k (w i)
                               (ring_sum k {m | m < n}
                                  (\m. ring_mul k (ring_of_int k (M j m))
                                                  (w m)))) =
                          if i = j
                          then ring_of_int k (number_field_discriminant k)
                          else ring_0 k"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN SUBGOAL_THEN (← q r"!i. i < n ==> (w:num->A) i IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_DISCRIMINANT_NONZERO) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] NUMBER_FIELD_DISCRIMINANT_BASIS) THEN ASM_REWRITE_TAC [basis_discriminant, RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN ABBREV_TAC (← q r"t = \i j. algebra_trace (integer_ring,ring_of_integers k)
                          (ring_of_int k)
                          (ring_mul k ((w:num->A) i) (w j))") THEN DISCH_TAC THEN EXISTS_TAC (← q r"ring_cofactor integer_ring {i:num | i < n} t") THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"{i:num | i < n}"), (← q r"t:num->num->int")] RING_DET_COFACTOR) THEN ASM_REWRITE_TAC [INTEGRAL_DOMAIN_INTEGER_RING, FINITE_NUMSEG_LT, INTEGER_RING, IN_UNIV, CARD_NUMSEG_LT, INTEGER_RING_POW], ALL_TAC] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_TRACE_MUL_LINCOMB, FINITE_NUMSEG_LT, IN_ELIM_THM, RING_OF_INT_IN_SUBFIELD_GENERATED] THEN TRANS_TAC EQ_TRANS (← q r"ring_of_int k (ring_sum integer_ring {m | m < n}
      (\m:num. ring_mul integer_ring (t i m)
             (ring_cofactor integer_ring {i | i < n} t j m))):A") THEN CONJ_TAC THENL [REWRITE_TAC [INTEGER_RING_SUM, INTEGER_RING] THEN SIMP_TAC [RING_OF_INT_ISUM, FINITE_NUMSEG_LT] THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN EXPAND_TAC "t" THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] NUMBER_FIELD_TRACE_INTEGRAL_BASIS) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_SIMP_TAC [IN_SUBRING_MUL, RING_OF_INTEGERS_SUBRING, (← GSYM RING_OF_INT_MUL)] THEN REWRITE_TAC [INT_MUL_SYM], MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"{i:num | i < n}"), (← q r"t:num->num->int"), (← q r"i:num"), (← q r"j:num")] RING_DET_ADJUGATE_ROWS) THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, INTEGER_RING, IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [RING_OF_INT_0]])

  let NUMBER_FIELD_CODIFFERENT_DUAL_BASIS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(!x. x IN s ==> f x = x) ==> s = IMAGE (f:A->A) s")
    let r2 ← RING_RULE (← q r"ring_mul (r:A ring) a (ring_mul r b c) =
        ring_mul r b (ring_mul r a c)")
    let r3 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    prove
      r"!k:A ring n w.
          number_field k /\
          free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w
          ==> ?w'. (!i j. i < n /\ j < n
                          ==> algebra_trace (subfield_generated k {ring_0 k},k) I
                                (ring_mul k (w i) (w' j)) =
                              if i = j then ring_1 k else ring_0 k) /\
                   number_field_codifferent
                     (subfield_generated k {ring_0 k},k) I =
                   {ring_sum k {i | i < n}
                             (\i. ring_mul k (ring_of_int k (c i)) (w' i)) |
                    c IN (:num->int)}"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"!i. i < n ==> (w:num->A) i IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [FREE_BASIS_IN_CARRIER, RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] NUMBER_FIELD_CODIFFERENT_ADJUGATE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"M:num->num->int") (ASSUME_TAC o CONJUNCT2)) THEN ABBREV_TAC (← q r"d = ring_of_int k (number_field_discriminant k):A") THEN ABBREV_TAC (← q r"g = \j. ring_sum k {m | m < n}
       (\m. ring_mul k (ring_of_int k ((M:num->num->int) j m))
                       ((w:num->A) m))") THEN SUBGOAL_THEN (← q r"(d:A) IN ring_carrier(subfield_generated k {ring_0 k}) /\
      ~(d = ring_0 k) /\ (!j. (g:num->A) j IN ring_carrier k)") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["d", "g"] THEN REWRITE_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED, RING_SUM] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0, NUMBER_FIELD_DISCRIMINANT_NONZERO], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_inv k d IN ring_carrier(subfield_generated k {ring_0 k}) /\
      ring_inv k d IN ring_carrier k /\
      ring_mul k (ring_inv k d) d = ring_1 (k:A ring)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_INV_IN_SUBFIELD_GENERATED, FIELD_SUBFIELD_GENERATED] THEN SUBGOAL_THEN (← q r"(d:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_CARRIER_SUBFIELD_GENERATED_SUBSET, SUBSET], ASM_SIMP_TAC [RING_INV, RING_MUL_LINV, FIELD_UNIT]], ALL_TAC] THEN EXISTS_TAC (← q r"\j. ring_mul k (ring_inv k d) ((g:num->A) j)") THEN REWRITE_TAC [] THEN MATCH_MP_TAC r3 THEN CONJ_TAC THENL [MAP_EVERY X_GEN_TAC [(← q r"i:num"), (← q r"j:num")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_mul k (w i) (ring_mul k (ring_inv k d) ((g:num->A) j)) =
        ring_mul k (ring_inv k d) (ring_mul k ((w:num->A) i) (g j))") SUBST1_TAC THENL [MATCH_MP_TAC r2 THEN ASM_SIMP_TAC [], ASM_SIMP_TAC [NUMBER_FIELD_TRACE_SCALAR_MUL, RING_MUL] THEN EXPAND_TAC "g" THEN ASM_SIMP_TAC [] THEN COND_CASES_TAC THEN ASM_SIMP_TAC [RING_MUL_RZERO]], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"\j. ring_mul k (ring_inv k d) ((g:num->A) j)"), (← q r"ring_1 k:A")] NUMBER_FIELD_CODIFFERENT_DUAL_SPAN) THEN ASM_SIMP_TAC [RING_MUL, RING_1, FIELD_NONTRIVIAL] THEN ANTS_TAC THENL [MP_TAC (← ISPEC (← q r"subfield_generated k {ring_0 k}:A ring") RING_1) THEN REWRITE_TAC [(← CONJUNCT1 (← CONJUNCT2 (← CONJUNCT2 SUBFIELD_GENERATED)))], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC r1 THEN SIMP_TAC [NUMBER_FIELD_CODIFFERENT_PRIME_SUBFIELD, IN_ELIM_THM, RING_MUL_LID])

  let NUMBER_FIELD_CODIFFERENT_IDEAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let p1 ← prove r"(!k:A ring a x.
        a IN ring_carrier(ring_of_integers k) /\
        x IN number_field_codifferent (subfield_generated k {ring_0 k},k) I
        ==> ring_mul k a x IN
            number_field_codifferent (subfield_generated k {ring_0 k},k) I) /\
     (!k:A ring x y.
        number_field k /\
        x IN number_field_codifferent (subfield_generated k {ring_0 k},k) I /\
        y IN number_field_codifferent (subfield_generated k {ring_0 k},k) I
        ==> ring_add k x y IN
            number_field_codifferent (subfield_generated k {ring_0 k},k) I)" (SIMP_TAC [NUMBER_FIELD_CODIFFERENT_MUL, NUMBER_FIELD_CODIFFERENT_ADD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION])
    let (lmul, ladd) ← CONJ_PAIR p1
    let r2 ← RING_RULE (← q r"ring_mul (r:A ring) a (ring_mul r d x) =
      ring_mul r d (ring_mul r a x)")
    let r3 ← RING_RULE (← q r"ring_neg (r:A ring) (ring_mul r d x) =
        ring_mul r d (ring_mul r (ring_neg r (ring_1 r)) x)")
    prove
      r"!k:A ring.
          number_field k
          ==> ring_ideal (ring_of_integers k)
                (IMAGE (ring_mul k (ring_of_int k (number_field_discriminant k)))
                       (number_field_codifferent
                          (subfield_generated k {ring_0 k},k) I))"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"w:num->A")) o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I") THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] NUMBER_FIELD_CODIFFERENT_ADJUGATE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"M:num->num->int") (ASSUME_TAC o CONJUNCT2)) THEN ABBREV_TAC (← q r"d = ring_of_int k (number_field_discriminant k):A") THEN ABBREV_TAC (← q r"g = \j. ring_sum k {m | m < n}
       (\m. ring_mul k (ring_of_int k ((M:num->num->int) j m))
                       ((w:num->A) m))") THEN SUBGOAL_THEN (← q r"(d:A) IN ring_carrier(ring_of_integers k) /\
      d IN ring_carrier(subfield_generated k {ring_0 k}) /\ ~(d = ring_0 k) /\
      !j. (g:num->A) j IN ring_carrier(ring_of_integers k)") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["d", "g"] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN ASM_SIMP_TAC [RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_IN_SUBFIELD_GENERATED, RING_OF_INT_EQ_0_CHAR_0, NUMBER_FIELD_DISCRIMINANT_NONZERO] THEN DISCH_TAC THEN GEN_TAC THEN MATCH_MP_TAC IN_SUBRING_SUM THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x. x IN number_field_codifferent (subfield_generated k {ring_0 k},k) I
          ==> x IN ring_carrier (k:A ring)") ASSUME_TAC THENL [SIMP_TAC [NUMBER_FIELD_CODIFFERENT_PRIME_SUBFIELD, IN_ELIM_THM], ALL_TAC] THEN REWRITE_TAC [ring_ideal, RING_OF_INTEGERS] THEN REWRITE_TAC [FORALL_IN_IMAGE, IN_IMAGE] THEN REPEAT CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"g:num->A"), (← q r"d:A")] NUMBER_FIELD_CODIFFERENT_DUAL_SPAN) THEN ANTS_TAC THENL [ASM_SIMP_TAC [(← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET)] THEN EXPAND_TAC "g" THEN ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, IN_UNIV] THEN GEN_TAC THEN MATCH_MP_TAC IN_SUBRING_SUM THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING, RING_OF_INT_IN_RING_OF_INTEGERS], EXISTS_TAC (← q r"ring_0 k:A") THEN ASM_SIMP_TAC [RING_MUL_RZERO, (← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET), (← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET_CODIFFERENT), FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, IN_SUBRING_0, RING_OF_INTEGERS_SUBRING], X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN EXISTS_TAC (← q r"ring_mul k (ring_neg k (ring_1 k)) x:A") THEN CONJ_TAC THENL [MATCH_MP_TAC r3 THEN ASM_SIMP_TAC [(← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET)], MATCH_MP_TAC lmul THEN ASM_SIMP_TAC [IN_SUBRING_NEG, IN_SUBRING_1, RING_OF_INTEGERS_SUBRING]], MAP_EVERY X_GEN_TAC [(← q r"u:A"), (← q r"v:A")] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"x:A") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) (X_CHOOSE_THEN (← q r"y:A") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN EXISTS_TAC (← q r"ring_add k x y:A") THEN ASM_SIMP_TAC [ladd, RING_ADD_LDISTRIB, (← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET)], MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"y:A")] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"x:A") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN EXISTS_TAC (← q r"ring_mul k a x:A") THEN ASM_SIMP_TAC [lmul] THEN MATCH_MP_TAC r2 THEN ASM_SIMP_TAC [(← REWRITE_RULE [SUBSET] RING_OF_INTEGERS_SUBSET)]])

  let NUMBER_FIELD_DISCRIMINANT_IN_DIFFERENT ← prove
    r"!k:A ring.
        number_field k
        ==> ring_of_int k (number_field_discriminant k) IN
            number_field_different (subfield_generated k {ring_0 k},k) I"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [number_field_different, IN_ELIM_THM, RING_OF_INT_IN_RING_OF_INTEGERS] THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o ((MATCH_MP RING_IDEAL_IMP_SUBSET) o (MATCH_MP NUMBER_FIELD_CODIFFERENT_IDEAL))) THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN ASM_SIMP_TAC [])

  let NUMBER_FIELD_DIFFERENT_CODIFFERENT_Q ← prove
    r"!k:A ring.
        number_field k
        ==> ideal_prod (ring_of_integers k)
              (number_field_different (subfield_generated k {ring_0 k},k) I)
              (IMAGE (ring_mul k (ring_of_int k (number_field_discriminant k)))
                     (number_field_codifferent
                        (subfield_generated k {ring_0 k},k) I)) =
            ideal_generated (ring_of_integers k)
              {ring_of_int k (number_field_discriminant k)}"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k}:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"ring_of_int k (number_field_discriminant k):A")] NUMBER_FIELD_DIFFERENT_CODIFFERENT) THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_THM, RING_OF_INTEGERS_SUBFIELD_GENERATED, IN_INTER, RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_IN_SUBFIELD_GENERATED, RING_IDEAL_IMP_SUBSET, NUMBER_FIELD_CODIFFERENT_IDEAL] THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0, NUMBER_FIELD_DISCRIMINANT_NONZERO, SUBFIELD_GENERATED])

  let NUMBER_FIELD_IDEAL_NORM_DIFFERENT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"~q /\ p ==> ~(p <=> q)")
    prove
      r"!k:A ring.
          number_field k
          ==> ideal_norm (ring_of_integers k)
                (number_field_different (subfield_generated k {ring_0 k},k) I) =
              num_of_int(abs(number_field_discriminant k))"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"w:num->A")) o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_DEGREE_POS)) THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I") THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] NUMBER_FIELD_CODIFFERENT_ADJUGATE) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"M:num->num->int") STRIP_ASSUME_TAC) THEN ABBREV_TAC (← q r"g = \j. ring_sum k {m | m < n}
       (\m. ring_mul k (ring_of_int k ((M:num->num->int) j m))
                       ((w:num->A) m))") THEN SUBGOAL_THEN (← q r"!i. i < n
          ==> (g:num->A) i =
              ring_sum (ring_of_integers k) {j | j < n}
                (\j. ring_mul k (ring_of_int k (M i j)) (w j)) /\
              g i IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC [] THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS, MATCH_MP_TAC IN_SUBRING_SUM THEN REWRITE_TAC [RING_OF_INTEGERS_SUBRING]] THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_DISCRIMINANT_NONZERO)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_DIFFERENT_CODIFFERENT_Q) THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_CODIFFERENT_IDEAL) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"g:num->A"), (← q r"ring_of_int k (number_field_discriminant k):A")] NUMBER_FIELD_CODIFFERENT_DUAL_SPAN) THEN ASM_SIMP_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED, RING_OF_INT_EQ_0_CHAR_0] THEN ANTS_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN ABBREV_TAC (← q r"D = number_field_discriminant (k:A ring)") THEN ABBREV_TAC (← q r"J = IMAGE (ring_mul k (ring_of_int k D))
                          (number_field_codifferent
                            (subfield_generated k {ring_0 k},k) I:A->bool)") THEN DISCH_THEN (LABEL_TAC "J") THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"ideal_norm (ring_of_integers k) (J:A->bool) =
      num_of_int(abs D) EXP (n - 1)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"g:num->A"), (← q r"M:num->num->int")] FREE_BASIS_INTEGER_RING_SPAN_INDEX) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, INT_POW_EQ_0, INT_ABS_POW, NUM_OF_INT_ABS_POW] THEN SUBGOAL_THEN (← q r"!c. ring_sum (ring_of_integers k) {i | i < n}
              (\i. ring_mul k (ring_of_int k (c i)) ((g:num->A) i)) =
            ring_sum k {i | i < n}
              (\i. ring_mul k (ring_of_int k (c i)) (g i))") (fun th => REWRITE_TAC [th]) THENL [GEN_TAC THEN MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBRING, RING_OF_INT_IN_RING_OF_INTEGERS], REMOVE_THEN "J" (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [ideal_norm, QUOTIENT_RING_CARRIER, HAS_SIZE]], REMOVE_THEN "J" (fun (_ : thm) => ALL_TAC)] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"number_field_different (subfield_generated k {ring_0 k},k) I:A->bool"), (← q r"J:A->bool")] NUMBER_FIELD_IDEAL_NORM_MUL_Q) THEN ASM_SIMP_TAC [RING_OF_INTEGERS_IDEAL_NORM_INTEGER, NUMBER_FIELD_DIFFERENT_NONZERO, FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_IDEAL_NUMBER_FIELD_DIFFERENT] THEN ANTS_TAC THENL [DISCH_THEN (MP_TAC o (AP_TERM (← q r"\s:A->bool. ring_of_int k D IN s"))) THEN EXPAND_TAC "J" THEN REWRITE_TAC [IN_IMAGE, IN_SING] THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0] THEN EXISTS_TAC (← q r"ring_1 k:A") THEN SIMP_TAC [RING_MUL_RID, RING_OF_INT] THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k}:A ring"), (← q r"k:A ring"), (← q r"I:A->A")] RING_OF_INTEGERS_SUBSET_CODIFFERENT) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION], ALL_TAC] THEN ASM_REWRITE_TAC [SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC [IN_SUBRING_1, RING_OF_INTEGERS_SUBRING], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(num_of_int(abs D) = 0)") MP_TAC THENL [REWRITE_TAC [(← GSYM INT_OF_NUM_EQ)] THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS, INT_ABS_ZERO], UNDISCH_TAC (← q r"1 <= n") THEN SPEC_TAC ((← q r"num_of_int(abs D)"), (← q r"a:num"))] THEN REPEAT STRIP_TAC THEN MP_TAC (← SPECL [(← q r"ideal_norm (ring_of_integers k)
        (number_field_different (subfield_generated k {ring_0 k},k) I:A->bool)"), (← q r"a:num"), (← q r"a EXP (n - 1)")] EQ_MULT_RCANCEL) THEN ASM_REWRITE_TAC [EXP_EQ_0] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN TRANS_TAC EQ_TRANS (← q r"a EXP n") THEN CONJ_TAC THENL [ASM_REWRITE_TAC [], REWRITE_TAC [(← GSYM (← CONJUNCT2 EXP))] THEN AP_TERM_TAC THEN UNDISCH_TAC (← q r"1 <= n") THEN ARITH_TAC])

  let NUMBER_FIELD_DIFFERENT_EQ_CARRIER ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(~p ==> F) ==> p")
    prove
      r"!k:A ring.
          number_field k
          ==> (number_field_different (subfield_generated k {ring_0 k},k) I =
               ring_carrier(ring_of_integers k) <=>
               abs(number_field_discriminant k) = &1)"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_IDEAL_NORM_DIFFERENT) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN EQ_TAC THENL [DISCH_THEN (MP_TAC o (AP_TERM (← q r"ideal_norm (ring_of_integers k:A ring)"))) THEN ASM_REWRITE_TAC [IDEAL_NORM_CARRIER] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"int_of_num"))) THEN SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS], DISCH_TAC THEN MATCH_MP_TAC r1 THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"~(number_field_different (subfield_generated k {ring_0 k},k) I =
          {ring_0 k:A})") ASSUME_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_DIFFERENT_NONZERO THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"number_field_different
                        (subfield_generated k {ring_0 k},k) I:A->bool")] IDEAL_NORM_GT_1) THEN ASM_SIMP_TAC [RING_IDEAL_NUMBER_FIELD_DIFFERENT, RING_OF_INTEGERS_FINITE_QUOTIENT] THEN REWRITE_TAC [NUM_OF_INT_OF_NUM] THEN ARITH_TAC])

  let NUMBER_FIELD_CODIFFERENT_DIV_NUM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(p ==> (q <=> r)) ==> (p ==> q <=> p ==> r)")
    let r2 ← RING_RULE (← q r"ring_mul (r:A ring) e q = ring_1 r
        ==> ring_mul r e (ring_mul r q b) = b")
    let r3 ← RING_RULE (← q r"ring_mul (r:A ring) e q = ring_1 r
        ==> a = ring_mul r q (ring_mul r e a)")
    prove
      r"!k:A ring n w p x.
          number_field k /\
          free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
          ~(p = 0) /\ x IN ring_carrier(ring_of_integers k)
          ==> (ring_mul k (ring_inv k (ring_of_num k p)) x IN
               number_field_codifferent (subfield_generated k {ring_0 k},k) I <=>
               !y. y IN ring_carrier(ring_of_integers k)
                   ==> &p divides
                       algebra_trace (integer_ring,ring_of_integers k)
                         (ring_of_int k) (ring_mul k x y))"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SUBGOAL_THEN (← q r"~(ring_of_num k p = ring_0 (k:A ring))") ASSUME_TAC THENL [ASM_REWRITE_TAC [RING_OF_NUM_EQ_0, DIVIDES_ZERO], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_inv k (ring_of_num k p) IN
      ring_carrier(subfield_generated k {ring_0 (k:A ring)})") ASSUME_TAC THENL [MATCH_MP_TAC RING_INV_IN_SUBFIELD_GENERATED THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED] THEN REWRITE_TAC [(← GSYM RING_OF_INT_OF_NUM), RING_OF_INT_IN_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"!a b. a IN ring_carrier k /\ b IN ring_carrier k
            ==> (ring_mul k (ring_inv k (ring_of_num k p)) a = b <=>
                 a = ring_mul (k:A ring) (ring_of_num k p) b)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_of_num k p:A")] RING_MUL_LINV) THEN ASM_SIMP_TAC [FIELD_UNIT, RING_OF_NUM] THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN EQ_TAC THENL [DISCH_THEN (SUBST1_TAC o SYM), DISCH_THEN SUBST1_TAC] THEN UNDISCH_TAC (← q r"ring_mul k (ring_inv k (ring_of_num k p)) (ring_of_num k p) =
                   ring_1 (k:A ring)") THENL [MATCH_MP_TAC r3, MATCH_MP_TAC r2] THEN ASM_SIMP_TAC [RING_OF_NUM, RING_INV], ALL_TAC] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN REWRITE_TAC [NUMBER_FIELD_CODIFFERENT_PRIME_SUBFIELD, IN_ELIM_THM] THEN ASM_SIMP_TAC [RING_MUL, RING_INV, RING_OF_NUM] THEN AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC r1 THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(y:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul k x y IN ring_carrier(ring_of_integers (k:A ring))") ASSUME_TAC THENL [MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_REWRITE_TAC [RING_OF_INTEGERS_SUBRING], ALL_TAC] THEN ABBREV_TAC (← q r"t = algebra_trace (integer_ring,ring_of_integers k) (ring_of_int k)
            (ring_mul k x y:A)") THEN SUBGOAL_THEN (← q r"algebra_trace (subfield_generated k {ring_0 k},k) I
        (ring_mul k (ring_mul k (ring_inv k (ring_of_num k p)) x) y) =
      ring_mul k (ring_inv k (ring_of_num k p)) (ring_of_int (k:A ring) t)") ASSUME_TAC THENL [EXPAND_TAC "t" THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A")] NUMBER_FIELD_TRACE_INTEGRAL_BASIS) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_SIMP_TAC [(← GSYM RING_MUL_ASSOC), RING_INV, RING_OF_NUM, NUMBER_FIELD_TRACE_SCALAR_MUL, RING_MUL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ring_mul k (ring_mul k (ring_inv k (ring_of_num k p)) x) y:A")] NUMBER_FIELD_TRACE_IN_RING_OF_INTEGERS) THEN ASM_SIMP_TAC [RING_MUL, RING_INV, RING_OF_NUM] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN ASM_SIMP_TAC [RING_OF_INT] THEN REWRITE_TAC [int_divides, (← GSYM RING_OF_INT_OF_NUM), (← GSYM RING_OF_INT_MUL)] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_CHAR_0] THEN MESON_TAC [])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_CODIFFERENT_ADJUGATE, NUMBER_FIELD_CODIFFERENT_DUAL_BASIS,
           NUMBER_FIELD_CODIFFERENT_IDEAL, NUMBER_FIELD_DISCRIMINANT_IN_DIFFERENT,
           NUMBER_FIELD_DIFFERENT_CODIFFERENT_Q, NUMBER_FIELD_IDEAL_NORM_DIFFERENT,
           NUMBER_FIELD_DIFFERENT_EQ_CARRIER, NUMBER_FIELD_CODIFFERENT_DIV_NUM }
  -- @@RETURN END

end HolANT.Different
