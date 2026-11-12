/- ========================================================================= -/
/- ANT: Splitting of primes in relative extensions                         -/
/- ========================================================================= -/
/- File: HolANT/RelativeSplit.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/relative_split.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antrelativesplitdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/ideal_norm.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/prime_split.ml, ANT/discriminant.ml, ANT/trace_form.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.RelativeSplit fills them).

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

namespace HolANT.RelativeSplit

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD1 ADD_CLAUSES AND_FORALL_THM CARD_EQ_NSUM CARD_EXTENSION_DEGREE
   CARRIER_SUBRING_GENERATED_SUBRING CARRIER_SUBRING_OF CONJ_ASSOC CONTRAPOS_THM
   DEDEKIND_FINITE_MAXIMAL_IDEALS_ABOVE DEDEKIND_IDEAL_FACTORIZATION
   DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES
   DEDEKIND_IDEAL_SUBSET_POW_VALUATION DEDEKIND_IDEAL_SUBSET_VALUATION
   DEDEKIND_IMP_INTEGRAL_DOMAIN DEDEKIND_IN_IDEAL_POW_VALUATION
   DEDEKIND_KRULL_DIMENSION_ONE DEDEKIND_MAXIMAL_IDEAL_INVERSE
   DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL DEDEKIND_RING_OF_INTEGERS
   DEDEKIND_UNIFORMIZER_CRITERION DEDEKIND_VALUATION DE_MORGAN_THM DIVIDES_ZERO
   EMPTY_GSPEC EQ_EXP EQ_TRANS ETA_AX EXISTS_UNIQUE EXISTS_UNIQUE_DEF
   EXISTS_UNIQUE_THM EXP_1 EXP_EXP EXTENSION EXTENSION_DEGREE_EQ_IMAGE
   EXTENSION_DEGREE_SUBFIELD_TOWER FIELD_DIVIDES FIELD_FRACTION_NONZERO
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_IMP_NONTRIVIAL_RING FIELD_NONTRIVIAL
   FIELD_QUOTIENT_RING FIELD_REAL_RING FIELD_RING_HOMOMORPHISM_MONOMORPHISM
   FIELD_SUBFIELD_GENERATED FINITE_IMP_FIELD_EXTENSION
   FINITE_INTEGRAL_DOMAIN_IMP_FIELD FINITE_NUMSEG_LT
   FINITE_RING_MONOMORPHIC_PREIMAGE FINITE_SUBSET FORALL_IN_GSPEC
   FORALL_IN_IMAGE FREE_BASIS_EXISTS FREE_BASIS_IN_CARRIER FUN_EQ_THM
   FUN_IN_IMAGE IDEAL_GENERATED_EQ_0 IDEAL_GENERATED_IMAGE_IDEAL_GENERATED
   IDEAL_GENERATED_INC IDEAL_GENERATED_INC_GEN IDEAL_GENERATED_MINIMAL
   IDEAL_GENERATED_MINIMAL_EQ IDEAL_GENERATED_MONO
   IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0 IDEAL_GENERATED_SUBSET IDEAL_NORM_GT_1
   IDEAL_POW_0 IDEAL_POW_1 IDEAL_POW_ANTIMONO IDEAL_POW_EQ_ZERO
   IDEAL_POW_HOMOMORPHIC_IMAGE IDEAL_POW_HOMOMORPHIC_IMAGE_SUBSET IDEAL_POW_MUL
   IDEAL_POW_PRINCIPAL IDEAL_POW_SUC IDEAL_POW_SUC_SUBSET IDEAL_PRODUCT_EQ
   IDEAL_PROD_CARRIER IDEAL_PROD_CARRIER_LEFT IDEAL_PROD_COMM
   IDEAL_PROD_HOMOMORPHIC_IMAGE IDEAL_PROD_MONO IDEAL_PROD_RZERO
   IDEAL_VALUATION_EQ_0 IDEAL_VALUATION_IDEAL_POW IDEAL_VALUATION_IDEAL_PROD
   IDEAL_VALUATION_PRIME IDEAL_VALUATION_PRINCIPAL_MUL IDEAL_VALUATION_SETADD
   IMAGE_CLAUSES IMAGE_EQ IMAGE_I IMAGE_SUBSET IMAGE_o IMP_CONJ INTEGER_RING
   INTEGRAL_DOMAIN_CHAR INTEGRAL_DOMAIN_MUL_EQ_0 INTEGRAL_DOMAIN_MUL_LCANCEL
   INTEGRAL_DOMAIN_POW_EQ_0 INTEGRAL_DOMAIN_QUOTIENT_RING
   INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE
   INTEGRAL_ELEMENT_SUBRING_GENERATED INT_OF_NUM_MUL IN_ELIM_THM
   IN_IDEAL_GENERATED_SING IN_IDEAL_GENERATED_SING_EQ IN_IMAGE IN_INSERT
   IN_RING_IDEAL_0 IN_RING_IDEAL_ADD IN_RING_IDEAL_LMUL IN_RING_IDEAL_RMUL
   IN_RING_IDEAL_SUB IN_RING_IDEAL_SUM IN_SING IN_UNIV I_DEF I_O_ID I_THM
   LEFT_IMP_EXISTS_THM LE_MULT_LCANCEL LE_REFL LT LT_REFL
   MAXIMAL_IDEAL_IMP_SUBSET MAXIMAL_IMP_PRIME_IDEAL MAXIMAL_IMP_RING_IDEAL
   MAXIMAL_SUPERIDEAL_EXISTS : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (MEMBER_NOT_EMPTY MIN MONO_EXISTS MULT_CLAUSES MULT_EQ_0 MULT_SYM
   NOT_FORALL_THM NSUM_EQ NSUM_GROUP NUMBER_FIELD_DEGREE_POS
   NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_ISOMORPHIC_IMAGE NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q
   NUMBER_FIELD_PRIME_SUBFIELD PRIME_EXP PRIME_IDEAL_HOMOMORPHIC_PREIMAGE
   PRIME_IDEAL_IMP_PSUBSET PRIME_IDEAL_IMP_SUBSET PRIME_IMP_NZ
   PRIME_IMP_RING_IDEAL PRIME_SUBFIELD_EQ_SUBRING
   PRIME_SUBFIELD_SUBFIELD_GENERATED PRIME_SUBFIELD_TOWER_LAW PSUBSET
   QUOTIENT_RING_0 QUOTIENT_RING_CARRIER QUOTIENT_RING_UNIVERSAL_EXPLICIT
   REAL_RING_CLAUSES REAL_RING_OF_INT RIGHT_EXISTS_IMP_THM RIGHT_FORALL_IMP_THM
   RING_0 RING_1 RING_ADD RING_ADD_LZERO RING_COSET_EQ RING_COSET_EQ_IDEAL
   RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_ADD RING_HOMOMORPHISM_COMPOSE
   RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED
   RING_HOMOMORPHISM_INTEGER_RING_OF_INT RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_RING_COSET
   RING_HOMOMORPHISM_RING_OF_INT RING_HOMOMORPHISM_RING_OF_INTEGERS
   RING_HOMOMORPHISM_SUB RING_HOMOMORPHISM_SUBFIELD_INCLUSION
   RING_HOMOMORPHISM_SUM_MUL RING_IDEAL_0 RING_IDEAL_CARRIER
   RING_IDEAL_HOMOMORPHIC_PREIMAGE RING_IDEAL_IDEAL_GENERATED
   RING_IDEAL_IDEAL_POW RING_IDEAL_IDEAL_PROD RING_IDEAL_IMP_SUBSET
   RING_IDEAL_SETADD RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE RING_MATROID_SPANNING
   RING_MONOMORPHISM_EQ_0 RING_MONOMORPHISM_IMP_HOMOMORPHISM
   RING_MONOMORPHISM_INCLUSION RING_MONOMORPHISM_RING_OF_INTEGERS RING_MUL
   RING_MUL_IN_IDEAL_POW RING_OF_INT RING_OF_INTEGERS RING_OF_INTEGERS_CARRIER
   RING_OF_INTEGERS_DENOMINATOR RING_OF_INTEGERS_FINITE_QUOTIENT
   RING_OF_INTEGERS_IDEAL_INTEGER RING_OF_INTEGERS_PRIME_IDEAL_ABOVE
   RING_OF_INTEGERS_PRIME_SUBFIELD RING_OF_INTEGERS_SUBSET
   RING_OF_INT_EQ_0_CHAR_0 RING_OF_INT_IN_PRIME_IDEAL
   RING_OF_INT_IN_RING_OF_INTEGERS RING_OF_INT_IN_SUBFIELD_GENERATED
   RING_OF_INT_MUL RING_OF_INT_OF_NUM RING_OF_INT_SUBFIELD_GENERATED RING_OF_NUM
   RING_OF_NUM_EQ_0 RING_OF_NUM_SUBFIELD_GENERATED RING_POW
   RING_POW_IN_IDEAL_POW RING_SUB RING_SUB_RZERO RING_SUM RING_SUM_ADD
   RING_SUM_CLAUSES RING_SUM_EQ RING_SUM_LMUL SELECT_UNIQUE SIMPLE_IMAGE
   SING_SUBSET SKOLEM_THM SUBFIELD_GENERATED
   SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE
   SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED SUBFIELD_GENERATED_MINIMAL
   SUBFIELD_SUBFIELD_GENERATED SUBRING_GENERATED_BY_SUBFIELD_GENERATED
   SUBRING_OF_HOMOMORPHIC_IMAGE SUBRING_SUBFIELD_GENERATED SUBSET SUBSET_ANTISYM
   SUBSET_REFL SUBSET_TRANS extension_degree field_extension field_of_fractions
   finite_extension free_basis ideal_norm int_divides int_tybij
   matroid_finite_dimensional number_field o_THM proper_ideal ramification_index
   residue_degree ring_divides ring_homomorphism ring_monomorphism
   ring_of_integers ring_setadd : thm)
  deriving Inhabited

/-- What relative_split.ml uses from Session besides theorems. -/
structure RelativeSplitDeps where
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
/- relative_split.ml phrases from line 88 to 789                          -/
/- ---------------------------------------------------------------------- -/

structure RelativeSplit01 where
  -- @@FIELDS
  RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE : thm
  RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ : thm
  RING_OF_INTEGERS_SUBFIELD_GENERATED : thm
  NUMBER_FIELD_HOMOMORPHIC_PREIMAGE : thm
  NUMBER_FIELD_SUBFIELD_GENERATED : thm
  NUMBER_FIELD_TOWER_LAW : thm
  NUMBER_FIELD_SUBFIELD_DEGREE_POS : thm
  NUMBER_FIELD_SUBFIELD_HOMOMORPHIC_IMAGE : thm
  RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION : thm
  RING_OF_INTEGERS_PRIME_IDEAL_BELOW : thm
  RING_OF_INTEGERS_IDEAL_EXTENSION : thm
  RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME : thm
  NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO : thm
  NUMBER_FIELD_PRIME_IDEAL_ABOVE : thm
  NUMBER_FIELD_PRIME_IDEALS_ABOVE : thm
  NUMBER_FIELD_PRIME_FACTORIZATION : thm
  NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE : thm
  RESIDUE_DEGREE_QUOTIENT_RING : thm
  FINITE_QUOTIENT_RING_HOMOMORPHIC_PREIMAGE : thm
  IDEAL_NORM_RESIDUE_DEGREE : thm
  RING_OF_INTEGERS_IDEAL_NORM_PRIME : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupRelativeSplit01 [HolBase] (D : RelativeSplitDeps) :
    ExceptT String IO RelativeSplit01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, TAUT, .. } := D
  let { CARD_EXTENSION_DEGREE, CARRIER_SUBRING_GENERATED_SUBRING, CARRIER_SUBRING_OF,
        CONTRAPOS_THM, DEDEKIND_FINITE_MAXIMAL_IDEALS_ABOVE,
        DEDEKIND_IDEAL_FACTORIZATION, DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE,
        DEDEKIND_KRULL_DIMENSION_ONE, DEDEKIND_MAXIMAL_IDEAL_INVERSE,
        DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL, DEDEKIND_RING_OF_INTEGERS, DE_MORGAN_THM,
        EXISTS_UNIQUE_THM, EXTENSION, EXTENSION_DEGREE_EQ_IMAGE,
        EXTENSION_DEGREE_SUBFIELD_TOWER, FIELD_DIVIDES, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_IMP_NONTRIVIAL_RING, FIELD_NONTRIVIAL,
        FIELD_RING_HOMOMORPHISM_MONOMORPHISM, FIELD_SUBFIELD_GENERATED,
        FINITE_INTEGRAL_DOMAIN_IMP_FIELD, FINITE_RING_MONOMORPHIC_PREIMAGE,
        FINITE_SUBSET, FORALL_IN_GSPEC, FORALL_IN_IMAGE, FUN_EQ_THM, FUN_IN_IMAGE,
        IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, IDEAL_GENERATED_INC_GEN,
        IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_MINIMAL_EQ, IDEAL_GENERATED_MONO,
        IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0, IDEAL_GENERATED_SUBSET, IDEAL_POW_0,
        IDEAL_POW_HOMOMORPHIC_IMAGE, IDEAL_PRODUCT_EQ, IDEAL_PROD_CARRIER,
        IDEAL_PROD_CARRIER_LEFT, IDEAL_PROD_HOMOMORPHIC_IMAGE, IMAGE_CLAUSES, IMAGE_EQ,
        IMAGE_I, IMAGE_SUBSET, IMAGE_o, IMP_CONJ, INTEGRAL_DOMAIN_MUL_LCANCEL,
        INTEGRAL_DOMAIN_QUOTIENT_RING, INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE,
        INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE, IN_ELIM_THM, IN_IDEAL_GENERATED_SING,
        IN_IDEAL_GENERATED_SING_EQ, IN_RING_IDEAL_0, IN_SING, I_THM,
        LEFT_IMP_EXISTS_THM, MAXIMAL_IDEAL_IMP_SUBSET, MAXIMAL_IMP_PRIME_IDEAL,
        MAXIMAL_IMP_RING_IDEAL, MAXIMAL_SUPERIDEAL_EXISTS, .. } := D.core1
  let { MEMBER_NOT_EMPTY, MONO_EXISTS, MULT_EQ_0, NUMBER_FIELD_DEGREE_POS,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_ISOMORPHIC_IMAGE,
        PRIME_IDEAL_HOMOMORPHIC_PREIMAGE, PRIME_IDEAL_IMP_PSUBSET,
        PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_RING_IDEAL,
        PRIME_SUBFIELD_SUBFIELD_GENERATED, PRIME_SUBFIELD_TOWER_LAW, PSUBSET,
        QUOTIENT_RING_CARRIER, QUOTIENT_RING_UNIVERSAL_EXPLICIT, RIGHT_FORALL_IMP_THM,
        RING_0, RING_1, RING_COSET_EQ, RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_COMPOSE,
        RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED,
        RING_HOMOMORPHISM_INTEGER_RING_OF_INT, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_RING_COSET,
        RING_HOMOMORPHISM_RING_OF_INT, RING_HOMOMORPHISM_RING_OF_INTEGERS,
        RING_HOMOMORPHISM_SUB, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_IDEAL_0,
        RING_IDEAL_CARRIER, RING_IDEAL_HOMOMORPHIC_PREIMAGE,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IMP_SUBSET,
        RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE, RING_MONOMORPHISM_EQ_0,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MONOMORPHISM_RING_OF_INTEGERS,
        RING_OF_INTEGERS, RING_OF_INTEGERS_CARRIER, RING_OF_INTEGERS_FINITE_QUOTIENT,
        RING_OF_INTEGERS_IDEAL_INTEGER, RING_OF_INTEGERS_SUBSET,
        RING_OF_INT_EQ_0_CHAR_0, RING_OF_INT_IN_RING_OF_INTEGERS, RING_SUB,
        SIMPLE_IMAGE, SING_SUBSET, SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE,
        SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED, SUBFIELD_GENERATED_MINIMAL,
        SUBFIELD_SUBFIELD_GENERATED, SUBRING_OF_HOMOMORPHIC_IMAGE, SUBSET,
        SUBSET_ANTISYM, SUBSET_REFL, field_extension, finite_extension, ideal_norm,
        number_field, o_THM, proper_ideal, ramification_index, residue_degree,
        ring_divides, ring_homomorphism, ring_monomorphism, .. } := D.core2
  -- @@SCOPE END

  let RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE ← prove
    r"!k:A ring l:B ring h x.
        ring_monomorphism(k,l) h /\ x IN ring_carrier k
        ==> (h x IN ring_carrier(ring_of_integers l) <=>
             x IN ring_carrier(ring_of_integers k))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM] THEN SUBGOAL_THEN (← q r"ring_of_int l = (h:A->B) o ring_of_int k") SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_RING_OF_INT], EQ_TAC THEN DISCH_TAC] THENL [MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_int k:int->A"), (← q r"h:A->B"), (← q r"x:A")] INTEGRAL_ELEMENT_MONOMORPHIC_PREIMAGE), MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_of_int k:int->A"), (← q r"h:A->B"), (← q r"x:A")] INTEGRAL_ELEMENT_HOMOMORPHIC_IMAGE)] THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT])

  let RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ ← prove
    r"!k:A ring l:B ring h.
        ring_monomorphism(k,l) h
        ==> {a | a IN ring_carrier k /\
                 h a IN ring_carrier(ring_of_integers l)} =
            ring_carrier(ring_of_integers k)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"a:A") THEN ASM_CASES_TAC (← q r"(a:A) IN ring_carrier k") THEN ASM_SIMP_TAC [RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE] THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET])

  let RING_OF_INTEGERS_SUBFIELD_GENERATED ← prove
    r"!(k:A ring) s.
        ring_carrier(ring_of_integers(subfield_generated k s)) =
        ring_carrier(ring_of_integers k) INTER
        ring_carrier(subfield_generated k s)"
    (REPEAT GEN_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated k (s:A->bool)"), (← q r"k:A ring"), (← q r"I:A->A")] RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ) THEN REWRITE_TAC [ring_monomorphism, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_THM] THEN ANTS_TAC THENL [MESON_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN SET_TAC [])

  let NUMBER_FIELD_HOMOMORPHIC_PREIMAGE ← prove
    r"!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> number_field k"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring")] PRIME_SUBFIELD_TOWER_LAW) THEN FIRST_X_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP NUMBER_FIELD_IMP_FIELD th)] THEN MP_TAC (← REWRITE_RULE [number_field] th))) THEN ASM_SIMP_TAC [number_field])

  let NUMBER_FIELD_SUBFIELD_GENERATED ← prove
    r"!(k:A ring) s.
        number_field k ==> number_field (subfield_generated k s)"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← ISPECL [(← q r"subfield_generated k (s:A->bool)"), (← q r"k:A ring"), (← q r"I:A->A")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION])

  let NUMBER_FIELD_TOWER_LAW ← prove
    r"!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> finite_extension(k,l) h /\
            extension_degree(subfield_generated l {ring_0 l},l) I =
            extension_degree(subfield_generated k {ring_0 k},k) I *
            extension_degree(k,l) h"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring")] PRIME_SUBFIELD_TOWER_LAW) THEN FIRST_X_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP NUMBER_FIELD_IMP_FIELD th)] THEN MP_TAC (← REWRITE_RULE [number_field] th))) THEN ASM_SIMP_TAC [])

  let NUMBER_FIELD_SUBFIELD_DEGREE_POS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 <= n <=> ~(n:num = 0)")
    prove
      r"!(m:A ring) s t.
          number_field m /\
          ring_carrier(subfield_generated m s) SUBSET
          ring_carrier(subfield_generated m t)
          ==> 1 <= extension_degree(subfield_generated m s,
                                    subfield_generated m t) I"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPEC (← q r"subfield_generated m (t:A->bool)") NUMBER_FIELD_DEGREE_POS) THEN ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED, PRIME_SUBFIELD_SUBFIELD_GENERATED] THEN MP_TAC (← ISPECL [(← q r"m:A ring"), (← q r"{ring_0 m:A}"), (← q r"s:A->bool"), (← q r"t:A->bool")] EXTENSION_DEGREE_SUBFIELD_TOWER) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBFIELD_GENERATED_MINIMAL THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED, SING_SUBSET] THEN ASM_MESON_TAC [RING_0, SUBFIELD_GENERATED, SUBSET], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [r1, MULT_EQ_0, DE_MORGAN_THM] THEN SIMP_TAC [])

  let NUMBER_FIELD_SUBFIELD_HOMOMORPHIC_IMAGE ← prove
    r"!(k:A ring) (m:B ring) j X.
        number_field k /\ field m /\ ring_homomorphism(k,m) j /\
        X SUBSET ring_carrier k
        ==> extension_degree(subfield_generated m {ring_0 m},
                             subfield_generated m (IMAGE j X)) I =
            extension_degree(subfield_generated k {ring_0 k},
                             subfield_generated k X) I /\
            number_field_discriminant(subfield_generated m (IMAGE j X)) =
            number_field_discriminant(subfield_generated k X)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"ring_monomorphism(k:A ring,m:B ring) j") ASSUME_TAC THENL [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"j:A->B"), (← q r"subfield_generated k (X:A->bool)"), (← q r"m:B ring")] RING_ISOMORPHISM_ONTO_SUBFIELD_IMAGE) THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_FROM_SUBFIELD_GENERATED] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"m:B ring"), (← q r"j:A->B"), (← q r"X:A->bool")] SUBFIELD_GENERATED_BY_MONOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated k (X:A->bool)"), (← q r"subfield_generated m (IMAGE (j:A->B) X)"), (← q r"j:A->B")] NUMBER_FIELD_ISOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [NUMBER_FIELD_SUBFIELD_GENERATED, PRIME_SUBFIELD_SUBFIELD_GENERATED])

  let RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION ← prove
    r"!k:A ring l:B ring h p P.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) P
        ==> (IMAGE h p SUBSET P <=>
             {x | x IN ring_carrier(ring_of_integers k) /\ h x IN P} = p)"
    (REPEAT STRIP_TAC THEN EQ_TAC THENL [DISCH_TAC, DISCH_THEN (SUBST1_TAC o SYM) THEN SET_TAC []] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"{x | x IN ring_carrier(ring_of_integers k) /\
                       (h:A->B) x IN P}"), (← q r"p:A->bool")] DEDEKIND_KRULL_DIMENSION_ONE) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN ANTS_TAC THENL [ALL_TAC, DISCH_THEN (ACCEPT_TAC o SYM)] THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC DEDEKIND_RING_OF_INTEGERS THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [], MATCH_MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring")] PRIME_IDEAL_HOMOMORPHIC_PREIMAGE) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS], UNDISCH_TAC (← q r"IMAGE (h:A->B) p SUBSET P") THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool")] PRIME_IDEAL_IMP_SUBSET) THEN ASM_REWRITE_TAC [] THEN SET_TAC []])

  let RING_OF_INTEGERS_PRIME_IDEAL_BELOW ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!x:A. x IN s /\ ~(x = a) ==> ~(s = {a})")
    prove
      r"!k:A ring l:B ring h P.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers l) P /\ ~(P = {ring_0 l})
          ==> ?!p. prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
                   IMAGE h p SUBSET P"
      (REPEAT STRIP_TAC THEN REWRITE_TAC [EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL [ALL_TAC, MAP_EVERY X_GEN_TAC [(← q r"p1:A->bool"), (← q r"p2:A->bool")] THEN STRIP_TAC THEN MAP_EVERY (fun t => tactic_of do pure (MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), t, (← q r"P:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION))) [(← q r"p1:A->bool"), (← q r"p2:A->bool")] THEN ASM_REWRITE_TAC [] THEN MESON_TAC []] THEN EXISTS_TAC (← q r"{x | x IN ring_carrier(ring_of_integers k) /\ (h:A->B) x IN P}") THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN CONJ_TAC THENL [MATCH_MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring")] PRIME_IDEAL_HOMOMORPHIC_PREIMAGE) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [number_field] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"P:B->bool")] RING_OF_INTEGERS_IDEAL_INTEGER) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL, NUMBER_FIELD_IMP_FIELD] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"m:int") STRIP_ASSUME_TAC) THEN MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"ring_of_int k m:A") THEN ASM_SIMP_TAC [IN_ELIM_THM, RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_EQ_0_CHAR_0] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th)])))

  let RING_OF_INTEGERS_IDEAL_EXTENSION ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"c:A"
    let q2 ← q r"h:A->B"
    let q3 ← q r"l:B ring"
    let q4 ← q r"k:A ring"
    let v5 ← ISPECL [q4, q3, q2, q1] RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE
    let q6 ← q r"(c:A) IN ring_carrier(ring_of_integers k)"
    let q7 ← q r"h:A->B"
    let q8 ← q r"l:B ring"
    let q9 ← q r"k:A ring"
    let v10 ← ISPECL [q9, q8, q7] RING_HOMOMORPHISM_MUL
    let q11 ← q r"h:A->B"
    let q12 ← q r"l:B ring"
    let q13 ← q r"k:A ring"
    let v14 ← ISPECL [q13, q12, q11] RING_HOMOMORPHISM_IN_CARRIER
    let q15 ← q r"a:A"
    let q16 ← q r"h:A->B"
    let q17 ← q r"l:B ring"
    let q18 ← q r"k:A ring"
    let v19 ← ISPECL [q18, q17, q16, q15] RING_MONOMORPHISM_EQ_0
    let q20 ← q r"(h:A->B) b = ring_mul l (h a) y"
    let q21 ← q r"(h:A->B) a"
    let q22 ← q r"l:B ring"
    let v23 ← ISPEC q22 INTEGRAL_DOMAIN_MUL_LCANCEL
    let q24 ← q r"(h:A->B) c = y"
    let q25 ← q r"c:A"
    let q26 ← q r"b:A"
    let q27 ← q r"a:A"
    let q28 ← q r"k:A ring"
    let v29 ← ISPECL [q28, q27, q26] FIELD_DIVIDES
    let q30 ← q r"h:A->B"
    let q31 ← q r"ring_of_integers l:B ring"
    let q32 ← q r"ring_of_integers k:A ring"
    let v33 ← ISPECL [q32, q31, q30] RING_HOMOMORPHISM_IN_CARRIER
    let q34 ← q r"(h:A->B) b IN ideal_generated (ring_of_integers l) {h a}"
    let q35 ← q r"?y:B. y IN ring_carrier(ring_of_integers l) /\
                        (h:A->B) b = ring_mul l (h a) y"
    let q36 ← q r"l:B ring"
    let v37 ← ISPEC q36 RING_OF_INTEGERS_SUBSET
    let q38 ← q r"k:A ring"
    let v39 ← ISPEC q38 RING_OF_INTEGERS_SUBSET
    let p40 ← prove r"!k:A ring l:B ring h a b.
        field k /\ field l /\ ring_monomorphism(k,l) h /\
        a IN ring_carrier(ring_of_integers k) /\ ~(a = ring_0 k) /\
        b IN ring_carrier(ring_of_integers k) /\
        h b IN ideal_generated (ring_of_integers l) {h a}
        ==> b IN ideal_generated (ring_of_integers k) {a}" (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN MP_TAC v39 THEN MP_TAC v37 THEN REWRITE_TAC [SUBSET] THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN q35 STRIP_ASSUME_TAC THENL [UNDISCH_TAC q34 THEN MP_TAC v33 THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS] THEN DISCH_TAC THEN ASM_SIMP_TAC [IN_IDEAL_GENERATED_SING_EQ, ring_divides, RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC v29 THEN ASM_SIMP_TAC [ring_divides, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC q25 THEN STRIP_TAC THEN SUBGOAL_THEN q24 ASSUME_TAC THENL [MATCH_MP_TAC v23 THEN EXISTS_TAC q21 THEN UNDISCH_TAC q20 THEN MP_TAC v19 THEN MP_TAC v14 THEN MP_TAC v10 THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN SUBGOAL_THEN q6 ASSUME_TAC THENL [MP_TAC v5 THEN ASM_REWRITE_TAC [], MATCH_MP_TAC IN_IDEAL_GENERATED_SING THEN REWRITE_TAC [ring_divides, RING_OF_INTEGERS] THEN ASM_MESON_TAC []])
    let lemma1 := p40
    let q44 ← q r"{a:A}"
    let q45 ← q r"h:A->B"
    let q46 ← q r"ring_of_integers l:B ring"
    let q47 ← q r"ring_of_integers k:A ring"
    let v48 ← ISPECL [q47, q46, q45, q44] IDEAL_GENERATED_IMAGE_IDEAL_GENERATED
    let q49 ← q r"ideal_generated (ring_of_integers l) {(h:A->B) a} =
      ideal_generated (ring_of_integers l) (IMAGE h q)"
    let q50 ← q r"h:A->B"
    let q51 ← q r"l:B ring"
    let q52 ← q r"~((b:A) IN ideal_generated (ring_of_integers k) {a})"
    let q53 ← q r"q:A->bool"
    let q54 ← q r"ring_of_integers k:A ring"
    let v55 ← ISPECL [q54, q53] RING_IDEAL_IMP_SUBSET
    let q56 ← q r"k:A ring"
    let v57 ← ISPEC q56 FIELD_NONTRIVIAL
    let q58 ← q r"ring_of_integers k:A ring"
    let v59 ← ISPEC q58 RING_1
    let q60 ← q r"ring_carrier(ring_of_integers k):A->bool"
    let q61 ← q r"?b:A. b IN q /\ b IN ring_carrier(ring_of_integers k) /\
            ~(b IN ideal_generated (ring_of_integers k) {a})"
    let q62 ← q r"q:A->bool"
    let q63 ← q r"a:A"
    let q64 ← q r"m:A->bool"
    let q65 ← q r"ring_of_integers k:A ring"
    let v66 ← ISPECL [q65, q64, q63] DEDEKIND_MAXIMAL_IDEAL_INVERSE
    let q67 ← q r"~(m = {ring_0 k:A})"
    let q68 ← q r"m:A->bool"
    let q69 ← q r"ring_of_integers k:A ring"
    let v70 ← ISPECL [q69, q68] MAXIMAL_IDEAL_IMP_SUBSET
    let q71 ← q r"m:A->bool"
    let q72 ← q r"ring_of_integers k:A ring"
    let v73 ← ISPECL [q72, q71] IN_RING_IDEAL_0
    let q74 ← q r"?a:A. a IN m /\ a IN ring_carrier(ring_of_integers k) /\ ~(a = ring_0 k)"
    let q75 ← q r"l:B ring"
    let v76 ← ISPEC q75 FIELD_NONTRIVIAL
    let q77 ← q r"ring_of_integers l:B ring"
    let v78 ← ISPEC q77 RING_1
    let q79 ← q r"m:A->bool"
    let q80 ← q r"h:A->B"
    let q81 ← q r"ring_of_integers l:B ring"
    let q82 ← q r"ring_of_integers k:A ring"
    let v83 ← ISPECL [q82, q81, q80, q79] IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0
    let q84 ← q r"m = {ring_0 k:A}"
    let p85 ← prove r"!k:A ring l:B ring h m.
        number_field k /\ field l /\ ring_monomorphism(k,l) h /\
        maximal_ideal (ring_of_integers k) m
        ==> ~(ideal_generated (ring_of_integers l) (IMAGE h m) =
              ring_carrier(ring_of_integers l))" (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_RING_OF_INTEGERS)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN ASM_CASES_TAC q84 THENL [MP_TAC v83 THEN ASM_SIMP_TAC [MAXIMAL_IMP_RING_IDEAL, RING_OF_INTEGERS] THEN MP_TAC v78 THEN MP_TAC v76 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q74 STRIP_ASSUME_TAC THENL [MP_TAC v73 THEN MP_TAC v70 THEN ASM_SIMP_TAC [MAXIMAL_IMP_RING_IDEAL, RING_OF_INTEGERS] THEN UNDISCH_TAC q67 THEN SET_TAC [], ALL_TAC] THEN MP_TAC v66 THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS] THEN DISCH_THEN (X_CHOOSE_THEN q62 STRIP_ASSUME_TAC) THEN SUBGOAL_THEN q61 STRIP_ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o (SPEC q60)) THEN ASM_SIMP_TAC [RING_IDEAL_CARRIER, IDEAL_PROD_CARRIER_LEFT, IDEAL_PROD_CARRIER, RING_IDEAL_IDEAL_GENERATED] THEN MP_TAC v59 THEN MP_TAC v57 THEN MP_TAC v55 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN SET_TAC [], ALL_TAC] THEN UNDISCH_TAC q52 THEN REWRITE_TAC [] THEN MATCH_MP_TAC lemma1 THEN MAP_EVERY EXISTS_TAC [q51, q50] THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN q49 SUBST1_TAC THENL [MP_TAC v48 THEN ASM_REWRITE_TAC [SING_SUBSET, IMAGE_CLAUSES] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun z41 => (do let z42 ← (do let z43 ← (pure z41); pure (concl z43)); pure (is_eq z42)))))) THEN ASM_SIMP_TAC [IDEAL_PROD_HOMOMORPHIC_IMAGE, MAXIMAL_IDEAL_IMP_SUBSET, RING_IDEAL_IMP_SUBSET, IDEAL_PROD_CARRIER_LEFT, RING_IDEAL_IDEAL_GENERATED], MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN ASM_SIMP_TAC [FUN_IN_IMAGE] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_MONOMORPHISM_IMP_HOMOMORPHISM]])
    let lemma2 := p85
    let q86 ← q r"(s:B->bool) SUBSET t /\ t SUBSET u ==> ~(t = u) ==> ~(s = u)"
    let r87 ← SET_RULE q86
    let q88 ← q r"m:A->bool"
    let q89 ← q r"h:A->B"
    let q90 ← q r"l:B ring"
    let q91 ← q r"k:A ring"
    let v92 ← ISPECL [q91, q90, q89, q88] lemma2
    let q93 ← q r"m:A->bool"
    let q94 ← q r"j:A->bool"
    let q95 ← q r"ring_of_integers k:A ring"
    let v96 ← ISPECL [q95, q94] MAXIMAL_SUPERIDEAL_EXISTS
    let v97 ← GSYM CONTRAPOS_THM
    let q98 ← q r"0"
    let q99 ← q r"ring_carrier(ring_of_integers k):A->bool"
    let q100 ← q r"h:A->B"
    let q101 ← q r"ring_of_integers l:B ring"
    let q102 ← q r"ring_of_integers k:A ring"
    let v103 ← ISPECL [q102, q101, q100, q99, q98] IDEAL_POW_HOMOMORPHIC_IMAGE
    let q104 ← q r"j:A->bool"
    let q105 ← q r"h:A->B"
    let q106 ← q r"ring_of_integers l:B ring"
    let q107 ← q r"ring_of_integers k:A ring"
    let v108 ← ISPECL [q107, q106, q105, q104] IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0
    let q109 ← q r"ring_monomorphism(k:A ring,l:B ring) h"
    let q110 ← q r"h:A->B"
    let q111 ← q r"l:B ring"
    let q112 ← q r"k:A ring"
    let v113 ← ISPECL [q112, q111, q110] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE
    prove
      r"!k:A ring l:B ring h j.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          ring_ideal (ring_of_integers k) j
          ==> (ideal_generated (ring_of_integers l) (IMAGE h j) =
               ring_carrier(ring_of_integers l) <=>
               j = ring_carrier(ring_of_integers k)) /\
              (ideal_generated (ring_of_integers l) (IMAGE h j) = {ring_0 l} <=>
               j = {ring_0 k})"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC v113 THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN q109 ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_RING_HOMOMORPHISM_MONOMORPHISM, NUMBER_FIELD_IMP_FIELD, FIELD_IMP_NONTRIVIAL_RING], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_RING_OF_INTEGERS)) THEN CONJ_TAC THENL [ALL_TAC, MP_TAC v108 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS]] THEN EQ_TAC THENL [ALL_TAC, DISCH_THEN SUBST1_TAC THEN MP_TAC v103 THEN ASM_SIMP_TAC [IDEAL_POW_0, SUBSET_REFL, RING_MONOMORPHISM_IMP_HOMOMORPHISM]] THEN GEN_REWRITE_TAC id [v97] THEN DISCH_TAC THEN MP_TAC v96 THEN ASM_SIMP_TAC [proper_ideal, PSUBSET, RING_IDEAL_IMP_SUBSET] THEN DISCH_THEN (X_CHOOSE_THEN q93 STRIP_ASSUME_TAC) THEN MP_TAC v92 THEN ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD] THEN MATCH_MP_TAC r87 THEN REWRITE_TAC [IDEAL_GENERATED_SUBSET] THEN MATCH_MP_TAC IDEAL_GENERATED_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC [])

  let RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(s:B->bool) SUBSET t ==> t INTER s = s")
    prove
      r"!k:A ring l:B ring h p.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
          ==> ~(ideal_generated (ring_of_integers l) (IMAGE h p) =
                ring_carrier(ring_of_integers l)) /\
              ~(ideal_generated (ring_of_integers l) (IMAGE h p) = {ring_0 l}) /\
              {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P} =
              {P | prime_ideal (ring_of_integers l) P /\ ~(P = {ring_0 l}) /\
                   ideal_generated (ring_of_integers l) (IMAGE h p) SUBSET P}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:A->bool")] PRIME_IDEAL_IMP_PSUBSET) THEN ASM_REWRITE_TAC [PSUBSET] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"IMAGE (h:A->B) p SUBSET ring_carrier(ring_of_integers l)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN ASM_REWRITE_TAC [ring_homomorphism] THEN ASM SET_TAC [], ALL_TAC] THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"P:B->bool") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"prime_ideal (ring_of_integers l) (P:B->bool)") THEN ASM_SIMP_TAC [IDEAL_GENERATED_MINIMAL_EQ, PRIME_IMP_RING_IDEAL, r1] THEN ASM_CASES_TAC (← q r"P = {ring_0 l:B}") THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~(ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p) =
                   {ring_0 l})") THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPEC (← q r"ring_of_integers l:B ring") RING_IDEAL_0) THEN REWRITE_TAC [RING_OF_INTEGERS], MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)")] IN_RING_IDEAL_0) THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS] THEN SET_TAC []])

  let NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO ← prove
    r"!k:A ring l:B ring h p P.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P
        ==> ~(P = {ring_0 l})"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN ASM_REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN DISCH_THEN (fun z1 => tactic_of do pure (MP_TAC (← SPEC (← q r"P:B->bool") (← (do let z2 ← (pure (CONJUNCTS z1)); liftExcept (last z2)))))) THEN ASM_SIMP_TAC [])

  let NUMBER_FIELD_PRIME_IDEAL_ABOVE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q /\ r) /\ s ==> p /\ q /\ r /\ s")
    prove
      r"!(h:A->B) k l p Q.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          prime_ideal (ring_of_integers l) Q /\ IMAGE h p SUBSET Q
          ==> ~(Q = {ring_0 l}) /\ maximal_ideal (ring_of_integers l) Q /\
              FINITE(ring_carrier(quotient_ring (ring_of_integers l) Q)) /\
              {a | a IN ring_carrier k /\ h a IN Q} = p"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN SUBGOAL_THEN (← q r"ring_monomorphism(k:A ring,l:B ring) h") ASSUME_TAC THENL [ASM_MESON_TAC [finite_extension, field_extension], ALL_TAC] THEN MATCH_MP_TAC r1 THEN REPEAT CONJ_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(p = {ring_0(k:A ring)})") THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"IMAGE (h:A->B) p SUBSET {ring_0 l}") THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_SING] THEN DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [PRIME_IDEAL_IMP_SUBSET, RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_0) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"ring_monomorphism(k:A ring,l:B ring) h") THEN REWRITE_TAC [ring_monomorphism] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_0], REWRITE_TAC [SING_SUBSET] THEN ASM_MESON_TAC [IN_RING_IDEAL_0, PRIME_IMP_RING_IDEAL, RING_OF_INTEGERS]], DISCH_TAC THEN CONJ_TAC THENL [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS], MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL]], MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"Q:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"Q:B->bool")] PRIME_IDEAL_IMP_SUBSET) THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_SUBSET) THEN ASM_REWRITE_TAC [] THEN SET_TAC []])

  let NUMBER_FIELD_PRIME_IDEALS_ABOVE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(a:B) IN s /\ s SUBSET {a} ==> s = {a}")
    prove
      r"!k:A ring l:B ring h p.
          field k /\ number_field l /\ ring_homomorphism(k,l) h /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
          ==> FINITE {P | prime_ideal (ring_of_integers l) P /\
                          IMAGE h p SUBSET P} /\
              ~({P | prime_ideal (ring_of_integers l) P /\
                     IMAGE h p SUBSET P} = {})"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"J = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN SUBGOAL_THEN (← q r"dedekind_domain(ring_of_integers l:B ring) /\
                  ring_ideal (ring_of_integers l) (J:B->bool)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "J" THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{m | maximal_ideal (ring_of_integers l) m /\
                       (J:B->bool) SUBSET m}") THEN CONJ_TAC THENL [MATCH_MP_TAC DEDEKIND_FINITE_MAXIMAL_IDEALS_ABOVE THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [(← REWRITE_RULE [RING_OF_INTEGERS] (← ISPEC (← q r"ring_of_integers l:B ring") DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL))]], MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool")] MAXIMAL_SUPERIDEAL_EXISTS) THEN ASM_SIMP_TAC [proper_ideal, PSUBSET, RING_IDEAL_IMP_SUBSET] THEN REWRITE_TAC [(← GSYM MEMBER_NOT_EMPTY), IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"P:B->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [MAXIMAL_IMP_PRIME_IDEAL] THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(J = {ring_0 l:B})") THEN REWRITE_TAC [] THEN MATCH_MP_TAC r1 THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"J:B->bool")] IN_RING_IDEAL_0) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS]])

  let NUMBER_FIELD_PRIME_FACTORIZATION ← prove
    r"!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> ideal_generated (ring_of_integers l) (IMAGE h p) =
            ideal_product (ring_of_integers l)
              {P | prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P}
              (\P. ideal_pow (ring_of_integers l) P
                     (ramification_index
                        (ring_of_integers k,ring_of_integers l) h P))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 (fun (_ : thm) => ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (fun th => tactic_of do pure (SUBST1_TAC th THEN ASSUME_TAC (← SYM th))))) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)")] DEDEKIND_IDEAL_FACTORIZATION) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, RING_OF_INTEGERS] THEN DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [(← GSYM (← CONJUNCT2 th))])) THEN MATCH_MP_TAC IDEAL_PRODUCT_EQ THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"P:B->bool") THEN STRIP_TAC THEN REWRITE_TAC [ramification_index] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN ASM_SIMP_TAC [])

  let NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE ← prove
    r"!k:A ring l:B ring h p s e.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        FINITE s /\
        (!P. P IN s ==> prime_ideal (ring_of_integers l) P /\ ~(e P = 0)) /\
        ideal_generated (ring_of_integers l) (IMAGE h p) =
        ideal_product (ring_of_integers l) s
          (\P. ideal_pow (ring_of_integers l) P (e P))
        ==> s = {P | prime_ideal (ring_of_integers l) P /\
                     IMAGE h p SUBSET P} /\
            !P. P IN s
                ==> ramification_index
                      (ring_of_integers k,ring_of_integers l) h P = e P"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_eq z2))))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (CONJUNCTS_THEN2 (fun (_ : thm) => ALL_TAC) (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN ABBREV_TAC (← q r"J = ideal_product (ring_of_integers l) s
                   (\P. ideal_pow (ring_of_integers l) P
                                  ((e:(B->bool)->num) P))") THEN DISCH_TAC THEN DISCH_THEN (fun th => SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN MP_TAC (← REWRITE_RULE [RING_OF_INTEGERS] (← ISPECL [(← q r"ring_of_integers l:B ring"), (← q r"s:(B->bool)->bool"), (← q r"e:(B->bool)->num")] DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE)) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS] THEN STRIP_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC [EXTENSION, IN_ELIM_THM], ALL_TAC] THEN X_GEN_TAC (← q r"P:B->bool") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"IMAGE (h:A->B) p SUBSET P") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"P:B->bool")) o ((GEN_REWRITE_RULE id [EXTENSION]) o (CONJUNCT2 o CONJUNCT2)))) THEN ASM_REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN REWRITE_TAC [ramification_index] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [])

  let RESIDUE_DEGREE_QUOTIENT_RING ← prove
    r"!r:A ring s:B ring h P.
        ring_homomorphism(r,s) h /\ ring_ideal s P
        ==> ?g. ring_monomorphism
                  (quotient_ring r {x | x IN ring_carrier r /\ h x IN P},
                   quotient_ring s P) g /\
                (!y. y IN ring_carrier r
                     ==> g(ring_coset r {x | x IN ring_carrier r /\ h x IN P}
                                      y) =
                         ring_coset s P (h y)) /\
                residue_degree (r,s) h P =
                extension_degree
                  (quotient_ring r {x | x IN ring_carrier r /\ h x IN P},
                   quotient_ring s P) g"
    (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"p = {x | x IN ring_carrier r /\ (h:A->B) x IN P}") THEN SUBGOAL_THEN (← q r"ring_ideal r (p:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "p" THEN MATCH_MP_TAC RING_IDEAL_HOMOMORPHIC_PREIMAGE THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x y:A. x IN ring_carrier r /\ y IN ring_carrier r
            ==> (ring_coset r p x = ring_coset r p y <=>
                 ring_coset s P (h x) = ring_coset s P ((h:A->B) y))") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [ring_homomorphism])) THEN SUBGOAL_THEN (← q r"(h:A->B) x IN ring_carrier s /\ h y IN ring_carrier s") STRIP_ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [RING_COSET_EQ] THEN EXPAND_TAC "p" THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B")] RING_HOMOMORPHISM_SUB) THEN ASM_SIMP_TAC [IN_ELIM_THM, RING_SUB], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(r:A ring,quotient_ring s P)
                                  (ring_coset s P o (h:A->B))") ASSUME_TAC THENL [MATCH_MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"quotient_ring s (P:B->bool)")] RING_HOMOMORPHISM_COMPOSE) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"quotient_ring s (P:B->bool)"), (← q r"p:A->bool"), (← q r"ring_coset s P o (h:A->B)")] QUOTIENT_RING_UNIVERSAL_EXPLICIT) THEN ASM_SIMP_TAC [o_THM] THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"g:(A->bool)->(B->bool)") THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN CONJ_TAC THENL [ASM_REWRITE_TAC [ring_monomorphism] THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC], REWRITE_TAC [residue_degree] THEN MATCH_MP_TAC EXTENSION_DEGREE_EQ_IMAGE THEN REWRITE_TAC [IMAGE_I] THEN SUBGOAL_THEN (← q r"IMAGE (ring_coset s P o (h:A->B)) (ring_carrier r) subring_of
                  quotient_ring s P") ASSUME_TAC THENL [MATCH_MP_TAC (← ISPEC (← q r"r:A ring") SUBRING_OF_HOMOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [CARRIER_SUBRING_OF], ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING, QUOTIENT_RING_CARRIER]] THEN REWRITE_TAC [SIMPLE_IMAGE, (← GSYM IMAGE_o)] THEN MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC [o_THM]])

  let FINITE_QUOTIENT_RING_HOMOMORPHIC_PREIMAGE ← prove
    r"!r:A ring s:B ring h j.
        ring_homomorphism(r,s) h /\ ring_ideal s j /\
        FINITE(ring_carrier(quotient_ring s j))
        ==> FINITE(ring_carrier
             (quotient_ring r {x | x IN ring_carrier r /\ h x IN j}))"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"j:B->bool")] RESIDUE_DEGREE_QUOTIENT_RING) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"g:(A->bool)->(B->bool)") (MP_TAC o CONJUNCT1)) THEN ASM_MESON_TAC [FINITE_RING_MONOMORPHIC_PREIMAGE])

  let IDEAL_NORM_RESIDUE_DEGREE ← prove
    r"!r:A ring s:B ring h P.
        ring_homomorphism(r,s) h /\ prime_ideal s P /\
        FINITE(ring_carrier(quotient_ring s P))
        ==> ideal_norm s P =
            ideal_norm r {x | x IN ring_carrier r /\ h x IN P} EXP
            residue_degree (r,s) h P"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"P:B->bool")] RESIDUE_DEGREE_QUOTIENT_RING) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"P:B->bool")] FINITE_QUOTIENT_RING_HOMOMORPHIC_PREIMAGE) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"P:B->bool")] PRIME_IDEAL_HOMOMORPHIC_PREIMAGE) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN ABBREV_TAC (← q r"p = {x | x IN ring_carrier r /\ (h:A->B) x IN P}") THEN REPEAT DISCH_TAC THEN FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"g:(A->bool)->(B->bool)") STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [ideal_norm] THEN MATCH_MP_TAC CARD_EXTENSION_DEGREE THEN ASM_REWRITE_TAC [field_extension] THEN CONJ_TAC THEN MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_IMP_FIELD THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_QUOTIENT_RING, PRIME_IMP_RING_IDEAL])

  let RING_OF_INTEGERS_IDEAL_NORM_PRIME ← prove
    r"!k:A ring l:B ring h p P.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P
        ==> ideal_norm (ring_of_integers l) P =
            ideal_norm (ring_of_integers k) p EXP
            residue_degree (ring_of_integers k,ring_of_integers l)
                                    h P"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IDEAL_NORM_RESIDUE_DEGREE THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS] THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"P:B->bool")) o ((GEN_REWRITE_RULE id [EXTENSION]) o (CONJUNCT2 o CONJUNCT2)))) THEN ASM_SIMP_TAC [IN_ELIM_THM])

  -- @@RETURN BEGIN
  return { RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE,
           RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE_EQ, RING_OF_INTEGERS_SUBFIELD_GENERATED,
           NUMBER_FIELD_HOMOMORPHIC_PREIMAGE, NUMBER_FIELD_SUBFIELD_GENERATED,
           NUMBER_FIELD_TOWER_LAW, NUMBER_FIELD_SUBFIELD_DEGREE_POS,
           NUMBER_FIELD_SUBFIELD_HOMOMORPHIC_IMAGE,
           RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION, RING_OF_INTEGERS_PRIME_IDEAL_BELOW,
           RING_OF_INTEGERS_IDEAL_EXTENSION, RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME,
           NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO, NUMBER_FIELD_PRIME_IDEAL_ABOVE,
           NUMBER_FIELD_PRIME_IDEALS_ABOVE, NUMBER_FIELD_PRIME_FACTORIZATION,
           NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE, RESIDUE_DEGREE_QUOTIENT_RING,
           FINITE_QUOTIENT_RING_HOMOMORPHIC_PREIMAGE, IDEAL_NORM_RESIDUE_DEGREE,
           RING_OF_INTEGERS_IDEAL_NORM_PRIME }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- relative_split.ml phrases from line 813 to 1449                        -/
/- ---------------------------------------------------------------------- -/

structure RelativeSplit02 where
  -- @@FIELDS
  NUMBER_FIELD_PRIME_NORM_CARD : thm
  IDEAL_VALUATION_HOMOMORPHIC_IMAGE : thm
  IDEAL_VALUATION_HOMOMORPHIC_IMAGE_SING : thm
  DEDEKIND_VALUATION_RAMIFICATION_INDEX : thm
  DEDEKIND_RAMIFICATION_INDEX_NONZERO : thm
  NUMBER_FIELD_VALUATION_RAMIFICATION_INDEX : thm
  NUMBER_FIELD_IDEAL_VALUATION_EXTENSION : thm
  RESIDUE_DEGREE_TOWER : thm
  RAMIFICATION_INDEX_TOWER : thm
  NUMBER_FIELD_RAMIFICATION_INDEX_TOWER : thm
  NUMBER_FIELD_RESIDUE_DEGREE_TOWER : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupRelativeSplit02 [HolBase] (D : RelativeSplitDeps) (BRelativeSplit01 : RelativeSplit01) :
    ExceptT String IO RelativeSplit02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, INT_ARITH_TAC, MESON_TAC, SET_RULE,
        SET_TAC, .. } := D
  let { ADD_CLAUSES, CARD_EQ_NSUM, DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES,
        DEDEKIND_IDEAL_SUBSET_POW_VALUATION, DEDEKIND_IMP_INTEGRAL_DOMAIN,
        DEDEKIND_RING_OF_INTEGERS, DEDEKIND_VALUATION, EQ_EXP, EXISTS_UNIQUE,
        EXISTS_UNIQUE_DEF, EXISTS_UNIQUE_THM, EXP_1, EXP_EXP, EXTENSION,
        FIELD_FRACTION_NONZERO, FIELD_IMP_NONTRIVIAL_RING,
        FIELD_RING_HOMOMORPHISM_MONOMORPHISM, FINITE_IMP_FIELD_EXTENSION,
        FINITE_SUBSET, FORALL_IN_IMAGE, IDEAL_GENERATED_EQ_0,
        IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, IDEAL_GENERATED_INC_GEN,
        IDEAL_GENERATED_MINIMAL, IDEAL_GENERATED_MINIMAL_EQ,
        IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0, IDEAL_NORM_GT_1, IDEAL_POW_1,
        IDEAL_POW_EQ_ZERO, IDEAL_POW_HOMOMORPHIC_IMAGE, IDEAL_POW_SUC, IDEAL_PROD_COMM,
        IDEAL_PROD_HOMOMORPHIC_IMAGE, IDEAL_PROD_MONO, IDEAL_PROD_RZERO,
        IDEAL_VALUATION_EQ_0, IDEAL_VALUATION_IDEAL_POW, IDEAL_VALUATION_IDEAL_PROD,
        IMAGE_CLAUSES, IMAGE_o, INT_OF_NUM_MUL, IN_ELIM_THM, IN_IMAGE, IN_RING_IDEAL_0,
        IN_SING, I_DEF, I_THM, LEFT_IMP_EXISTS_THM, LE_REFL, .. } := D.core1
  let { MONO_EXISTS, MULT_SYM, NOT_FORALL_THM, NSUM_EQ, NSUM_GROUP,
        NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM, NUMBER_FIELD_IMP_FIELD,
        PRIME_EXP, PRIME_IDEAL_HOMOMORPHIC_PREIMAGE, PRIME_IDEAL_IMP_PSUBSET,
        PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_RING_IDEAL, PSUBSET, RING_0,
        RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_COMPOSE, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_IDEAL_0,
        RING_IDEAL_HOMOMORPHIC_PREIMAGE, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_PROD, RING_IDEAL_IMP_SUBSET,
        RING_MONOMORPHISM_EQ_0, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
        RING_MONOMORPHISM_INCLUSION, RING_MONOMORPHISM_RING_OF_INTEGERS,
        RING_OF_INTEGERS, RING_OF_INTEGERS_DENOMINATOR,
        RING_OF_INTEGERS_FINITE_QUOTIENT, SELECT_UNIQUE, SING_SUBSET, SUBSET,
        SUBSET_ANTISYM, SUBSET_REFL, field_extension, field_of_fractions, o_THM,
        ramification_index, ring_of_integers, .. } := D.core2
  let { FINITE_QUOTIENT_RING_HOMOMORPHIC_PREIMAGE, IDEAL_NORM_RESIDUE_DEGREE,
        NUMBER_FIELD_HOMOMORPHIC_PREIMAGE, NUMBER_FIELD_PRIME_IDEALS_ABOVE,
        NUMBER_FIELD_PRIME_IDEAL_ABOVE, NUMBER_FIELD_TOWER_LAW,
        RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME, RING_OF_INTEGERS_IDEAL_NORM_PRIME,
        RING_OF_INTEGERS_PRIME_IDEAL_BELOW, RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION, .. } := BRelativeSplit01
  -- @@SCOPE END

  let NUMBER_FIELD_PRIME_NORM_CARD ← prove
    r"!(h:A->B) k l m.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\ prime m
        ==> CARD {P | prime_ideal (ring_of_integers l) P /\
                      ~(P = {ring_0 l}) /\
                      ideal_norm (ring_of_integers l) P = m} =
            nsum {p | prime_ideal (ring_of_integers k) p /\
                      ~(p = {ring_0 k}) /\
                      ideal_norm (ring_of_integers k) p = m}
                 (\p. CARD {P | prime_ideal (ring_of_integers l) P /\
                                IMAGE h p SUBSET P /\
                                residue_degree
                                 (ring_of_integers k,ring_of_integers l) h P =
                                1})"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"number_field(k:A ring)") ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_HOMOMORPHIC_PREIMAGE], ALL_TAC] THEN ABBREV_TAC (← q r"L = {P | prime_ideal (ring_of_integers l) P /\ ~(P = {ring_0 l}) /\
             ideal_norm (ring_of_integers l) (P:B->bool) = m}") THEN ABBREV_TAC (← q r"K = {p | prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
             ideal_norm (ring_of_integers k) (p:A->bool) = m}") THEN ABBREV_TAC (← q r"bel = \P:B->bool. @p. prime_ideal (ring_of_integers k) p /\
                          ~(p = {ring_0 k}) /\ IMAGE (h:A->B) p SUBSET P") THEN SUBGOAL_THEN (← q r"!P. prime_ideal (ring_of_integers l) P /\ ~(P = {ring_0 l})
        ==> prime_ideal (ring_of_integers k) ((bel:(B->bool)->A->bool) P) /\
            ~(bel P = {ring_0 k}) /\ IMAGE (h:A->B) (bel P) SUBSET P /\
            !p. prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
                IMAGE h p SUBSET P ==> p = bel P") ASSUME_TAC THENL [X_GEN_TAC (← q r"P:B->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"P:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_BELOW) THEN ASM_REWRITE_TAC [EXISTS_UNIQUE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"p0:A->bool") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(bel:(B->bool)->A->bool) P = p0") SUBST1_TAC THENL [EXPAND_TAC "bel" THEN REWRITE_TAC [] THEN MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC [], ASM_MESON_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"FINITE(L:(B->bool)->bool)") ASSUME_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{P | prime_ideal (ring_of_integers l) P /\ ~(P = {ring_0 l}) /\
           ideal_norm (ring_of_integers l) (P:B->bool) <= m}") THEN ASM_SIMP_TAC [NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM] THEN EXPAND_TAC "L" THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN MESON_TAC [LE_REFL], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P p. prime_ideal (ring_of_integers l) P /\
          prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
          IMAGE (h:A->B) p SUBSET P
          ==> ideal_norm (ring_of_integers l) P =
              ideal_norm (ring_of_integers k) p EXP
              residue_degree (ring_of_integers k,ring_of_integers l) h P") (LABEL_TAC "nrm") THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_OF_INTEGERS_IDEAL_NORM_PRIME THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [CARD_EQ_NSUM] THEN MP_TAC (← ISPECL [(← q r"bel:(B->bool)->A->bool"), (← q r"\x:B->bool. 1"), (← q r"L:(B->bool)->bool"), (← q r"K:(A->bool)->bool")] NSUM_GROUP) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN X_GEN_TAC (← q r"P:B->bool") THEN EXPAND_TAC "L" THEN EXPAND_TAC "K" THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"P:B->bool")) o (checkM (fun th => (do if ← (do let z17 ← (do let z18 ← (pure th); pure (concl z18)); pure (is_forall z17)) then (do let z20 ← (do let z21 ← (pure th); pure (concl z21)); let z19 ← (q r"bel:(B->bool)->A->bool"); pure (free_in z19 z20)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN USE_THEN "nrm" (MP_TAC o (SPECL [(← q r"P:B->bool"), (← q r"(bel:(B->bool)->A->bool) P")])) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [th] THEN MP_TAC (← REWRITE_RULE [th] (← ASSUME (← q r"prime m"))))) THEN SIMP_TAC [PRIME_EXP, EXP_1], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"p:A->bool") THEN EXPAND_TAC "K" THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"{P | P IN L /\ (bel:(B->bool)->A->bool) P = p} =
    {P | prime_ideal (ring_of_integers l) P /\ IMAGE (h:A->B) p SUBSET P /\
         residue_degree (ring_of_integers k,ring_of_integers l) h P = 1}") SUBST1_TAC THENL [EXPAND_TAC "L" THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"P:B->bool") THEN EQ_TAC THENL [STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"P:B->bool")) o (checkM (fun th => (do if ← (do let z12 ← (do let z13 ← (pure th); pure (concl z13)); pure (is_forall z12)) then (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); let z14 ← (q r"bel:(B->bool)->A->bool"); pure (free_in z14 z15)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN USE_THEN "nrm" (MP_TAC o (SPECL [(← q r"P:B->bool"), (← q r"p:A->bool")])) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"prime(m EXP residue_degree (ring_of_integers k,ring_of_integers l)
                      (h:A->B) P)") MP_TAC THENL [FIRST_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); pure (is_eq z6)) then (do let z11 ← (q r"m:num"); let z10 ← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); liftExcept (lhs z8)); pure (z10 == z11)) else pure false))))) THEN ASM_REWRITE_TAC [], SIMP_TAC [PRIME_EXP]], STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_PRIME_IDEAL_ABOVE) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [USE_THEN "nrm" (MP_TAC o (SPECL [(← q r"P:B->bool"), (← q r"p:A->bool")])) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [EXP_1], CONV_TAC SYM_CONV THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"P:B->bool")) o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); let z3 ← (q r"bel:(B->bool)->A->bool"); pure (free_in z3 z4)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC []]], ALL_TAC] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_EQ_NSUM THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{P | prime_ideal (ring_of_integers l) P /\
                   IMAGE (h:A->B) p SUBSET P}") THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool")] NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN ASM_SIMP_TAC [], SET_TAC []])

  let IDEAL_VALUATION_HOMOMORPHIC_IMAGE ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"ideal_pow r (p:A->bool) n"
    let q2 ← q r"p:A->bool"
    let q3 ← q r"r:A ring"
    let v4 ← ISPECL [q3, q2, q1] IDEAL_PROD_COMM
    let q5 ← q r"~(SUC n <= n)"
    let r6 ← ARITH_RULE q5
    let q7 ← q r"SUC n"
    let q8 ← q r"ideal_prod r (ideal_pow r p n) (i:A->bool)"
    let q9 ← q r"p:A->bool"
    let q10 ← q r"r:A ring"
    let v11 ← ISPECL [q10, q9, q8, q7] DEDEKIND_IDEAL_SUBSET_POW_VALUATION
    let q12 ← q r"~(ideal_prod r (ideal_pow r p n) i = {ring_0(r:A ring)})"
    let q13 ← q r"i:A->bool"
    let q14 ← q r"n:num"
    let q15 ← q r"j:A->bool"
    let q16 ← q r"p:A->bool"
    let q17 ← q r"r:A ring"
    let v18 ← ISPECL [q17, q16, q15, q14] DEDEKIND_IDEAL_SUBSET_POW_VALUATION
    let q19 ← q r"ideal_pow r (p:A->bool) n"
    let q20 ← q r"j:A->bool"
    let q21 ← q r"r:A ring"
    let v22 ← ISPECL [q21, q20, q19] DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES
    let q23 ← q r"n = ideal_valuation r p (j:A->bool)"
    let p24 ← prove r"!r p j:A->bool.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
        ring_ideal r j /\ ~(j = {ring_0 r})
        ==> ?i. ring_ideal r i /\ ~(i = {ring_0 r}) /\ ~(i SUBSET p) /\
                ideal_prod r (ideal_pow r p (ideal_valuation r p j)) i = j" (REPEAT STRIP_TAC THEN ABBREV_TAC q23 THEN MP_TAC v22 THEN MP_TAC v18 THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, LE_REFL] THEN DISCH_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q13 THEN STRIP_TAC THEN FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THEN DISCH_TAC THENL [UNDISCH_TAC q12 THEN ASM_SIMP_TAC [IDEAL_PROD_RZERO, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW], MP_TAC v11 THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_PROD, r6] THEN REWRITE_TAC [IDEAL_POW_SUC] THEN MP_TAC v4 THEN ASM_SIMP_TAC [PRIME_IDEAL_IMP_SUBSET, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN MATCH_MP_TAC IDEAL_PROD_MONO THEN ASM_REWRITE_TAC [SUBSET_REFL]])
    let lemma := p24
    let q25 ← q r"(s:C->bool) SUBSET t ==> t INTER s = s"
    let r26 ← SET_RULE q25
    let q27 ← q r"ideal_generated t (IMAGE (h:B->C) i)"
    let q28 ← q r"Q:C->bool"
    let q29 ← q r"t:C ring"
    let v30 ← ISPECL [q29, q28, q27] IDEAL_VALUATION_EQ_0
    let q31 ← q r"ideal_prod s (ideal_pow s P n) (i:B->bool) = j"
    let v32 ← ASSUME q31
    let v33 ← SYM v32
    let q34 ← q r"~(ideal_generated t (IMAGE (h:B->C) P) = {ring_0 t})"
    let q35 ← q r"~(Q = {ring_0(t:C ring)})"
    let q36 ← q r"~((i:B->bool) SUBSET P)"
    let q37 ← q r"h:B->C"
    let q38 ← q r"t:C ring"
    let q39 ← q r"s:B ring"
    let v40 ← ISPECL [q39, q38, q37] RING_HOMOMORPHISM_IN_CARRIER
    let q41 ← q r"i:B->bool"
    let q42 ← q r"s:B ring"
    let v43 ← ISPECL [q42, q41] RING_IDEAL_IMP_SUBSET
    let q44 ← q r"IMAGE (h:B->C) P SUBSET Q /\ IMAGE h i SUBSET ring_carrier t /\
                ~(IMAGE h i SUBSET Q)"
    let q45 ← q r"P:B->bool"
    let q46 ← q r"h:B->C"
    let q47 ← q r"t:C ring"
    let q48 ← q r"s:B ring"
    let v49 ← ISPECL [q48, q47, q46, q45] IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0
    let q50 ← q r"i:B->bool"
    let q51 ← q r"h:B->C"
    let q52 ← q r"t:C ring"
    let q53 ← q r"s:B ring"
    let v54 ← ISPECL [q53, q52, q51, q50] IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0
    let q55 ← q r"i:B->bool"
    let q56 ← q r"n = ideal_valuation s P (j:B->bool)"
    let q57 ← q r"j:B->bool"
    let q58 ← q r"P:B->bool"
    let q59 ← q r"s:B ring"
    let v60 ← ISPECL [q59, q58, q57] lemma
    let q61 ← q r"t:C ring"
    let q62 ← q r"s:B ring"
    let v63 ← ISPECL [q62, q61] PRIME_IDEAL_HOMOMORPHIC_PREIMAGE
    let q64 ← q r"prime_ideal s (P:B->bool)"
    let q65 ← q r"P = {y | y IN ring_carrier s /\ (h:B->C) y IN Q}"
    prove
      r"!s:B ring t:C ring h Q j.
          dedekind_domain s /\ dedekind_domain t /\ ring_monomorphism(s,t) h /\
          prime_ideal t Q /\
          ~({y | y IN ring_carrier s /\ h y IN Q} = {ring_0 s}) /\
          ring_ideal s j /\ ~(j = {ring_0 s})
          ==> ideal_valuation t Q (ideal_generated t (IMAGE h j)) =
              ramification_index (s,t) h Q *
              ideal_valuation s {y | y IN ring_carrier s /\ h y IN Q} j"
      (REPEAT STRIP_TAC THEN REWRITE_TAC [ramification_index] THEN ABBREV_TAC q65 THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN q64 ASSUME_TAC THENL [EXPAND_TAC "P" THEN MATCH_MP_TAC v63 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC v60 THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC q56 THEN DISCH_THEN (X_CHOOSE_THEN q55 STRIP_ASSUME_TAC) THEN MP_TAC v54 THEN MP_TAC v49 THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN q44 STRIP_ASSUME_TAC THENL [MP_TAC v43 THEN MP_TAC v40 THEN UNDISCH_TAC q36 THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "P" THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q35 ASSUME_TAC THENL [DISCH_TAC THEN UNDISCH_TAC q34 THEN REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_MESON_TAC [RING_IDEAL_0], REWRITE_TAC [SING_SUBSET] THEN MATCH_MP_TAC IN_RING_IDEAL_0 THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED]], ALL_TAC] THEN SUBST1_TAC v33 THEN ASM_SIMP_TAC [IDEAL_PROD_HOMOMORPHIC_IMAGE, IDEAL_POW_HOMOMORPHIC_IMAGE, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW, PRIME_IDEAL_IMP_SUBSET] THEN wPart lhand (lhand o rand) IDEAL_VALUATION_IDEAL_PROD THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_GENERATED, IDEAL_POW_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC v30 THEN ASM_SIMP_TAC [IDEAL_VALUATION_IDEAL_POW, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_MINIMAL_EQ, PRIME_IMP_RING_IDEAL, r26] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [ADD_CLAUSES, MULT_SYM])

  let IDEAL_VALUATION_HOMOMORPHIC_IMAGE_SING ← prove
    r"!r s (g:A->B) Q a.
        dedekind_domain r /\ dedekind_domain s /\ ring_monomorphism(r,s) g /\
        prime_ideal s Q /\
        ~({x | x IN ring_carrier r /\ g x IN Q} = {ring_0 r}) /\
        a IN ring_carrier r /\ ~(a = ring_0 r)
        ==> ideal_valuation s Q (ideal_generated s {g a}) =
            ramification_index (r,s) g Q *
            ideal_valuation r {x | x IN ring_carrier r /\ g x IN Q}
              (ideal_generated r {a})"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"g:A->B"), (← q r"Q:B->bool"), (← q r"ideal_generated r {a:A}")] IDEAL_VALUATION_HOMOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN ASM_SIMP_TAC [IDEAL_GENERATED_EQ_0, IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, RING_MONOMORPHISM_IMP_HOMOMORPHISM, SING_SUBSET] THEN REWRITE_TAC [IMAGE_CLAUSES] THEN ASM_SIMP_TAC [] THEN ASM_MESON_TAC [])

  let DEDEKIND_VALUATION_RAMIFICATION_INDEX ← prove
    r"!r s k l (h:A->B) (f:A->C) (g:B->D) (j:C->D) Q x.
        dedekind_domain r /\ dedekind_domain s /\ ring_monomorphism(r,s) h /\
        field_of_fractions (r,k) f /\
        ring_monomorphism(s,l) g /\ ring_homomorphism(k,l) j /\
        (!a. a IN ring_carrier r ==> j(f a) = g(h a)) /\
        prime_ideal s Q /\
        ~({a | a IN ring_carrier r /\ h a IN Q} = {ring_0 r}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> dedekind_valuation (s,l) g Q (j x) =
            &(ramification_index (r,s) h Q) *
            dedekind_valuation (r,k) f
              {a | a IN ring_carrier r /\ h a IN Q} x"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN ABBREV_TAC (← q r"P = {a | a IN ring_carrier r /\ (h:A->B) a IN Q}") THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"r:A ring"), (← q r"s:B ring")] RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN MP_TAC (← ISPECL [(← q r"f:A->C"), (← q r"r:A ring"), (← q r"k:C ring")] RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN MP_TAC (← ISPECL [(← q r"g:B->D"), (← q r"s:B ring"), (← q r"l:D ring")] RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"prime_ideal r (P:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "P" THEN MATCH_MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring")] PRIME_IDEAL_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(Q = {ring_0(s:B ring)})") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(P = {ring_0(r:A ring)})") THEN REWRITE_TAC [] THEN EXPAND_TAC "P" THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, IN_SING] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B")] RING_MONOMORPHISM_EQ_0) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [RING_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:C ring"), (← q r"f:A->C"), (← q r"x:C")] FIELD_FRACTION_NONZERO) THEN ASM_REWRITE_TAC [field_of_fractions, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:C ring"), (← q r"f:A->C"), (← q r"P:A->bool"), (← q r"x:C"), (← q r"a:A"), (← q r"b:A")] DEDEKIND_VALUATION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"l:D ring"), (← q r"g:B->D"), (← q r"Q:B->bool"), (← q r"(j:C->D) x"), (← q r"(h:A->B) a"), (← q r"(h:A->B) b")] DEDEKIND_VALUATION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0], ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0], FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← MATCH_MP th (← ASSUME (← q r"(a:A) IN ring_carrier r"))))])) THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM (← MATCH_MP th (← ASSUME (← q r"(b:A) IN ring_carrier r"))))])) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z4 ← (q r"(f:A->C) a"); let z3 ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); liftExcept (rand z1)); pure (z3 == z4)))))) THEN MATCH_MP_TAC (← GSYM (← MATCH_MP RING_HOMOMORPHISM_MUL (← ASSUME (← q r"ring_homomorphism(k:C ring,l:D ring) j")))) THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER]], DISCH_THEN SUBST1_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"{a:A}")] IDEAL_GENERATED_IMAGE_IDEAL_GENERATED) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"{b:A}")] IDEAL_GENERATED_IMAGE_IDEAL_GENERATED) THEN ASM_REWRITE_TAC [SING_SUBSET, IMAGE_CLAUSES] THEN REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"Q:B->bool"), (← q r"ideal_generated r {b:A}")] IDEAL_VALUATION_HOMOMORPHIC_IMAGE) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h:A->B"), (← q r"Q:B->bool"), (← q r"ideal_generated r {a:A}")] IDEAL_VALUATION_HOMOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC [(← GSYM INT_OF_NUM_MUL)] THEN INT_ARITH_TAC)

  let DEDEKIND_RAMIFICATION_INDEX_NONZERO ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"1 <= n ==> ~(n = 0)")
    prove
      r"!r s (g:A->B) Q.
          dedekind_domain s /\ ring_monomorphism(r,s) g /\
          prime_ideal s Q /\ ~(Q = {ring_0 s}) /\
          ~({x | x IN ring_carrier r /\ g x IN Q} = {ring_0 r})
          ==> ~(ramification_index (r,s) g Q = 0)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [ramification_index] THEN ABBREV_TAC (← q r"P = {x | x IN ring_carrier r /\ (g:A->B) x IN Q}") THEN ASSUME_TAC (← MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM (← ASSUME (← q r"ring_monomorphism(r,s) (g:A->B)"))) THEN SUBGOAL_THEN (← q r"?p:A. p IN P /\ ~(p = ring_0 r)") STRIP_ASSUME_TAC THENL [SUBGOAL_THEN (← q r"ring_0 r IN (P:A->bool)") MP_TAC THENL [EXPAND_TAC "P" THEN REWRITE_TAC [IN_ELIM_THM, RING_0] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_0, IN_RING_IDEAL_0, PRIME_IMP_RING_IDEAL], UNDISCH_TAC (← q r"~(P = {ring_0 r:A})") THEN SET_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"(g:A->B) p IN ideal_generated s (IMAGE g P) /\ ~(g p = ring_0 s)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"(p:A) IN P") THEN EXPAND_TAC "P" THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"p:A") THEN ASM_REWRITE_TAC [IN_ELIM_THM], ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0]], ALL_TAC] THEN MATCH_MP_TAC r1 THEN wPart Except.ok (rand o rand) DEDEKIND_IDEAL_SUBSET_POW_VALUATION THEN ANTS_TAC THENL [ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN REWRITE_TAC [EXTENSION, IN_SING, NOT_FORALL_THM] THEN EXISTS_TAC (← q r"(g:A->B) p") THEN ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN ASM_SIMP_TAC [IDEAL_POW_1, PRIME_IMP_RING_IDEAL] THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN EXPAND_TAC "P" THEN SET_TAC [])

  let NUMBER_FIELD_VALUATION_RAMIFICATION_INDEX ← prove
    r"!k:A ring l:B ring h Q x.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers l) Q /\ ~(Q = {ring_0 l}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> dedekind_valuation (ring_of_integers l,l) I Q (h x) =
            &(ramification_index (ring_of_integers k,ring_of_integers l) h Q) *
            dedekind_valuation (ring_of_integers k,k) I
             {y | y IN ring_carrier(ring_of_integers k) /\ h y IN Q} x"
    (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"number_field(k:A ring)") ASSUME_TAC THENL [ASM_MESON_TAC [NUMBER_FIELD_HOMOMORPHIC_PREIMAGE], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_monomorphism(k:A ring,l:B ring) h") ASSUME_TAC THENL [MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN ASM_SIMP_TAC [FIELD_IMP_NONTRIVIAL_RING, NUMBER_FIELD_IMP_FIELD], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_monomorphism(ring_of_integers k,k:A ring) I /\
                ring_monomorphism(ring_of_integers l,l:B ring) I") STRIP_ASSUME_TAC THENL [REWRITE_TAC [ring_of_integers, I_DEF, RING_MONOMORPHISM_INCLUSION], ALL_TAC] THEN MATCH_MP_TAC (← REWRITE_RULE [field_of_fractions, I_THM, RING_OF_INTEGERS] (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"I:A->A"), (← q r"I:B->B"), (← q r"h:A->B")] DEDEKIND_VALUATION_RAMIFICATION_INDEX)) THEN ASM_SIMP_TAC [RING_MONOMORPHISM_RING_OF_INTEGERS, DEDEKIND_RING_OF_INTEGERS, NUMBER_FIELD_IMP_FIELD] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"y:A")] RING_OF_INTEGERS_DENOMINATOR) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"Q:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_BELOW) THEN ASM_REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"p:A->bool") STRIP_ASSUME_TAC) o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"Q:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_IDEAL_VALUATION_EXTENSION ← prove
    r"!k:A ring l:B ring h p P j.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P /\
        ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
        ==> ideal_valuation (ring_of_integers l) P
              (ideal_generated (ring_of_integers l) (IMAGE h j)) =
            ramification_index (ring_of_integers k,ring_of_integers l) h P *
            ideal_valuation (ring_of_integers k) p j"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_TOWER_LAW) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (MP_TAC o ((MATCH_MP FINITE_IMP_FIELD_EXTENSION) o CONJUNCT1)) THEN REWRITE_TAC [field_extension] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h:A->B"), (← q r"P:B->bool"), (← q r"j:A->bool")] IDEAL_VALUATION_HOMOMORPHIC_IMAGE) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_MONOMORPHISM_RING_OF_INTEGERS, RING_OF_INTEGERS])

  let RESIDUE_DEGREE_TOWER ← prove
    r"!r:A ring s:B ring t:C ring h1 h2 Q.
        ring_homomorphism(r,s) h1 /\ ring_homomorphism(s,t) h2 /\
        prime_ideal t Q /\ FINITE(ring_carrier(quotient_ring t Q))
        ==> residue_degree (r,t) (h2 o h1) Q =
            residue_degree (s,t) h2 Q *
            residue_degree (r,s) h1
              {y | y IN ring_carrier s /\ h2 y IN Q}"
    (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"P = {y | y IN ring_carrier s /\ (h2:B->C) y IN Q}") THEN SUBGOAL_THEN (← q r"{x | x IN ring_carrier r /\ ((h2:B->C) o (h1:A->B)) x IN Q} =
                {x | x IN ring_carrier r /\ h1 x IN P}") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h1:A->B")] RING_HOMOMORPHISM_IN_CARRIER) THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "P" THEN REWRITE_TAC [o_THM, IN_ELIM_THM, EXTENSION] THEN MESON_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"p = {x | x IN ring_carrier r /\ (h1:A->B) x IN P}") THEN SUBGOAL_THEN (← q r"prime_ideal s (P:B->bool)") ASSUME_TAC THENL [EXPAND_TAC "P" THEN MATCH_MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"t:C ring")] PRIME_IDEAL_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"prime_ideal r (p:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "p" THEN MATCH_MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring")] PRIME_IDEAL_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"FINITE(ring_carrier(quotient_ring s (P:B->bool)))") ASSUME_TAC THENL [EXPAND_TAC "P" THEN MATCH_MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"t:C ring")] FINITE_QUOTIENT_RING_HOMOMORPHIC_PREIMAGE) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"FINITE(ring_carrier(quotient_ring r (p:A->bool)))") ASSUME_TAC THENL [EXPAND_TAC "p" THEN MATCH_MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring")] FINITE_QUOTIENT_RING_HOMOMORPHIC_PREIMAGE) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(r:A ring,t:C ring) ((h2:B->C) o (h1:A->B))") ASSUME_TAC THENL [MATCH_MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"t:C ring")] RING_HOMOMORPHISM_COMPOSE) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool")] PRIME_IDEAL_IMP_PSUBSET) THEN ASM_REWRITE_TAC [PSUBSET] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool")] IDEAL_NORM_GT_1) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h1:A->B"), (← q r"P:B->bool")] IDEAL_NORM_RESIDUE_DEGREE) THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"t:C ring"), (← q r"h2:B->C"), (← q r"Q:C->bool")] IDEAL_NORM_RESIDUE_DEGREE) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"t:C ring"), (← q r"(h2:B->C) o (h1:A->B)"), (← q r"Q:C->bool")] IDEAL_NORM_RESIDUE_DEGREE) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC [EXP_EXP, EQ_EXP] THEN ARITH_TAC)

  let RAMIFICATION_INDEX_TOWER ← prove
    r"!r:A ring s:B ring t:C ring h1 h2 Q.
        ring_monomorphism(r,s) h1 /\ ring_monomorphism(s,t) h2 /\
        dedekind_domain s /\ dedekind_domain t /\ prime_ideal t Q /\
        ~({x | x IN ring_carrier r /\ h2(h1 x) IN Q} = {ring_0 r})
        ==> ramification_index (r,t) (h2 o h1) Q =
            ramification_index (s,t) h2 Q *
            ramification_index (r,s) h1
              {y | y IN ring_carrier s /\ h2 y IN Q}"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"h1:A->B"), (← q r"r:A ring"), (← q r"s:B ring")] RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN MP_TAC (← ISPECL [(← q r"h2:B->C"), (← q r"s:B ring"), (← q r"t:C ring")] RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN ASM_REWRITE_TAC [] THEN REPEAT DISCH_TAC THEN ABBREV_TAC (← q r"P = {y | y IN ring_carrier s /\ (h2:B->C) y IN Q}") THEN SUBGOAL_THEN (← q r"{x | x IN ring_carrier r /\ (h2:B->C) ((h1:A->B) x) IN Q} =
    {x | x IN ring_carrier r /\ h1 x IN P}") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h1:A->B")] RING_HOMOMORPHISM_IN_CARRIER) THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "P" THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN GEN_REWRITE_TAC LAND_CONV [ramification_index] THEN GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ramification_index] THEN REWRITE_TAC [o_THM] THEN FIRST_X_ASSUM (fun th => REWRITE_TAC [th] THEN RULE_ASSUM_TAC (REWRITE_RULE [th])) THEN ABBREV_TAC (← q r"p = {x | x IN ring_carrier r /\ (h1:A->B) x IN P}") THEN SUBGOAL_THEN (← q r"prime_ideal s (P:B->bool)") ASSUME_TAC THENL [EXPAND_TAC "P" THEN MATCH_MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"t:C ring")] PRIME_IDEAL_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal r (p:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "p" THEN MATCH_MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring")] RING_IDEAL_HOMOMORPHIC_PREIMAGE) THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(P = {ring_0(s:B ring)})") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~(p = {ring_0(r:A ring)})") THEN REWRITE_TAC [] THEN EXPAND_TAC "p" THEN GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM, IN_SING] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h1:A->B")] RING_MONOMORPHISM_EQ_0) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [RING_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE (h1:A->B) p SUBSET ring_carrier s") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool")] RING_IDEAL_IMP_SUBSET) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h1:A->B")] RING_HOMOMORPHISM_IN_CARRIER) THEN ASM_REWRITE_TAC [] THEN SET_TAC [], ALL_TAC] THEN REWRITE_TAC [IMAGE_o] THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"t:C ring"), (← q r"h2:B->C"), (← q r"IMAGE (h1:A->B) p")] IDEAL_GENERATED_IMAGE_IDEAL_GENERATED) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"t:C ring"), (← q r"h2:B->C"), (← q r"Q:C->bool"), (← q r"ideal_generated s (IMAGE (h1:A->B) p)")] IDEAL_VALUATION_HOMOMORPHIC_IMAGE) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN ANTS_TAC THENL [ALL_TAC, DISCH_THEN SUBST1_TAC THEN REFL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"h1:A->B"), (← q r"p:A->bool")] IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0) THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_RAMIFICATION_INDEX_TOWER ← prove
    r"!k:A ring l:B ring m:C ring h1 h2 P Q.
        field k /\ field l /\ number_field m /\
        ring_homomorphism(k,l) h1 /\ ring_homomorphism(l,m) h2 /\
        prime_ideal (ring_of_integers l) P /\ ~(P = {ring_0 l}) /\
        prime_ideal (ring_of_integers m) Q /\ IMAGE h2 P SUBSET Q
        ==> ramification_index
              (ring_of_integers k,ring_of_integers m) (h2 o h1) Q =
            ramification_index
              (ring_of_integers l,ring_of_integers m) h2 Q *
            ramification_index
              (ring_of_integers k,ring_of_integers l) h1 P"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"h2:B->C")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"field(m:C ring)") ASSUME_TAC THENL [ASM_SIMP_TAC [NUMBER_FIELD_IMP_FIELD], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"h2:B->C"), (← q r"P:B->bool"), (← q r"Q:C->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"ring_of_integers m:C ring"), (← q r"h1:A->B"), (← q r"h2:B->C"), (← q r"Q:C->bool")] RAMIFICATION_INDEX_TOWER) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_MONOMORPHISM_RING_OF_INTEGERS, FIELD_RING_HOMOMORPHISM_MONOMORPHISM, FIELD_IMP_NONTRIVIAL_RING, NUMBER_FIELD_IMP_FIELD] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h1:A->B"), (← q r"P:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_BELOW) THEN ASM_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"p:A->bool") STRIP_ASSUME_TAC) o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h1:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"{x | x IN ring_carrier(ring_of_integers k) /\
         (h2:B->C) ((h1:A->B) x) IN Q} = p") (fun th => ASM_REWRITE_TAC [th]) THEN FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV [(← SYM th)])) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_eq z2)))))) THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ring_of_integers l:B ring"), (← q r"h1:A->B")] RING_HOMOMORPHISM_IN_CARRIER) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS] THEN MESON_TAC [])

  let NUMBER_FIELD_RESIDUE_DEGREE_TOWER ← prove
    r"!k:A ring l:B ring m:C ring h1 h2 P Q.
        field k /\ field l /\ number_field m /\
        ring_homomorphism(k,l) h1 /\ ring_homomorphism(l,m) h2 /\
        prime_ideal (ring_of_integers l) P /\ ~(P = {ring_0 l}) /\
        prime_ideal (ring_of_integers m) Q /\ IMAGE h2 P SUBSET Q
        ==> residue_degree
              (ring_of_integers k,ring_of_integers m) (h2 o h1) Q =
            residue_degree
              (ring_of_integers l,ring_of_integers m) h2 Q *
            residue_degree
              (ring_of_integers k,ring_of_integers l) h1 P"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"h2:B->C"), (← q r"P:B->bool"), (← q r"Q:C->bool")] RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RESIDUE_DEGREE_TOWER THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_OF_INTEGERS] THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"m:C ring"), (← q r"h2:B->C"), (← q r"P:B->bool")] RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"Q:C->bool")) o ((GEN_REWRITE_RULE id [EXTENSION]) o (CONJUNCT2 o CONJUNCT2)))) THEN ASM_SIMP_TAC [IN_ELIM_THM])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_PRIME_NORM_CARD, IDEAL_VALUATION_HOMOMORPHIC_IMAGE,
           IDEAL_VALUATION_HOMOMORPHIC_IMAGE_SING, DEDEKIND_VALUATION_RAMIFICATION_INDEX,
           DEDEKIND_RAMIFICATION_INDEX_NONZERO,
           NUMBER_FIELD_VALUATION_RAMIFICATION_INDEX,
           NUMBER_FIELD_IDEAL_VALUATION_EXTENSION, RESIDUE_DEGREE_TOWER,
           RAMIFICATION_INDEX_TOWER, NUMBER_FIELD_RAMIFICATION_INDEX_TOWER,
           NUMBER_FIELD_RESIDUE_DEGREE_TOWER }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- relative_split.ml phrases from line 1507 to 2105                       -/
/- ---------------------------------------------------------------------- -/

structure RelativeSplit03 where
  -- @@FIELDS
  DEDEKIND_VALUATION_LIFT_CANCEL : thm
  RAMIFICATION_INDEX_IMAGE_SUBSET : thm
  RAMIFICATION_INDEX_IMAGE_POW_SUBSET : thm
  DEDEKIND_EXTENSION_UNIFORMIZER_CRITERION : thm
  RESIDUE_DEGREE_LIFTED_BASIS : thm
  DEDEKIND_UNIFORMIZER_DIGITS_SPAN : thm
  DEDEKIND_UNIFORMIZER_DIGITS_INDEPENDENT : thm
  DEDEKIND_EXTENSION_DIGITS_LINEAR : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupRelativeSplit03 [HolBase] (D : RelativeSplitDeps) (BRelativeSplit01 : RelativeSplit01) (BRelativeSplit02 : RelativeSplit02) :
    ExceptT String IO RelativeSplit03 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC,
        RING_RULE, RING_TAC, SET_RULE, .. } := D
  let { ADD1, AND_FORALL_THM, CONTRAPOS_THM, DEDEKIND_IDEAL_SUBSET_POW_VALUATION,
        DEDEKIND_IDEAL_SUBSET_VALUATION, DEDEKIND_IMP_INTEGRAL_DOMAIN,
        DEDEKIND_IN_IDEAL_POW_VALUATION, DEDEKIND_UNIFORMIZER_CRITERION, EMPTY_GSPEC,
        EQ_TRANS, EXTENSION, FIELD_QUOTIENT_RING, FINITE_NUMSEG_LT, FORALL_IN_IMAGE,
        FREE_BASIS_EXISTS, FREE_BASIS_IN_CARRIER, IDEAL_GENERATED_EQ_0,
        IDEAL_GENERATED_INC, IDEAL_POW_0, IDEAL_POW_1, IDEAL_POW_ANTIMONO,
        IDEAL_POW_EQ_ZERO, IDEAL_POW_HOMOMORPHIC_IMAGE_SUBSET, IDEAL_POW_MUL,
        IDEAL_POW_PRINCIPAL, IDEAL_POW_SUC_SUBSET, IDEAL_VALUATION_IDEAL_POW,
        IDEAL_VALUATION_PRIME, IDEAL_VALUATION_PRINCIPAL_MUL, IDEAL_VALUATION_SETADD,
        INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_POW_EQ_0, IN_ELIM_THM,
        IN_IDEAL_GENERATED_SING_EQ, IN_IMAGE, IN_INSERT, IN_RING_IDEAL_0,
        IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL, IN_RING_IDEAL_RMUL, IN_RING_IDEAL_SUB,
        IN_RING_IDEAL_SUM, IN_SING, LEFT_IMP_EXISTS_THM, LE_REFL, LT, LT_REFL,
        MAXIMAL_IMP_RING_IDEAL, .. } := D.core1
  let { MIN, MULT_CLAUSES, PRIME_IDEAL_HOMOMORPHIC_PREIMAGE, PRIME_IMP_RING_IDEAL,
        QUOTIENT_RING_0, QUOTIENT_RING_CARRIER, RIGHT_EXISTS_IMP_THM, RING_0,
        RING_ADD_LZERO, RING_COSET_EQ, RING_COSET_EQ_IDEAL, RING_HOMOMORPHISM_0,
        RING_HOMOMORPHISM_ADD, RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_MUL,
        RING_HOMOMORPHISM_RING_COSET, RING_HOMOMORPHISM_SUM_MUL,
        RING_IDEAL_HOMOMORPHIC_PREIMAGE, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET, RING_IDEAL_SETADD,
        RING_MATROID_SPANNING, RING_MONOMORPHISM_EQ_0,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_MUL_IN_IDEAL_POW, RING_POW,
        RING_POW_IN_IDEAL_POW, RING_SUB_RZERO, RING_SUM, RING_SUM_ADD,
        RING_SUM_CLAUSES, RING_SUM_EQ, RING_SUM_LMUL, SKOLEM_THM, SUBSET, SUBSET_TRANS,
        extension_degree, free_basis, matroid_finite_dimensional, ramification_index,
        ring_divides, ring_setadd, .. } := D.core2
  let { RESIDUE_DEGREE_QUOTIENT_RING, .. } := BRelativeSplit01
  let { IDEAL_VALUATION_HOMOMORPHIC_IMAGE_SING, .. } := BRelativeSplit02
  -- @@SCOPE END

  let DEDEKIND_VALUATION_LIFT_CANCEL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!s t z:A. t SUBSET s /\ s = {z} /\ z IN t ==> t = {z}")
    let r2 ← RING_RULE (← q r"ring_sub r (ring_add r y z) y = z:A")
    prove
      r"!r P (x:A) d.
          dedekind_domain r /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\
          x IN ring_carrier r /\ ~(x = ring_0 r) /\
          ideal_valuation r P (ideal_generated r {x}) = d
          ==> (!k a. a IN ideal_pow r P d
                     ==> ?b. b IN ring_carrier r /\
                             ring_sub r a (ring_mul r x b) IN
                             ideal_pow r P (d + k)) /\
              (!k b. b IN ring_carrier r /\
                     ring_mul r x b IN ideal_pow r P (d + k)
                     ==> b IN ideal_pow r P k)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"!m. ring_ideal r (ideal_pow r (P:A->bool) m) /\
          ~(ideal_pow r P m = {ring_0 r})") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, IDEAL_POW_EQ_ZERO], ALL_TAC] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL [ALL_TAC, ASM_CASES_TAC (← q r"b = ring_0 (r:A ring)") THENL [ASM_SIMP_TAC [IN_RING_IDEAL_0], ALL_TAC] THEN UNDISCH_TAC (← q r"ring_mul r x b IN ideal_pow r (P:A->bool) (d + k)") THEN ASM_SIMP_TAC [DEDEKIND_IN_IDEAL_POW_VALUATION, RING_MUL, INTEGRAL_DOMAIN_MUL_EQ_0, IDEAL_VALUATION_PRINCIPAL_MUL] THEN ARITH_TAC] THEN SUBGOAL_THEN (← q r"ideal_pow r P d SUBSET
      ring_setadd r (ideal_generated r {x:A})
                    (ideal_pow r P (d + k))") MP_TAC THENL [ALL_TAC, REWRITE_TAC [SUBSET] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"a:A"))) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [ring_setadd, IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"y:A"), (← q r"z:A")] THEN STRIP_TAC THEN UNDISCH_TAC (← q r"(y:A) IN ideal_generated r {x}") THEN ASM_SIMP_TAC [IN_IDEAL_GENERATED_SING_EQ, ring_divides] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"b:A") STRIP_ASSUME_TAC)) THEN EXISTS_TAC (← q r"b:A") THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [r2, RING_MUL]] THEN SUBGOAL_THEN (← q r"ideal_pow r P (d + k) SUBSET
      ring_setadd r (ideal_generated r {x:A})
                    (ideal_pow r P (d + k))") ASSUME_TAC THENL [REWRITE_TAC [SUBSET, ring_setadd, IN_ELIM_THM] THEN X_GEN_TAC (← q r"z:A") THEN DISCH_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"ring_0 r:A"), (← q r"z:A")] THEN ASM_SIMP_TAC [IN_RING_IDEAL_0, RING_IDEAL_IDEAL_GENERATED] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_ADD_LZERO THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal r (ring_setadd r (ideal_generated r {x:A})
                                 (ideal_pow r P (d + k))) /\
      ~(ring_setadd r (ideal_generated r {x})
                      (ideal_pow r P (d + k)) = {ring_0 r})") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_SETADD, RING_IDEAL_IDEAL_GENERATED] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ideal_pow r P (d + k) = {ring_0 r:A}") MP_TAC THENL [MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"ring_setadd r (ideal_generated r {x:A})
                        (ideal_pow r P (d + k))") THEN ASM_SIMP_TAC [IN_RING_IDEAL_0], ASM_REWRITE_TAC []], ALL_TAC] THEN ASM_SIMP_TAC [DEDEKIND_IDEAL_SUBSET_VALUATION] THEN X_GEN_TAC (← q r"q:A->bool") THEN STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_VALUATION_SETADD, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, IDEAL_VALUATION_IDEAL_POW, IDEAL_VALUATION_PRIME, PRIME_IMP_RING_IDEAL] THEN ASM_CASES_TAC (← q r"P:A->bool = q") THENL [FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC [], ASM_REWRITE_TAC []] THEN REWRITE_TAC [MIN] THEN ARITH_TAC)

  let RAMIFICATION_INDEX_IMAGE_SUBSET ← prove
    r"!r s (g:A->B) Q.
        dedekind_domain s /\ ring_monomorphism(r,s) g /\
        prime_ideal s Q /\ ~(Q = {ring_0 s}) /\
        ~({x | x IN ring_carrier r /\ g x IN Q} = {ring_0 r})
        ==> IMAGE g {x | x IN ring_carrier r /\ g x IN Q} SUBSET
            ideal_pow s Q (ramification_index (r,s) g Q)"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC (← q r"ideal_generated s
               (IMAGE (g:A->B) {x | x IN ring_carrier r /\ g x IN Q})") THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"z:B") THEN DISCH_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ideal_generated s
        (IMAGE (g:A->B) {x | x IN ring_carrier r /\ g x IN Q}) =
      {ring_0 s})") ASSUME_TAC THENL [UNDISCH_TAC (← q r"~({x | x IN ring_carrier r /\ (g:A->B) x IN Q} = {ring_0 r})") THEN REWRITE_TAC [CONTRAPOS_THM] THEN DISCH_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_SING] THEN X_GEN_TAC (← q r"x:A") THEN EQ_TAC THENL [STRIP_TAC THEN SUBGOAL_THEN (← q r"(g:A->B) x IN
        ideal_generated s (IMAGE g {x | x IN ring_carrier r /\ g x IN Q})") MP_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_INC THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, IN_IMAGE] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_MONOMORPHISM_IMP_HOMOMORPHISM], EXISTS_TAC (← q r"x:A") THEN ASM_REWRITE_TAC []], ASM_REWRITE_TAC [IN_SING] THEN ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0]], DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC [RING_0, RING_HOMOMORPHISM_0, IN_RING_IDEAL_0, RING_MONOMORPHISM_IMP_HOMOMORPHISM, PRIME_IMP_RING_IDEAL]], ALL_TAC] THEN ASM_SIMP_TAC [DEDEKIND_IDEAL_SUBSET_POW_VALUATION, RING_IDEAL_IDEAL_GENERATED] THEN REWRITE_TAC [ramification_index, LE_REFL])

  let RAMIFICATION_INDEX_IMAGE_POW_SUBSET ← prove
    r"!r s (g:A->B) Q n.
        dedekind_domain s /\ ring_monomorphism(r,s) g /\
        prime_ideal s Q /\ ~(Q = {ring_0 s}) /\
        ~({x | x IN ring_carrier r /\ g x IN Q} = {ring_0 r})
        ==> IMAGE g (ideal_pow r {x | x IN ring_carrier r /\ g x IN Q} n)
            SUBSET ideal_pow s Q (ramification_index (r,s) g Q * n)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN ASM_SIMP_TAC [IDEAL_POW_MUL, RING_IDEAL_IMP_SUBSET] THEN MATCH_MP_TAC IDEAL_POW_HOMOMORPHIC_IMAGE_SUBSET THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, RAMIFICATION_INDEX_IMAGE_SUBSET] THEN MATCH_MP_TAC RING_IDEAL_HOMOMORPHIC_PREIMAGE THEN EXISTS_TAC (← q r"s:B ring") THEN ASM_REWRITE_TAC [])

  let DEDEKIND_EXTENSION_UNIFORMIZER_CRITERION ← prove
    r"!r s (g:A->B) Q P e p.
        dedekind_domain r /\ dedekind_domain s /\ ring_monomorphism(r,s) g /\
        prime_ideal s Q /\ ~(Q = {ring_0 s}) /\
        P = {x | x IN ring_carrier r /\ g x IN Q} /\ ~(P = {ring_0 r}) /\
        e = ramification_index (r,s) g Q /\
        p IN P /\ ~(p IN ideal_pow r P 2)
        ==> (!n k y. y IN ideal_pow s Q (e * n)
                     ==> ?b. b IN ring_carrier s /\
                             ring_sub s y (ring_mul s (g(ring_pow r p n)) b) IN
                             ideal_pow s Q (e * n + k)) /\
            (!n k b. b IN ring_carrier s /\
                     ring_mul s (g(ring_pow r p n)) b IN
                     ideal_pow s Q (e * n + k)
                     ==> b IN ideal_pow s Q k)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT (FIRST_X_ASSUM (MP_TAC o (SYM o (checkM (fun z1 => (do let z2 ← (do let z3 ← (do let z4 ← (pure z1); pure (concl z4)); liftExcept (lhs z3)); pure (is_var z2))))))) THEN REPEAT DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"prime_ideal r (P:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "P" THEN MATCH_MP_TAC PRIME_IDEAL_HOMOMORPHIC_PREIMAGE THEN EXISTS_TAC (← q r"s:B ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"(p:A) IN ring_carrier r /\ ~(p = ring_0 r)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET, IN_RING_IDEAL_0, RING_IDEAL_IDEAL_POW], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_valuation r P (ideal_generated r {p:A}) = 1") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"p:A"), (← q r"2:num")] DEDEKIND_IN_IDEAL_POW_VALUATION) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"p:A"), (← q r"1:num")] DEDEKIND_IN_IDEAL_POW_VALUATION) THEN ASM_SIMP_TAC [IDEAL_POW_1] THEN ARITH_TAC, ALL_TAC] THEN GEN_REWRITE_TAC id [AND_FORALL_THM] THEN X_GEN_TAC (← q r"n:num") THEN SUBGOAL_THEN (← q r"ring_pow r (p:A) n IN ring_carrier r /\ ~(ring_pow r p n = ring_0 r) /\
    ideal_valuation r P (ideal_generated r {ring_pow r p n}) = n") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_POW, INTEGRAL_DOMAIN_POW_EQ_0, DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN ASM_SIMP_TAC [(← GSYM IDEAL_POW_PRINCIPAL), IDEAL_VALUATION_IDEAL_POW, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0] THEN REWRITE_TAC [MULT_CLAUSES], ALL_TAC] THEN MATCH_MP_TAC DEDEKIND_VALUATION_LIFT_CANCEL THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0], MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"g:A->B"), (← q r"Q:B->bool"), (← q r"ring_pow r (p:A) n")] IDEAL_VALUATION_HOMOMORPHIC_IMAGE_SING) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []])

  let RESIDUE_DEGREE_LIFTED_BASIS ← prove
    r"!r s (g:A->B) Q P f.
        ring_homomorphism(r,s) g /\ maximal_ideal s Q /\
        P = {x | x IN ring_carrier r /\ g x IN Q} /\ maximal_ideal r P /\
        f = residue_degree (r,s) g Q /\ ~(f = 0)
        ==> ?w. (!i. i < f ==> w i IN ring_carrier s) /\
                (!y. y IN ring_carrier s
                     ==> ?a. (!i. a i IN ring_carrier r) /\
                             ring_sub s y
                              (ring_sum s {i | i < f}
                                (\i. ring_mul s (g(a i)) (w i))) IN Q) /\
                (!a. (!i. a i IN ring_carrier r) /\
                     ring_sum s {i | i < f}
                      (\i. ring_mul s (g(a i)) (w i)) IN Q
                     ==> !i. i < f ==> a i IN P)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT (FIRST_X_ASSUM (MP_TAC o (SYM o (checkM (fun z24 => (do let z25 ← (do let z26 ← (do let z27 ← (pure z24); pure (concl z27)); liftExcept (lhs z26)); pure (is_var z25))))))) THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_ideal r (P:A->bool) /\ ring_ideal s (Q:B->bool)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [MAXIMAL_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"field(quotient_ring r (P:A->bool)) /\ field(quotient_ring s (Q:B->bool))") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_QUOTIENT_RING], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"g:A->B"), (← q r"Q:B->bool")] RESIDUE_DEGREE_QUOTIENT_RING) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"gb:(A->bool)->(B->bool)") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN SUBGOAL_THEN (← q r"ring_homomorphism(quotient_ring r P,quotient_ring s Q)
                     (gb:(A->bool)->(B->bool))") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_MONOMORPHISM_IMP_HOMOMORPHISM], ALL_TAC] THEN SUBGOAL_THEN (← q r"?W. free_basis (quotient_ring r P,quotient_ring s Q)
                   (gb:(A->bool)->(B->bool)) f (W:num->B->bool)") STRIP_ASSUME_TAC THENL [REWRITE_TAC [(← GSYM (← ASSUME (← q r"extension_degree
      (quotient_ring r P,quotient_ring s Q) (gb:(A->bool)->(B->bool)) = f")))] THEN MATCH_MP_TAC FREE_BASIS_EXISTS THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"~(f = 0)") THEN REWRITE_TAC [(← GSYM (← ASSUME (← q r"extension_degree
      (quotient_ring r P,quotient_ring s Q) (gb:(A->bool)->(B->bool)) = f")))] THEN REWRITE_TAC [extension_degree] THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN POP_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [matroid_finite_dimensional])) THEN ASM_SIMP_TAC [RING_MATROID_SPANNING] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"?w. !i. i < f ==> (w:num->B) i IN ring_carrier s /\
                      (W:num->B->bool) i = ring_coset s Q (w i)") (X_CHOOSE_THEN (← q r"w:num->B") (LABEL_TAC "w")) THENL [REWRITE_TAC [(← GSYM SKOLEM_THM), RIGHT_EXISTS_IMP_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"i:num")) o (MATCH_MP FREE_BASIS_IN_CARRIER))) THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!a. (!i. (a:num->A) i IN ring_carrier r)
        ==> ring_sum (quotient_ring s Q) {i | i < f}
             (\i. ring_mul (quotient_ring s Q)
                   ((gb:(A->bool)->(B->bool)) (ring_coset r P (a i)))
                   ((W:num->B->bool) i)) =
            ring_coset s Q (ring_sum s {i | i < f}
                             (\i. ring_mul s ((g:A->B)(a i)) (w i)))") (LABEL_TAC "sum") THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"quotient_ring s (Q:B->bool)"), (← q r"ring_coset s (Q:B->bool)"), (← q r"{i:num | i < f}"), (← q r"\i. (g:A->B)((a:num->A) i)"), (← q r"w:num->B")] RING_HOMOMORPHISM_SUM_MUL) THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_RING_COSET, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN ANTS_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [], ALL_TAC] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [free_basis])) THEN EXISTS_TAC (← q r"w:num->B") THEN REPEAT CONJ_TAC THENL [ASM_SIMP_TAC [], X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"ring_coset s Q (y:B)")) o (checkM (fun th => (do if ← (do if ← (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); pure (is_forall z15)) then (do let z17 ← (do pure (Prod.snd (← (do let z18 ← (do let z19 ← (pure th); pure (concl z19)); liftExcept (dest_forall z18))))); pure (is_imp z17)) else pure false) then (do let z20 ← (do let z21 ← (do pure (Prod.snd (← (do let z22 ← (do let z23 ← (pure th); pure (concl z23)); liftExcept (dest_forall z22))))); liftExcept (rand z21)); pure (is_exists z20)) else pure false))))) THEN ANTS_TAC THENL [MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"Q:B->bool")] RING_HOMOMORPHISM_RING_COSET) THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->A->bool") STRIP_ASSUME_TAC)] THEN SUBGOAL_THEN (← q r"?a. !i. (a:num->A) i IN ring_carrier r /\
              (i < f ==> (c:num->A->bool) i = ring_coset r P (a i))") (X_CHOOSE_TAC (← q r"a:num->A")) THENL [REWRITE_TAC [(← GSYM SKOLEM_THM)] THEN X_GEN_TAC (← q r"i:num") THEN ASM_CASES_TAC (← q r"(i:num) < f") THENL [SUBGOAL_THEN (← q r"(c:num->A->bool) i IN ring_carrier(quotient_ring r P)") MP_TAC THENL [FIRST_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do if ← (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); pure (is_forall z10)) then (do let z13 ← (do let z14 ← (pure th); pure (concl z14)); let z12 ← (q r"c:num->A->bool"); pure (free_in z12 z13)) else pure false)))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SIMP_TAC [QUOTIENT_RING_CARRIER, (← ASSUME (← q r"ring_ideal r (P:A->bool)")), IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN MESON_TAC [], EXISTS_TAC (← q r"ring_0 r:A") THEN ASM_REWRITE_TAC [RING_0]], ALL_TAC] THEN EXISTS_TAC (← q r"a:num->A") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"Q:B->bool"), (← q r"y:B"), (← q r"ring_sum s {i | i < f}
                     (\i. ring_mul s ((g:A->B)((a:num->A) i)) (w i))")] RING_COSET_EQ) THEN ASM_REWRITE_TAC [RING_SUM] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN USE_THEN "sum" (MP_TAC o (SPEC (← q r"a:num->A"))) THEN ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN ASM_SIMP_TAC [], X_GEN_TAC (← q r"a:num->A") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"\i. ring_coset r P ((a:num->A) i)")) o (checkM (fun th => (do if ← (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_forall z1)) then (do let z3 ← (do pure (Prod.snd (← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (dest_forall z4))))); pure (is_imp z3)) else pure false) then (do let z6 ← (do let z7 ← (do pure (Prod.snd (← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); liftExcept (dest_forall z8))))); liftExcept (rand z7)); pure (is_forall z6)) else pure false))))) THEN USE_THEN "sum" (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP th (← ASSUME (← q r"!i. (a:num->A) i IN ring_carrier r")))])) THEN ASM_SIMP_TAC [QUOTIENT_RING_0, RING_COSET_EQ_IDEAL, RING_SUM] THEN ANTS_TAC THENL [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool")] RING_HOMOMORPHISM_RING_COSET) THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ASM_SIMP_TAC []]])

  let DEDEKIND_UNIFORMIZER_DIGITS_SPAN ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r4 ← ARITH_RULE (← q r"j < m ==> ~(j = m:num)")
    prove
      r"!r s (g:A->B) Q t f (w:num->B).
          dedekind_domain s /\ prime_ideal s Q /\ ~(Q = {ring_0 s}) /\
          t IN Q /\ ~(t IN ideal_pow s Q 2) /\
          (!y. y IN ring_carrier s
               ==> ?a. (!i. a i IN ring_carrier r) /\
                       ring_sub s y
                        (ring_sum s {i | i < f} (\i. ring_mul s (g(a i)) (w i)))
                       IN Q)
          ==> !m y. y IN ring_carrier s
                    ==> ?a. (!i j. a i j IN ring_carrier r) /\
                            ring_sub s y
                             (ring_sum s {j | j < m}
                               (\j. ring_mul s (ring_pow s t j)
                                     (ring_sum s {i | i < f}
                                       (\i. ring_mul s (g(a i j)) (w i)))))
                            IN ideal_pow s Q m"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN POP_ASSUM (LABEL_TAC "span") THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"(t:B) IN ring_carrier s") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"Q:B->bool"), (← q r"t:B")] DEDEKIND_UNIFORMIZER_CRITERION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN ((LABEL_TAC "tlift") o CONJUNCT1) THEN INDUCT_TAC THENL [REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"\i:num j:num. ring_0 r:A") THEN REWRITE_TAC [RING_0, IDEAL_POW_0, LT, EMPTY_GSPEC, RING_SUM_CLAUSES] THEN ASM_SIMP_TAC [RING_SUB_RZERO], POP_ASSUM (LABEL_TAC "ih")] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN REMOVE_THEN "ih" (MP_TAC o ((← do let c := (← ASSUME (← q r"(y:B) IN ring_carrier s")); pure (fun th => MATCH_MP th c)) o (SPEC (← q r"y:B")))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:num->num->A") STRIP_ASSUME_TAC) THEN ABBREV_TAC (← q r"sm = ring_sum s {j:num | j < m}
            (\j. ring_mul s (ring_pow s t j)
                  (ring_sum s {i:num | i < f}
                    (\i. ring_mul s ((g:A->B)((a:num->num->A) i j))
                                    (w i))))") THEN USE_THEN "tlift" (MP_TAC o ((← do let c := (← ASSUME (← q r"ring_sub s (y:B) sm IN ideal_pow s Q m")); pure (fun th => MATCH_MP th c)) o (SPECL [(← q r"m:num"), (← q r"1:num"), (← q r"ring_sub s (y:B) sm")]))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"b:B") STRIP_ASSUME_TAC) THEN USE_THEN "span" (MP_TAC o ((← do let c := (← ASSUME (← q r"(b:B) IN ring_carrier s")); pure (fun th => MATCH_MP th c)) o (SPEC (← q r"b:B")))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->A") STRIP_ASSUME_TAC) THEN ABBREV_TAC (← q r"tc = ring_sum s {i:num | i < f}
            (\i. ring_mul s ((g:A->B)((c:num->A) i)) (w i))") THEN SUBGOAL_THEN (← q r"(sm:B) IN ring_carrier s /\ (tc:B) IN ring_carrier s") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["sm", "tc"] THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN EXISTS_TAC (← q r"\i j:num. if j = m then (c:num->A) i
                          else (a:num->num->A) i j") THEN CONJ_TAC THENL [REPEAT GEN_TAC THEN REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"{j:num | j < SUC m} = m INSERT {j | j < m}") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_INSERT, IN_ELIM_THM] THEN ARITH_TAC, ALL_TAC] THEN ASM_SIMP_TAC [RING_SUM_CLAUSES, FINITE_NUMSEG_LT, IN_ELIM_THM, LT_REFL, RING_MUL, RING_POW, RING_SUM] THEN SUBGOAL_THEN (← q r"ring_sum s {j:num | j < m}
       (\j. ring_mul s (ring_pow s t j)
             (ring_sum s {i:num | i < f}
               (\i. ring_mul s ((g:A->B)
                      (if j = m then (c:num->A) i
                       else (a:num->num->A) i j)) (w i)))) = sm") SUBST1_TAC THENL [EXPAND_TAC "sm" THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN ASM_SIMP_TAC [r4], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_sub s (y:B) (ring_add s (ring_mul s (ring_pow s t m) tc) sm) =
      ring_add s (ring_sub s (ring_sub s y sm) (ring_mul s (ring_pow s t m) b))
                 (ring_mul s (ring_pow s (t:B) m) (ring_sub s (b:B) tc))") SUBST1_TAC THENL [SUBGOAL_THEN (← q r"(y:B) IN ring_carrier s /\ (b:B) IN ring_carrier s /\
        ring_pow s (t:B) m IN ring_carrier s /\ (sm:B) IN ring_carrier s /\
        (tc:B) IN ring_carrier s") MP_TAC THENL [ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN REPEAT (FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_eq z2)))))) THEN REPEAT STRIP_TAC THEN RING_TAC, ALL_TAC] THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW, ADD1] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, RING_POW_IN_IDEAL_POW, IDEAL_POW_1])

  let DEDEKIND_UNIFORMIZER_DIGITS_INDEPENDENT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r4 ← SET_RULE (← q r"!s t x:B. s SUBSET t /\ x IN s ==> x IN t")
    let r8 ← ARITH_RULE (← q r"SUC n <= m ==> n <= m")
    let r9 ← SET_RULE (← q r"!s t x:B. s SUBSET t /\ x IN s ==> x IN t")
    prove
      r"!r s (g:A->B) Q P t f (w:num->B) m.
          dedekind_domain s /\ prime_ideal s Q /\ ~(Q = {ring_0 s}) /\
          t IN Q /\ ~(t IN ideal_pow s Q 2) /\
          (!i. i < f ==> w i IN ring_carrier s) /\
          (!a. (!i. a i IN ring_carrier r) /\
               ring_sum s {i | i < f} (\i. ring_mul s (g(a i)) (w i)) IN Q
               ==> !i. i < f ==> a i IN P) /\
          IMAGE g P SUBSET ideal_pow s Q m
          ==> !a. (!i j. a i j IN ring_carrier r) /\
                  ring_sum s {j | j < m}
                   (\j. ring_mul s (ring_pow s t j)
                         (ring_sum s {i | i < f}
                           (\i. ring_mul s (g(a i j)) (w i))))
                  IN ideal_pow s Q m
                  ==> !i j. i < f /\ j < m ==> a i j IN P"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM ((LABEL_TAC "image") o (checkM (fun z25 => (do let z27 ← (do let z28 ← (pure z25); pure (concl z28)); let z26 ← (pure "SUBSET"); pure (is_binary z26 z27))))) THEN FIRST_X_ASSUM ((LABEL_TAC "indep") o (checkM (fun z22 => (do let z23 ← (do let z24 ← (pure z22); pure (concl z24)); pure (is_forall z23))))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"(t:B) IN ring_carrier s") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"Q:B->bool"), (← q r"t:B")] DEDEKIND_UNIFORMIZER_CRITERION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN ((LABEL_TAC "tcancel") o CONJUNCT2) THEN SUBGOAL_THEN (← q r"!(a:num->num->A) j.
          (!i. i < f ==> a i j IN P)
          ==> ring_sum s {i:num | i < f}
               (\i. ring_mul s ((g:A->B)(a i j)) (w i)) IN
              ideal_pow s Q m") (LABEL_TAC "sin") THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW, IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW] THEN USE_THEN "image" (MATCH_MP_TAC o (REWRITE_RULE [SUBSET, FORALL_IN_IMAGE])) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!n. n <= m
          ==> !a. (!i j. (a:num->num->A) i j IN ring_carrier r) /\
                  ring_sum s {j:num | j < n}
                   (\j. ring_mul s (ring_pow s t j)
                         (ring_sum s {i:num | i < f}
                           (\i. ring_mul s ((g:A->B)(a i j)) (w i))))
                  IN ideal_pow s Q n
                  ==> !i j. i < f /\ j < n ==> a i j IN P") (fun th => MESON_TAC [th, LE_REFL]) THEN INDUCT_TAC THENL [REWRITE_TAC [LT], ALL_TAC] THEN DISCH_TAC THEN X_GEN_TAC (← q r"a:num->num->A") THEN STRIP_TAC THEN ABBREV_TAC (← q r"sm = ring_sum s {j:num | j < n}
            (\j. ring_mul s (ring_pow s t j)
                  (ring_sum s {i:num | i < f}
                    (\i. ring_mul s ((g:A->B)((a:num->num->A) i j))
                                    (w i))))") THEN ABBREV_TAC (← q r"tm = ring_sum s {i:num | i < f}
            (\i. ring_mul s ((g:A->B)((a:num->num->A) i n)) (w i))") THEN SUBGOAL_THEN (← q r"(sm:B) IN ring_carrier s /\ (tm:B) IN ring_carrier s") STRIP_ASSUME_TAC THENL [MAP_EVERY EXPAND_TAC ["sm", "tm"] THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_add s (ring_mul s (ring_pow s t n) tm) sm IN
      ideal_pow s (Q:B->bool) (SUC n)") ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (tryCatch (do if ← (do let z18 ← (pure "ideal_pow"); let z17 ← (do pure (Prod.fst (← (do let z13 ← (do pure (Prod.fst (← (do let z14 ← (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); liftExcept (rand z15)); pure (strip_comb z14))))); liftExcept (dest_const z13))))); pure (z17 == z18)) then (do let z19 ← (do let z20 ← (do let z21 ← (pure th); pure (concl z21)); liftExcept (lhand z20)); pure (is_comb z19)) else pure false) (fun _ => (pure false)))))) THEN SUBGOAL_THEN (← q r"{j:num | j < SUC n} = n INSERT {j | j < n}") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_INSERT, IN_ELIM_THM] THEN ARITH_TAC, ALL_TAC] THEN ASM_SIMP_TAC [RING_SUM_CLAUSES, FINITE_NUMSEG_LT, IN_ELIM_THM, LT_REFL, RING_MUL, RING_POW, RING_SUM], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul s (ring_pow s t n) (tm:B) IN ideal_pow s (Q:B->bool) n") ASSUME_TAC THENL [MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, RING_POW_IN_IDEAL_POW], ALL_TAC] THEN SUBGOAL_THEN (← q r"(sm:B) IN ideal_pow s Q n") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"sm = ring_sub s (ring_add s (ring_mul s (ring_pow s t n) tm) sm)
                        (ring_mul s (ring_pow s (t:B) n) tm)") SUBST1_TAC THENL [SUBGOAL_THEN (← q r"ring_pow s (t:B) n IN ring_carrier s") MP_TAC THENL [ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN REPEAT (FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun z10 => (do let z11 ← (do let z12 ← (pure z10); pure (concl z12)); pure (is_eq z11)))))) THEN REPEAT STRIP_TAC THEN RING_TAC, ALL_TAC] THEN MATCH_MP_TAC IN_RING_IDEAL_SUB THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN MATCH_MP_TAC r9 THEN EXISTS_TAC (← q r"ideal_pow s (Q:B->bool) (SUC n)") THEN ASM_SIMP_TAC [IDEAL_POW_SUC_SUBSET], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"a:num->num->A")) o ((← do let c := (← MP r8 (← ASSUME (← q r"SUC n <= m"))); pure (fun th => MATCH_MP th c)) o (checkM (fun z5 => (do let z6 ← (do let z7 ← (pure z5); pure (concl z7)); pure (is_imp z6))))))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(sm:B) IN ideal_pow s Q (SUC n)") ASSUME_TAC THENL [EXPAND_TAC "sm" THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW, IN_ELIM_THM] THEN X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, RING_POW] THEN MATCH_MP_TAC r4 THEN EXISTS_TAC (← q r"ideal_pow s (Q:B->bool) m") THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_POW_ANTIMONO THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], USE_THEN "sin" MATCH_MP_TAC THEN ASM_SIMP_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul s (ring_pow s t n) (tm:B) IN ideal_pow s (Q:B->bool) (SUC n)") MP_TAC THENL [SUBGOAL_THEN (← q r"ring_mul s (ring_pow s t n) tm =
        ring_sub s (ring_add s (ring_mul s (ring_pow s (t:B) n) tm) sm)
                   (sm:B)") SUBST1_TAC THENL [SUBGOAL_THEN (← q r"ring_pow s (t:B) n IN ring_carrier s") MP_TAC THENL [ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN REPEAT (FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_eq z2)))))) THEN REPEAT STRIP_TAC THEN RING_TAC, ALL_TAC] THEN MATCH_MP_TAC IN_RING_IDEAL_SUB THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW], ALL_TAC] THEN REWRITE_TAC [ADD1] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(tm:B) IN ideal_pow s Q 1") MP_TAC THENL [USE_THEN "tcancel" MATCH_MP_TAC THEN EXISTS_TAC (← q r"n:num") THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [IDEAL_POW_1] THEN DISCH_TAC] THEN REMOVE_THEN "indep" (MP_TAC o (BETA_RULE o (SPEC (← q r"\i. (a:num->num->A) i n")))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"j = n:num") THEN ASM_SIMP_TAC [] THEN SUBGOAL_THEN (← q r"j < n:num") (fun th => ASM_SIMP_TAC [th]) THEN ASM_ARITH_TAC)

  let DEDEKIND_EXTENSION_DIGITS_LINEAR ← prove
    r"!r s (g:A->B) e (f:num) t (w:num->B) E.
        ring_homomorphism(r,s) g /\ t IN ring_carrier s /\
        (!i. i < f ==> w i IN ring_carrier s) /\
        (!a. E a = ring_sum s {j | j < e}
                    (\j. ring_mul s (ring_pow s t j)
                          (ring_sum s {i | i < f}
                            (\i. ring_mul s (g(a i j)) (w i)))))
        ==> !a c u. (!i j. a i j IN ring_carrier r) /\
                    (!i j. c i j IN ring_carrier r) /\ u IN ring_carrier r
                    ==> E (\i j. ring_add r (a i j) (ring_mul r u (c i j))) =
                        ring_add s (E a) (ring_mul s (g u) (E c))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"a:num->num->A"), (← q r"c:num->num->A"), (← q r"u:A")] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"!x. x IN ring_carrier r ==> (g:A->B) x IN ring_carrier s") ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"!k (x:num->B) y z.
        FINITE k /\ (!j. j IN k ==> x j IN ring_carrier s /\
                                    y j IN ring_carrier s) /\
        z IN ring_carrier s
        ==> ring_sum s k (\j. ring_add s (x j) (ring_mul s z (y j))) =
            ring_add s (ring_sum s k x) (ring_mul s z (ring_sum s k y))") (LABEL_TAC "slin") THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"x:num->B"), (← q r"\j:num. ring_mul s z ((y:num->B) j)"), (← q r"k:num->bool")] RING_SUM_ADD) THEN ASM_SIMP_TAC [RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_SUM_LMUL THEN ASM_SIMP_TAC [], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"ring_sum s {j | j < e}
     (\j. ring_add s
           (ring_mul s (ring_pow s t j)
             (ring_sum s {i | i < f}
               (\i. ring_mul s ((g:A->B)((a:num->num->A) i j)) (w i))))
           (ring_mul s (g u)
             (ring_mul s (ring_pow s t j)
               (ring_sum s {i | i < f}
                 (\i. ring_mul s (g((c:num->num->A) i j)) (w i))))))") THEN CONJ_TAC THENL [ALL_TAC, USE_THEN "slin" MATCH_MP_TAC THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, RING_MUL, RING_POW, RING_SUM]] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"j:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN TRANS_TAC EQ_TRANS (← q r"ring_mul s (ring_pow s t j)
     (ring_add s
       (ring_sum s {i | i < f}
         (\i. ring_mul s ((g:A->B)((a:num->num->A) i j)) (w i)))
       (ring_mul s (g u)
         (ring_sum s {i | i < f}
           (\i. ring_mul s (g((c:num->num->A) i j)) (w i)))))") THEN CONJ_TAC THENL [AP_TERM_TAC THEN TRANS_TAC EQ_TRANS (← q r"ring_sum s {i | i < f}
       (\i. ring_add s (ring_mul s ((g:A->B)((a:num->num->A) i j)) (w i))
                       (ring_mul s (g u)
                         (ring_mul s (g((c:num->num->A) i j)) (w i))))") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_MUL, (← MATCH_MP RING_HOMOMORPHISM_ADD (← ASSUME (← q r"ring_homomorphism(r,s) (g:A->B)"))), (← MATCH_MP RING_HOMOMORPHISM_MUL (← ASSUME (← q r"ring_homomorphism(r,s) (g:A->B)")))] THEN SUBGOAL_THEN (← q r"(g:A->B)((a:num->num->A) i j) IN ring_carrier s /\
        g u IN ring_carrier s /\ g((c:num->num->A) i j) IN ring_carrier s /\
        (w:num->B) i IN ring_carrier s") MP_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN REPEAT (FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun z4 => (do let z5 ← (do let z6 ← (pure z4); pure (concl z6)); pure (is_eq z5)))))) THEN RING_TAC, USE_THEN "slin" MATCH_MP_TAC THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, RING_MUL, IN_ELIM_THM]], SUBGOAL_THEN (← q r"ring_pow s (t:B) j IN ring_carrier s /\ (g:A->B) u IN ring_carrier s") MP_TAC THENL [ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"{i:num | i < f}"), (← q r"\i. ring_mul s ((g:A->B)((a:num->num->A) i j)) (w i)")] RING_SUM) THEN MP_TAC (← ISPECL [(← q r"s:B ring"), (← q r"{i:num | i < f}"), (← q r"\i. ring_mul s ((g:A->B)((c:num->num->A) i j)) (w i)")] RING_SUM) THEN REPEAT (FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun z1 => (do let z2 ← (do let z3 ← (pure z1); pure (concl z3)); pure (is_eq z2)))))) THEN SPEC_TAC ((← q r"ring_sum s {i:num | i < f}
               (\i. ring_mul s ((g:A->B)((a:num->num->A) i j)) (w i))"), (← q r"x1:B")) THEN SPEC_TAC ((← q r"ring_sum s {i:num | i < f}
               (\i. ring_mul s ((g:A->B)((c:num->num->A) i j)) (w i))"), (← q r"x2:B")) THEN RING_TAC])

  -- @@RETURN BEGIN
  return { DEDEKIND_VALUATION_LIFT_CANCEL, RAMIFICATION_INDEX_IMAGE_SUBSET,
           RAMIFICATION_INDEX_IMAGE_POW_SUBSET, DEDEKIND_EXTENSION_UNIFORMIZER_CRITERION,
           RESIDUE_DEGREE_LIFTED_BASIS, DEDEKIND_UNIFORMIZER_DIGITS_SPAN,
           DEDEKIND_UNIFORMIZER_DIGITS_INDEPENDENT, DEDEKIND_EXTENSION_DIGITS_LINEAR }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- relative_split.ml phrases from line 2203 to 2790                       -/
/- ---------------------------------------------------------------------- -/

structure RelativeSplit04 where
  -- @@FIELDS
  DEDEKIND_EXTENSION_DIGITS_IN_IDEAL_POW : thm
  DEDEKIND_EXTENSION_DIGITS_SPAN : thm
  DEDEKIND_EXTENSION_DIGITS_INDEPENDENT : thm
  DEDEKIND_EXTENSION_DIGITS : thm
  RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER : thm
  RING_OF_INTEGERS_RATIONAL_FIELD : thm
  RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL : thm
  RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL : thm
  RAMIFICATION_INDEX_PRIME_SUBFIELD : thm
  RESIDUE_DEGREE_PRIME_SUBFIELD : thm
  NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q : thm
  NUMBER_FIELD_RESIDUE_DEGREE_TOWER_Q : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupRelativeSplit04 [HolBase] (D : RelativeSplitDeps) (BRelativeSplit01 : RelativeSplit01) (BRelativeSplit02 : RelativeSplit02) (BRelativeSplit03 : RelativeSplit03) :
    ExceptT String IO RelativeSplit04 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, RING_TAC,
        SET_RULE, SET_TAC, .. } := D
  let { ADD1, CONJ_ASSOC, DEDEKIND_UNIFORMIZER_CRITERION, DIVIDES_ZERO, EQ_TRANS,
        ETA_AX, EXISTS_UNIQUE_THM, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_REAL_RING,
        FIELD_SUBFIELD_GENERATED, FORALL_IN_GSPEC, FORALL_IN_IMAGE, FUN_EQ_THM,
        IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, IDEAL_GENERATED_MINIMAL,
        IDEAL_GENERATED_MINIMAL_EQ, IDEAL_GENERATED_SUBSET, IDEAL_POW_0, IDEAL_POW_1,
        IDEAL_POW_ANTIMONO, IMAGE_CLAUSES, IMAGE_I, IMAGE_o, INTEGER_RING,
        INTEGRAL_DOMAIN_CHAR, INTEGRAL_ELEMENT_SUBRING_GENERATED, IN_ELIM_THM,
        IN_IDEAL_GENERATED_SING, IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL,
        IN_RING_IDEAL_RMUL, IN_RING_IDEAL_SUB, IN_RING_IDEAL_SUM, IN_UNIV, I_O_ID,
        I_THM, LE_MULT_LCANCEL, .. } := D.core1
  let { MEMBER_NOT_EMPTY, MONO_EXISTS, MULT_CLAUSES, NUMBER_FIELD_IMP_FIELD,
        NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q, NUMBER_FIELD_PRIME_SUBFIELD,
        PRIME_IDEAL_HOMOMORPHIC_PREIMAGE, PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_NZ,
        PRIME_IMP_RING_IDEAL, PRIME_SUBFIELD_EQ_SUBRING, REAL_RING_CLAUSES,
        REAL_RING_OF_INT, RING_0, RING_ADD, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        RING_HOMOMORPHISM_IN_CARRIER, RING_HOMOMORPHISM_RING_OF_INT,
        RING_HOMOMORPHISM_RING_OF_INTEGERS, RING_HOMOMORPHISM_SUBFIELD_INCLUSION,
        RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_MUL_IN_IDEAL_POW,
        RING_OF_INT, RING_OF_INTEGERS, RING_OF_INTEGERS_CARRIER,
        RING_OF_INTEGERS_PRIME_IDEAL_ABOVE, RING_OF_INTEGERS_PRIME_SUBFIELD,
        RING_OF_INTEGERS_SUBSET, RING_OF_INT_IN_PRIME_IDEAL,
        RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_IN_SUBFIELD_GENERATED,
        RING_OF_INT_MUL, RING_OF_INT_OF_NUM, RING_OF_INT_SUBFIELD_GENERATED,
        RING_OF_NUM, RING_OF_NUM_EQ_0, RING_OF_NUM_SUBFIELD_GENERATED, RING_POW,
        RING_POW_IN_IDEAL_POW, RING_SUB, RING_SUM, SIMPLE_IMAGE, SING_SUBSET,
        SKOLEM_THM, SUBFIELD_GENERATED, SUBRING_GENERATED_BY_SUBFIELD_GENERATED,
        SUBRING_SUBFIELD_GENERATED, SUBSET, SUBSET_ANTISYM, SUBSET_REFL, SUBSET_TRANS,
        int_divides, int_tybij, number_field, o_THM, ramification_index,
        residue_degree, ring_divides, ring_homomorphism, .. } := D.core2
  let { NUMBER_FIELD_HOMOMORPHIC_PREIMAGE, .. } := BRelativeSplit01
  let { NUMBER_FIELD_RAMIFICATION_INDEX_TOWER, NUMBER_FIELD_RESIDUE_DEGREE_TOWER, .. } := BRelativeSplit02
  let { DEDEKIND_EXTENSION_DIGITS_LINEAR, DEDEKIND_EXTENSION_UNIFORMIZER_CRITERION,
        DEDEKIND_UNIFORMIZER_DIGITS_INDEPENDENT, DEDEKIND_UNIFORMIZER_DIGITS_SPAN,
        RAMIFICATION_INDEX_IMAGE_POW_SUBSET, RAMIFICATION_INDEX_IMAGE_SUBSET, .. } := BRelativeSplit03
  -- @@SCOPE END

  let DEDEKIND_EXTENSION_DIGITS_IN_IDEAL_POW ← prove
    r"!r s (g:A->B) Q P e (f:num) t (w:num->B) E.
        dedekind_domain s /\ ring_monomorphism(r,s) g /\
        prime_ideal s Q /\ ~(Q = {ring_0 s}) /\
        P = {x | x IN ring_carrier r /\ g x IN Q} /\ ~(P = {ring_0 r}) /\
        e = ramification_index (r,s) g Q /\
        t IN ring_carrier s /\ (!i. i < f ==> w i IN ring_carrier s) /\
        (!a. E a = ring_sum s {j | j < e}
                    (\j. ring_mul s (ring_pow s t j)
                          (ring_sum s {i | i < f}
                            (\i. ring_mul s (g(a i j)) (w i)))))
        ==> !n a. (!i j. i < f /\ j < e ==> a i j IN ideal_pow r P n)
                  ==> E a IN ideal_pow s Q (e * n)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT (FIRST_X_ASSUM (MP_TAC o (SYM o (checkM (fun z1 => (do let z2 ← (do let z3 ← (do let z4 ← (pure z1); pure (concl z4)); liftExcept (lhs z3)); pure (is_var z2))))))) THEN REPEAT DISCH_TAC THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"a:num->num->A")] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"g:A->B"), (← q r"Q:B->bool"), (← q r"n:num")] RAMIFICATION_INDEX_IMAGE_POW_SUBSET) THEN ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW, IN_ELIM_THM] THEN X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, RING_POW] THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW, IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW])

  let DEDEKIND_EXTENSION_DIGITS_SPAN ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"e * SUC n = e * n + e:num")
    let r5 ← SET_RULE (← q r"x IN s ==> IMAGE (g:A->B) s SUBSET t ==> g x IN t")
    prove
      r"!r s (g:A->B) Q P e (f:num) t p (w:num->B) E.
          dedekind_domain r /\ dedekind_domain s /\ ring_monomorphism(r,s) g /\
          prime_ideal s Q /\ ~(Q = {ring_0 s}) /\
          P = {x | x IN ring_carrier r /\ g x IN Q} /\ ~(P = {ring_0 r}) /\
          e = ramification_index (r,s) g Q /\
          t IN Q /\ ~(t IN ideal_pow s Q 2) /\
          p IN P /\ ~(p IN ideal_pow r P 2) /\
          (!i. i < f ==> w i IN ring_carrier s) /\
          (!y. y IN ring_carrier s
               ==> ?a. (!i. a i IN ring_carrier r) /\
                       ring_sub s y
                        (ring_sum s {i | i < f} (\i. ring_mul s (g(a i)) (w i)))
                       IN Q) /\
          (!a. E a = ring_sum s {j | j < e}
                      (\j. ring_mul s (ring_pow s t j)
                            (ring_sum s {i | i < f}
                              (\i. ring_mul s (g(a i j)) (w i)))))
          ==> !n y. y IN ring_carrier s
                    ==> ?a. (!i j. a i j IN ring_carrier r) /\
                            ring_sub s y (E a) IN ideal_pow s Q (e * n)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT (FIRST_X_ASSUM (MP_TAC o (SYM o (checkM (fun z6 => (do let z7 ← (do let z8 ← (do let z9 ← (pure z6); pure (concl z9)); liftExcept (lhs z8)); pure (is_var z7))))))) THEN REPEAT DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"prime_ideal r (P:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "P" THEN MATCH_MP_TAC PRIME_IDEAL_HOMOMORPHIC_PREIMAGE THEN EXISTS_TAC (← q r"s:B ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal r (P:A->bool) /\ ring_ideal s (Q:B->bool)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"(p:A) IN ring_carrier r /\ (t:B) IN ring_carrier s") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"g:A->B"), (← q r"Q:B->bool"), (← q r"P:A->bool"), (← q r"e:num"), (← q r"p:A")] DEDEKIND_EXTENSION_UNIFORMIZER_CRITERION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN ((LABEL_TAC "plift") o CONJUNCT1) THEN SUBGOAL_THEN (← q r"!n. (g:A->B)(ring_pow r p n) IN ideal_pow s Q (e * n)") ASSUME_TAC THENL [GEN_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"g:A->B"), (← q r"Q:B->bool"), (← q r"n:num")] RAMIFICATION_INDEX_IMAGE_POW_SUBSET) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r5 THEN ASM_SIMP_TAC [RING_POW_IN_IDEAL_POW], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"g:A->B"), (← q r"e:num"), (← q r"f:num"), (← q r"t:B"), (← q r"w:num->B"), (← q r"E:(num->num->A)->B")] DEDEKIND_EXTENSION_DIGITS_LINEAR) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (LABEL_TAC "lin")] THEN SUBGOAL_THEN (← q r"!y. y IN ring_carrier s
          ==> ?a. (!i j. (a:num->num->A) i j IN ring_carrier r) /\
                  ring_sub s y ((E:(num->num->A)->B) a) IN
                  ideal_pow s (Q:B->bool) e") (LABEL_TAC "a0") THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"g:A->B"), (← q r"Q:B->bool"), (← q r"t:B"), (← q r"f:num"), (← q r"w:num->B")] DEDEKIND_UNIFORMIZER_DIGITS_SPAN) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (ACCEPT_TAC o (SPEC (← q r"e:num")))], ALL_TAC] THEN INDUCT_TAC THENL [REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"\i:num j:num. ring_0 r:A") THEN ASM_REWRITE_TAC [RING_0, MULT_CLAUSES, IDEAL_POW_0] THEN ASM_SIMP_TAC [RING_SUB, RING_SUM], POP_ASSUM (LABEL_TAC "ih")] THEN X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN REMOVE_THEN "ih" (MP_TAC o ((← do let c := (← ASSUME (← q r"(y:B) IN ring_carrier s")); pure (fun th => MATCH_MP th c)) o (SPEC (← q r"y:B")))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:num->num->A") STRIP_ASSUME_TAC) THEN USE_THEN "plift" (MP_TAC o ((← do let c := (← ASSUME (← q r"ring_sub s (y:B) ((E:(num->num->A)->B) a) IN             ideal_pow s Q (e * n)")); pure (fun th => MATCH_MP th c)) o (SPECL [(← q r"n:num"), (← q r"e:num"), (← q r"ring_sub s (y:B) ((E:(num->num->A)->B) a)")]))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"b:B") STRIP_ASSUME_TAC) THEN USE_THEN "a0" (MP_TAC o ((← do let c := (← ASSUME (← q r"(b:B) IN ring_carrier s")); pure (fun th => MATCH_MP th c)) o (SPEC (← q r"b:B")))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->num->A") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"\i j. ring_add r ((a:num->num->A) i j)
                      (ring_mul r (ring_pow r p n) ((c:num->num->A) i j))") THEN CONJ_TAC THENL [REPEAT GEN_TAC THEN REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_ADD, RING_MUL, RING_POW], ALL_TAC] THEN USE_THEN "lin" (MP_TAC o (SPECL [(← q r"a:num->num->A"), (← q r"c:num->num->A"), (← q r"ring_pow r (p:A) n")])) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_POW], DISCH_THEN SUBST1_TAC] THEN SUBGOAL_THEN (← q r"ring_sub s y (ring_add s ((E:(num->num->A)->B) a)
                    (ring_mul s ((g:A->B)(ring_pow r p n)) (E c))) =
      ring_add s (ring_sub s (ring_sub s y (E a))
                             (ring_mul s (g(ring_pow r p n)) b))
                 (ring_mul s (g(ring_pow r p n)) (ring_sub s (b:B) (E c)))") SUBST1_TAC THENL [SUBGOAL_THEN (← q r"(E:(num->num->A)->B) a IN ring_carrier s /\ E c IN ring_carrier s") MP_TAC THENL [ASM_REWRITE_TAC [RING_SUM], ALL_TAC] THEN SUBGOAL_THEN (← q r"(g:A->B)(ring_pow r p n) IN ring_carrier s") MP_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_POW], ALL_TAC] THEN REPEAT (FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun z2 => (do let z3 ← (do let z4 ← (pure z2); pure (concl z4)); pure (is_eq z3)))))) THEN REPEAT STRIP_TAC THEN RING_TAC, ALL_TAC] THEN REWRITE_TAC [r1] THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET]])

  let DEDEKIND_EXTENSION_DIGITS_INDEPENDENT ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"SUC n = n + 1")
    let r8 ← ARITH_RULE (← q r"e * n + e = e * SUC n:num")
    let r9 ← ARITH_RULE (← q r"e * SUC n = e * n + e:num")
    let r29 ← SET_RULE (← q r"!s t x:B. s SUBSET t /\ x IN s ==> x IN t")
    prove
      r"!r s (g:A->B) Q P e (f:num) t p (w:num->B) E.
          dedekind_domain r /\ dedekind_domain s /\ ring_monomorphism(r,s) g /\
          prime_ideal s Q /\ ~(Q = {ring_0 s}) /\
          P = {x | x IN ring_carrier r /\ g x IN Q} /\ ~(P = {ring_0 r}) /\
          e = ramification_index (r,s) g Q /\
          t IN Q /\ ~(t IN ideal_pow s Q 2) /\
          p IN P /\ ~(p IN ideal_pow r P 2) /\
          (!i. i < f ==> w i IN ring_carrier s) /\
          (!a. (!i. a i IN ring_carrier r) /\
               ring_sum s {i | i < f} (\i. ring_mul s (g(a i)) (w i)) IN Q
               ==> !i. i < f ==> a i IN P) /\
          (!a. E a = ring_sum s {j | j < e}
                      (\j. ring_mul s (ring_pow s t j)
                            (ring_sum s {i | i < f}
                              (\i. ring_mul s (g(a i j)) (w i)))))
          ==> !n a. (!i j. a i j IN ring_carrier r) /\
                    E a IN ideal_pow s Q (e * n)
                    ==> !i j. i < f /\ j < e ==> a i j IN ideal_pow r P n"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT (FIRST_X_ASSUM (MP_TAC o (SYM o (checkM (fun z30 => (do let z31 ← (do let z32 ← (do let z33 ← (pure z30); pure (concl z33)); liftExcept (lhs z32)); pure (is_var z31))))))) THEN REPEAT DISCH_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"prime_ideal r (P:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "P" THEN MATCH_MP_TAC PRIME_IDEAL_HOMOMORPHIC_PREIMAGE THEN EXISTS_TAC (← q r"s:B ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal r (P:A->bool) /\ ring_ideal s (Q:B->bool)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"(p:A) IN ring_carrier r /\ (t:B) IN ring_carrier s") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"p:A")] DEDEKIND_UNIFORMIZER_CRITERION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN ((LABEL_TAC "plift") o CONJUNCT1) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"g:A->B"), (← q r"Q:B->bool"), (← q r"P:A->bool"), (← q r"e:num"), (← q r"p:A")] DEDEKIND_EXTENSION_UNIFORMIZER_CRITERION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN ((LABEL_TAC "lc") o CONJUNCT2) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"g:A->B"), (← q r"e:num"), (← q r"f:num"), (← q r"t:B"), (← q r"w:num->B"), (← q r"E:(num->num->A)->B")] DEDEKIND_EXTENSION_DIGITS_LINEAR) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (LABEL_TAC "lin")] THEN SUBGOAL_THEN (← q r"!a. (!i j. (a:num->num->A) i j IN ring_carrier r) /\
          (E:(num->num->A)->B) a IN ideal_pow s (Q:B->bool) e
          ==> !i j. i < f /\ j < e ==> a i j IN P") (LABEL_TAC "a1") THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"g:A->B"), (← q r"Q:B->bool"), (← q r"P:A->bool"), (← q r"t:B"), (← q r"f:num"), (← q r"w:num->B"), (← q r"e:num")] DEDEKIND_UNIFORMIZER_DIGITS_INDEPENDENT) THEN ANTS_TAC THENL [ALL_TAC, DISCH_THEN ACCEPT_TAC] THEN ASM_REWRITE_TAC [] THEN MAP_EVERY EXPAND_TAC ["P", "e"] THEN MATCH_MP_TAC RAMIFICATION_INDEX_IMAGE_SUBSET THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"g:A->B"), (← q r"Q:B->bool"), (← q r"P:A->bool"), (← q r"e:num"), (← q r"f:num"), (← q r"t:B"), (← q r"w:num->B"), (← q r"E:(num->num->A)->B")] DEDEKIND_EXTENSION_DIGITS_IN_IDEAL_POW) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (LABEL_TAC "ein")] THEN INDUCT_TAC THENL [REWRITE_TAC [IDEAL_POW_0] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [], POP_ASSUM (LABEL_TAC "ih")] THEN X_GEN_TAC (← q r"a:num->num->A") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!i j. i < f /\ j < e ==> (a:num->num->A) i j IN ideal_pow r P n") (LABEL_TAC "an") THENL [USE_THEN "ih" MATCH_MP_TAC THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN MATCH_MP_TAC r29 THEN EXISTS_TAC (← q r"ideal_pow s (Q:B->bool) (e * SUC n)") THEN CONJ_TAC THENL [ALL_TAC, FIRST_ASSUM ACCEPT_TAC] THEN MATCH_MP_TAC IDEAL_POW_ANTIMONO THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, LE_MULT_LCANCEL] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"?b. !i j. (b:num->num->A) i j IN ring_carrier r /\
                (i < f /\ j < e
                 ==> ring_sub r ((a:num->num->A) i j)
                      (ring_mul r (ring_pow r p n) (b i j))
                     IN ideal_pow r P (n + 1))") (X_CHOOSE_THEN (← q r"b:num->num->A") (LABEL_TAC "b")) THENL [REWRITE_TAC [(← GSYM SKOLEM_THM)] THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [(← GSYM SKOLEM_THM)] THEN X_GEN_TAC (← q r"j:num") THEN ASM_CASES_TAC (← q r"(i:num) < f /\ (j:num) < e") THENL [USE_THEN "an" (fun an => tactic_of do pure (USE_THEN "plift" (fun pl => tactic_of do pure (MP_TAC (← MATCH_MP (← SPECL [(← q r"n:num"), (← q r"1:num"), (← q r"(a:num->num->A) i j")] pl) (← MATCH_MP (← SPECL [(← q r"i:num"), (← q r"j:num")] an) (← ASSUME (← q r"(i:num) < f /\ (j:num) < e")))))))) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"b0:A") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"b0:A") THEN ASM_REWRITE_TAC [], EXISTS_TAC (← q r"ring_0 r:A") THEN ASM_REWRITE_TAC [RING_0]], ALL_TAC] THEN ABBREV_TAC (← q r"c = \i j. ring_sub r ((a:num->num->A) i j)
                 (ring_mul r (ring_pow r p n) ((b:num->num->A) i j))") THEN SUBGOAL_THEN (← q r"(!i j. (c:num->num->A) i j IN ring_carrier r) /\
      (!i j. i < f /\ j < e ==> c i j IN ideal_pow r P (SUC n)) /\
      (a:num->num->A) =
      (\i j. ring_add r (c i j) (ring_mul r (ring_pow r p n) (b i j)))") STRIP_ASSUME_TAC THENL [EXPAND_TAC "c" THEN REWRITE_TAC [ADD1] THEN ASM_SIMP_TAC [RING_SUB, RING_MUL, RING_POW] THEN REWRITE_TAC [FUN_EQ_THM] THEN REPEAT GEN_TAC THEN SUBGOAL_THEN (← q r"(a:num->num->A) x x' IN ring_carrier r /\
        ring_mul r (ring_pow r p n) ((b:num->num->A) x x') IN ring_carrier r") MP_TAC THENL [ASM_SIMP_TAC [RING_MUL, RING_POW], ALL_TAC] THEN REPEAT (FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun z26 => (do let z27 ← (do let z28 ← (pure z26); pure (concl z28)); pure (is_eq z27)))))) THEN REPEAT STRIP_TAC THEN RING_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"(E:(num->num->A)->B) a =
      ring_add s (E c) (ring_mul s ((g:A->B)(ring_pow r p n)) (E b))") ASSUME_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [(← (do let z19 ← (pure th); checkM (fun th => (do if ← (do let z20 ← (do let z21 ← (pure th); pure (concl z21)); pure (is_eq z20)) then (do let z25 ← (q r"a:num->num->A"); let z24 ← (do let z22 ← (do let z23 ← (pure th); pure (concl z23)); liftExcept (lhs z22)); pure (z24 == z25)) else pure false)) z19))])) THEN USE_THEN "lin" MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN SUBGOAL_THEN (← q r"(E:(num->num->A)->B) b IN ideal_pow s Q e") ASSUME_TAC THENL [USE_THEN "lc" (MATCH_MP_TAC o (SPECL [(← q r"n:num"), (← q r"e:num")])) THEN CONJ_TAC THENL [ASM_REWRITE_TAC [RING_SUM], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul s ((g:A->B)(ring_pow r p n)) ((E:(num->num->A)->B) b) =
        ring_sub s (E a) (E c)") SUBST1_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z13 ← (do let z14 ← (pure th); pure (concl z14)); pure (is_eq z13)) then (do let z18 ← (q r"(E:(num->num->A)->B) a"); let z17 ← (do let z15 ← (do let z16 ← (pure th); pure (concl z16)); liftExcept (lhs z15)); pure (z17 == z18)) else pure false)))) THEN SUBGOAL_THEN (← q r"(E:(num->num->A)->B) b IN ring_carrier s /\ E c IN ring_carrier s") MP_TAC THENL [ASM_REWRITE_TAC [RING_SUM], ALL_TAC] THEN SUBGOAL_THEN (← q r"(g:A->B)(ring_pow r p n) IN ring_carrier s") MP_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_POW], ALL_TAC] THEN REPEAT (FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun z10 => (do let z11 ← (do let z12 ← (pure z10); pure (concl z12)); pure (is_eq z11)))))) THEN REPEAT STRIP_TAC THEN RING_TAC, ALL_TAC] THEN MATCH_MP_TAC IN_RING_IDEAL_SUB THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"(E:(num->num->A)->B) a IN ideal_pow s (Q:B->bool) (e * SUC n)") THEN REWRITE_TAC [r9], ONCE_REWRITE_TAC [r8] THEN USE_THEN "ein" MATCH_MP_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i j. i < f /\ j < e ==> (b:num->num->A) i j IN P") ASSUME_TAC THENL [USE_THEN "a1" MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN USE_THEN "b" (fun th => REWRITE_TAC [th]), ALL_TAC] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_eq z2)) then (do let z7 ← (q r"a:num->num->A"); let z6 ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (lhs z4)); pure (z6 == z7)) else pure false)))) THEN REWRITE_TAC [] THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW] THEN ONCE_REWRITE_TAC [r1] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, RING_POW_IN_IDEAL_POW, IDEAL_POW_1])

  let DEDEKIND_EXTENSION_DIGITS ← prove
    r"!r s (g:A->B) Q P e (f:num) t p (w:num->B) E.
        dedekind_domain r /\ dedekind_domain s /\ ring_monomorphism(r,s) g /\
        prime_ideal s Q /\ ~(Q = {ring_0 s}) /\
        P = {x | x IN ring_carrier r /\ g x IN Q} /\ ~(P = {ring_0 r}) /\
        e = ramification_index (r,s) g Q /\
        t IN Q /\ ~(t IN ideal_pow s Q 2) /\
        p IN P /\ ~(p IN ideal_pow r P 2) /\
        (!i. i < f ==> w i IN ring_carrier s) /\
        (!y. y IN ring_carrier s
             ==> ?a. (!i. a i IN ring_carrier r) /\
                     ring_sub s y
                      (ring_sum s {i | i < f} (\i. ring_mul s (g(a i)) (w i)))
                     IN Q) /\
        (!a. (!i. a i IN ring_carrier r) /\
             ring_sum s {i | i < f} (\i. ring_mul s (g(a i)) (w i)) IN Q
             ==> !i. i < f ==> a i IN P) /\
        (!a. E a = ring_sum s {j | j < e}
                    (\j. ring_mul s (ring_pow s t j)
                          (ring_sum s {i | i < f}
                            (\i. ring_mul s (g(a i j)) (w i)))))
        ==> (!n y. y IN ring_carrier s
                   ==> ?a. (!i j. a i j IN ring_carrier r) /\
                           ring_sub s y (E a) IN ideal_pow s Q (e * n)) /\
            (!n a. (!i j. a i j IN ring_carrier r) /\
                   E a IN ideal_pow s Q (e * n)
                   ==> !i j. i < f /\ j < e ==> a i j IN ideal_pow r P n)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"g:A->B"), (← q r"Q:B->bool"), (← q r"P:A->bool"), (← q r"e:num"), (← q r"f:num"), (← q r"t:B"), (← q r"p:A"), (← q r"w:num->B"), (← q r"E:(num->num->A)->B")] DEDEKIND_EXTENSION_DIGITS_SPAN), MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:B ring"), (← q r"g:A->B"), (← q r"Q:B->bool"), (← q r"P:A->bool"), (← q r"e:num"), (← q r"f:num"), (← q r"t:B"), (← q r"p:A"), (← q r"w:num->B"), (← q r"E:(num->num->A)->B")] DEDEKIND_EXTENSION_DIGITS_INDEPENDENT)] THEN (ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN ACCEPT_TAC]))

  let RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER ← prove
    r"!k:A ring.
        field k
        ==> ring_carrier(ring_of_integers(subfield_generated k {ring_0 k})) =
            {ring_of_int k n | n IN (:int)}"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [SUBSET, FORALL_IN_GSPEC, IN_UNIV] THEN MESON_TAC [RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_SUBFIELD_GENERATED]] THEN FIRST_ASSUM (DISJ_CASES_TAC o ((MATCH_MP INTEGRAL_DOMAIN_CHAR) o (MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN))) THENL [ALL_TAC, TRANS_TAC SUBSET_TRANS (← q r"ring_carrier(subfield_generated k {ring_0 k:A})") THEN ASM_SIMP_TAC [RING_OF_INTEGERS_SUBSET, PRIME_SUBFIELD_EQ_SUBRING, SUBSET_REFL]] THEN MP_TAC (← ISPEC (← q r"k:A ring") RING_OF_INTEGERS_PRIME_SUBFIELD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [RING_OF_INTEGERS_CARRIER, RING_OF_INT_SUBFIELD_GENERATED] THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [(← GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED)] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"ring_of_int k:int->A"), (← q r"ring_carrier(subfield_generated k {ring_0 k:A})")] INTEGRAL_ELEMENT_SUBRING_GENERATED) THEN REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT, SUBRING_SUBFIELD_GENERATED, SUBSET, FORALL_IN_IMAGE, RING_OF_INT_IN_SUBFIELD_GENERATED] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN SET_TAC [])

  let RING_OF_INTEGERS_RATIONAL_FIELD ← prove
    r"!x. x IN ring_carrier
             (ring_of_integers(subfield_generated real_ring {&0})) <=>
       integer x"
    (MP_TAC (← ISPEC (← q r"real_ring") RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER) THEN REWRITE_TAC [FIELD_REAL_RING, REAL_RING_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [REAL_RING_OF_INT, IN_ELIM_THM, IN_UNIV] THEN MESON_TAC [int_tybij])

  let RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"m:int"
    let q2 ← q r"(x:A) IN P"
    let q3 ← q r"k:A ring"
    let v4 ← ISPEC q3 RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER
    let q5 ← q r"?n. x = ring_of_int k n:A"
    let q6 ← q r"x:A"
    let q7 ← q r"p:num"
    let q8 ← q r"P:A->bool"
    let q9 ← q r"O:A ring"
    let v10 ← ISPECL [q9, q8, q7] RING_OF_INT_IN_PRIME_IDEAL
    let q11 ← q r"ring_of_int (O:A ring) = ring_of_int k /\
                  ring_of_num O = ring_of_num k /\ ring_mul O = ring_mul k"
    let q12 ← q r"O = ring_of_integers(subfield_generated k {ring_0 k:A})"
    let p13 ← prove r"!k:A ring P p.
        field k /\
        prime_ideal (ring_of_integers(subfield_generated k {ring_0 k})) P /\
        prime p /\ ring_of_num k p IN P
        ==> P = ideal_generated
                  (ring_of_integers(subfield_generated k {ring_0 k}))
                  {ring_of_num k p}" (REPEAT STRIP_TAC THEN ABBREV_TAC q12 THEN SUBGOAL_THEN q11 STRIP_ASSUME_TAC THENL [EXPAND_TAC "O" THEN REWRITE_TAC [RING_OF_INTEGERS, RING_OF_INT_SUBFIELD_GENERATED, RING_OF_NUM_SUBFIELD_GENERATED, SUBFIELD_GENERATED], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_SIMP_TAC [SING_SUBSET, PRIME_IMP_RING_IDEAL]] THEN MP_TAC v10 THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN REWRITE_TAC [SUBSET] THEN X_GEN_TAC q6 THEN DISCH_TAC THEN SUBGOAL_THEN q5 STRIP_ASSUME_TAC THENL [MP_TAC v4 THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP PRIME_IDEAL_IMP_SUBSET)) THEN ASM SET_TAC [], ALL_TAC] THEN UNDISCH_TAC q2 THEN ASM_REWRITE_TAC [int_divides] THEN DISCH_THEN (X_CHOOSE_THEN q1 SUBST1_TAC) THEN MATCH_MP_TAC IN_IDEAL_GENERATED_SING THEN REWRITE_TAC [ring_divides, RING_OF_INT_MUL, RING_OF_INT_OF_NUM] THEN ASM_MESON_TAC [RING_OF_INT, RING_OF_NUM, RING_MUL])
    let lemma := p13
    let q14 ← q r"ring_of_num k p:A"
    let q15 ← q r"!x:A. x IN s /\ ~(x = a) ==> ~(s = {a})"
    let r16 ← SET_RULE q15
    let q17 ← q r"p:num"
    let q18 ← q r"Q:A->bool"
    let q19 ← q r"k:A ring"
    let v20 ← ISPECL [q19, q18, q17] lemma
    let q21 ← q r"Q:A->bool"
    let v22 ← GSYM MEMBER_NOT_EMPTY
    let q23 ← q r"p:num"
    let q24 ← q r"subfield_generated k {ring_0 k:A}"
    let v25 ← ISPECL [q24, q23] NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q
    let q26 ← q r"p:num"
    let q27 ← q r"P:A->bool"
    let q28 ← q r"subfield_generated k {ring_0 k:A}"
    let v29 ← ISPECL [q28, q27] RING_OF_INTEGERS_PRIME_IDEAL_ABOVE
    let q30 ← q r"k:A ring"
    let v31 ← ISPEC q30 NUMBER_FIELD_PRIME_SUBFIELD
    prove
      r"!k:A ring P.
          field k /\ ring_char k = 0
          ==> (prime_ideal (ring_of_integers(subfield_generated k {ring_0 k}))
                           P /\
               ~(P = {ring_0 k}) <=>
               ?p. prime p /\
                   P = ideal_generated
                         (ring_of_integers(subfield_generated k {ring_0 k}))
                         {ring_of_num k p})"
      (REPEAT STRIP_TAC THEN MP_TAC v31 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN EQ_TAC THENL [STRIP_TAC THEN MP_TAC v29 THEN ASM_REWRITE_TAC [SUBFIELD_GENERATED, RING_OF_NUM_SUBFIELD_GENERATED, EXISTS_UNIQUE_THM] THEN DISCH_THEN (MP_TAC o CONJUNCT1) THEN MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC [lemma], DISCH_THEN (X_CHOOSE_THEN q26 STRIP_ASSUME_TAC)] THEN MP_TAC v25 THEN ASM_REWRITE_TAC [RING_OF_NUM_SUBFIELD_GENERATED, v22, IN_ELIM_THM] THEN DISCH_THEN ((X_CHOOSE_THEN q21 STRIP_ASSUME_TAC) o (CONJUNCT1 o CONJUNCT2)) THEN MP_TAC v20 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC r16 THEN EXISTS_TAC q14 THEN ASM_SIMP_TAC [RING_OF_NUM_EQ_0, DIVIDES_ZERO, PRIME_IMP_NZ])

  let RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(t:A->bool) SUBSET s ==> (t SUBSET q <=> s INTER t SUBSET q)")
    prove
      r"!(k:A ring) p.
          number_field k /\ prime p
          ==> prime_ideal (ring_of_integers(subfield_generated k {ring_0 k}))
                (ideal_generated
                   (ring_of_integers(subfield_generated k {ring_0 k}))
                   {ring_of_num k p}) /\
              ~(ideal_generated
                  (ring_of_integers(subfield_generated k {ring_0 k}))
                  {ring_of_num k p} = {ring_0 k}) /\
              (!P. ring_ideal (ring_of_integers k) P
                   ==> (IMAGE I
                         (ideal_generated
                           (ring_of_integers(subfield_generated k {ring_0 k}))
                           {ring_of_num k p}) SUBSET P <=>
                        ring_of_num k p IN P))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN ABBREV_TAC (← q r"q = ring_of_integers(subfield_generated k {ring_0 k:A})") THEN SUBGOAL_THEN (← q r"ring_homomorphism(q,ring_of_integers k) (I:A->A) /\
      ring_of_num k p IN ring_carrier q") STRIP_ASSUME_TAC THENL [EXPAND_TAC "q" THEN REWRITE_TAC [(← REWRITE_RULE [RING_OF_INTEGERS, RING_OF_NUM_SUBFIELD_GENERATED] (← ISPEC (← q r"ring_of_integers(subfield_generated k {ring_0 k:A})") RING_OF_NUM))] THEN MATCH_MP_TAC RING_HOMOMORPHISM_RING_OF_INTEGERS THEN REWRITE_TAC [RING_HOMOMORPHISM_SUBFIELD_INCLUSION], ALL_TAC] THEN REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"ideal_generated q {ring_of_num k p:A}")] RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_MESON_TAC [number_field], ALL_TAC] THEN DISCH_THEN (fun z2 => tactic_of do pure (MP_TAC (← (do pure (Prod.snd (← (do pure (← EQ_IMP_RULE z2)))))))) THEN ANTS_TAC THENL [EXISTS_TAC (← q r"p:num") THEN ASM_REWRITE_TAC [], SIMP_TAC []], ALL_TAC] THEN X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN TRANS_TAC EQ_TRANS (← q r"ideal_generated (ring_of_integers k)
        (IMAGE (I:A->A) (ideal_generated q {ring_of_num k p})) SUBSET P") THEN CONJ_TAC THENL [ASM_SIMP_TAC [IDEAL_GENERATED_MINIMAL_EQ] THEN MATCH_MP_TAC r1 THEN MP_TAC (← CONJUNCT1 (← REWRITE_RULE [ring_homomorphism] (← ASSUME (← q r"ring_homomorphism(q,ring_of_integers k) (I:A->A)")))) THEN REWRITE_TAC [IMAGE_I] THEN MESON_TAC [IDEAL_GENERATED_SUBSET, SUBSET_TRANS], ASM_SIMP_TAC [IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, SING_SUBSET] THEN ASM_SIMP_TAC [IDEAL_GENERATED_MINIMAL_EQ, IMAGE_CLAUSES, I_THM] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"p:num")] RING_OF_NUM) THEN REWRITE_TAC [RING_OF_INTEGERS] THEN SET_TAC []])

  let RAMIFICATION_INDEX_PRIME_SUBFIELD ← prove
    r"!k:A ring P.
        field k /\ ring_ideal (ring_of_integers k) P
        ==> ramification_index
              (ring_of_integers(subfield_generated k {ring_0 k}),
               ring_of_integers k) I P =
            ramification_index (integer_ring,ring_of_integers k)
              (ring_of_int k) P"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [ramification_index, RING_OF_INTEGERS, INTEGER_RING, RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER, IMAGE_I, I_THM] THEN REPEAT AP_TERM_TAC THEN SET_TAC [])

  let RESIDUE_DEGREE_PRIME_SUBFIELD ← prove
    r"!k:A ring P.
        number_field k /\ prime_ideal (ring_of_integers k) P /\
        ~(P = {ring_0 k})
        ==> residue_degree
              (ring_of_integers(subfield_generated k {ring_0 k}),
               ring_of_integers k) I P =
            residue_degree (integer_ring,ring_of_integers k) (ring_of_int k) P"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [residue_degree, RING_OF_INTEGERS, INTEGER_RING, RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER, I_O_ID, NUMBER_FIELD_IMP_FIELD] THEN REWRITE_TAC [SIMPLE_IMAGE, IMAGE_o, ETA_AX])

  let NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q ← prove
    r"!k:A ring l:B ring h p P.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P
        ==> ramification_index (integer_ring,ring_of_integers l)
              (ring_of_int l) P =
            ramification_index
              (ring_of_integers k,ring_of_integers l) h P *
            ramification_index (integer_ring,ring_of_integers k)
              (ring_of_int k) p"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k}:A ring"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"I:A->A"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_RAMIFICATION_INDEX_TOWER) THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_O_ID, RAMIFICATION_INDEX_PRIME_SUBFIELD, PRIME_IMP_RING_IDEAL] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_HOMOMORPHISM_RING_OF_INT)) THEN ASM_SIMP_TAC [ramification_index, RING_OF_INTEGERS, INTEGER_RING, RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER] THEN REPEAT AP_TERM_TAC THEN ASM SET_TAC [])

  let NUMBER_FIELD_RESIDUE_DEGREE_TOWER_Q ← prove
    r"!k:A ring l:B ring h p P.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        prime_ideal (ring_of_integers l) P /\ IMAGE h p SUBSET P
        ==> residue_degree (integer_ring,ring_of_integers l) (ring_of_int l) P =
            residue_degree
              (ring_of_integers k,ring_of_integers l) h P *
            residue_degree (integer_ring,ring_of_integers k) (ring_of_int k) p"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k}:A ring"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"I:A->A"), (← q r"h:A->B"), (← q r"p:A->bool"), (← q r"P:B->bool")] NUMBER_FIELD_RESIDUE_DEGREE_TOWER) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"l:B ring"), (← q r"h:A->B")] NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, I_O_ID, RESIDUE_DEGREE_PRIME_SUBFIELD] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_HOMOMORPHISM_RING_OF_INT)) THEN ASM_SIMP_TAC [residue_degree, RING_OF_INTEGERS, INTEGER_RING, RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER] THEN REWRITE_TAC [SIMPLE_IMAGE, (← GSYM IMAGE_o)] THEN REPEAT (AP_THM_TAC ORELSE AP_TERM_TAC) THEN ASM_REWRITE_TAC [FUN_EQ_THM, o_THM])

  -- @@RETURN BEGIN
  return { DEDEKIND_EXTENSION_DIGITS_IN_IDEAL_POW, DEDEKIND_EXTENSION_DIGITS_SPAN,
           DEDEKIND_EXTENSION_DIGITS_INDEPENDENT, DEDEKIND_EXTENSION_DIGITS,
           RING_OF_INTEGERS_PRIME_SUBFIELD_CARRIER, RING_OF_INTEGERS_RATIONAL_FIELD,
           RING_OF_INTEGERS_PRIME_SUBFIELD_PRIME_IDEAL,
           RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL, RAMIFICATION_INDEX_PRIME_SUBFIELD,
           RESIDUE_DEGREE_PRIME_SUBFIELD, NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q,
           NUMBER_FIELD_RESIDUE_DEGREE_TOWER_Q }
  -- @@RETURN END

end HolANT.RelativeSplit
