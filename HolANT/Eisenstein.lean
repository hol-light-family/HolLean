/- ========================================================================= -/
/- ANT: Eisenstein polynomials                                             -/
/- ========================================================================= -/
/- File: HolANT/Eisenstein.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/eisenstein.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/anteisensteindiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/products.ml, ANT/algmisc.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/integral.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/dedekind_kummer.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.Eisenstein fills them).

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
import HolLibrary.Products
import HolANT.Algmisc
import HolLibrary.Matroids
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolLibrary.FieldTheory
import HolANT.Integral
import HolANT.IdealArith
import HolANT.Dedekind
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.PrimeSplit
import HolANT.NormIndex
import HolANT.Discriminant
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.TraceForm
import HolANT.RelativeSplit
import HolANT.RelativeDegree
import HolANT.NfValuation
import HolANT.Integrality
import HolANT.DedekindKummer

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
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.DedekindStruct
open HolANT.IdealNorm
open HolANT.RingOfIntegers
open HolANT.PrimeSplit
open HolANT.NormIndex
open HolANT.Discriminant
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.TraceForm
open HolANT.RelativeSplit
open HolANT.RelativeDegree
open HolANT.NfValuation
open HolANT.Integrality
open HolANT.DedekindKummer

namespace HolANT.Eisenstein

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD1 COEFF_ABOVE_DEG COEFF_COMPOSE COEFF_POLY_VARPOW CONTRAPOS_THM
   DEDEKIND_IDEAL_SUBSET_POW_VALUATION DEDEKIND_IMP_INTEGRAL_DOMAIN
   DEDEKIND_IN_IDEAL_POW_VALUATION DEDEKIND_KUMMER_Q DEDEKIND_RING_OF_INTEGERS
   EMPTY_GSPEC EXTENSION FIELD_IMP_INTEGRAL_DOMAIN FIELD_IMP_NONTRIVIAL_RING
   FIELD_INTEGER_MOD_RING FINITE_NUMSEG_LT FINITE_SING FORALL_IN_IMAGE
   FUN_EQ_COEFF FUN_EQ_THM HAS_SIZE HAS_SIZE_FUNSPACE HAS_SIZE_IMAGE_INJ
   HAS_SIZE_NUMSEG_LT IDEAL_GENERATED_EQ_0 IDEAL_GENERATED_MINIMAL IDEAL_POW_1
   IDEAL_POW_ANTIMONO IDEAL_POW_SUC IDEAL_PRODUCT_SING IDEAL_VALUATION_EQ_0
   IDEAL_VALUATION_PRINCIPAL_MUL IDEAL_VALUATION_PRINCIPAL_POW IMAGE_CLAUSES
   INTEGER_MOD_RING_CHAR INTEGER_MOD_RING_CLAUSES INTEGER_RING
   INTEGRAL_DOMAIN_MUL_EQ_0 INTEGRAL_DOMAIN_POW_EQ_0 INT_ABS_NUM INT_DIVIDES_LE
   INT_ENTIRE INT_OF_NUM_EQ INT_OF_NUM_LT INT_POS INT_POW_2 INT_REM_EQ_SELF
   IN_DELETE IN_ELIM_THM IN_IDEAL_GENERATED_SELF IN_IDEAL_GENERATED_SING
   IN_IMAGE IN_RING_IDEAL_ADD IN_RING_IDEAL_LMUL IN_RING_IDEAL_NEG
   IN_RING_IDEAL_RMUL IN_RING_IDEAL_SUB IN_RING_IDEAL_SUM IN_SING IN_SUBRING_MUL
   IN_SUBRING_POW IN_SUBRING_SUM IN_UNIV LEFT_IMP_EXISTS_THM LE_ANTISYM LE_REFL
   LT LT_NZ MEMBER_NOT_EMPTY MONIC_POLY_VAR MONO_EXISTS MULT_CLAUSES NOT_IMP
   NOT_LT NUMBER_FIELD_DEGREE_POS NUMBER_FIELD_IMP_FIELD
   NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (NUM_OF_INT_OF_NUM POLY_DEG_VAR POLY_EXTEND_MONIC_UNIVARIATE POLY_EXTEND_VAR
   POLY_RING_CLAUSES PRIME_GE_2 PRIME_IDEAL_IMP_SUBSET PRIME_IMP_NZ
   PRIME_IMP_RING_IDEAL QUOTIENT_RING_CARRIER RAMIFICATION_INDEX_INTEGER_RING
   RAMIFICATION_INDEX_PRIME RING_0 RING_1 RING_ADD RING_ADD_LZERO RING_ADD_RZERO
   RING_COSET_EQ RING_HOMOMORPHISM_INTEGER_RING_OF_INT
   RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_POW RING_IDEAL_IMP_SUBSET
   RING_IRREDUCIBLE_POLY_VAR RING_MUL RING_MUL_IN_IDEAL_PROD RING_MUL_RID
   RING_MUL_RZERO RING_OF_INT RING_OF_INTEGERS RING_OF_INTEGERS_CARRIER
   RING_OF_INTEGERS_FINITE_QUOTIENT RING_OF_INTEGERS_IDEAL_NORM_INTEGER
   RING_OF_INTEGERS_SUBRING RING_OF_INTEGERS_SUBSET RING_OF_INT_0 RING_OF_INT_1
   RING_OF_INT_EQ_0 RING_OF_INT_EQ_0_CHAR_0 RING_OF_INT_IN_PRIME_IDEAL
   RING_OF_INT_IN_RING_OF_INTEGERS RING_OF_INT_MUL RING_OF_INT_OF_NUM
   RING_OF_INT_SUB RING_OF_NUM_IN_PRIME_IDEAL RING_POLYNOMIAL
   RING_POLYNOMIAL_VAR RING_POW RING_POW_ADD RING_POW_IN_PRIME_IDEAL
   RING_POW_ZERO RING_PRODUCT_SING RING_SUB_RDISTRIB RING_SUM RING_SUM_CLAUSES
   RING_SUM_DELETE RING_SUM_EQ RING_SUM_EQ_0 RING_SUM_LMUL
   RING_SUM_RING_OF_INTEGERS RING_SUM_SUB SING_SUBSET
   SUBRING_GENERATED_INDEX_COPRIME SUBRING_GENERATED_INT_LINCOMB SUBSET SUC_SUB1
   SURJECTIVE_IFF_INJECTIVE_GEN TRIVIAL_RING_10 ideal_norm int_divides
   integral_element monic num_WOP number_field poly_var ring_divides ring_pow
   ring_setadd : thm)
  deriving Inhabited

/-- What eisenstein.ml uses from Session besides theorems. -/
structure EisensteinDeps where
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
/- eisenstein.ml phrases from line 71 to 564                              -/
/- ---------------------------------------------------------------------- -/

structure Eisenstein01 where
  -- @@FIELDS
  NUMBER_FIELD_EISENSTEIN_VALUATION : thm
  NUMBER_FIELD_EISENSTEIN_POW : thm
  IDEAL_VALUATION_RING_OF_INT_COPRIME : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupEisenstein01 [HolBase] (D : EisensteinDeps) :
    ExceptT String IO Eisenstein01 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE, RING_RULE,
        SET_TAC, .. } := D
  let { ADD1, CONTRAPOS_THM, DEDEKIND_IMP_INTEGRAL_DOMAIN,
        DEDEKIND_IN_IDEAL_POW_VALUATION, DEDEKIND_RING_OF_INTEGERS, EMPTY_GSPEC,
        FIELD_IMP_NONTRIVIAL_RING, FINITE_NUMSEG_LT, IDEAL_GENERATED_EQ_0,
        IDEAL_GENERATED_MINIMAL, IDEAL_POW_1, IDEAL_POW_ANTIMONO, IDEAL_POW_SUC,
        IDEAL_VALUATION_EQ_0, IDEAL_VALUATION_PRINCIPAL_MUL,
        IDEAL_VALUATION_PRINCIPAL_POW, INTEGRAL_DOMAIN_POW_EQ_0, INT_ENTIRE,
        INT_OF_NUM_EQ, INT_POW_2, IN_DELETE, IN_ELIM_THM, IN_IDEAL_GENERATED_SELF,
        IN_IDEAL_GENERATED_SING, IN_RING_IDEAL_ADD, IN_RING_IDEAL_NEG,
        IN_RING_IDEAL_RMUL, IN_RING_IDEAL_SUM, IN_SUBRING_MUL, IN_SUBRING_POW,
        IN_SUBRING_SUM, LE_ANTISYM, LE_REFL, LT, LT_NZ, MONO_EXISTS, NOT_LT,
        NUMBER_FIELD_IMP_FIELD, .. } := D.core1
  let { POLY_EXTEND_MONIC_UNIVARIATE, PRIME_IDEAL_IMP_SUBSET, PRIME_IMP_NZ,
        PRIME_IMP_RING_IDEAL, RAMIFICATION_INDEX_INTEGER_RING, RING_0, RING_1,
        RING_ADD_LZERO, RING_ADD_RZERO, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW, RING_MUL,
        RING_MUL_IN_IDEAL_PROD, RING_MUL_RID, RING_MUL_RZERO, RING_OF_INT,
        RING_OF_INTEGERS, RING_OF_INTEGERS_CARRIER, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, RING_OF_INT_EQ_0_CHAR_0, RING_OF_INT_IN_PRIME_IDEAL,
        RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_MUL, RING_OF_INT_OF_NUM,
        RING_OF_NUM_IN_PRIME_IDEAL, RING_POW, RING_POW_IN_PRIME_IDEAL, RING_POW_ZERO,
        RING_SUM, RING_SUM_CLAUSES, RING_SUM_DELETE, RING_SUM_EQ_0,
        RING_SUM_RING_OF_INTEGERS, SING_SUBSET, SUBSET, TRIVIAL_RING_10, int_divides,
        integral_element, number_field, ring_divides, ring_pow, .. } := D.core2
  -- @@SCOPE END

  let NUMBER_FIELD_EISENSTEIN_VALUATION ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"ring_add r x (ring_add r y z) = ring_0 r
        ==> y = ring_neg r (ring_add r x (z:A))"
    let r2 ← RING_RULE q1
    let q3 ← q r"ring_add r x (ring_add r y z) = ring_0 r
        ==> x = ring_neg r (ring_add r y (z:A))"
    let r4 ← RING_RULE q3
    let p11 ← prove r"!r x y z:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r /\
        ring_add r x (ring_add r y z) = ring_0 r
        ==> x = ring_neg r (ring_add r y z) /\
            y = ring_neg r (ring_add r x z)" (REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); pure (is_eq z5)) then (do let z10 ← (q r"ring_0 r:A"); let z9 ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); liftExcept (rhs z7)); pure (z9 == z10)) else pure false)))) THENL [MATCH_MP_TAC r4, MATCH_MP_TAC r2] THEN ASM_REWRITE_TAC [])
    let lemma := p11
    let q12 ← q r"S:A"
    let q13 ← q r"ring_of_int k (coeff 0 m):A"
    let q14 ← q r"ideal_pow (ring_of_integers k) P e:A->bool"
    let q15 ← q r"ring_of_integers k:A ring"
    let v16 ← ISPECL [q15, q14, q13, q12] IN_RING_IDEAL_ADD
    let q17 ← q r"ring_add k (ring_of_int k (coeff 0 m)) (S:A)"
    let q18 ← q r"ideal_pow (ring_of_integers k) P e:A->bool"
    let q19 ← q r"ring_of_integers k:A ring"
    let v20 ← ISPECL [q19, q18, q17] IN_RING_IDEAL_NEG
    let q21 ← q r"e <= e + 1"
    let r22 ← ARITH_RULE q21
    let q23 ← q r"e + 1"
    let q24 ← q r"e:num"
    let q25 ← q r"P:A->bool"
    let q26 ← q r"ring_of_integers k:A ring"
    let v27 ← ISPECL [q26, q25, q24, q23] IDEAL_POW_ANTIMONO
    let q28 ← q r"(S:A) IN ideal_pow (ring_of_integers k) P e /\
      ring_of_int k (coeff 0 m) IN ideal_pow (ring_of_integers k) P e"
    let q29 ← q r"S:A"
    let q30 ← q r"ring_of_int k (coeff 0 m):A"
    let q31 ← q r"ring_pow k a n:A"
    let q32 ← q r"k:A ring"
    let v33 ← ISPECL [q32, q31, q30, q29] lemma
    let q34 ← q r"ring_pow k (a:A) n IN ideal_pow (ring_of_integers k) P e"
    let q35 ← q r"S:A"
    let q36 ← q r"ring_pow k a n:A"
    let q37 ← q r"ideal_pow (ring_of_integers k) P (e + 1):A->bool"
    let q38 ← q r"ring_of_integers k:A ring"
    let v39 ← ISPECL [q38, q37, q36, q35] IN_RING_IDEAL_ADD
    let q40 ← q r"ring_add k (ring_pow k a n) (S:A)"
    let q41 ← q r"ideal_pow (ring_of_integers k) P (e + 1):A->bool"
    let q42 ← q r"ring_of_integers k:A ring"
    let v43 ← ISPECL [q42, q41, q40] IN_RING_IDEAL_NEG
    let q44 ← q r"S:A"
    let q45 ← q r"ring_of_int k (coeff 0 m):A"
    let q46 ← q r"ring_pow k a n:A"
    let q47 ← q r"k:A ring"
    let v48 ← ISPECL [q47, q46, q45, q44] lemma
    let q49 ← q r"ring_of_int k (coeff 0 m):A IN
      ideal_pow (ring_of_integers k) P (e + 1)"
    let q50 ← q r"ring_pow k (a:A) n IN ideal_pow (ring_of_integers k) P (e + 1)"
    let v51 ← GSYM NOT_LT
    let v52 ← GSYM LE_ANTISYM
    let q53 ← q r"!x j. x IN ring_carrier(ring_of_integers k) /\ ~(x = ring_0 k)
          ==> (x IN ideal_pow (ring_of_integers k) P j <=>
               j <= ideal_valuation (ring_of_integers k) P
                      (ideal_generated (ring_of_integers k) {x:A}))"
    let q54 ← q r"n:num"
    let q55 ← q r"a:A"
    let q56 ← q r"ring_of_integers k:A ring"
    let v57 ← ISPECL [q56, q55, q54] INTEGRAL_DOMAIN_POW_EQ_0
    let q58 ← q r"~(ring_pow k a n = ring_0 (k:A ring))"
    let q59 ← q r"n:num"
    let q60 ← q r"a:A"
    let q61 ← q r"P:A->bool"
    let q62 ← q r"ring_of_integers k:A ring"
    let v63 ← ISPECL [q62, q61, q60, q59] IDEAL_VALUATION_PRINCIPAL_POW
    let q64 ← q r"ideal_valuation (ring_of_integers k) P
      (ideal_generated (ring_of_integers k) {ring_pow k a n:A}) = n * w"
    let q65 ← q r"1"
    let q66 ← q r"a:A"
    let q67 ← q r"P:A->bool"
    let q68 ← q r"ring_of_integers k:A ring"
    let v69 ← ISPECL [q68, q67, q66, q65] DEDEKIND_IN_IDEAL_POW_VALUATION
    let q70 ← q r"1 <= w"
    let q71 ← q r"w = ideal_valuation (ring_of_integers k) P
          (ideal_generated (ring_of_integers k) {a:A})"
    let q72 ← q r"ring_add k (ring_pow k a n) (ring_add k (ring_of_int k (coeff 0 m)) S) =
      ring_0 (k:A ring)"
    let q73 ← q r"~(ring_of_int k (coeff 0 m) = ring_0 (k:A ring))"
    let q74 ← q r"ring_pow k a n = ring_0 (k:A ring) /\ S = ring_0 k"
    let q75 ← q r"~(a = ring_0 (k:A ring))"
    let q76 ← q r"~(ring_of_int k (coeff 0 m) = ring_0 (k:A ring))"
    let q77 ← q r"~(ring_of_int k u:A IN P)"
    let q78 ← q r"ideal_generated (ring_of_integers k) {ring_of_int k u:A}"
    let q79 ← q r"P:A->bool"
    let q80 ← q r"ring_of_integers k:A ring"
    let v81 ← ISPECL [q80, q79, q78] IDEAL_VALUATION_EQ_0
    let q82 ← q r"y = 0 ==> e + y = e"
    let r83 ← ARITH_RULE q82
    let q84 ← q r"ring_of_int k u:A"
    let q85 ← q r"ring_of_int k (&p):A"
    let q86 ← q r"P:A->bool"
    let q87 ← q r"ring_of_integers k:A ring"
    let v88 ← ISPECL [q87, q86, q85, q84] IDEAL_VALUATION_PRINCIPAL_MUL
    let v89 ← GSYM RING_OF_INT_OF_NUM
    let q90 ← q r"ideal_valuation (ring_of_integers k) P
      (ideal_generated (ring_of_integers k)
         {ring_of_int k (coeff 0 m):A}) = e"
    let q91 ← q r"p:num"
    let q92 ← q r"P:A->bool"
    let q93 ← q r"ring_of_integers k:A ring"
    let v94 ← ISPECL [q93, q92, q91] RING_OF_INT_IN_PRIME_IDEAL
    let q95 ← q r"~(ring_of_int k u:A = ring_0 k) /\ ~(ring_of_int k u:A IN P)"
    let q96 ← q r"!d:int. d divides &0"
    let r97 ← INTEGER_RULE q96
    let q98 ← q r"~((&p:int) divides &0)"
    let q99 ← q r"~(u:int = &0)"
    let q100 ← q r"~(&p pow 2 divides coeff 0 (m:(1->num)->int))"
    let q101 ← q r"u:int"
    let q111 ← q r"0"
    let q112 ← q r"?u. coeff 0 (m:(1->num)->int) = &p * u /\ ~(&p divides u)"
    let v113 ← GSYM RING_OF_INT_OF_NUM
    let q114 ← q r"ring_mul k (ring_of_int k t)
                        (ring_pow k a (i - 1)):A"
    let q115 ← q r"ring_of_num k p:A"
    let q116 ← q r"ideal_pow (ring_of_integers k) P e:A->bool"
    let q117 ← q r"ring_of_integers k:A ring"
    let v118 ← ISPECL [q117, q116, q115, q114] IN_RING_IDEAL_RMUL
    let q119 ← q r"ring_mul k (ring_of_int k t) (ring_pow k a (i - 1)):A IN
      ring_carrier(ring_of_integers k)"
    let q120 ← q r"ring_mul k (ring_of_num k p)
                      (ring_mul k (ring_of_int k t)
                         (ring_pow k a (i - 1))):A"
    let q121 ← q r"a:A"
    let q122 ← q r"ideal_pow (ring_of_integers k) P e:A->bool"
    let q123 ← q r"P:A->bool"
    let q124 ← q r"ring_of_integers k:A ring"
    let v125 ← ISPECL [q124, q123, q122, q121, q120] RING_MUL_IN_IDEAL_PROD
    let v126 ← GSYM ADD1
    let q127 ← q r"ring_mul r (ring_mul r p t) (ring_mul r a x) =
        ring_mul r a (ring_mul r p (ring_mul r t (x:A)))"
    let r128 ← RING_RULE q127
    let v129 ← GSYM RING_OF_INT_OF_NUM
    let q130 ← q r"i = SUC(i - 1)"
    let q131 ← q r"ring_mul k (ring_of_int k (&p * t)) (ring_pow k a i) =
      ring_mul k a (ring_mul k (ring_of_num k p)
        (ring_mul k (ring_of_int k t) (ring_pow k a (i - 1)))):A"
    let q132 ← q r"t:int"
    let q142 ← q r"i:num"
    let q143 ← q r"i:num"
    let q144 ← q r"(S:A) IN ideal_pow (ring_of_integers k) P (e + 1)"
    let q145 ← q r"S:A"
    let q146 ← q r"ring_of_int k (coeff 0 m):A"
    let q147 ← q r"P:A->bool"
    let q148 ← q r"ring_of_integers k:A ring"
    let v149 ← ISPECL [q148, q147, q146, q145] IN_RING_IDEAL_ADD
    let q150 ← q r"ring_add k (ring_of_int k (coeff 0 m)) (S:A)"
    let q151 ← q r"P:A->bool"
    let q152 ← q r"ring_of_integers k:A ring"
    let v153 ← ISPECL [q152, q151, q150] IN_RING_IDEAL_NEG
    let q154 ← q r"S:A"
    let q155 ← q r"ring_of_int k (coeff 0 m):A"
    let q156 ← q r"ring_pow k a n:A"
    let q157 ← q r"k:A ring"
    let v158 ← ISPECL [q157, q156, q155, q154] lemma
    let q159 ← q r"n:num"
    let q160 ← q r"a:A"
    let q161 ← q r"P:A->bool"
    let q162 ← q r"ring_of_integers k:A ring"
    let v163 ← ISPECL [q162, q161, q160, q159] RING_POW_IN_PRIME_IDEAL
    let q164 ← q r"(a:A) IN P"
    let q165 ← q r"ring_of_int k (coeff 0 m) IN ring_carrier k /\
    (S:A) IN ring_carrier k /\ ring_pow k a n IN ring_carrier k"
    let q166 ← q r"ring_of_int k (coeff 0 m) IN ring_carrier(ring_of_integers k) /\
    (S:A) IN ring_carrier(ring_of_integers k) /\
    ring_pow k a n IN ring_carrier(ring_of_integers k)"
    let q173 ← q r"(S:A) IN P"
    let q183 ← q r"0"
    let q184 ← q r"ring_of_int k (coeff 0 m) IN (P:A->bool)"
    let q185 ← q r"ideal_generated (ring_of_integers k) {ring_of_num k p:A} SUBSET P"
    let q186 ← q r"ring_mul r (ring_mul r x y) z = ring_mul r x (ring_mul r y (z:A))"
    let r187 ← RING_RULE q186
    let q188 ← q r"ring_mul k (ring_of_int k t) (ring_pow k a i):A"
    let v189 ← GSYM RING_OF_INT_OF_NUM
    let q190 ← q r"t:int"
    let q200 ← q r"i:num"
    let q201 ← q r"i:num"
    let q202 ← q r"!i. i < n
        ==> ring_mul k (ring_of_int k (coeff i m)) (ring_pow k a i) IN
            ideal_generated (ring_of_integers k) {ring_of_num k p:A}"
    let q203 ← q r"ring_add r x (ring_sub r y x) = (y:A)"
    let r204 ← RING_RULE q203
    let q205 ← q r"0"
    let q206 ← q r"{i:num | i < n}"
    let q207 ← q r"\i. ring_mul k (ring_of_int k (coeff i (m:(1->num)->int)))
                      (ring_pow k (a:A) i)"
    let q208 ← q r"k:A ring"
    let v209 ← ISPECL [q208, q207, q206, q205] RING_SUM_DELETE
    let q216 ← q r"ring_add k (ring_pow k a n) (ring_add k (ring_of_int k (coeff 0 m)) S) =
    ring_0 (k:A ring)"
    let q217 ← q r"S = ring_sum k ({i | i < n} DELETE 0)
          (\i. ring_mul k (ring_of_int k (coeff i m))
                 (ring_pow k (a:A) i))"
    let v218 ← GSYM TRIVIAL_RING_10
    let q219 ← q r"ring_add k (ring_pow k a 0)
        (ring_sum k {i | i < 0}
           (\i. ring_mul k (ring_of_int k (coeff i m)) (ring_pow k a i))) =
      ring_0 (k:A ring)"
    let q220 ← q r"~(n = 0)"
    let q227 ← q r"ring_add k (ring_pow k a n)
      (ring_sum k {i | i < n}
         (\i. ring_mul k (ring_of_int k (coeff i m)) (ring_pow k a i))) =
    ring_0 (k:A ring)"
    let v228 ← GSYM RING_OF_INT_OF_NUM
    let q229 ← q r"e:num"
    let q230 ← q r"ring_of_num k p:A"
    let q231 ← q r"P:A->bool"
    let q232 ← q r"ring_of_integers k:A ring"
    let v233 ← ISPECL [q232, q231, q230, q229] DEDEKIND_IN_IDEAL_POW_VALUATION
    let q234 ← q r"(ring_of_num k p:A) IN ideal_pow (ring_of_integers k) P e"
    let q235 ← q r"e = ideal_valuation (ring_of_integers k) P
          (ideal_generated (ring_of_integers k) {ring_of_num k p:A})"
    let q236 ← q r"p:num"
    let q237 ← q r"P:A->bool"
    let q238 ← q r"ring_of_integers k:A ring"
    let v239 ← ISPECL [q238, q237, q236] RING_OF_NUM_IN_PRIME_IDEAL
    let q240 ← q r"P:A->bool"
    let q241 ← q r"ring_of_integers k:A ring"
    let v242 ← ISPECL [q241, q240] RAMIFICATION_INDEX_INTEGER_RING
    let q243 ← q r"ramification_index (integer_ring,ring_of_integers k) (ring_of_int k) P =
    ideal_valuation (ring_of_integers k) P
      (ideal_generated (ring_of_integers k) {ring_of_num k p:A})"
    let q244 ← q r"~(P = {ring_0 (ring_of_integers k:A ring)})"
    let v245 ← GSYM RING_OF_INT_OF_NUM
    let q246 ← q r"~(ring_of_num k p = ring_0 (k:A ring))"
    let q247 ← q r"ring_ideal (ring_of_integers k) (P:A->bool)"
    let q248 ← q r"ring_carrier(ring_of_integers k) subring_of (k:A ring)"
    let q249 ← q r"n = poly_deg integer_ring (m:(1->num)->int)"
    let q250 ← q r"(a:A) IN ring_carrier(ring_of_integers k)"
    prove
      r"!(k:A ring) a m p P.
          number_field k /\ a IN ring_carrier k /\
          m IN ring_carrier(poly_ring integer_ring (:1)) /\
          monic integer_ring m /\
          poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
          prime p /\
          (!i. i < poly_deg integer_ring m ==> &p divides coeff i m) /\
          ~(&p pow 2 divides coeff 0 m) /\
          prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P
          ==> a IN ring_carrier(ring_of_integers k) /\ ~(a = ring_0 k) /\
              1 <= ideal_valuation (ring_of_integers k) P
                     (ideal_generated (ring_of_integers k) {a}) /\
              poly_deg integer_ring m *
              ideal_valuation (ring_of_integers k) P
                (ideal_generated (ring_of_integers k) {a}) =
              ramification_index (integer_ring,ring_of_integers k)
                (ring_of_int k) P"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_RING_OF_INTEGERS)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FIELD_IMP_NONTRIVIAL_RING)) THEN SUBGOAL_THEN q250 ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM, integral_element] THEN ASM_MESON_TAC [], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC q249 THEN SUBGOAL_THEN q248 ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING], ALL_TAC] THEN SUBGOAL_THEN q247 ASSUME_TAC THENL [ASM_SIMP_TAC [PRIME_IMP_RING_IDEAL], ALL_TAC] THEN SUBGOAL_THEN q246 ASSUME_TAC THENL [REWRITE_TAC [v245] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0, INT_OF_NUM_EQ, PRIME_IMP_NZ], ALL_TAC] THEN SUBGOAL_THEN q244 ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS] THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q243 SUBST1_TAC THENL [MP_TAC v242 THEN MP_TAC v239 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN SIMP_TAC [], ALL_TAC] THEN ABBREV_TAC q235 THEN SUBGOAL_THEN q234 ASSUME_TAC THENL [MP_TAC v233 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, v228, RING_OF_INT_IN_RING_OF_INTEGERS] THEN ASM_REWRITE_TAC [RING_OF_INT_OF_NUM, LE_REFL], ALL_TAC] THEN SUBGOAL_THEN q227 ASSUME_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z221 ← (do let z222 ← (pure th); pure (concl z222)); pure (is_eq z221)) then (do let z226 ← (q r"ring_0 k:A"); let z225 ← (do let z223 ← (do let z224 ← (pure th); pure (concl z224)); liftExcept (rhs z223)); pure (z225 == z226)) else pure false))))) THEN EXPAND_TAC "n" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC POLY_EXTEND_MONIC_UNIVARIATE THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT], ALL_TAC] THEN SUBGOAL_THEN q220 ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC q219 THEN REWRITE_TAC [LT, EMPTY_GSPEC, RING_SUM_CLAUSES, ring_pow] THEN ASM_SIMP_TAC [RING_ADD_RZERO, RING_1, v218], ALL_TAC] THEN ABBREV_TAC q217 THEN SUBGOAL_THEN q216 ASSUME_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z210 ← (do let z211 ← (pure th); pure (concl z211)); pure (is_eq z210)) then (do let z215 ← (q r"ring_0 k:A"); let z214 ← (do let z212 ← (do let z213 ← (pure th); pure (concl z213)); liftExcept (rhs z212)); pure (z214 == z215)) else pure false))))) THEN AP_TERM_TAC THEN EXPAND_TAC "S" THEN MP_TAC v209 THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, LT_NZ, RING_MUL, RING_OF_INT, RING_POW] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [ring_pow] THEN ASM_SIMP_TAC [RING_MUL_RID, RING_OF_INT] THEN MATCH_MP_TAC r204 THEN ASM_SIMP_TAC [RING_OF_INT, RING_SUM], ALL_TAC] THEN SUBGOAL_THEN q202 ASSUME_TAC THENL [X_GEN_TAC q201 THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q200) o (checkM (fun th => (do if ← (do let z191 ← (do let z192 ← (pure th); pure (concl z192)); pure (is_forall z191)) then (do let z193 ← (do let z194 ← (pure th); pure (concl z194)); canM (fun z195 => (do let z196 ← (pure z195); find_termM (fun z197 => (do let z199 ← (pure z197); let z198 ← (q r"(divides):int->int->bool"); pure (z198 == z199))) z196)) z193) else pure false))))) THEN ASM_REWRITE_TAC [int_divides] THEN DISCH_THEN (X_CHOOSE_THEN q190 SUBST1_TAC) THEN MATCH_MP_TAC IN_IDEAL_GENERATED_SING THEN REWRITE_TAC [ring_divides, RING_OF_INTEGERS] THEN REWRITE_TAC [RING_OF_INT_MUL, v189] THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS] THEN EXISTS_TAC q188 THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS] THEN MATCH_MP_TAC r187 THEN ASM_SIMP_TAC [RING_OF_INT, RING_POW], ALL_TAC] THEN SUBGOAL_THEN q185 ASSUME_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], ALL_TAC] THEN SUBGOAL_THEN q184 ASSUME_TAC THENL [FIRST_X_ASSUM (MATCH_MP_TAC o (REWRITE_RULE [SUBSET])) THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q183) o (checkM (fun th => (do if ← (do let z174 ← (do let z175 ← (pure th); pure (concl z175)); pure (is_forall z174)) then (do let z176 ← (do let z177 ← (pure th); pure (concl z177)); canM (fun z178 => (do let z179 ← (pure z178); find_termM (fun z180 => (do let z182 ← (pure z180); let z181 ← (q r"ideal_generated:(A ring)->(A->bool)->A->bool"); pure (z181 == z182))) z179)) z176) else pure false))))) THEN ASM_REWRITE_TAC [LT_NZ, ring_pow] THEN ASM_SIMP_TAC [RING_MUL_RID, RING_OF_INT], ALL_TAC] THEN SUBGOAL_THEN q173 ASSUME_TAC THENL [EXPAND_TAC "S" THEN wPart lhand (rand o rand) RING_SUM_RING_OF_INTEGERS THEN ANTS_TAC THENL [REWRITE_TAC [IN_DELETE, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [IN_DELETE, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do if ← (do let z167 ← (do let z168 ← (pure th); pure (concl z168)); pure (is_comb z167)) then (do let z172 ← (q r"P:A->bool"); let z171 ← (do let z169 ← (do let z170 ← (pure th); pure (concl z170)); liftExcept (rand z169)); pure (z171 == z172)) else pure false))))) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN q166 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS] THEN ASM_MESON_TAC [PRIME_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN q165 STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN q164 ASSUME_TAC THENL [MP_TAC v163 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC v158 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o CONJUNCT1)] THEN MP_TAC v153 THEN MP_TAC v149 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN q144 ASSUME_TAC THENL [EXPAND_TAC "S" THEN wPart lhand (rand o rand) RING_SUM_RING_OF_INTEGERS THEN ANTS_TAC THENL [REWRITE_TAC [IN_DELETE, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN REWRITE_TAC [IN_DELETE, IN_ELIM_THM] THEN X_GEN_TAC q143 THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC q142) o (checkM (fun th => (do if ← (do let z133 ← (do let z134 ← (pure th); pure (concl z134)); pure (is_forall z133)) then (do let z135 ← (do let z136 ← (pure th); pure (concl z136)); canM (fun z137 => (do let z138 ← (pure z137); find_termM (fun z139 => (do let z141 ← (pure z139); let z140 ← (q r"(divides):int->int->bool"); pure (z140 == z141))) z138)) z135) else pure false))))) THEN ASM_REWRITE_TAC [int_divides] THEN DISCH_THEN (X_CHOOSE_THEN q132 SUBST1_TAC) THEN SUBGOAL_THEN q131 SUBST1_TAC THENL [SUBGOAL_THEN q130 (fun th => GEN_REWRITE_TAC (LAND_CONV o (RAND_CONV o RAND_CONV)) [th]) THENL [ASM_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [ring_pow, RING_OF_INT_MUL, v129] THEN MATCH_MP_TAC r128 THEN ASM_SIMP_TAC [RING_OF_INT, RING_POW], ALL_TAC] THEN REWRITE_TAC [v126, IDEAL_POW_SUC] THEN MP_TAC v125 THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN q119 ASSUME_TAC THENL [ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN CONJ_TAC THENL [MP_TAC v118 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_IDEAL_IDEAL_POW], MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [v113, RING_OF_INT_IN_RING_OF_INTEGERS]], ALL_TAC] THEN SUBGOAL_THEN q112 STRIP_ASSUME_TAC THENL [FIRST_X_ASSUM (MP_TAC o ((SPEC q111) o (checkM (fun th => (do if ← (do let z102 ← (do let z103 ← (pure th); pure (concl z103)); pure (is_forall z102)) then (do let z104 ← (do let z105 ← (pure th); pure (concl z105)); canM (fun z106 => (do let z107 ← (pure z106); find_termM (fun z108 => (do let z110 ← (pure z108); let z109 ← (q r"(divides):int->int->bool"); pure (z109 == z110))) z107)) z104) else pure false))))) THEN ASM_REWRITE_TAC [LT_NZ, int_divides] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q101 THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC q100 THEN ASM_REWRITE_TAC [INT_POW_2, CONTRAPOS_THM] THEN CONV_TAC INTEGER_RULE, ALL_TAC] THEN SUBGOAL_THEN q99 ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC q98 THEN REWRITE_TAC [r97], ALL_TAC] THEN SUBGOAL_THEN q95 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0] THEN MP_TAC v94 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q90 ASSUME_TAC THENL [ASM_REWRITE_TAC [RING_OF_INT_MUL, v89] THEN MP_TAC v88 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_OF_INT_IN_RING_OF_INTEGERS] THEN ASM_REWRITE_TAC [RING_OF_INT_OF_NUM] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC r83 THEN MP_TAC v81 THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, RING_OF_INTEGERS, RING_OF_INT_IN_RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN UNDISCH_TAC q77 THEN REWRITE_TAC [] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (REWRITE_RULE [SUBSET])) THEN REWRITE_TAC [IN_IDEAL_GENERATED_SELF, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN q76 ASSUME_TAC THENL [ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0, INT_ENTIRE, INT_OF_NUM_EQ, PRIME_IMP_NZ], ALL_TAC] THEN SUBGOAL_THEN q75 ASSUME_TAC THENL [DISCH_TAC THEN SUBGOAL_THEN q74 STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC [RING_POW_ZERO] THEN EXPAND_TAC "S" THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN REWRITE_TAC [IN_DELETE, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [RING_POW_ZERO, RING_MUL_RZERO, RING_OF_INT], ALL_TAC] THEN UNDISCH_TAC q73 THEN REWRITE_TAC [] THEN UNDISCH_TAC q72 THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_ADD_LZERO, RING_ADD_RZERO, RING_0, RING_OF_INT], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC q71 THEN SUBGOAL_THEN q70 ASSUME_TAC THENL [EXPAND_TAC "w" THEN MP_TAC v69 THEN ASM_SIMP_TAC [RING_OF_INTEGERS, IDEAL_POW_1], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN q64 ASSUME_TAC THENL [EXPAND_TAC "w" THEN MP_TAC v63 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN q58 ASSUME_TAC THENL [MP_TAC v57 THEN ASM_SIMP_TAC [RING_OF_INTEGERS, DEDEKIND_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN SUBGOAL_THEN q53 (LABEL_TAC "mem") THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC DEDEKIND_IN_IDEAL_POW_VALUATION THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN REWRITE_TAC [v52, v51] THEN CONJ_TAC THEN DISCH_TAC THENL [SUBGOAL_THEN q50 ASSUME_TAC THENL [USE_THEN "mem" (fun th => ASM_SIMP_TAC [th]) THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q49 MP_TAC THENL [MP_TAC v48 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o CONJUNCT2)] THEN MP_TAC v43 THEN MP_TAC v39 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_IDEAL_IDEAL_POW] THEN SIMP_TAC [], USE_THEN "mem" (fun th => ASM_SIMP_TAC [th]) THEN ARITH_TAC], SUBGOAL_THEN q34 MP_TAC THENL [ALL_TAC, USE_THEN "mem" (fun th => ASM_SIMP_TAC [th]) THEN ASM_ARITH_TAC] THEN MP_TAC v33 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o CONJUNCT1)] THEN SUBGOAL_THEN q28 STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [MP_TAC v27 THEN ASM_SIMP_TAC [PRIME_IDEAL_IMP_SUBSET, r22] THEN ASM SET_TAC [], USE_THEN "mem" (fun th => ASM_SIMP_TAC [th, LE_REFL])], ALL_TAC] THEN MP_TAC v20 THEN MP_TAC v16 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_IDEAL_IDEAL_POW] THEN SIMP_TAC []])

  let NUMBER_FIELD_EISENSTEIN_POW ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul r (ring_mul r x y) z = ring_mul r x (ring_mul r y (z:A))")
    let r11 ← RING_RULE (← q r"ring_0 r = ring_add r x y ==> x = ring_neg r (y:A)")
    prove
      r"!(k:A ring) a m p.
          number_field k /\ a IN ring_carrier k /\
          m IN ring_carrier(poly_ring integer_ring (:1)) /\
          monic integer_ring m /\
          poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
          (!i. i < poly_deg integer_ring m ==> &p divides coeff i m)
          ==> a IN ring_carrier(ring_of_integers k) /\
              ring_pow k a (poly_deg integer_ring m) IN
              ideal_generated (ring_of_integers k) {ring_of_num k p}"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(a:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_CARRIER, IN_ELIM_THM, integral_element] THEN ASM_MESON_TAC [], ASM_REWRITE_TAC []] THEN ABBREV_TAC (← q r"n = poly_deg integer_ring (m:(1->num)->int)") THEN SUBGOAL_THEN (← q r"ring_carrier(ring_of_integers k) subring_of (k:A ring)") ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING], ALL_TAC] THEN ABBREV_TAC (← q r"S = ring_sum k {i | i < n}
            (\i. ring_mul k (ring_of_int k (coeff i m))
                   (ring_pow k (a:A) i))") THEN SUBGOAL_THEN (← q r"(S:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [EXPAND_TAC "S" THEN MATCH_MP_TAC IN_SUBRING_SUM THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow k a n = ring_neg k (S:A)") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"k:A ring"), (← q r"ring_of_int k:int->A"), (← q r"a:A"), (← q r"m:(1->num)->int")] POLY_EXTEND_MONIC_UNIVARIATE) THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN MATCH_MP_TAC r11 THEN ASM_SIMP_TAC [RING_POW] THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"ideal_generated (ring_of_integers k) {ring_of_num k p:A}"), (← q r"S:A")] IN_RING_IDEAL_NEG) THEN REWRITE_TAC [RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED] THEN DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "S" THEN wPart lhand (rand o rand) RING_SUM_RING_OF_INTEGERS THEN ANTS_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"i:num")) o (checkM (fun th => (do if ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); pure (is_forall z2)) then (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); canM (fun z6 => (do let z7 ← (pure z6); find_termM (fun z8 => (do let z10 ← (pure z8); let z9 ← (q r"(divides):int->int->bool"); pure (z9 == z10))) z7)) z4) else pure false))))) THEN ASM_REWRITE_TAC [int_divides] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:int") SUBST1_TAC) THEN MATCH_MP_TAC IN_IDEAL_GENERATED_SING THEN REWRITE_TAC [ring_divides, RING_OF_INTEGERS] THEN REWRITE_TAC [RING_OF_INT_MUL, (← GSYM RING_OF_INT_OF_NUM)] THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS] THEN EXISTS_TAC (← q r"ring_mul k (ring_of_int k t) (ring_pow k a i):A") THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS] THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_OF_INT, RING_POW] THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET])

  let IDEAL_VALUATION_RING_OF_INT_COPRIME ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← INTEGER_RULE (← q r"!d:int. d divides &0")
    prove
      r"!(k:A ring) P p u.
          number_field k /\ prime p /\
          prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P /\
          ~(&p divides u)
          ==> ~(ring_of_int k u = ring_0 k) /\
              ideal_valuation (ring_of_integers k) P
                (ideal_generated (ring_of_integers k) {ring_of_int k u}) = 0"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SUBGOAL_THEN (← q r"~(u:int = &0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~((&p:int) divides &0)") THEN REWRITE_TAC [r1], ALL_TAC] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0] THEN SUBGOAL_THEN (← q r"~(ring_of_int k u:A IN P)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] RING_OF_INT_IN_PRIME_IDEAL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(ring_of_num k p = ring_0 (k:A ring))") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM RING_OF_INT_OF_NUM)] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0, INT_OF_NUM_EQ, PRIME_IMP_NZ], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"ideal_generated (ring_of_integers k) {ring_of_int k u:A}")] IDEAL_VALUATION_EQ_0) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, RING_OF_INTEGERS, RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_EQ_0_CHAR_0] THEN ANTS_TAC THENL [ASM SET_TAC [], DISCH_THEN SUBST1_TAC] THEN DISCH_TAC THEN UNDISCH_TAC (← q r"~(ring_of_int k u:A IN P)") THEN REWRITE_TAC [] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (REWRITE_RULE [SUBSET])) THEN REWRITE_TAC [IN_IDEAL_GENERATED_SELF, RING_OF_INT_IN_RING_OF_INTEGERS])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_EISENSTEIN_VALUATION, NUMBER_FIELD_EISENSTEIN_POW,
           IDEAL_VALUATION_RING_OF_INT_COPRIME }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- eisenstein.ml phrases from line 606 to 1170                            -/
/- ---------------------------------------------------------------------- -/

structure Eisenstein02 where
  -- @@FIELDS
  NUMBER_FIELD_EISENSTEIN_INDEPENDENT : thm
  NUMBER_FIELD_EISENSTEIN_INDEX_COPRIME : thm
  NUMBER_FIELD_EISENSTEIN : thm
  NUMBER_FIELD_EISENSTEIN_INDEX : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupEisenstein02 [HolBase] (D : EisensteinDeps) (BEisenstein01 : Eisenstein01) :
    ExceptT String IO Eisenstein02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INT_ARITH_TAC, MESON,
        MESON_TAC, RING_RULE, SET_TAC, TAUT, .. } := D
  let { COEFF_ABOVE_DEG, COEFF_COMPOSE, COEFF_POLY_VARPOW,
        DEDEKIND_IDEAL_SUBSET_POW_VALUATION, DEDEKIND_IMP_INTEGRAL_DOMAIN,
        DEDEKIND_IN_IDEAL_POW_VALUATION, DEDEKIND_KUMMER_Q, DEDEKIND_RING_OF_INTEGERS,
        EXTENSION, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING,
        FIELD_INTEGER_MOD_RING, FINITE_NUMSEG_LT, FINITE_SING, FORALL_IN_IMAGE,
        FUN_EQ_COEFF, FUN_EQ_THM, HAS_SIZE, HAS_SIZE_FUNSPACE, HAS_SIZE_IMAGE_INJ,
        HAS_SIZE_NUMSEG_LT, IDEAL_GENERATED_EQ_0, IDEAL_PRODUCT_SING,
        IDEAL_VALUATION_PRINCIPAL_MUL, IDEAL_VALUATION_PRINCIPAL_POW, IMAGE_CLAUSES,
        INTEGER_MOD_RING_CHAR, INTEGER_MOD_RING_CLAUSES, INTEGER_RING,
        INTEGRAL_DOMAIN_MUL_EQ_0, INTEGRAL_DOMAIN_POW_EQ_0, INT_ABS_NUM,
        INT_DIVIDES_LE, INT_OF_NUM_EQ, INT_OF_NUM_LT, INT_POS, INT_REM_EQ_SELF,
        IN_DELETE, IN_ELIM_THM, IN_IDEAL_GENERATED_SELF, IN_IDEAL_GENERATED_SING,
        IN_IMAGE, IN_RING_IDEAL_LMUL, IN_RING_IDEAL_NEG, IN_RING_IDEAL_RMUL,
        IN_RING_IDEAL_SUB, IN_RING_IDEAL_SUM, IN_SING, IN_SUBRING_MUL, IN_SUBRING_POW,
        IN_SUBRING_SUM, IN_UNIV, LEFT_IMP_EXISTS_THM, LE_REFL, MEMBER_NOT_EMPTY,
        MONIC_POLY_VAR, MULT_CLAUSES, NOT_IMP, NUMBER_FIELD_DEGREE_POS,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q,
        NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q, .. } := D.core1
  let { NUM_OF_INT_OF_NUM, POLY_DEG_VAR, POLY_EXTEND_VAR, POLY_RING_CLAUSES,
        PRIME_GE_2, PRIME_IMP_NZ, QUOTIENT_RING_CARRIER, RAMIFICATION_INDEX_PRIME,
        RING_ADD, RING_COSET_EQ, RING_HOMOMORPHISM_INTEGER_RING_OF_INT,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET,
        RING_IRREDUCIBLE_POLY_VAR, RING_MUL, RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_IDEAL_NORM_INTEGER,
        RING_OF_INTEGERS_SUBRING, RING_OF_INTEGERS_SUBSET, RING_OF_INT_0,
        RING_OF_INT_1, RING_OF_INT_EQ_0, RING_OF_INT_EQ_0_CHAR_0,
        RING_OF_INT_IN_RING_OF_INTEGERS, RING_OF_INT_MUL, RING_OF_INT_OF_NUM,
        RING_OF_INT_SUB, RING_POLYNOMIAL, RING_POLYNOMIAL_VAR, RING_POW, RING_POW_ADD,
        RING_PRODUCT_SING, RING_SUB_RDISTRIB, RING_SUM, RING_SUM_DELETE, RING_SUM_EQ,
        RING_SUM_LMUL, RING_SUM_RING_OF_INTEGERS, RING_SUM_SUB,
        SUBRING_GENERATED_INDEX_COPRIME, SUBRING_GENERATED_INT_LINCOMB, SUBSET,
        SUC_SUB1, SURJECTIVE_IFF_INJECTIVE_GEN, TRIVIAL_RING_10, ideal_norm,
        int_divides, monic, num_WOP, number_field, poly_var, ring_divides, ring_setadd, .. } := D.core2
  let { IDEAL_VALUATION_RING_OF_INT_COPRIME, NUMBER_FIELD_EISENSTEIN_POW,
        NUMBER_FIELD_EISENSTEIN_VALUATION, .. } := BEisenstein01
  -- @@SCOPE END

  let NUMBER_FIELD_EISENSTEIN_INDEPENDENT ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q7 ← q r"~(n = 0) ==> n = SUC(n - 1)"
    let r8 ← ARITH_RULE q7
    let q9 ← q r"n = SUC(n - 1)"
    let q10 ← q r"n - 1"
    let q11 ← q r"a:A"
    let q12 ← q r"P:A->bool"
    let q13 ← q r"ring_of_integers k:A ring"
    let v14 ← ISPECL [q13, q12, q11, q10] IDEAL_VALUATION_PRINCIPAL_POW
    let q15 ← q r"ring_pow k a (n - 1):A"
    let q16 ← q r"ring_of_int k ((c:num->int) j):A"
    let q17 ← q r"P:A->bool"
    let q18 ← q r"ring_of_integers k:A ring"
    let v19 ← ISPECL [q18, q17, q16, q15] IDEAL_VALUATION_PRINCIPAL_MUL
    let q30 ← q r"e:num"
    let q31 ← q r"ring_mul k (ring_of_int k ((c:num->int) j))
                      (ring_pow k a (n - 1)):A"
    let q32 ← q r"P:A->bool"
    let q33 ← q r"ring_of_integers k:A ring"
    let v34 ← ISPECL [q33, q32, q31, q30] DEDEKIND_IN_IDEAL_POW_VALUATION
    let q35 ← q r"e <= ideal_valuation (ring_of_integers k) P
           (ideal_generated (ring_of_integers k)
              {ring_mul k (ring_of_int k ((c:num->int) j))
                 (ring_pow k a (n - 1)):A})"
    let q36 ← q r"n - 1"
    let q37 ← q r"a:A"
    let q38 ← q r"ring_of_integers k:A ring"
    let v39 ← ISPECL [q38, q37, q36] INTEGRAL_DOMAIN_POW_EQ_0
    let q40 ← q r"ring_pow k a (n - 1):A"
    let q41 ← q r"ring_of_int k ((c:num->int) j):A"
    let q42 ← q r"ring_of_integers k:A ring"
    let v43 ← ISPECL [q42, q41, q40] INTEGRAL_DOMAIN_MUL_EQ_0
    let q44 ← q r"~(ring_pow k a (n - 1) = ring_0 (k:A ring)) /\
    ~(ring_mul k (ring_of_int k ((c:num->int) j)) (ring_pow k a (n - 1)) =
      ring_0 (k:A ring))"
    let q45 ← q r"ring_sub r y (ring_sub r y x) = (x:A)"
    let r46 ← RING_RULE q45
    let q47 ← q r"(a:A) = b ==> a IN s ==> b IN s"
    let r48 ← MESON [] q47
    let q49 ← q r"ring_sum k ({i | i < n} DELETE j)
                      (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                             (ring_pow k (a:A) (i + (n - 1 - j))))"
    let q50 ← q r"ring_sum k {i | i < n}
                      (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                             (ring_pow k (a:A) (i + (n - 1 - j))))"
    let q51 ← q r"ideal_generated (ring_of_integers k) {ring_of_num k p:A}"
    let q52 ← q r"ring_of_integers k:A ring"
    let v53 ← ISPECL [q52, q51, q50, q49] IN_RING_IDEAL_SUB
    let q54 ← q r"j + (n - 1 - j) = n - 1"
    let q55 ← q r"j:num"
    let q56 ← q r"{i:num | i < n}"
    let q57 ← q r"\i. ring_mul k (ring_of_int k ((c:num->int) i))
                      (ring_pow k (a:A) (i + (n - 1 - j)))"
    let q58 ← q r"k:A ring"
    let v59 ← ISPECL [q58, q57, q56, q55] RING_SUM_DELETE
    let q60 ← q r"ring_pow k (a:A) (i - j - 1)"
    let q61 ← q r"ring_pow k a n:A"
    let q62 ← q r"ideal_generated (ring_of_integers k)
                        {ring_of_num k p:A}"
    let q63 ← q r"ring_of_integers k:A ring"
    let v64 ← ISPECL [q63, q62, q61, q60] IN_RING_IDEAL_RMUL
    let q65 ← q r"ring_mul k (ring_pow k a n)
                        (ring_pow k (a:A) (i - j - 1))"
    let q66 ← q r"ring_of_int k ((c:num->int) i):A"
    let q67 ← q r"ideal_generated (ring_of_integers k)
                        {ring_of_num k p:A}"
    let q68 ← q r"ring_of_integers k:A ring"
    let v69 ← ISPECL [q68, q67, q66, q65] IN_RING_IDEAL_LMUL
    let v70 ← GSYM RING_POW_ADD
    let q71 ← q r"ring_pow k a (i + (n - 1 - j)) =
        ring_mul k (ring_pow k a n) (ring_pow k (a:A) (i - j - 1))"
    let q72 ← q r"ring_mul r (ring_mul r x y) z =
          ring_mul r x (ring_mul r y (z:A))"
    let r73 ← RING_RULE q72
    let q74 ← q r"ring_mul k (ring_of_int k t) (ring_pow k a (i + (n - 1 - j))):A"
    let v75 ← GSYM RING_OF_INT_OF_NUM
    let q76 ← q r"t:int"
    let q77 ← q r"i:num"
    let q78 ← q r"i:num < j"
    let v79 ← ASSUME q78
    let q80 ← q r"i:num < j"
    let q81 ← q r"i:num"
    let q82 ← q r"ring_sum k ({i | i < n} DELETE j)
        (\i. ring_mul k (ring_of_int k ((c:num->int) i))
               (ring_pow k a (i + (n - 1 - j)))) IN
      ideal_generated (ring_of_integers k) {ring_of_num k p:A}"
    let q83 ← q r"ring_sum k {i | i < n}
                          (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                                 (ring_pow k (a:A) i))"
    let q84 ← q r"ring_pow k a (n - 1 - j):A"
    let q85 ← q r"ideal_generated (ring_of_integers k)
                          {ring_of_num k p:A}"
    let q86 ← q r"ring_of_integers k:A ring"
    let v87 ← ISPECL [q86, q85, q84, q83] IN_RING_IDEAL_LMUL
    let q88 ← q r"ring_mul r c (ring_mul r x y) =
          ring_mul r y (ring_mul r c (x:A))"
    let r89 ← RING_RULE q88
    let q90 ← q r"i:num"
    let v91 ← GSYM RING_SUM_LMUL
    let q92 ← q r"ring_sum k {i | i < n}
          (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                 (ring_pow k a (i + (n - 1 - j)))) =
        ring_mul k (ring_pow k a (n - 1 - j))
          (ring_sum k {i | i < n}
             (\i. ring_mul k (ring_of_int k (c i)) (ring_pow k (a:A) i)))"
    let q93 ← q r"ring_sum k {i | i < n}
        (\i. ring_mul k (ring_of_int k ((c:num->int) i))
               (ring_pow k a (i + (n - 1 - j)))) IN
      ideal_generated (ring_of_integers k) {ring_of_num k p:A}"
    let q94 ← q r"(a:A) IN ring_carrier k"
    let q95 ← q r"!i. ring_mul k (ring_of_int k ((c:num->int) i))
            (ring_pow k a (i + (n - 1 - j))):A IN
          ring_carrier(ring_of_integers k)"
    let q96 ← q r"ring_mul k (ring_of_int k ((c:num->int) j)) (ring_pow k a (n - 1)):A IN
    ideal_generated (ring_of_integers k) {ring_of_num k p}"
    let q97 ← q r"(c:num->int) j"
    let q98 ← q r"p:num"
    let q99 ← q r"P:A->bool"
    let q100 ← q r"k:A ring"
    let v101 ← ISPECL [q100, q99, q98, q97] IDEAL_VALUATION_RING_OF_INT_COPRIME
    let q102 ← q r"j:num"
    let q103 ← q r"(!i:num. P i) <=> ~(?i. ~P i)"
    let r104 ← MESON [] q103
    let q105 ← q r"e:num"
    let q106 ← q r"ideal_generated (ring_of_integers k) {ring_of_num k p:A}"
    let q107 ← q r"P:A->bool"
    let q108 ← q r"ring_of_integers k:A ring"
    let v109 ← ISPECL [q108, q107, q106, q105] DEDEKIND_IDEAL_SUBSET_POW_VALUATION
    let q110 ← q r"ideal_generated (ring_of_integers k) {ring_of_num k p:A} SUBSET
    ideal_pow (ring_of_integers k) P e"
    let v111 ← GSYM RING_OF_INT_OF_NUM
    let q112 ← q r"(ring_of_num k p:A) IN ring_carrier(ring_of_integers k)"
    let q113 ← q r"~(P = {ring_0 (ring_of_integers k:A ring)})"
    let v114 ← GSYM RING_OF_INT_OF_NUM
    let q115 ← q r"~(ring_of_num k p = ring_0 (k:A ring))"
    let q116 ← q r"e = ideal_valuation (ring_of_integers k) P
          (ideal_generated (ring_of_integers k) {ring_of_num k p:A})"
    let q117 ← q r"w = ideal_valuation (ring_of_integers k) P
          (ideal_generated (ring_of_integers k) {a:A})"
    let q118 ← q r"n = poly_deg integer_ring (m:(1->num)->int)"
    let q119 ← q r"p:num"
    let q120 ← q r"P:A->bool"
    let q121 ← q r"ring_of_integers k:A ring"
    let v122 ← ISPECL [q121, q120, q119] RAMIFICATION_INDEX_PRIME
    let q123 ← q r"p:num"
    let q124 ← q r"P:A->bool"
    let q125 ← q r"k:A ring"
    let v126 ← ISPECL [q125, q124, q123] NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q
    let q127 ← q r"P:A->bool"
    let q128 ← q r"p:num"
    let q129 ← q r"m:(1->num)->int"
    let q130 ← q r"a:A"
    let q131 ← q r"k:A ring"
    let v132 ← ISPECL [q131, q130, q129, q128, q127] NUMBER_FIELD_EISENSTEIN_VALUATION
    let q133 ← q r"P:A->bool"
    let v134 ← GSYM MEMBER_NOT_EMPTY
    let q135 ← q r"p:num"
    let q136 ← q r"k:A ring"
    let v137 ← ISPECL [q136, q135] NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q
    let q138 ← q r"p:num"
    let q139 ← q r"m:(1->num)->int"
    let q140 ← q r"a:A"
    let q141 ← q r"k:A ring"
    let v142 ← ISPECL [q141, q140, q139, q138] NUMBER_FIELD_EISENSTEIN_POW
    let q143 ← q r"ring_carrier(ring_of_integers k) subring_of (k:A ring)"
    prove
      r"!(k:A ring) a m p c.
          number_field k /\ a IN ring_carrier k /\
          m IN ring_carrier(poly_ring integer_ring (:1)) /\
          monic integer_ring m /\
          poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
          prime p /\
          (!i. i < poly_deg integer_ring m ==> &p divides coeff i m) /\
          ~(&p pow 2 divides coeff 0 m) /\
          ring_sum k {i | i < poly_deg integer_ring m}
            (\i. ring_mul k (ring_of_int k (c i)) (ring_pow k a i)) IN
          ideal_generated (ring_of_integers k) {ring_of_num k p}
          ==> !i. i < poly_deg integer_ring m ==> &p divides c i"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_RING_OF_INTEGERS)) THEN SUBGOAL_THEN q143 ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING], ALL_TAC] THEN MP_TAC v142 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC v137 THEN ASM_REWRITE_TAC [v134, IN_ELIM_THM] THEN DISCH_THEN ((X_CHOOSE_THEN q133 STRIP_ASSUME_TAC) o (CONJUNCT1 o CONJUNCT2)) THEN MP_TAC v132 THEN MP_TAC v126 THEN MP_TAC v122 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN STRIP_TAC THEN ABBREV_TAC q118 THEN ABBREV_TAC q117 THEN ABBREV_TAC q116 THEN SUBGOAL_THEN q115 ASSUME_TAC THENL [REWRITE_TAC [v114] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0, INT_OF_NUM_EQ, PRIME_IMP_NZ], ALL_TAC] THEN SUBGOAL_THEN q113 ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS] THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN q112 ASSUME_TAC THENL [REWRITE_TAC [v111, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN q110 ASSUME_TAC THENL [MP_TAC v109 THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0, RING_OF_INTEGERS, LE_REFL], ALL_TAC] THEN GEN_REWRITE_TAC id [r104] THEN REWRITE_TAC [NOT_IMP] THEN ONCE_REWRITE_TAC [num_WOP] THEN DISCH_THEN (X_CHOOSE_THEN q102 (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "min"))) THEN MP_TAC v101 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN SUBGOAL_THEN q96 ASSUME_TAC THENL [SUBGOAL_THEN q95 ASSUME_TAC THENL [ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN q94 ASSUME_TAC THENL [ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN q93 ASSUME_TAC THENL [SUBGOAL_THEN q92 SUBST1_TAC THENL [ASM_SIMP_TAC [v91, FINITE_NUMSEG_LT, RING_MUL, RING_OF_INT, RING_POW] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q90 THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_POW_ADD] THEN MATCH_MP_TAC r89 THEN ASM_SIMP_TAC [RING_OF_INT, RING_POW], MP_TAC v87 THEN ASM_SIMP_TAC [RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, IN_SUBRING_POW]], ALL_TAC] THEN SUBGOAL_THEN q82 ASSUME_TAC THENL [wPart lhand (rand o rand) RING_SUM_RING_OF_INTEGERS THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IN_DELETE, IN_ELIM_THM] THEN X_GEN_TAC q81 THEN STRIP_TAC THEN REWRITE_TAC [] THEN ASM_CASES_TAC q80 THENL [USE_THEN "min" (MP_TAC o ((← do let c := v79; pure (fun th => MP th c)) o (SPEC q77))) THEN ASM_REWRITE_TAC [int_divides] THEN DISCH_THEN (X_CHOOSE_THEN q76 SUBST1_TAC) THEN MATCH_MP_TAC IN_IDEAL_GENERATED_SING THEN REWRITE_TAC [ring_divides, RING_OF_INTEGERS] THEN REWRITE_TAC [RING_OF_INT_MUL, v75] THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS] THEN EXISTS_TAC q74 THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS] THEN MATCH_MP_TAC r73 THEN ASM_SIMP_TAC [RING_OF_INT, RING_POW], ALL_TAC] THEN SUBGOAL_THEN q71 SUBST1_TAC THENL [ASM_SIMP_TAC [v70] THEN AP_TERM_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC v69 THEN MP_TAC v64 THEN ASM_SIMP_TAC [RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN MP_TAC v59 THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL, RING_OF_INT, RING_POW], ALL_TAC] THEN REWRITE_TAC [] THEN SUBGOAL_THEN q54 (fun th => REWRITE_TAC [th]) THENL [ASM_ARITH_TAC, ALL_TAC] THEN DISCH_TAC THEN MP_TAC v53 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS, RING_IDEAL_IDEAL_GENERATED] THEN MATCH_MP_TAC r48 THEN MATCH_MP_TAC r46 THEN ASM_SIMP_TAC [RING_SUM, RING_MUL, RING_OF_INT, RING_POW], ALL_TAC] THEN SUBGOAL_THEN q44 STRIP_ASSUME_TAC THENL [MP_TAC v43 THEN MP_TAC v39 THEN ASM_SIMP_TAC [RING_OF_INTEGERS, DEDEKIND_IMP_INTEGRAL_DOMAIN, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN q35 MP_TAC THENL [MP_TAC v34 THEN ASM_SIMP_TAC [RING_OF_INTEGERS, IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (checkM (fun th => (do if ← (do if ← (do let z20 ← (do let z21 ← (pure th); pure (concl z21)); pure (is_comb z20)) then (do let z22 ← (do let z23 ← (do let z24 ← (pure th); pure (concl z24)); liftExcept (rator z23)); pure (is_comb z22)) else pure false) then (do let z29 ← (pure "SUBSET"); let z28 ← (do pure (Prod.fst (← (do let z25 ← (do pure (Prod.fst (← (do let z26 ← (do let z27 ← (pure th); pure (concl z27)); pure (strip_comb z26))))); liftExcept (dest_const z25))))); pure (z28 == z29)) else pure false))))) THEN FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN MP_TAC v19 THEN MP_TAC v14 THEN ASM_SIMP_TAC [RING_OF_INTEGERS, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN q9 MP_TAC THENL [MATCH_MP_TAC r8 THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN DISCH_THEN (fun th => tactic_of do pure (FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th' => (do if ← (do let z1 ← (do let z2 ← (pure th'); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"n * w:num"); let z5 ← (do let z3 ← (do let z4 ← (pure th'); pure (concl z4)); liftExcept (lhs z3)); pure (z5 == z6)) else pure false))))) THEN SUBST1_TAC th)) THEN REWRITE_TAC [MULT_CLAUSES, SUC_SUB1] THEN ASM_ARITH_TAC)

  let NUMBER_FIELD_EISENSTEIN_INDEX_COPRIME ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"ring_add r y (ring_sub r x y) = (x:A)"
    let r2 ← RING_RULE q1
    let q3 ← q r"ring_neg r (ring_sub r y x) = ring_sub r x (y:A)"
    let r4 ← RING_RULE q3
    let q5 ← q r"(a:A) = b ==> a IN s ==> b IN s"
    let r6 ← MESON [] q5
    let q7 ← q r"ring_sub k
         (ring_sum k {i | i < n}
            (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                   (ring_pow k (a:A) i))) x"
    let q8 ← q r"J:A->bool"
    let q9 ← q r"ring_of_integers k:A ring"
    let v10 ← ISPECL [q9, q8, q7] IN_RING_IDEAL_NEG
    let q11 ← q r"c:num->int"
    let q12 ← q r"ring_sub k x
      (ring_sum k {i | i < n}
         (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                (ring_pow k (a:A) i)))"
    let q13 ← q r"ring_sum k {i | i < n}
      (\i. ring_mul k (ring_of_int k ((c:num->int) i))
             (ring_pow k (a:A) i))"
    let q14 ← q r"x:A"
    let q15 ← q r"ring_sum k {i | i < n}
       (\i. ring_mul k (ring_of_int k ((c:num->int) i))
              (ring_pow k (a:A) i))"
    let q16 ← q r"J:A->bool"
    let q17 ← q r"ring_of_integers k:A ring"
    let v18 ← ISPECL [q17, q16, q15, q14] RING_COSET_EQ
    let q19 ← q r"c:num->int"
    let q20 ← q r"x:A"
    let q21 ← q r"ring_coset (ring_of_integers k) J (x:A)"
    let q22 ← q r"ring_of_integers k:A ring"
    let v23 ← ISPEC q22 RING_ADD
    let q24 ← q r"z:A"
    let q25 ← q r"y:A"
    let q26 ← q r"x:A"
    let v27 ← GSYM INT_OF_NUM_LT
    let q28 ← q r"v:num < p"
    let q29 ← q r"u:num < p"
    let q30 ← q r"v:num"
    let v31 ← SPEC q30 INT_POS
    let q32 ← q r"u:num"
    let v33 ← SPEC q32 INT_POS
    let q34 ← q r"u:num"
    let q35 ← q r"v:num"
    let q36 ← q r"i:num"
    let q37 ← q r"i:num < n"
    let v38 ← ASSUME q37
    let q39 ← q r"i:num"
    let q40 ← q r"i:num < n"
    let v41 ← ASSUME q40
    let q42 ← q r"i:num"
    let v43 ← GSYM RING_SUM_SUB
    let q44 ← q r"(a:A) IN ring_carrier k"
    let q45 ← q r"(a:A) = b ==> a IN s ==> b IN s"
    let r46 ← MESON [] q45
    let q61 ← q r"\i. (c:num->int) i - d i"
    let q62 ← q r"i:num"
    let q63 ← q r"i:num"
    let q64 ← q r"i:num < n"
    let q65 ← q r"i:num"
    let q66 ← q r"ring_sum k {i | i < n}
         (\i. ring_mul k (ring_of_int k ((d:num->int) i))
                (ring_pow k (a:A) i))"
    let q67 ← q r"ring_sum k {i | i < n}
         (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                (ring_pow k (a:A) i))"
    let q68 ← q r"J:A->bool"
    let q69 ← q r"ring_of_integers k:A ring"
    let v70 ← ISPECL [q69, q68, q67, q66] RING_COSET_EQ
    let q71 ← q r"d:num->int"
    let q72 ← q r"c:num->int"
    let q73 ← q r"q /\ (p ==> r) ==> (p <=> q) ==> r"
    let r74 ← TAUT q73
    let q75 ← q r"ring_sum k {i | i < n}
      (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                       (ring_pow k (a:A) i))"
    let q76 ← q r"c:num->int"
    let q77 ← q r"\c:num->int. ring_coset (ring_of_integers k) J
                    (ring_sum k {i | i < n}
                       (\i. ring_mul k (ring_of_int k (c i))
                              (ring_pow k (a:A) i)))"
    let q78 ← q r"ring_carrier(quotient_ring (ring_of_integers k) (J:A->bool))"
    let q79 ← q r"D:(num->int)->bool"
    let v80 ← ISPECL [q79, q78, q77] SURJECTIVE_IFF_INJECTIVE_GEN
    let q81 ← q r"(D:(num->int)->bool) HAS_SIZE p EXP n"
    let q82 ← q r"D = {c:num->int | (!i. i IN {i | i < n} ==> c i IN IMAGE (&) {j | j < p}) /\
                      (!i. ~(i IN {i | i < n}) ==> c i = &0)}"
    let q83 ← q r"&p:int"
    let q84 ← q r"k:A ring"
    let v85 ← ISPECL [q84, q83] RING_OF_INTEGERS_IDEAL_NORM_INTEGER
    let q86 ← q r"\s:A->bool. ring_of_int k (&p):A IN s"
    let v87 ← GSYM RING_OF_INT_OF_NUM
    let q88 ← q r"ring_carrier(quotient_ring (ring_of_integers k) (J:A->bool))
    HAS_SIZE p EXP n"
    let q89 ← q r"!c. ring_sum k {i | i < n}
          (\i. ring_mul k (ring_of_int k (c i)) (ring_pow k a i)) IN
        ring_carrier(ring_of_integers k:A ring)"
    let q90 ← q r"ring_ideal (ring_of_integers k) (J:A->bool)"
    let q91 ← q r"J = ideal_generated (ring_of_integers k) {ring_of_num k p:A}"
    let q92 ← q r"p:num"
    let q93 ← q r"m:(1->num)->int"
    let q94 ← q r"a:A"
    let q95 ← q r"k:A ring"
    let v96 ← ISPECL [q95, q94, q93, q92] NUMBER_FIELD_EISENSTEIN_INDEPENDENT
    let q97 ← q r"m:(1->num)->int"
    let q98 ← q r"a:A"
    let q99 ← q r"k:A ring"
    let v100 ← ISPECL [q99, q98, q97] SUBRING_GENERATED_INT_LINCOMB
    let q101 ← q r"p:num"
    let q102 ← q r"m:(1->num)->int"
    let q103 ← q r"a:A"
    let q104 ← q r"k:A ring"
    let v105 ← ISPECL [q104, q103, q102, q101] NUMBER_FIELD_EISENSTEIN_POW
    let q106 ← q r"!x:A. x IN ring_carrier(ring_of_integers k) ==> x IN ring_carrier k"
    let q107 ← q r"ring_carrier(ring_of_integers k) subring_of (k:A ring)"
    let q114 ← q r"n = poly_deg integer_ring (m:(1->num)->int)"
    prove
      r"!(k:A ring) a m p.
          number_field k /\ a IN ring_carrier k /\
          m IN ring_carrier(poly_ring integer_ring (:1)) /\
          monic integer_ring m /\
          poly_deg integer_ring m =
          extension_degree (subfield_generated k {ring_0 k},k) I /\
          poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
          prime p /\
          (!i. i < poly_deg integer_ring m ==> &p divides coeff i m) /\
          ~(&p pow 2 divides coeff 0 m)
          ==> ring_setadd (ring_of_integers k)
                (ring_carrier(subring_generated k {a}))
                (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
              ring_carrier(ring_of_integers k)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC q114 THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do if ← (do let z108 ← (do let z109 ← (pure th); pure (concl z109)); pure (is_eq z108)) then (do let z113 ← (q r"n:num"); let z112 ← (do let z110 ← (do let z111 ← (pure th); pure (concl z111)); liftExcept (lhs z110)); pure (z112 == z113)) else pure false))))) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SUBGOAL_THEN q107 ASSUME_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS_SUBRING], ALL_TAC] THEN SUBGOAL_THEN q106 (LABEL_TAC "sub") THENL [MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC v105 THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN MP_TAC v100 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC v96 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (LABEL_TAC "ind") THEN ABBREV_TAC q91 THEN SUBGOAL_THEN q90 ASSUME_TAC THENL [EXPAND_TAC "J" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN SUBGOAL_THEN q89 ASSUME_TAC THENL [GEN_TAC THEN MATCH_MP_TAC IN_SUBRING_SUM THEN ASM_SIMP_TAC [IN_SUBRING_MUL, IN_SUBRING_POW, RING_OF_INT_IN_RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN q88 ASSUME_TAC THENL [REWRITE_TAC [HAS_SIZE] THEN CONJ_TAC THENL [MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "J" THEN REWRITE_TAC [v87] THEN DISCH_THEN (MP_TAC o (AP_TERM q86)) THEN REWRITE_TAC [IN_IDEAL_GENERATED_SELF, IN_SING, RING_OF_INT_IN_RING_OF_INTEGERS] THEN ASM_SIMP_TAC [RING_OF_INT_EQ_0_CHAR_0, INT_OF_NUM_EQ, PRIME_IMP_NZ], MP_TAC v85 THEN ASM_SIMP_TAC [INT_OF_NUM_EQ, PRIME_IMP_NZ, RING_OF_INT_OF_NUM, INT_ABS_NUM, NUM_OF_INT_OF_NUM] THEN REWRITE_TAC [ideal_norm]], ALL_TAC] THEN ABBREV_TAC q82 THEN SUBGOAL_THEN q81 ASSUME_TAC THENL [EXPAND_TAC "D" THEN MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN REWRITE_TAC [HAS_SIZE_NUMSEG_LT] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN REWRITE_TAC [HAS_SIZE_NUMSEG_LT, INT_OF_NUM_EQ] THEN MESON_TAC [], ALL_TAC] THEN MP_TAC v80 THEN ANTS_TAC THENL [RULE_ASSUM_TAC (REWRITE_RULE [HAS_SIZE]) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC q76 THEN DISCH_TAC THEN EXISTS_TAC q75 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC r74 THEN CONJ_TAC THENL [MAP_EVERY X_GEN_TAC [q72, q71] THEN EXPAND_TAC "D" THEN REWRITE_TAC [IN_ELIM_THM, IN_IMAGE] THEN DISCH_THEN (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "c1") (LABEL_TAC "c2")) (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "d1") (LABEL_TAC "d2")) ASSUME_TAC)) THEN MP_TAC v70 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC q65 THEN ASM_CASES_TAC q64 THENL [ALL_TAC, USE_THEN "c2" (MP_TAC o (SPEC q63)) THEN USE_THEN "d2" (MP_TAC o (SPEC q62)) THEN ASM_SIMP_TAC []] THEN USE_THEN "ind" (MP_TAC o (SPEC q61)) THEN ANTS_TAC THENL [EXPAND_TAC "J" THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z47 ← (do let z48 ← (pure th); pure (concl z48)); canM (fun z49 => (do let z50 ← (pure z49); find_termM (fun z51 => (do let z53 ← (pure z51); let z52 ← (q r"J:A->bool"); pure (z52 == z53))) z50)) z47) then (do let z54 ← (do let z55 ← (pure th); pure (concl z55)); canM (fun z56 => (do let z57 ← (pure z56); find_termM (fun z58 => (do let z60 ← (pure z58); let z59 ← (q r"ring_sub:(A ring)->A->A->A"); pure (z59 == z60))) z57)) z54) else pure false)))) THEN EXPAND_TAC "J" THEN MATCH_MP_TAC r46 THEN SUBGOAL_THEN q44 ASSUME_TAC THENL [USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [v43, FINITE_NUMSEG_LT, RING_MUL, RING_OF_INT, RING_POW] THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN REWRITE_TAC [RING_OF_INT_SUB] THEN ASM_SIMP_TAC [RING_SUB_RDISTRIB, RING_OF_INT, RING_POW], DISCH_THEN (MP_TAC o (SPEC q42)) THEN ASM_REWRITE_TAC []] THEN USE_THEN "c1" (MP_TAC o ((← do let c := v41; pure (fun th => MP th c)) o (SPEC q39))) THEN USE_THEN "d1" (MP_TAC o ((← do let c := v38; pure (fun th => MP th c)) o (SPEC q36))) THEN DISCH_THEN (X_CHOOSE_THEN q35 STRIP_ASSUME_TAC) THEN DISCH_THEN (X_CHOOSE_THEN q34 STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (MATCH_MP INT_DIVIDES_LE)) THEN MP_TAC v33 THEN MP_TAC v31 THEN UNDISCH_TAC q29 THEN UNDISCH_TAC q28 THEN REWRITE_TAC [v27] THEN INT_ARITH_TAC, ALL_TAC] THEN DISCH_TAC THEN REWRITE_TAC [ring_setadd, EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC q26 THEN EQ_TAC THENL [REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [q25, q24] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN MP_TAC v23 THEN REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM (MATCH_MP_TAC o ((REWRITE_RULE [SUBSET]) o (MATCH_MP RING_IDEAL_IMP_SUBSET))) THEN ASM_REWRITE_TAC [], DISCH_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC q21)) THEN ANTS_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN REWRITE_TAC [IN_ELIM_THM] THEN EXISTS_TAC q20 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN q19 (STRIP_ASSUME_TAC o BETA_RULE)) THEN MP_TAC v18 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_TAC THEN EXISTS_TAC q13 THEN EXISTS_TAC q12 THEN REPEAT CONJ_TAC THENL [EXISTS_TAC q11 THEN REWRITE_TAC [IN_UNIV], MP_TAC v10 THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN MATCH_MP_TAC r6 THEN MATCH_MP_TAC r4 THEN CONJ_TAC THEN USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC [], CONV_TAC SYM_CONV THEN MATCH_MP_TAC r2 THEN CONJ_TAC THEN USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC []])

  let NUMBER_FIELD_EISENSTEIN ← prove
    r"!(k:A ring) a m p.
        number_field k /\ a IN ring_carrier k /\
        m IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring m /\
        poly_deg integer_ring m =
        extension_degree (subfield_generated k {ring_0 k},k) I /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
        prime p /\
        (!i. i < poly_deg integer_ring m ==> &p divides coeff i m) /\
        ~(&p pow 2 divides coeff 0 m)
        ==> prime_ideal (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p, a}) /\
            {P | prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P} =
            {ideal_generated (ring_of_integers k) {ring_of_num k p, a}} /\
            ideal_generated (ring_of_integers k) {ring_of_num k p} =
            ideal_pow (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p, a})
              (poly_deg integer_ring m) /\
            ramification_index (integer_ring,ring_of_integers k)
              (ring_of_int k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p, a}) =
            poly_deg integer_ring m /\
            residue_degree (integer_ring,ring_of_integers k) (ring_of_int k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p, a}) =
            1 /\
            ring_setadd (ring_of_integers k)
              (ring_carrier(subring_generated k {a}))
              (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
            ring_carrier(ring_of_integers k)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"m:(1->num)->int"), (← q r"p:num")] NUMBER_FIELD_EISENSTEIN_INDEX_COPRIME) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"n = poly_deg integer_ring (m:(1->num)->int)") THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"n:num"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (lhs z3)); pure (z5 == z6)) else pure false))))) THEN SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL [MP_TAC (← ISPEC (← q r"k:A ring") NUMBER_FIELD_DEGREE_POS) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"field(integer_mod_ring p)") ASSUME_TAC THENL [ASM_REWRITE_TAC [FIELD_INTEGER_MOD_RING], ALL_TAC] THEN SUBGOAL_THEN (← q r"poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
      (poly_var (integer_mod_ring p) one) = (a:A)") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"poly_var (integer_mod_ring p) one = poly_var integer_ring one") SUBST1_TAC THENL [REWRITE_TAC [poly_var, INTEGER_MOD_RING_CLAUSES, INTEGER_RING] THEN SUBGOAL_THEN (← q r"&1 rem &p = &1") (fun th => REWRITE_TAC [th]) THEN REWRITE_TAC [INT_REM_EQ_SELF, INT_ABS_NUM, INT_OF_NUM_LT, INT_POS, INT_OF_NUM_EQ] THEN FIRST_ASSUM (MP_TAC o (MATCH_MP PRIME_GE_2)) THEN ARITH_TAC, MATCH_MP_TAC POLY_EXTEND_VAR THEN ASM_REWRITE_TAC [RING_HOMOMORPHISM_INTEGER_RING_OF_INT]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_int (integer_mod_ring p) o (m:(1->num)->int) =
    poly_pow (integer_mod_ring p) (poly_var (integer_mod_ring p) one) n") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM FUN_EQ_COEFF), COEFF_COMPOSE, COEFF_POLY_VARPOW] THEN X_GEN_TAC (← q r"d:num") THEN ASM_CASES_TAC (← q r"d:num < n") THENL [SUBGOAL_THEN (← q r"~(d:num = n)") (fun th => REWRITE_TAC [th]) THENL [ASM_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [RING_OF_INT_EQ_0, INTEGER_MOD_RING_CHAR] THEN ASM_SIMP_TAC [], ALL_TAC] THEN ASM_CASES_TAC (← q r"d:num = n") THENL [UNDISCH_TAC (← q r"monic integer_ring (m:(1->num)->int)") THEN ASM_REWRITE_TAC [monic, INTEGER_RING] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [RING_OF_INT_1], ALL_TAC] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"integer_ring"), (← q r"m:(1->num)->int"), (← q r"d:num")] COEFF_ABOVE_DEG) THEN ASM_REWRITE_TAC [RING_POLYNOMIAL] THEN ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [INTEGER_RING] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [RING_OF_INT_0], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"p:num"), (← q r"m:(1->num)->int"), (← q r"{0}"), (← q r"\i:num. poly_var (integer_mod_ring p) one"), (← q r"\i:num. (n:num)"), (← q r"\i:num. ideal_generated (ring_of_integers k) {ring_of_num k p, a:A}")] DEDEKIND_KUMMER_Q) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [FINITE_SING, IN_SING] THEN REPEAT CONJ_TAC THENL [GEN_TAC THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN REWRITE_TAC [(← GSYM RING_POLYNOMIAL), RING_POLYNOMIAL_VAR, MONIC_POLY_VAR] THEN MATCH_MP_TAC RING_IRREDUCIBLE_POLY_VAR THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, IN_UNIV], MESON_TAC [], SUBGOAL_THEN (← q r"ring_pow (poly_ring (integer_mod_ring p) (:1))
          (poly_var (integer_mod_ring p) one) n IN
        ring_carrier(poly_ring (integer_mod_ring p) (:1))") ASSUME_TAC THENL [MATCH_MP_TAC RING_POW THEN REWRITE_TAC [(← GSYM RING_POLYNOMIAL), RING_POLYNOMIAL_VAR], ASM_REWRITE_TAC [RING_PRODUCT_SING] THEN REWRITE_TAC [POLY_RING_CLAUSES]]], ALL_TAC] THEN REWRITE_TAC [IN_SING, IMAGE_CLAUSES] THEN SIMP_TAC [IDEAL_PRODUCT_SING, RING_IDEAL_IDEAL_POW] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o (SPEC (← q r"0"))))) THEN REWRITE_TAC [POLY_DEG_VAR] THEN SUBGOAL_THEN (← q r"~(ring_1 (integer_mod_ring p) = ring_0 (integer_mod_ring p))") (fun th => REWRITE_TAC [th]) THENL [ASM_MESON_TAC [FIELD_IMP_NONTRIVIAL_RING, TRIVIAL_RING_10], ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC [])

  let NUMBER_FIELD_EISENSTEIN_INDEX ← prove
    r"!(k:A ring) a m p N.
        number_field k /\ a IN ring_carrier k /\
        m IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring m /\
        poly_deg integer_ring m =
        extension_degree (subfield_generated k {ring_0 k},k) I /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
        prime p /\
        (!i. i < poly_deg integer_ring m ==> &p divides coeff i m) /\
        ~(&p pow 2 divides coeff 0 m) /\
        {ring_coset (ring_of_integers k)
           (ring_carrier(subring_generated k {a})) x |
         x | x IN ring_carrier(ring_of_integers k)} HAS_SIZE N
        ==> ~(p divides N)"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"p:num"), (← q r"N:num")] SUBRING_GENERATED_INDEX_COPRIME) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"m:(1->num)->int"), (← q r"p:num")] NUMBER_FIELD_EISENSTEIN_INDEX_COPRIME) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"a:A"), (← q r"m:(1->num)->int"), (← q r"p:num")] NUMBER_FIELD_EISENSTEIN_POW) THEN ASM_SIMP_TAC [])

  -- @@RETURN BEGIN
  return { NUMBER_FIELD_EISENSTEIN_INDEPENDENT, NUMBER_FIELD_EISENSTEIN_INDEX_COPRIME,
           NUMBER_FIELD_EISENSTEIN, NUMBER_FIELD_EISENSTEIN_INDEX }
  -- @@RETURN END

end HolANT.Eisenstein
