/- ========================================================================= -/
/- ANT: The exact exponent of the different and of the discriminant        -/
/- ========================================================================= -/
/- File: HolANT/DifferentExponent.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/different_exponent.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antdifferentexponentdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/products.ml, ANT/ideal_arith.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/ideal_norm.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/trace_form.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/classgroup.ml, ANT/relative_split.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/different.ml, ANT/relative_degree.ml, ANT/different_extension.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.DifferentExponent fills them).

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
import HolANT.IdealArith
import HolANT.Algmisc
import HolANT.Integral
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
import HolANT.PrimeSplit
import HolANT.NormIndex
import HolANT.Discriminant
import HolANT.TraceForm
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.Classgroup
import HolANT.RelativeSplit
import HolANT.NfValuation
import HolANT.Integrality
import HolANT.Different
import HolANT.RelativeDegree
import HolANT.DifferentExtension

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
open HolANT.PrimeSplit
open HolANT.NormIndex
open HolANT.Discriminant
open HolANT.TraceForm
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.Classgroup
open HolANT.RelativeSplit
open HolANT.NfValuation
open HolANT.Integrality
open HolANT.Different
open HolANT.RelativeDegree
open HolANT.DifferentExtension

namespace HolANT.DifferentExponent

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD_CLAUSES ADD_MULT_LT_MULT ALGEBRA_TRACE_0
   ALGEBRA_TRACE_FINITE_FIELD_NONZERO ALGEBRA_TRACE_FREE_BASIS
   ALGEBRA_TRACE_ISOMORPHIC_IMAGE ALGEBRA_TRACE_NILPOTENT_INTEGER_MOD
   ALGEBRA_TRACE_NORM_IN_CARRIER ALGEBRA_TRACE_PROD_RING
   ALGEBRA_TRACE_QUOTIENT_RING_INTEGER_MOD AND_FORALL_THM ARITH_EQ
   BASIS_COORDINATES BASIS_COORDINATES_UNIQUE CARD_NUMSEG_LT COMAXIMAL_IDEAL_POW
   CONTRAPOS_THM DEDEKIND_IDEAL_FACTORIZATION DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT
   DEDEKIND_IDEAL_PROD_SUBSET_CANCEL DEDEKIND_IDEAL_SUBSET_POW_VALUATION
   DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL DEDEKIND_PRIME_IDEAL_UNIFORMIZER
   DEDEKIND_RING_OF_INTEGERS DEDEKIND_UNIFORMIZER_CRITERION DIVIDES_0
   DIVIDES_ZERO DIVISION DIV_LT DIV_MULT_ADD EMPTY_GSPEC EQ_TRANS
   EXISTS_IN_GSPEC EXISTS_UNIQUE_THM EXP_EQ_0 EXTENSION
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_INTEGER_MOD_RING FIELD_QUOTIENT_RING
   FIELD_SUBFIELD_GENERATED FINITE_INTEGER_MOD_RING FINITE_NUMSEG_LT
   FINITE_QUOTIENT_RING_MONO FINITE_RESTRICT FORALL_AND_THM FORALL_IN_GSPEC
   FREE_BASIS_EXISTS FREE_BASIS_HAS_SIZE FREE_BASIS_QUOTIENT_RING_INTEGER_MOD
   FUN_EQ_THM HAS_SIZE IDEAL_GENERATED_INC IDEAL_GENERATED_MINIMAL
   IDEAL_NORM_FACTORIZATION IDEAL_POW_0 IDEAL_POW_1 IDEAL_POW_ANTIMONO
   IDEAL_POW_SUC IDEAL_PROD_COMAXIMAL IDEAL_PROD_COMM IDEAL_PROD_MINIMAL
   IDEAL_PROD_MONO IDEAL_VALUATION_EQ_0 INDEX_EXP INDEX_NPRODUCT INDEX_PRIME
   INTEGER_MOD_RING_CARRIER_REM INTEGER_MOD_RING_CHAR INTEGER_MOD_RING_CLAUSES
   INTEGRAL_DOMAIN_MUL_EQ_0 INT_ADD_LID INT_REM_EQ_0 IN_ELIM_THM IN_RING_IDEAL_0
   IN_RING_IDEAL_ADD IN_RING_IDEAL_LMUL IN_RING_IDEAL_NEG IN_RING_IDEAL_RMUL
   IN_RING_IDEAL_SUB IN_RING_IDEAL_SUB_SUM_RESTRICT IN_SING IN_SUBRING_1
   IN_SUBRING_NUM LE_0 LE_MULT_LCANCEL LE_REFL LT LT_IMP_LE LT_MULT_LCANCEL
   MAXIMAL_IDEAL_COMAXIMAL MOD_LT MOD_LT_EQ MOD_MULT_ADD MULT_CLAUSES : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (MULT_EQ_0 MUL_MATRIX_IN_CARRIER NOT_FORALL_THM NOT_IMP NSUM_EQ
   NSUM_EQ_SUPERSET NSUM_LE NSUM_LT NSUM_SUPERSET NUMBER_FIELD_CODIFFERENT_DIV
   NUMBER_FIELD_CODIFFERENT_DIV_NUM NUMBER_FIELD_DIFFERENT_NONZERO
   NUMBER_FIELD_DIFFERENT_SUBSET_RAMIFICATION NUMBER_FIELD_IDEAL_NORM_DIFFERENT
   NUMBER_FIELD_IMP_FIELD NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q PAIR_EQ
   PRIME_IMP_NZ PRIME_IMP_RING_IDEAL QUOTIENT_RING_0 QUOTIENT_RING_CARRIER
   QUOTIENT_RING_LINCOMB_LIFT QUOTIENT_RING_MUL RAMIFICATION_INDEX_PRIME
   RAMIFICATION_INDEX_PRIME_SUBFIELD RDIV_LT_EQ RING_0 RING_1 RING_ADD_RDISTRIB
   RING_ADD_RZERO RING_CHAR_QUOTIENT_RING_DIVIDES RING_COSET_EQ
   RING_COSET_EQ_IDEAL RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING
   RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT RING_HOMOMORPHISM_RING_COSET
   RING_HOMOMORPHISM_RING_OF_INT RING_HOMOMORPHISM_SUBFIELD_INCLUSION
   RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_POW RING_IDEAL_IDEAL_QUOTIENT
   RING_IDEAL_IMP_SUBSET RING_IDEAL_NUMBER_FIELD_DIFFERENT
   RING_ISOMORPHISM_QUOTIENT_RING_INTER RING_MUL RING_MUL_IN_IDEAL_POW
   RING_MUL_IN_IDEAL_PROD RING_MUL_LZERO RING_MUL_RID RING_MUL_RZERO
   RING_MUL_SYM RING_OF_INT RING_OF_INTEGERS RING_OF_INTEGERS_FINITE_QUOTIENT
   RING_OF_INTEGERS_FREE RING_OF_INTEGERS_IDEAL_GENERATED_PRIME
   RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q RING_OF_INTEGERS_PRIME_IDEAL_ABOVE
   RING_OF_INTEGERS_SUBRING RING_OF_INTEGERS_SUBSET RING_OF_INT_ADD
   RING_OF_INT_CLAUSES RING_OF_INT_REM_CHAR_DIVIDES RING_OF_NUM RING_OF_NUM_EQ_0
   RING_POW RING_POW_1 RING_POW_IN_IDEAL_POW RING_SPAN_SELF RING_SUB
   RING_SUB_LDISTRIB RING_SUB_LZERO RING_SUB_RZERO RING_SUM RING_SUM_0
   RING_SUM_ADD RING_SUM_CLAUSES RING_SUM_CONST RING_SUM_EQ RING_SUM_LMUL
   RING_SUM_MOD_DIV RING_SUM_NUMSEG_DIV_SLICE SING_SUBSET SKOLEM_THM SUBSET
   SUBSET_REFL SUBSET_TRANS free_basis mul_matrix num_WF number_field o_THM
   ring_setadd ring_spanning : thm)
  deriving Inhabited

/-- What different_exponent.ml uses from Session besides theorems. -/
structure DifferentExponentDeps where
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
/- different_exponent.ml phrases from line 97 to 746                      -/
/- ---------------------------------------------------------------------- -/

structure DifferentExponent01 where
  -- @@FIELDS
  DEDEKIND_IDEAL_POW_LEVEL_SPAN : thm
  DEDEKIND_IDEAL_POW_LEVEL_COEFFS : thm
  DEDEKIND_IDEAL_POW_LEVEL_INDEPENDENT : thm
  DEDEKIND_QUOTIENT_POW_FREE_BASIS : thm
  DEDEKIND_ALGEBRA_TRACE_QUOTIENT_POW : thm
  FREE_BASIS_QUOTIENT_RING_PRIME_EXISTS : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDifferentExponent01 [HolBase] (D : DifferentExponentDeps) :
    ExceptT String IO DifferentExponent01 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON, MESON_TAC,
        RING_RULE, SET_RULE, SET_TAC, TAUT, .. } := D
  let { ADD_CLAUSES, ADD_MULT_LT_MULT, ALGEBRA_TRACE_FREE_BASIS,
        ALGEBRA_TRACE_NORM_IN_CARRIER, BASIS_COORDINATES, BASIS_COORDINATES_UNIQUE,
        CARD_NUMSEG_LT, DEDEKIND_PRIME_IDEAL_UNIFORMIZER,
        DEDEKIND_UNIFORMIZER_CRITERION, DIVISION, DIV_LT, DIV_MULT_ADD, EMPTY_GSPEC,
        EQ_TRANS, FIELD_INTEGER_MOD_RING, FINITE_INTEGER_MOD_RING, FINITE_NUMSEG_LT,
        FINITE_QUOTIENT_RING_MONO, FORALL_AND_THM, FORALL_IN_GSPEC, FREE_BASIS_EXISTS,
        FREE_BASIS_HAS_SIZE, FREE_BASIS_QUOTIENT_RING_INTEGER_MOD, HAS_SIZE,
        IDEAL_GENERATED_MINIMAL, IDEAL_POW_0, IDEAL_POW_1, IDEAL_POW_ANTIMONO,
        INTEGER_MOD_RING_CARRIER_REM, INTEGER_MOD_RING_CLAUSES, INT_ADD_LID,
        IN_ELIM_THM, IN_RING_IDEAL_0, IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL,
        IN_RING_IDEAL_NEG, IN_RING_IDEAL_RMUL, IN_RING_IDEAL_SUB,
        IN_RING_IDEAL_SUB_SUM_RESTRICT, LE_0, LE_REFL, LT, LT_IMP_LE, MOD_LT,
        MOD_LT_EQ, MOD_MULT_ADD, MULT_CLAUSES, .. } := D.core1
  let { MUL_MATRIX_IN_CARRIER, PRIME_IMP_NZ, PRIME_IMP_RING_IDEAL, QUOTIENT_RING_0,
        QUOTIENT_RING_CARRIER, QUOTIENT_RING_LINCOMB_LIFT, QUOTIENT_RING_MUL,
        RDIV_LT_EQ, RING_0, RING_ADD_RDISTRIB, RING_CHAR_QUOTIENT_RING_DIVIDES,
        RING_COSET_EQ, RING_COSET_EQ_IDEAL,
        RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING,
        RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IDEAL_POW, RING_IDEAL_IMP_SUBSET, RING_MUL, RING_MUL_IN_IDEAL_POW,
        RING_MUL_LZERO, RING_MUL_RZERO, RING_OF_INT, RING_OF_INT_ADD,
        RING_OF_INT_CLAUSES, RING_OF_INT_REM_CHAR_DIVIDES, RING_POW,
        RING_POW_IN_IDEAL_POW, RING_SPAN_SELF, RING_SUB, RING_SUB_LDISTRIB,
        RING_SUB_LZERO, RING_SUB_RZERO, RING_SUM, RING_SUM_0, RING_SUM_ADD,
        RING_SUM_CLAUSES, RING_SUM_CONST, RING_SUM_EQ, RING_SUM_LMUL, RING_SUM_MOD_DIV,
        RING_SUM_NUMSEG_DIV_SLICE, SING_SUBSET, SKOLEM_THM, SUBSET, SUBSET_REFL,
        free_basis, mul_matrix, num_WF, ring_spanning, .. } := D.core2
  -- @@SCOPE END

  let DEDEKIND_IDEAL_POW_LEVEL_SPAN ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"ring_mul r a (ring_mul r u v) = ring_mul r u (ring_mul r a (v:A))"
    let r2 ← RING_RULE q1
    let q3 ← q r"~(f = 0)"
    let q4 ← q r"j:num"
    let q5 ← q r"!j. (b:num->A) j IN ring_carrier r"
    let v6 ← ASSUME q5
    let q7 ← q r"(t:A) IN ring_carrier r"
    let v8 ← ASSUME q7
    let v9 ← GSYM RING_SUM_LMUL
    let v10 ← CONJUNCT1 RING_OF_INT_CLAUSES
    let v11 ← GSYM v10
    let q12 ← q r"s:num"
    let q13 ← q r"ring_sum r {s:num | s < f * e}
      (\s. if s DIV f = i
           then ring_mul r (ring_of_int r ((d0:num->int) (s MOD f)))
                  (ring_mul r (ring_pow r t (s DIV f)) ((b:num->A) (s MOD f)))
           else ring_0 r)"
    let q14 ← q r"ring_sub r (ring_sub r y w) z = ring_sub r y (ring_add r z (w:A))"
    let r15 ← RING_RULE q14
    let q16 ← q r"(a:A) = b ==> a IN s ==> b IN s"
    let r17 ← MESON [] q16
    let q24 ← q r"ring_sum r {s:num | s < f * e}
      (\s. ring_mul r
             (ring_of_int r ((c:num->int) s +
                (if s DIV f = i then (d0:num->int) (s MOD f) else &0)))
             (ring_mul r (ring_pow r t (s DIV f)) ((b:num->A) (s MOD f)))) =
    ring_add r
     (ring_sum r {s:num | s < f * e}
        (\s. ring_mul r (ring_of_int r (c s))
                      (ring_mul r (ring_pow r t (s DIV f)) (b (s MOD f)))))
     (ring_mul r (ring_pow r t i)
        (ring_sum r {j:num | j < f}
          (\j. ring_mul r (ring_of_int r (d0 j)) (b j))))"
    let q25 ← q r"~(s DIV f = i) /\ s DIV f < i + 1"
    let q26 ← q r"s:num"
    let q27 ← q r"\s. (c:num->int) s + (if s DIV f = i then (d0:num->int) (s MOD f)
                          else &0)"
    let q28 ← q r"c:num->int"
    let q29 ← q r"ring_sub r y (ring_mul r u z) =
        ring_add r (ring_sub r y (ring_mul r u a))
                   (ring_mul r u (ring_sub r a (z:A)))"
    let r30 ← RING_RULE q29
    let q31 ← q r"ring_add r (ring_sub r y (ring_mul r (ring_pow r t i) a))
        (ring_mul r (ring_pow r t i)
          (ring_sub r a
            (ring_sum r {j:num | j < f}
              (\j. ring_mul r (ring_of_int r ((d0:num->int) j))
                              ((b:num->A) j)))))"
    let q32 ← q r"!u w:A s. u = w /\ w IN s ==> u IN s"
    let r33 ← MESON [] q32
    let q34 ← q r"ring_sub r y
      (ring_mul r (ring_pow r t i)
        (ring_sum r {j:num | j < f}
          (\j. ring_mul r (ring_of_int r ((d0:num->int) j))
                          ((b:num->A) j))))"
    let q35 ← q r"i + 1:num"
    let q36 ← q r"d0:num->int"
    let q37 ← q r"g:num->A->bool"
    let q38 ← q r"b:num->A"
    let q39 ← q r"f:num"
    let q40 ← q r"P:A->bool"
    let q41 ← q r"r:A ring"
    let v42 ← ISPECL [q41, q40, q39, q38, q37, q36] QUOTIENT_RING_LINCOMB_LIFT
    let q43 ← q r"ring_sum r {j:num | j < f}
         (\j. ring_mul r (ring_of_int r ((d0:num->int) j)) ((b:num->A) j))"
    let q44 ← q r"a:A"
    let q45 ← q r"P:A->bool"
    let q46 ← q r"r:A ring"
    let v47 ← ISPECL [q46, q45, q44, q43] RING_COSET_EQ
    let q48 ← q r"ring_sub r a (ring_sum r {j:num | j < f}
                   (\j. ring_mul r (ring_of_int r ((d0:num->int) j))
                                   ((b:num->A) j))) IN P"
    let q49 ← q r"d0:num->int"
    let q50 ← q r"ring_coset r P (a:A)"
    let q51 ← q r"a:A"
    let q52 ← q r"y:A"
    let q53 ← q r"1:num"
    let q54 ← q r"i:num"
    let q55 ← q r"(y:A) IN ring_carrier r"
    let q56 ← q r"y:A"
    let q57 ← q r"i:num"
    let q58 ← q r"(y:A) IN ring_carrier r"
    let v59 ← CONJUNCT1 RING_OF_INT_CLAUSES
    let v60 ← GSYM v59
    let q61 ← q r"\s:num. &0:int"
    let q62 ← q r"!d i (y:A). i + d = e /\ y IN ideal_pow r P i
            ==> ?c:num->int.
                  (!s. s DIV f < i ==> c s = &0) /\
                  ring_sub r y
                   (ring_sum r {s:num | s < f * e}
                     (\s. ring_mul r (ring_of_int r (c s))
                           (ring_mul r (ring_pow r t (s DIV f))
                                       (b (s MOD f))))) IN
                  ideal_pow r P e"
    let q63 ← q r"t:A"
    let q64 ← q r"P:A->bool"
    let q65 ← q r"r:A ring"
    let v66 ← ISPECL [q65, q64, q63] DEDEKIND_UNIFORMIZER_CRITERION
    let q67 ← q r"(t:A) IN ring_carrier r"
    prove
      r"!r P (t:A) p f g (b:num->A) e.
          dedekind_domain r /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\
          t IN P /\ ~(t IN ideal_pow r P 2) /\
          free_basis (integer_mod_ring p,quotient_ring r P)
                     (ring_of_int (quotient_ring r P)) f g /\
          (!j. b j IN ring_carrier r) /\
          (!j. j < f ==> ring_coset r P (b j) = g j)
          ==> !i y. i <= e /\ y IN ideal_pow r P i
                    ==> ?c:num->int.
                          (!s. s DIV f < i ==> c s = &0) /\
                          ring_sub r y
                           (ring_sum r {s:num | s < f * e}
                             (\s. ring_mul r (ring_of_int r (c s))
                                   (ring_mul r (ring_pow r t (s DIV f))
                                               (b (s MOD f))))) IN
                          ideal_pow r P e"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN q67 ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC v66 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN ((LABEL_TAC "u1") o CONJUNCT1) THEN SUBGOAL_THEN q62 (fun th => tactic_of do pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN EXISTS_TAC (← q r"e - i:num") THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC)) THEN INDUCT_TAC THENL [REWRITE_TAC [ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN EXISTS_TAC q61 THEN REWRITE_TAC [] THEN REWRITE_TAC [v60] THEN SUBGOAL_THEN q58 ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET, RING_IDEAL_IDEAL_POW], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_LZERO, RING_MUL, RING_POW, RING_SUM_0, RING_SUB_RZERO] THEN ASM_MESON_TAC [], ALL_TAC] THEN POP_ASSUM (LABEL_TAC "ih") THEN MAP_EVERY X_GEN_TAC [q57, q56] THEN STRIP_TAC THEN SUBGOAL_THEN q55 ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET, RING_IDEAL_IDEAL_POW], ALL_TAC] THEN REMOVE_THEN "u1" (MP_TAC o (SPECL [q54, q53, q52])) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q51 STRIP_ASSUME_TAC) THEN FIRST_ASSUM (MP_TAC o ((SPEC q50) o (CONJUNCT1 o (CONJUNCT2 o (GEN_REWRITE_RULE id [free_basis]))))) THEN ANTS_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN ASM_MESON_TAC [], DISCH_THEN (X_CHOOSE_THEN q49 (ASSUME_TAC o CONJUNCT2))] THEN SUBGOAL_THEN q48 ASSUME_TAC THENL [MP_TAC v47 THEN ASM_REWRITE_TAC [RING_SUM] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC v42 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REMOVE_THEN "ih" (MP_TAC o (SPECL [q35, q34])) THEN ANTS_TAC THENL [CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN MATCH_MP_TAC r33 THEN EXISTS_TAC q31 THEN CONJ_TAC THENL [MATCH_MP_TAC r30 THEN ASM_SIMP_TAC [RING_POW, RING_SUM], ALL_TAC] THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, RING_POW_IN_IDEAL_POW, IDEAL_POW_1], DISCH_THEN (X_CHOOSE_THEN q28 STRIP_ASSUME_TAC)] THEN EXISTS_TAC q27 THEN REWRITE_TAC [] THEN CONJ_TAC THENL [X_GEN_TAC q26 THEN DISCH_TAC THEN SUBGOAL_THEN q25 STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC, ASM_SIMP_TAC [INT_ADD_LID]], ALL_TAC] THEN SUBGOAL_THEN q24 SUBST1_TAC THENL [ALL_TAC, FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z19 ← (do let z20 ← (pure th); pure (concl z20)); let z18 ← (q r"ideal_pow r (P:A->bool) e"); pure (free_in z18 z19)) then (do let z22 ← (do let z23 ← (pure th); pure (concl z23)); let z21 ← (q r"c:num->int"); pure (free_in z21 z22)) else pure false)))) THEN MATCH_MP_TAC r17 THEN MATCH_MP_TAC r15 THEN ASM_SIMP_TAC [RING_SUM, RING_MUL, RING_POW]] THEN REWRITE_TAC [RING_OF_INT_ADD] THEN ASM_SIMP_TAC [RING_ADD_RDISTRIB, RING_OF_INT, RING_MUL, RING_POW] THEN wPart lhand (lhand o rand) RING_SUM_ADD THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, RING_MUL, RING_POW, RING_OF_INT] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN TRANS_TAC EQ_TRANS q13 THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q12 THEN DISCH_TAC THEN REWRITE_TAC [] THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN REWRITE_TAC [v11] THEN ASM_SIMP_TAC [RING_MUL_LZERO, RING_MUL, RING_POW], ALL_TAC] THEN wPart lhand (lhand o rand) RING_SUM_NUMSEG_DIV_SLICE THEN ASM_SIMP_TAC [RING_MUL, RING_POW, RING_OF_INT] THEN ANTS_TAC THENL [ASM_ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN SIMP_TAC [v9, FINITE_NUMSEG_LT, RING_MUL, RING_OF_INT, RING_POW, v8, v6] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q4 THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN SUBGOAL_THEN q3 ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN ASM_SIMP_TAC [MOD_MULT_ADD, DIV_MULT_ADD, MOD_LT, DIV_LT, ADD_CLAUSES] THEN MATCH_MP_TAC r2 THEN ASM_SIMP_TAC [RING_OF_INT, RING_POW])

  let DEDEKIND_IDEAL_POW_LEVEL_COEFFS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(x:A) IN s ==> s SUBSET t ==> x IN t")
    let r7 ← RING_RULE (← q r"ring_mul r a (ring_mul r u v) = ring_mul r u (ring_mul r a (v:A))")
    prove
      r"!r P (t:A) f g (b:num->A) e (c:num->int) l a.
          dedekind_domain r /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\
          t IN P /\ ~(t IN ideal_pow r P 2) /\
          (!j. b j IN ring_carrier r) /\
          (!j. j < f ==> ring_coset r P (b j) = g j) /\
          l < e /\ (!s. s < f * e /\ s DIV f < l ==> c s = &0) /\
          a IN ring_carrier r /\
          ring_sub r (ring_mul r (ring_pow r t l) a)
            (ring_sum r {s:num | s < f * e}
              (\s. ring_mul r (ring_of_int r (c s))
                    (ring_mul r (ring_pow r t (s DIV f)) (b (s MOD f))))) IN
          ideal_pow r P (l + 1)
          ==> ring_coset r P a =
              ring_sum (quotient_ring r P) {j:num | j < f}
                (\j. ring_mul (quotient_ring r P)
                       (ring_of_int (quotient_ring r P) (c (j + f * l))) (g j))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"t:A")] DEDEKIND_UNIFORMIZER_CRITERION) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN ((LABEL_TAC "u2") o CONJUNCT2) THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"f:num"), (← q r"b:num->A"), (← q r"g:num->A->bool"), (← q r"\j. (c:num->int) (j + f * l)")] QUOTIENT_RING_LINCOMB_LIFT)) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN wPart Except.ok (lhand o rand) RING_COSET_EQ THEN ASM_SIMP_TAC [RING_SUM] THEN DISCH_THEN SUBST1_TAC THEN REMOVE_THEN "u2" (MP_TAC o (SPECL [(← q r"l:num"), (← q r"1:num"), (← q r"ring_sub r a
        (ring_sum r {j:num | j < f}
          (\j. ring_mul r (ring_of_int r ((c:num->int) (j + f * l)))
                          ((b:num->A) j)))")])) THEN ASM_SIMP_TAC [RING_SUB, RING_SUM, IDEAL_POW_1] THEN DISCH_THEN MATCH_MP_TAC THEN SUBGOAL_THEN (← q r"~(f = 0) \/ f = 0") STRIP_ASSUME_TAC THENL [ARITH_TAC, ALL_TAC, ASM_REWRITE_TAC [(← CONJUNCT1 LT), EMPTY_GSPEC, RING_SUM_CLAUSES] THEN ASM_SIMP_TAC [RING_SUB_RZERO, RING_MUL_RZERO, RING_POW] THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); let z8 ← (q r"ideal_pow r (P:A->bool) (l + 1)"); pure (free_in z8 z9))))) THEN ASM_REWRITE_TAC [MULT_CLAUSES, (← CONJUNCT1 LT), EMPTY_GSPEC, RING_SUM_CLAUSES] THEN ASM_SIMP_TAC [RING_SUB_RZERO, RING_MUL, RING_POW]] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"f:num"), (← q r"e:num"), (← q r"l:num"), (← q r"\s. ring_mul r (ring_of_int r ((c:num->int) s))
             (ring_mul r (ring_pow r t (s DIV f)) ((b:num->A) (s MOD f)))")] RING_SUM_NUMSEG_DIV_SLICE) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_MUL, RING_POW, RING_OF_INT], DISCH_THEN (MP_TAC o BETA_RULE)] THEN SUBGOAL_THEN (← q r"ring_sum r {j:num | j < f}
        (\j. ring_mul r (ring_of_int r ((c:num->int) (j + f * l)))
               (ring_mul r (ring_pow r t ((j + f * l) DIV f))
                           ((b:num->A) ((j + f * l) MOD f)))) =
      ring_mul r (ring_pow r t l)
        (ring_sum r {j:num | j < f}
           (\j. ring_mul r (ring_of_int r (c (j + f * l))) (b j)))") SUBST1_TAC THENL [SIMP_TAC [(← GSYM RING_SUM_LMUL), FINITE_NUMSEG_LT, RING_MUL, RING_OF_INT, RING_POW, (← ASSUME (← q r"(t:A) IN ring_carrier r")), (← ASSUME (← q r"!j. (b:num->A) j IN ring_carrier r"))] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"j:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN ASM_SIMP_TAC [MOD_MULT_ADD, DIV_MULT_ADD, MOD_LT, DIV_LT, ADD_CLAUSES] THEN MATCH_MP_TAC r7 THEN ASM_SIMP_TAC [RING_OF_INT, RING_POW], DISCH_THEN (LABEL_TAC "sl")] THEN SUBGOAL_THEN (← q r"ring_mul r (ring_pow r t l)
        (ring_sub r a
          (ring_sum r {j:num | j < f}
            (\j. ring_mul r (ring_of_int r ((c:num->int) (j + f * l)))
                            ((b:num->A) j)))) =
      ring_sub r (ring_mul r (ring_pow r t l) a)
        (ring_mul r (ring_pow r t l)
          (ring_sum r {j:num | j < f}
            (\j. ring_mul r (ring_of_int r (c (j + f * l))) (b j))))") SUBST1_TAC THENL [MATCH_MP_TAC RING_SUB_LDISTRIB THEN ASM_SIMP_TAC [RING_POW, RING_SUM], REMOVE_THEN "sl" (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC IN_RING_IDEAL_SUB_SUM_RESTRICT THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, FINITE_NUMSEG_LT, RING_MUL, RING_POW, RING_OF_INT] THEN X_GEN_TAC (← q r"s:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN ASM_CASES_TAC (← q r"s DIV f < l") THENL [FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"s:num")) o (checkM (fun th => (do if ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); let z2 ← (q r"c:num->int"); pure (free_in z2 z3)) then (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); pure (is_forall z5)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [(← GSYM (← CONJUNCT1 RING_OF_INT_CLAUSES))] THEN ASM_SIMP_TAC [RING_MUL_LZERO, RING_MUL, RING_POW, IN_RING_IDEAL_0, RING_IDEAL_IDEAL_POW], MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW, RING_OF_INT] THEN SUBGOAL_THEN (← q r"l + 1 <= s DIV f") ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"l + 1"), (← q r"s DIV f")] IDEAL_POW_ANTIMONO) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN MATCH_MP_TAC r1 THEN MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, RING_POW_IN_IDEAL_POW]])

  let DEDEKIND_IDEAL_POW_LEVEL_INDEPENDENT ← prove
    r"!r P (t:A) p f g (b:num->A) e m (c:num->int).
        dedekind_domain r /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\
        t IN P /\ ~(t IN ideal_pow r P 2) /\
        free_basis (integer_mod_ring p,quotient_ring r P)
                   (ring_of_int (quotient_ring r P)) f g /\
        (!j. b j IN ring_carrier r) /\
        (!j. j < f ==> ring_coset r P (b j) = g j) /\
        m <= e /\
        (!s. s < f * e ==> c s IN ring_carrier(integer_mod_ring p)) /\
        ring_sum r {s:num | s < f * e}
          (\s. ring_mul r (ring_of_int r (c s))
                (ring_mul r (ring_pow r t (s DIV f)) (b (s MOD f)))) IN
        ideal_pow r P m
        ==> !s. s < f * e /\ s DIV f < m ==> c s = &0"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"!l. l < m ==> !j. j < f ==> (c:num->int)(j + f * l) = &0") ASSUME_TAC THENL [ALL_TAC, X_GEN_TAC (← q r"s:num") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(f = 0)") ASSUME_TAC THENL [ASM_MESON_TAC [MULT_CLAUSES, (← CONJUNCT1 LT)], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"s DIV f"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"s MOD f"))) THEN ASM_SIMP_TAC [MOD_LT_EQ] THEN SUBGOAL_THEN (← q r"s MOD f + f * s DIV f = s") (fun th => REWRITE_TAC [th]) THEN MP_TAC (← SPECL [(← q r"s:num"), (← q r"f:num")] DIVISION) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC] THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q r"l:num") THEN DISCH_THEN (LABEL_TAC "lt") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"t:A"), (← q r"f:num"), (← q r"g:num->A->bool"), (← q r"b:num->A"), (← q r"e:num"), (← q r"c:num->int"), (← q r"l:num"), (← q r"ring_0 r:A")] DEDEKIND_IDEAL_POW_LEVEL_COEFFS) THEN ASM_REWRITE_TAC [RING_0] THEN ANTS_TAC THENL [REPEAT CONJ_TAC THENL [ASM_ARITH_TAC, X_GEN_TAC (← q r"s:num") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(f = 0)") ASSUME_TAC THENL [ASM_MESON_TAC [MULT_CLAUSES, (← CONJUNCT1 LT)], ALL_TAC] THEN REMOVE_THEN "lt" (MP_TAC o (SPEC (← q r"s DIV f"))) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"s MOD f"))) THEN ASM_SIMP_TAC [MOD_LT_EQ] THEN SUBGOAL_THEN (← q r"s MOD f + f * s DIV f = s") (fun th => REWRITE_TAC [th]) THEN MP_TAC (← SPECL [(← q r"s:num"), (← q r"f:num")] DIVISION) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, SUBGOAL_THEN (← q r"(t:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_RZERO, RING_POW, RING_SUB_LZERO, RING_SUM] THEN MATCH_MP_TAC IN_RING_IDEAL_NEG THEN REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"l + 1"), (← q r"m:num")] IDEAL_POW_ANTIMONO) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN ANTS_TAC THENL [ASM_ARITH_TAC, ASM SET_TAC []]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_coset r P (ring_0 r:A) = ring_0 (quotient_ring r P)") SUBST1_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_0, RING_COSET_EQ_IDEAL, IN_RING_IDEAL_0, RING_0], DISCH_THEN (ASSUME_TAC o SYM)] THEN FIRST_ASSUM (MP_TAC o ((SPEC (← q r"\j. (c:num->int) (j + f * l)")) o (CONJUNCT2 o (CONJUNCT2 o (GEN_REWRITE_RULE id [free_basis]))))) THEN REWRITE_TAC [INTEGER_MOD_RING_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL [ALL_TAC, ASM_REWRITE_TAC []] THEN X_GEN_TAC (← q r"j:num") THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC ADD_MULT_LT_MULT THEN ASM_ARITH_TAC)

  let DEDEKIND_QUOTIENT_POW_FREE_BASIS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r2 ← TAUT (← q r"p /\ (q ==> r) ==> (p ==> q) ==> r")
    prove
      r"!r P (t:A) p f g (b:num->A) e.
          dedekind_domain r /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\
          t IN P /\ ~(t IN ideal_pow r P 2) /\
          ring_of_num r p IN ideal_pow r P e /\
          free_basis (integer_mod_ring p,quotient_ring r P)
                     (ring_of_int (quotient_ring r P)) f g /\
          (!j. b j IN ring_carrier r) /\
          (!j. j < f ==> ring_coset r P (b j) = g j)
          ==> free_basis
                (integer_mod_ring p,quotient_ring r (ideal_pow r P e))
                (ring_of_int (quotient_ring r (ideal_pow r P e))) (f * e)
                (\s. ring_coset r (ideal_pow r P e)
                       (ring_mul r (ring_pow r t (s DIV f)) (b (s MOD f))))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"(t:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!c:num->int.
        ring_coset r (ideal_pow r P e)
         (ring_sum r {s:num | s < f * e}
           (\s. ring_mul r (ring_of_int r (c s))
                  (ring_mul r (ring_pow r t (s DIV f)) ((b:num->A) (s MOD f))))) =
        ring_sum (quotient_ring r (ideal_pow r P e)) {s:num | s < f * e}
          (\s. ring_mul (quotient_ring r (ideal_pow r P e))
                 (ring_of_int (quotient_ring r (ideal_pow r P e)) (c s))
                 (ring_coset r (ideal_pow r P e)
                   (ring_mul r (ring_pow r t (s DIV f)) (b (s MOD f)))))") (LABEL_TAC "lin") THENL [GEN_TAC THEN MP_TAC (← BETA_RULE (← ISPECL [(← q r"r:A ring"), (← q r"ideal_pow r (P:A->bool) e"), (← q r"f * e:num"), (← q r"\s. ring_mul r (ring_pow r t (s DIV f)) ((b:num->A) (s MOD f))"), (← q r"\s. ring_coset r (ideal_pow r P e)
               (ring_mul r (ring_pow r t (s DIV f)) ((b:num->A) (s MOD f)))"), (← q r"c:num->int")] QUOTIENT_RING_LINCOMB_LIFT)) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, RING_MUL, RING_POW], ALL_TAC] THEN REWRITE_TAC [free_basis] THEN REPEAT CONJ_TAC THENL [REPEAT STRIP_TAC THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, RING_IDEAL_IDEAL_POW, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_MUL, RING_POW], ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, RING_IDEAL_IDEAL_POW, FORALL_IN_GSPEC] THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"t:A"), (← q r"p:num"), (← q r"f:num"), (← q r"g:num->A->bool"), (← q r"b:num->A"), (← q r"e:num")] DEDEKIND_IDEAL_POW_LEVEL_SPAN) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"0"), (← q r"y:A")])) THEN ASM_REWRITE_TAC [LE_0, IDEAL_POW_0, (← CONJUNCT1 LT)] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"c:num->int") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"\s. (c:num->int) s rem &p") THEN REWRITE_TAC [INTEGER_MOD_RING_CARRIER_REM] THEN MP_TAC (← ISPECL [(← q r"quotient_ring r (ideal_pow r (P:A->bool) e)"), (← q r"p:num")] RING_OF_INT_REM_CHAR_DIVIDES) THEN ASM_SIMP_TAC [RING_CHAR_QUOTIENT_RING_DIVIDES, RING_IDEAL_IDEAL_POW] THEN DISCH_THEN (fun (_ : thm) => ALL_TAC) THEN REMOVE_THEN "lin" (SUBST1_TAC o (SYM o (SPEC (← q r"c:num->int")))) THEN wPart Except.ok (lhand o rand) RING_COSET_EQ THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, RING_SUM], X_GEN_TAC (← q r"c:num->int") THEN REWRITE_TAC [] THEN STRIP_TAC THEN REWRITE_TAC [INTEGER_MOD_RING_CLAUSES] THEN X_GEN_TAC (← q r"s:num") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"t:A"), (← q r"p:num"), (← q r"f:num"), (← q r"g:num->A->bool"), (← q r"b:num->A"), (← q r"e:num"), (← q r"e:num"), (← q r"c:num->int")] DEDEKIND_IDEAL_POW_LEVEL_INDEPENDENT) THEN ASM_REWRITE_TAC [LE_REFL] THEN MATCH_MP_TAC r2 THEN CONJ_TAC THENL [ALL_TAC, DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"~(f = 0)") ASSUME_TAC THENL [ASM_MESON_TAC [MULT_CLAUSES, (← CONJUNCT1 LT)], ASM_SIMP_TAC [RDIV_LT_EQ]]] THEN W (fun (_, w) => tactic_of do pure (MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_pow r (P:A->bool) e"), (← (do let z1 ← (pure w); liftExcept (lhand z1)))] RING_COSET_EQ_IDEAL))) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, RING_SUM] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN REMOVE_THEN "lin" (fun th => REWRITE_TAC [th]) THEN ASM_SIMP_TAC [QUOTIENT_RING_0, RING_IDEAL_IDEAL_POW]])

  let DEDEKIND_ALGEBRA_TRACE_QUOTIENT_POW ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"j:num"
    let q2 ← q r"\i. (C:num->int) (i + f * l)"
    let q3 ← q r"ring_coset r P (ring_mul r x ((b:num->A) j))"
    let q4 ← q r"g:num->A->bool"
    let q5 ← q r"f:num"
    let q6 ← q r"quotient_ring r (P:A->bool)"
    let q7 ← q r"integer_mod_ring p"
    let q8 ← q r"ring_of_int (quotient_ring r P):int->A->bool"
    let v9 ← ISPECL [q8, q7, q6, q5, q4, q3, q2] BASIS_COORDINATES_UNIQUE
    let q10 ← q r"e:num"
    let q11 ← q r"l + 1"
    let q12 ← q r"P:A->bool"
    let q13 ← q r"r:A ring"
    let v14 ← ISPECL [q13, q12, q11, q10] IDEAL_POW_ANTIMONO
    let q15 ← q r"ring_mul r u (ring_mul r x v) = ring_mul r x (ring_mul r u (v:A))"
    let r16 ← RING_RULE q15
    let q17 ← q r"ring_mul r (ring_pow r t l) (ring_mul r x ((b:num->A) j)) =
      ring_mul r x (ring_mul r (ring_pow r t l) (b j))"
    let q18 ← q r"ring_mul r x ((b:num->A) j)"
    let q19 ← q r"l:num"
    let q20 ← q r"C:num->int"
    let q21 ← q r"e:num"
    let q22 ← q r"b:num->A"
    let q23 ← q r"g:num->A->bool"
    let q24 ← q r"f:num"
    let q25 ← q r"t:A"
    let q26 ← q r"P:A->bool"
    let q27 ← q r"r:A ring"
    let v28 ← ISPECL [q27, q26, q25, q24, q23, q22, q21, q20, q19, q18] DEDEKIND_IDEAL_POW_LEVEL_COEFFS
    let q29 ← q r"e:num"
    let q30 ← q r"l:num"
    let q31 ← q r"P:A->bool"
    let q32 ← q r"r:A ring"
    let v33 ← ISPECL [q32, q31, q30, q29] IDEAL_POW_ANTIMONO
    let q34 ← q r"ring_mul r x (ring_mul r (ring_pow r t l) ((b:num->A) j))"
    let q35 ← q r"!a b:A. a IN ring_carrier r /\ b IN ring_carrier r /\
              a IN ideal_pow r P l /\ ring_sub r a b IN ideal_pow r P l
              ==> b IN ideal_pow r P l"
    let q36 ← q r"ring_sub r a (ring_sub r a (b:A)) = b"
    let r37 ← RING_RULE q36
    let r38 ← MESON [IN_RING_IDEAL_SUB, RING_IDEAL_IDEAL_POW, r37] q35
    let q39 ← q r"C:num->int"
    let q40 ← q r"l:num"
    let q41 ← q r"e:num"
    let q42 ← q r"b:num->A"
    let q43 ← q r"g:num->A->bool"
    let q44 ← q r"f:num"
    let q45 ← q r"p:num"
    let q46 ← q r"t:A"
    let q47 ← q r"P:A->bool"
    let q48 ← q r"r:A ring"
    let v49 ← ISPECL [q48, q47, q46, q45, q44, q43, q42, q41, q40, q39] DEDEKIND_IDEAL_POW_LEVEL_INDEPENDENT
    let q50 ← q r"ring_sub r (ring_mul r x (ring_mul r (ring_pow r t l) ((b:num->A) j)))
      (ring_sum r {s:num | s < f * e}
        (\s. ring_mul r (ring_of_int r ((C:num->int) s))
              (ring_mul r (ring_pow r t (s DIV f)) (b (s MOD f))))) IN
    ideal_pow r P e"
    let q51 ← q r"C:num->int"
    let q52 ← q r"G:num->A->bool"
    let q53 ← q r"\s. ring_mul r (ring_pow r t (s DIV f)) ((b:num->A) (s MOD f))"
    let q54 ← q r"f * e:num"
    let q55 ← q r"ideal_pow r (P:A->bool) e"
    let q56 ← q r"r:A ring"
    let v57 ← ISPECL [q56, q55, q54, q53, q52, q51] QUOTIENT_RING_LINCOMB_LIFT
    let v58 ← BETA_RULE v57
    let q59 ← q r"ring_coset r (ideal_pow r P e)
       (ring_mul r x (ring_mul r (ring_pow r t l) ((b:num->A) j)))"
    let q60 ← q r"G:num->A->bool"
    let q61 ← q r"f * e:num"
    let q62 ← q r"quotient_ring r (ideal_pow r (P:A->bool) e)"
    let q63 ← q r"integer_mod_ring p"
    let q64 ← q r"ring_of_int (quotient_ring r (ideal_pow r P e)):int->A->bool"
    let v65 ← ISPECL [q64, q63, q62, q61, q60, q59] BASIS_COORDINATES
    let q66 ← q r"C = basis_coordinates
          (integer_mod_ring p,quotient_ring r (ideal_pow r P e))
          (ring_of_int (quotient_ring r (ideal_pow r P e))) (f * e) G
          (ring_coset r (ideal_pow r P e)
            (ring_mul r x (ring_mul r (ring_pow r t l) ((b:num->A) j))))"
    let q67 ← q r"j:num < f"
    let v68 ← ASSUME q67
    let q69 ← q r"!j. j < f ==> ring_coset r P ((b:num->A) j) = g j"
    let v70 ← ASSUME q69
    let v71 ← MATCH_MP v70 v68
    let v72 ← GSYM v71
    let q73 ← q r"~(f = 0)"
    let v74 ← ASSUME q73
    let q75 ← q r"j:num < f"
    let v76 ← ASSUME q75
    let q77 ← q r"(G:num->A->bool) (j + f * l) =
    ring_coset r (ideal_pow r P e) (ring_mul r (ring_pow r t l) (b j))"
    let q78 ← q r"~(f = 0)"
    let q79 ← q r"j:num"
    let q80 ← q r"ring_coset r P (x:A)"
    let q81 ← q r"g:num->A->bool"
    let q82 ← q r"f:num"
    let q83 ← q r"quotient_ring r (P:A->bool)"
    let q84 ← q r"integer_mod_ring p"
    let q85 ← q r"ring_of_int (quotient_ring r P):int->A->bool"
    let v86 ← ISPECL [q85, q84, q83, q82, q81, q80] ALGEBRA_TRACE_FREE_BASIS
    let q87 ← q r"ring_homomorphism(integer_mod_ring p,quotient_ring r P)
      (ring_of_int (quotient_ring r P):int->A->bool)"
    let q88 ← q r"e:num"
    let q89 ← q r"1:num"
    let q90 ← q r"P:A->bool"
    let q91 ← q r"r:A ring"
    let v92 ← ISPECL [q91, q90, q89, q88] IDEAL_POW_ANTIMONO
    let q93 ← q r"ring_of_num r p IN (P:A->bool)"
    let q94 ← q r"l:num"
    let v95 ← CONJUNCT1 LT
    let q96 ← q r"f:num"
    let q97 ← q r"s:num"
    let v98 ← SPECL [q97, q96] DIVISION
    let q99 ← q r"s MOD f + f * s DIV f = s"
    let q100 ← q r"s:num"
    let q101 ← q r"ring_sum (integer_mod_ring p) {l:num | l < e}
     (\l. ring_sum (integer_mod_ring p) {j:num | j < f}
       (\j. mul_matrix
              (integer_mod_ring p,quotient_ring r (ideal_pow r P e))
              (ring_of_int (quotient_ring r (ideal_pow r P e))) (f * e) G
              (ring_coset r (ideal_pow r P e) (x:A))
              (j + f * l) (j + f * l)))"
    let q102 ← q r"{l:num | l < e}"
    let q103 ← q r"algebra_trace (integer_mod_ring p,quotient_ring r P)
                    (ring_of_int (quotient_ring r P)) (ring_coset r P (x:A))"
    let q104 ← q r"integer_mod_ring p"
    let v105 ← ISPECL [q104, q103, q102] RING_SUM_CONST
    let q106 ← q r"ring_coset r (ideal_pow r P e) (x:A)"
    let q107 ← q r"G:num->A->bool"
    let q108 ← q r"f * e:num"
    let q109 ← q r"quotient_ring r (ideal_pow r (P:A->bool) e)"
    let q110 ← q r"integer_mod_ring p"
    let q111 ← q r"ring_of_int (quotient_ring r (ideal_pow r P e)):int->A->bool"
    let v112 ← ISPECL [q111, q110, q109, q108, q107, q106] ALGEBRA_TRACE_FREE_BASIS
    let q113 ← q r"ring_coset r (ideal_pow r P e) (x:A) IN
    ring_carrier(quotient_ring r (ideal_pow r P e))"
    let q114 ← q r"ring_homomorphism(integer_mod_ring p,quotient_ring r (ideal_pow r P e))
      (ring_of_int (quotient_ring r (ideal_pow r P e)):int->A->bool)"
    let q115 ← q r"G = \s. ring_coset r (ideal_pow r P e)
              (ring_mul r (ring_pow r t (s DIV f)) ((b:num->A) (s MOD f)))"
    let q116 ← q r"e:num"
    let q117 ← q r"b:num->A"
    let q118 ← q r"g:num->A->bool"
    let q119 ← q r"f:num"
    let q120 ← q r"p:num"
    let q121 ← q r"t:A"
    let q122 ← q r"P:A->bool"
    let q123 ← q r"r:A ring"
    let v124 ← ISPECL [q123, q122, q121, q120, q119, q118, q117, q116] DEDEKIND_QUOTIENT_POW_FREE_BASIS
    let q125 ← q r"b:num->A"
    let q126 ← q r"j:num"
    let q127 ← q r"j:num < f"
    let q128 ← q r"j:num"
    let v129 ← GSYM SKOLEM_THM
    let q130 ← q r"?b:num->A. !j. b j IN ring_carrier r /\
                   (j < f ==> ring_coset r P (b j) = g j)"
    let q131 ← q r"(t:A) IN ring_carrier r"
    let q132 ← q r"t:A"
    let q133 ← q r"P:A->bool"
    let q134 ← q r"r:A ring"
    let v135 ← ISPECL [q134, q133] DEDEKIND_PRIME_IDEAL_UNIFORMIZER
    prove
      r"!r P p f g e (x:A).
          dedekind_domain r /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\
          ring_of_num r p IN ideal_pow r P e /\
          free_basis (integer_mod_ring p,quotient_ring r P)
                     (ring_of_int (quotient_ring r P)) f g /\
          x IN ring_carrier r
          ==> algebra_trace
                (integer_mod_ring p,quotient_ring r (ideal_pow r P e))
                (ring_of_int (quotient_ring r (ideal_pow r P e)))
                (ring_coset r (ideal_pow r P e) x) =
              ring_mul (integer_mod_ring p) (ring_of_num (integer_mod_ring p) e)
                (algebra_trace (integer_mod_ring p,quotient_ring r P)
                   (ring_of_int (quotient_ring r P)) (ring_coset r P x))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN MP_TAC v135 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN q132 STRIP_ASSUME_TAC) THEN SUBGOAL_THEN q131 ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN q130 MP_TAC THENL [REWRITE_TAC [v129] THEN X_GEN_TAC q128 THEN ASM_CASES_TAC q127 THEN ASM_REWRITE_TAC [] THENL [FIRST_ASSUM (MP_TAC o ((SPEC q126) o (CONJUNCT1 o (GEN_REWRITE_RULE id [free_basis])))) THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN MESON_TAC [], MESON_TAC [RING_0]], REWRITE_TAC [FORALL_AND_THM] THEN DISCH_THEN (X_CHOOSE_THEN q125 STRIP_ASSUME_TAC)] THEN MP_TAC v124 THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC q115 THEN DISCH_TAC THEN SUBGOAL_THEN q114 ASSUME_TAC THENL [ASM_SIMP_TAC [RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT, RING_CHAR_QUOTIENT_RING_DIVIDES, RING_IDEAL_IDEAL_POW], ALL_TAC] THEN SUBGOAL_THEN q113 ASSUME_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, RING_IDEAL_IDEAL_POW, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN MP_TAC v112 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MP_TAC v105 THEN REWRITE_TAC [FINITE_NUMSEG_LT, CARD_NUMSEG_LT, ALGEBRA_TRACE_NORM_IN_CARRIER] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN TRANS_TAC EQ_TRANS q101 THEN CONJ_TAC THENL [wPart rand (rand o rand) RING_SUM_MOD_DIV THEN ANTS_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC MUL_MATRIX_IN_CARRIER THEN ASM_SIMP_TAC [ADD_MULT_LT_MULT], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q100 THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN SUBGOAL_THEN q99 (fun th => REWRITE_TAC [th]) THEN MP_TAC v98 THEN ANTS_TAC THENL [ASM_MESON_TAC [MULT_CLAUSES, v95], ALL_TAC] THEN ARITH_TAC, MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q94 THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC []] THEN SUBGOAL_THEN q93 ASSUME_TAC THENL [MP_TAC v92 THEN ASM_SIMP_TAC [IDEAL_POW_1, RING_IDEAL_IMP_SUBSET] THEN ANTS_TAC THENL [ASM_ARITH_TAC, ASM SET_TAC []], ALL_TAC] THEN SUBGOAL_THEN q87 ASSUME_TAC THENL [ASM_SIMP_TAC [RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT, RING_CHAR_QUOTIENT_RING_DIVIDES], ALL_TAC] THEN MP_TAC v86 THEN ANTS_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, IN_ELIM_THM] THEN ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC q79 THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC [mul_matrix] THEN SUBGOAL_THEN q78 ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN q77 SUBST1_TAC THENL [EXPAND_TAC "G" THEN REWRITE_TAC [] THEN SIMP_TAC [MOD_MULT_ADD, DIV_MULT_ADD, MOD_LT, DIV_LT, ADD_CLAUSES, v76, v74], ALL_TAC] THEN REWRITE_TAC [v72] THEN ASM_SIMP_TAC [QUOTIENT_RING_MUL, RING_IDEAL_IDEAL_POW, RING_MUL, RING_POW] THEN ABBREV_TAC q66 THEN MP_TAC v65 THEN ANTS_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, RING_IDEAL_IDEAL_POW, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_MUL, RING_POW], ASM_REWRITE_TAC [] THEN STRIP_TAC] THEN MP_TAC v58 THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, RING_MUL, RING_POW] THEN EXPAND_TAC "G" THEN REWRITE_TAC [], ASM_REWRITE_TAC [] THEN DISCH_TAC] THEN SUBGOAL_THEN q50 ASSUME_TAC THENL [wPart Except.ok (rand o rand) RING_COSET_EQ THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, RING_SUM, RING_MUL, RING_POW], ALL_TAC] THEN MP_TAC v49 THEN ASM_SIMP_TAC [LT_IMP_LE] THEN ANTS_TAC THENL [MATCH_MP_TAC r38 THEN EXISTS_TAC q34 THEN ASM_SIMP_TAC [RING_MUL, RING_POW, RING_SUM] THEN CONJ_TAC THENL [MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW] THEN MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_POW, RING_POW_IN_IDEAL_POW], MP_TAC v33 THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, LT_IMP_LE] THEN ASM SET_TAC []], DISCH_TAC] THEN MP_TAC v28 THEN ASM_SIMP_TAC [RING_MUL] THEN ANTS_TAC THENL [SUBGOAL_THEN q17 SUBST1_TAC THENL [MATCH_MP_TAC r16 THEN ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN MP_TAC v14 THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET] THEN ANTS_TAC THENL [ASM_ARITH_TAC, ASM SET_TAC []], DISCH_TAC] THEN CONV_TAC SYM_CONV THEN MP_TAC v9 THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (MP_TAC o (SPEC q1)) THEN ASM_REWRITE_TAC []])

  let FREE_BASIS_QUOTIENT_RING_PRIME_EXISTS ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r")
    prove
      r"!r:A ring n w p i.
          free_basis (integer_ring,r) (ring_of_int r) n w /\ prime p /\
          ring_ideal r i /\ ring_of_num r p IN i
          ==> FINITE(ring_carrier(quotient_ring r i)) /\
              ring_homomorphism(integer_mod_ring p,quotient_ring r i)
                               (ring_of_int(quotient_ring r i)) /\
              ?m g. free_basis (integer_mod_ring p,quotient_ring r i)
                               (ring_of_int(quotient_ring r i)) m g"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"j = ideal_generated r {ring_of_num r p:A}") THEN SUBGOAL_THEN (← q r"ring_ideal r (j:A->bool) /\ (j:A->bool) SUBSET i") STRIP_ASSUME_TAC THENL [EXPAND_TAC "j" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [SING_SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"FINITE(ring_carrier(quotient_ring r (j:A->bool)))") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_int(quotient_ring r (j:A->bool))"), (← q r"integer_mod_ring p"), (← q r"quotient_ring r (j:A->bool)"), (← q r"n:num"), (← q r"\i. ring_coset r j ((w:num->A) i)")] FREE_BASIS_HAS_SIZE) THEN EXPAND_TAC "j" THEN ASM_SIMP_TAC [FREE_BASIS_QUOTIENT_RING_INTEGER_MOD, RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING, FINITE_INTEGER_MOD_RING, PRIME_IMP_NZ] THEN SIMP_TAC [HAS_SIZE], ALL_TAC] THEN MATCH_MP_TAC r1 THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC FINITE_QUOTIENT_RING_MONO THEN EXISTS_TAC (← q r"j:A->bool") THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT, RING_CHAR_QUOTIENT_RING_DIVIDES], STRIP_TAC THEN EXISTS_TAC (← q r"extension_degree (integer_mod_ring p,quotient_ring r i)
                         (ring_of_int(quotient_ring r (i:A->bool)))") THEN MATCH_MP_TAC FREE_BASIS_EXISTS THEN EXISTS_TAC (← q r"ring_carrier(quotient_ring r (i:A->bool))") THEN ASM_REWRITE_TAC [ring_spanning, RING_SPAN_SELF, SUBSET_REFL, FIELD_INTEGER_MOD_RING]])

  -- @@RETURN BEGIN
  return { DEDEKIND_IDEAL_POW_LEVEL_SPAN, DEDEKIND_IDEAL_POW_LEVEL_COEFFS,
           DEDEKIND_IDEAL_POW_LEVEL_INDEPENDENT, DEDEKIND_QUOTIENT_POW_FREE_BASIS,
           DEDEKIND_ALGEBRA_TRACE_QUOTIENT_POW, FREE_BASIS_QUOTIENT_RING_PRIME_EXISTS }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- different_exponent.ml phrases from line 790 to 1447                    -/
/- ---------------------------------------------------------------------- -/

structure DifferentExponent02 where
  -- @@FIELDS
  ALGEBRA_TRACE_INTEGER_MOD_SPLIT : thm
  ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW_DIVIDES : thm
  ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW : thm
  NUMBER_FIELD_DIFFERENT_WILD : thm
  NUMBER_FIELD_DIFFERENT_TAME : thm
  NUMBER_FIELD_DIFFERENT_VALUATION_TAME_Q : thm
  NUMBER_FIELD_DIFFERENT_VALUATION_WILD_Q : thm
  NUMBER_FIELD_IDEAL_NORM_PRIME_EXPONENT : thm
  NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT : thm
  NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT_TAME : thm
  NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT_GE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDifferentExponent02 [HolBase] (D : DifferentExponentDeps) (BDifferentExponent01 : DifferentExponent01) :
    ExceptT String IO DifferentExponent02 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, RING_RULE,
        SET_RULE, SET_TAC, TAUT, .. } := D
  let { ALGEBRA_TRACE_0, ALGEBRA_TRACE_FINITE_FIELD_NONZERO,
        ALGEBRA_TRACE_ISOMORPHIC_IMAGE, ALGEBRA_TRACE_NILPOTENT_INTEGER_MOD,
        ALGEBRA_TRACE_NORM_IN_CARRIER, ALGEBRA_TRACE_PROD_RING,
        ALGEBRA_TRACE_QUOTIENT_RING_INTEGER_MOD, AND_FORALL_THM, ARITH_EQ,
        COMAXIMAL_IDEAL_POW, CONTRAPOS_THM, DEDEKIND_IDEAL_FACTORIZATION,
        DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT, DEDEKIND_IDEAL_PROD_SUBSET_CANCEL,
        DEDEKIND_IDEAL_SUBSET_POW_VALUATION, DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL,
        DEDEKIND_RING_OF_INTEGERS, DIVIDES_0, DIVIDES_ZERO, EQ_TRANS, EXISTS_IN_GSPEC,
        EXISTS_UNIQUE_THM, EXP_EQ_0, EXTENSION, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_INTEGER_MOD_RING, FIELD_QUOTIENT_RING, FIELD_SUBFIELD_GENERATED,
        FINITE_RESTRICT, FREE_BASIS_QUOTIENT_RING_INTEGER_MOD, FUN_EQ_THM,
        IDEAL_GENERATED_INC, IDEAL_NORM_FACTORIZATION, IDEAL_POW_0, IDEAL_POW_1,
        IDEAL_POW_ANTIMONO, IDEAL_POW_SUC, IDEAL_PROD_COMAXIMAL, IDEAL_PROD_COMM,
        IDEAL_PROD_MINIMAL, IDEAL_PROD_MONO, IDEAL_VALUATION_EQ_0, INDEX_EXP,
        INDEX_NPRODUCT, INDEX_PRIME, INTEGER_MOD_RING_CHAR, INTEGER_MOD_RING_CLAUSES,
        INTEGRAL_DOMAIN_MUL_EQ_0, INT_REM_EQ_0, IN_ELIM_THM, IN_RING_IDEAL_0,
        IN_RING_IDEAL_LMUL, IN_RING_IDEAL_NEG, IN_RING_IDEAL_RMUL, IN_SING,
        IN_SUBRING_1, IN_SUBRING_NUM, LE_MULT_LCANCEL, LE_REFL, LT_MULT_LCANCEL,
        MAXIMAL_IDEAL_COMAXIMAL, MULT_CLAUSES, .. } := D.core1
  let { MULT_EQ_0, NOT_FORALL_THM, NOT_IMP, NSUM_EQ, NSUM_EQ_SUPERSET, NSUM_LE,
        NSUM_LT, NSUM_SUPERSET, NUMBER_FIELD_CODIFFERENT_DIV,
        NUMBER_FIELD_CODIFFERENT_DIV_NUM, NUMBER_FIELD_DIFFERENT_NONZERO,
        NUMBER_FIELD_DIFFERENT_SUBSET_RAMIFICATION, NUMBER_FIELD_IDEAL_NORM_DIFFERENT,
        NUMBER_FIELD_IMP_FIELD, NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q, PAIR_EQ,
        PRIME_IMP_NZ, PRIME_IMP_RING_IDEAL, QUOTIENT_RING_0, QUOTIENT_RING_CARRIER,
        RAMIFICATION_INDEX_PRIME, RAMIFICATION_INDEX_PRIME_SUBFIELD, RING_1,
        RING_ADD_RZERO, RING_CHAR_QUOTIENT_RING_DIVIDES, RING_COSET_EQ,
        RING_COSET_EQ_IDEAL, RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING,
        RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT, RING_HOMOMORPHISM_RING_COSET,
        RING_HOMOMORPHISM_RING_OF_INT, RING_HOMOMORPHISM_SUBFIELD_INCLUSION,
        RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_QUOTIENT,
        RING_IDEAL_IMP_SUBSET, RING_IDEAL_NUMBER_FIELD_DIFFERENT,
        RING_ISOMORPHISM_QUOTIENT_RING_INTER, RING_MUL, RING_MUL_IN_IDEAL_PROD,
        RING_MUL_RID, RING_MUL_SYM, RING_OF_INT, RING_OF_INTEGERS,
        RING_OF_INTEGERS_FINITE_QUOTIENT, RING_OF_INTEGERS_FREE,
        RING_OF_INTEGERS_IDEAL_GENERATED_PRIME, RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q,
        RING_OF_INTEGERS_PRIME_IDEAL_ABOVE, RING_OF_INTEGERS_SUBRING,
        RING_OF_INTEGERS_SUBSET, RING_OF_NUM, RING_OF_NUM_EQ_0, RING_POW_1,
        SING_SUBSET, SUBSET, SUBSET_REFL, SUBSET_TRANS, number_field, o_THM,
        ring_setadd, .. } := D.core2
  let { DEDEKIND_ALGEBRA_TRACE_QUOTIENT_POW, FREE_BASIS_QUOTIENT_RING_PRIME_EXISTS, .. } := BDifferentExponent01
  -- @@SCOPE END

  let ALGEBRA_TRACE_INTEGER_MOD_SPLIT ← prove
    r"!r:A ring n w p j1 j2 y.
        free_basis (integer_ring,r) (ring_of_int r) n w /\ prime p /\
        ring_ideal r j1 /\ ring_ideal r j2 /\
        ring_setadd r j1 j2 = ring_carrier r /\
        j1 INTER j2 = ideal_generated r {ring_of_num r p} /\
        y IN ring_carrier r
        ==> algebra_trace (integer_ring,r) (ring_of_int r) y rem &p =
            ring_add (integer_mod_ring p)
             (algebra_trace (integer_mod_ring p,quotient_ring r j1)
                (ring_of_int (quotient_ring r j1)) (ring_coset r j1 y))
             (algebra_trace (integer_mod_ring p,quotient_ring r j2)
                (ring_of_int (quotient_ring r j2)) (ring_coset r j2 y))"
    (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"j = ideal_generated r {ring_of_num r p:A}") THEN SUBGOAL_THEN (← q r"ring_ideal r (j:A->bool) /\ ring_of_num r p IN j") STRIP_ASSUME_TAC THENL [EXPAND_TAC "j" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN REWRITE_TAC [SING_SUBSET, IN_SING, RING_OF_NUM], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_num r p IN (j1:A->bool) /\ ring_of_num r p IN j2") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"j1 INTER j2 = (j:A->bool)") THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"p:num"), (← q r"j2:A->bool")] FREE_BASIS_QUOTIENT_RING_PRIME_EXISTS) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"p:num"), (← q r"j1:A->bool")] FREE_BASIS_QUOTIENT_RING_PRIME_EXISTS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"n1:num") (X_CHOOSE_TAC (← q r"g1:num->A->bool"))))) THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"n2:num") (X_CHOOSE_TAC (← q r"g2:num->A->bool"))))) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"p:num"), (← q r"y:A")] ALGEBRA_TRACE_QUOTIENT_RING_INTEGER_MOD) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j1:A->bool"), (← q r"j2:A->bool")] RING_ISOMORPHISM_QUOTIENT_RING_INTER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"h:(A->bool)->(A->bool)#(A->bool)") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"integer_mod_ring p"), (← q r"quotient_ring r (j:A->bool)"), (← q r"prod_ring (quotient_ring r j1) (quotient_ring r (j2:A->bool))"), (← q r"ring_of_int(quotient_ring r (j:A->bool))"), (← q r"h:(A->bool)->(A->bool)#(A->bool)"), (← q r"n:num"), (← q r"\i. ring_coset r j ((w:num->A) i)"), (← q r"ring_coset r j (y:A)")] ALGEBRA_TRACE_ISOMORPHIC_IMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN EXPAND_TAC "j" THEN ASM_SIMP_TAC [FREE_BASIS_QUOTIENT_RING_INTEGER_MOD, RING_HOMOMORPHISM_INTEGER_MOD_QUOTIENT_RING, QUOTIENT_RING_CARRIER, RING_IDEAL_IDEAL_GENERATED] THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN ASM_SIMP_TAC [] THEN SUBGOAL_THEN (← q r"(h:(A->bool)->(A->bool)#(A->bool)) o
    ring_of_int (quotient_ring r j) =
    (\a. ring_of_int (quotient_ring r j1) a,
         ring_of_int (quotient_ring r j2) a)") SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM, o_THM] THEN X_GEN_TAC (← q r"a:int") THEN REWRITE_TAC [(← GSYM (← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT (← MATCH_MP RING_HOMOMORPHISM_RING_COSET (← ASSUME (← q r"ring_ideal r (j:A->bool)")))))] THEN ASM_SIMP_TAC [RING_OF_INT, PAIR_EQ] THEN REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT (← MATCH_MP RING_HOMOMORPHISM_RING_COSET (← ASSUME (← q r"ring_ideal r (j1:A->bool)"))))] THEN REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT (← MATCH_MP RING_HOMOMORPHISM_RING_COSET (← ASSUME (← q r"ring_ideal r (j2:A->bool)"))))], ALL_TAC] THEN MATCH_MP_TAC ALGEBRA_TRACE_PROD_RING THEN MAP_EVERY EXISTS_TAC [(← q r"n1:num"), (← q r"n2:num"), (← q r"g1:num->A->bool"), (← q r"g2:num->A->bool")] THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER] THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [])

  let ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW_DIVIDES ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_1 r = ring_add r u v
      ==> ring_sub r (ring_mul r a v) a = ring_neg r (ring_mul r a (u:A))")
    let r2 ← TAUT (← q r"(~q ==> ~p) ==> p ==> q")
    let r3 ← SET_RULE (← q r"!x:A s t u. s INTER t = u /\ x IN u ==> x IN s /\ x IN t")
    prove
      r"!r:A ring n w p P Q e.
          dedekind_domain r /\ free_basis (integer_ring,r) (ring_of_int r) n w /\
          prime p /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\ ring_ideal r Q /\
          ring_setadd r (ideal_pow r P e) Q = ring_carrier r /\
          ideal_pow r P e INTER Q = ideal_generated r {ring_of_num r p}
          ==> ((!x. x IN Q
                    ==> &p divides
                        algebra_trace (integer_ring,r) (ring_of_int r) x) <=>
               p divides e)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"ring_of_num r p IN ideal_pow r (P:A->bool) e /\
                  ring_of_num r p IN Q") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r3 THEN EXISTS_TAC (← q r"ideal_generated r {ring_of_num r p:A}") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN REWRITE_TAC [SING_SUBSET, IN_SING, RING_OF_NUM], ALL_TAC] THEN ASM_CASES_TAC (← q r"e = 0") THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC [DIVIDES_0] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN MATCH_MP_TAC ALGEBRA_TRACE_NILPOTENT_INTEGER_MOD THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"w:num->A"), (← q r"1")] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_POW_1, ARITH_EQ] THEN UNDISCH_TAC (← q r"ideal_pow r P 0 INTER Q = ideal_generated r {ring_of_num r p:A}") THEN REWRITE_TAC [IDEAL_POW_0] THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_of_num r p IN (P:A->bool)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"1"), (← q r"e:num")] IDEAL_POW_ANTIMONO) THEN ASM_SIMP_TAC [IDEAL_POW_1, RING_IDEAL_IMP_SUBSET] THEN ANTS_TAC THENL [ASM_ARITH_TAC, ASM SET_TAC []], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"p:num"), (← q r"P:A->bool")] FREE_BASIS_QUOTIENT_RING_PRIME_EXISTS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN (← q r"f:num") (X_CHOOSE_TAC (← q r"g:num->A->bool"))))) THEN SUBGOAL_THEN (← q r"field(quotient_ring r (P:A->bool))") ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_QUOTIENT_RING, DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x:A. x IN Q
            ==> algebra_trace (integer_ring,r) (ring_of_int r) x rem &p =
                ring_mul (integer_mod_ring p)
                  (ring_of_num (integer_mod_ring p) e)
                  (algebra_trace (integer_mod_ring p,quotient_ring r P)
                     (ring_of_int (quotient_ring r P)) (ring_coset r P x))") (LABEL_TAC "key") THENL [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"p:num"), (← q r"ideal_pow r (P:A->bool) e"), (← q r"Q:A->bool"), (← q r"x:A")] ALGEBRA_TRACE_INTEGER_MOD_SPLIT) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"ring_coset r Q (x:A) = ring_0(quotient_ring r Q)") SUBST1_TAC THENL [ASM_SIMP_TAC [QUOTIENT_RING_0, RING_COSET_EQ_IDEAL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"Q:A->bool")] RING_HOMOMORPHISM_RING_COSET) THEN MP_TAC (← ISPECL [(← q r"quotient_ring r (Q:A->bool)"), (← q r"p:num")] RING_HOMOMORPHISM_INTEGER_MOD_RING_OF_INT) THEN ASM_SIMP_TAC [RING_CHAR_QUOTIENT_RING_DIVIDES] THEN DISCH_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC [ALGEBRA_TRACE_0] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"p:num"), (← q r"f:num"), (← q r"g:num->A->bool"), (← q r"e:num"), (← q r"x:A")] DEDEKIND_ALGEBRA_TRACE_QUOTIENT_POW) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_ADD_RZERO THEN SIMP_TAC [RING_MUL, RING_OF_NUM, ALGEBRA_TRACE_NORM_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"!t. t IN ring_carrier(integer_mod_ring p)
          ==> (ring_mul (integer_mod_ring p) (ring_of_num (integer_mod_ring p) e)
                 t = ring_0 (integer_mod_ring p) <=>
               p divides e \/ t = ring_0 (integer_mod_ring p))") (LABEL_TAC "mul") THENL [REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"integer_mod_ring p"), (← q r"ring_of_num (integer_mod_ring p) e"), (← q r"t:int")] INTEGRAL_DOMAIN_MUL_EQ_0) THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, FIELD_INTEGER_MOD_RING, RING_OF_NUM] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [RING_OF_NUM_EQ_0, INTEGER_MOD_RING_CHAR], ALL_TAC] THEN SUBGOAL_THEN (← q r"!x:A. x IN Q
            ==> (&p divides algebra_trace (integer_ring,r) (ring_of_int r) x <=>
                 p divides e \/
                 algebra_trace (integer_mod_ring p,quotient_ring r P)
                   (ring_of_int (quotient_ring r P)) (ring_coset r P x) =
                 ring_0 (integer_mod_ring p))") (LABEL_TAC "dvd") THENL [X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN REWRITE_TAC [(← GSYM INT_REM_EQ_0)] THEN USE_THEN "key" (fun th => ASM_SIMP_TAC [th]) THEN REWRITE_TAC [(← SYM (← SPEC (← q r"p:num") (← CONJUNCT1 (← CONJUNCT2 (← CONJUNCT2 INTEGER_MOD_RING_CLAUSES)))))] THEN USE_THEN "mul" MATCH_MP_TAC THEN REWRITE_TAC [ALGEBRA_TRACE_NORM_IN_CARRIER], ALL_TAC] THEN EQ_TAC THENL [ALL_TAC, ASM_SIMP_TAC []] THEN MATCH_MP_TAC r2 THEN DISCH_TAC THEN REWRITE_TAC [NOT_FORALL_THM, NOT_IMP] THEN MP_TAC (← ISPECL [(← q r"integer_mod_ring p"), (← q r"quotient_ring r (P:A->bool)"), (← q r"ring_of_int (quotient_ring r (P:A->bool))"), (← q r"f:num"), (← q r"g:num->A->bool")] ALGEBRA_TRACE_FINITE_FIELD_NONZERO) THEN ASM_REWRITE_TAC [FIELD_INTEGER_MOD_RING] THEN ASM_SIMP_TAC [QUOTIENT_RING_CARRIER, EXISTS_IN_GSPEC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC) THEN UNDISCH_TAC (← q r"ring_setadd r (ideal_pow r P e) Q = ring_carrier(r:A ring)") THEN REWRITE_TAC [EXTENSION] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"ring_1 r:A"))) THEN REWRITE_TAC [RING_1, ring_setadd, IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"u:A") (X_CHOOSE_THEN (← q r"v:A") STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"(u:A) IN ring_carrier r /\ (v:A) IN ring_carrier r") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET, RING_IDEAL_IDEAL_POW], ALL_TAC] THEN EXISTS_TAC (← q r"ring_mul r a v:A") THEN SUBGOAL_THEN (← q r"ring_mul r a v IN (Q:A->bool)") ASSUME_TAC THENL [ASM_SIMP_TAC [IN_RING_IDEAL_LMUL], ASM_SIMP_TAC []] THEN SUBGOAL_THEN (← q r"ring_coset r P (ring_mul r a v) = ring_coset r P (a:A)") (fun th => ASM_REWRITE_TAC [th]) THEN ASM_SIMP_TAC [RING_COSET_EQ, RING_MUL] THEN SUBGOAL_THEN (← q r"ring_sub r (ring_mul r a v) a = ring_neg r (ring_mul r a (u:A))") SUBST1_TAC THENL [MP_TAC r1 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC IN_RING_IDEAL_NEG THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"P:A->bool"), (← q r"1"), (← q r"e:num")] IDEAL_POW_ANTIMONO) THEN ASM_SIMP_TAC [IDEAL_POW_1, RING_IDEAL_IMP_SUBSET] THEN ANTS_TAC THENL [ASM_ARITH_TAC, ASM SET_TAC []])

  let ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW ← prove
    r"!r:A ring n w p P Q e.
        dedekind_domain r /\ free_basis (integer_ring,r) (ring_of_int r) n w /\
        prime p /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\ ring_ideal r Q /\
        ring_setadd r (ideal_pow r P e) Q = ring_carrier r /\
        ideal_pow r P e INTER Q = ideal_generated r {ring_of_num r p} /\
        ~(p divides e)
        ==> ?x. x IN Q /\
                ~(&p divides
                  algebra_trace (integer_ring,r) (ring_of_int r) x)"
    (REPEAT STRIP_TAC THEN MP_TAC (← SPEC_ALL ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW_DIVIDES) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [])

  let NUMBER_FIELD_DIFFERENT_WILD ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(p ==> (q <=> r)) ==> (p ==> q <=> p ==> r)")
    let r2 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    let r3 ← SET_RULE (← q r"s = t ==> (s:A->bool) SUBSET t")
    let r4 ← ARITH_RULE (← q r"~(SUC e <= e)")
    prove
      r"!k:A ring P p.
          number_field k /\ prime_ideal (ring_of_integers k) P /\
          prime p /\ ring_of_num k p IN P
          ==> (number_field_different (subfield_generated k {ring_0 k},k) I SUBSET
               ideal_pow (ring_of_integers k) P
                 (ramification_index (integer_ring,ring_of_integers k)
                                     (ring_of_int k) P) <=>
               p divides ramification_index (integer_ring,ring_of_integers k)
                                             (ring_of_int k) P)"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"w:num->A")) o (MATCH_MP RING_OF_INTEGERS_FREE)) THEN ABBREV_TAC (← q r"n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I") THEN SUBGOAL_THEN (← q r"~(P = {ring_0 k:A})") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ring_of_num k p IN {ring_0 k:A}") THEN REWRITE_TAC [IN_SING, RING_OF_NUM_EQ_0] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SIMP_TAC [DIVIDES_ZERO] THEN ASM_MESON_TAC [PRIME_IMP_NZ], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] RAMIFICATION_INDEX_PRIME) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] RING_OF_INTEGERS_IDEAL_GENERATED_PRIME) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN ABBREV_TAC (← q r"e = ramification_index (integer_ring,ring_of_integers k)
                      (ring_of_int k) (P:A->bool)") THEN ABBREV_TAC (← q r"q = ideal_generated (ring_of_integers k) {ring_of_num k p:A}") THEN STRIP_TAC THEN DISCH_THEN (ASSUME_TAC o SYM) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_RING_OF_INTEGERS)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP PRIME_IMP_RING_IDEAL) o (checkM (fun th => (do let z10 ← (q r"prime_ideal (ring_of_integers k) (P:A->bool)"); let z9 ← (do let z8 ← (pure th); pure (concl z8)); pure (z9 == z10)))))) THEN SUBGOAL_THEN (← q r"maximal_ideal (ring_of_integers k) (P:A->bool)") ASSUME_TAC THENL [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal (ring_of_integers k) (q:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "q" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"!m. q SUBSET ideal_pow (ring_of_integers (k:A ring)) P m <=> m <= e") ASSUME_TAC THENL [ASM_SIMP_TAC [DEDEKIND_IDEAL_SUBSET_POW_VALUATION, RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"?Q. ring_ideal (ring_of_integers k) Q /\
          ideal_prod (ring_of_integers k)
            (ideal_pow (ring_of_integers k) P e) Q = (q:A->bool)") (X_CHOOSE_THEN (← q r"Q:A->bool") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pq"))) THENL [EXISTS_TAC (← q r"ideal_quotient (ring_of_integers k) q
          (ideal_pow (ring_of_integers k) (P:A->bool) e)") THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_QUOTIENT, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW] THEN MATCH_MP_TAC DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW, LE_REFL], ALL_TAC] THEN SUBGOAL_THEN (← q r"~((Q:A->bool) SUBSET P)") ASSUME_TAC THENL [DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"SUC e")) o (checkM (fun z5 => (do let z6 ← (do let z7 ← (pure z5); pure (concl z7)); pure (is_forall z6)))))) THEN REWRITE_TAC [r4] THEN USE_THEN "pq" (SUBST1_TAC o SYM) THEN REWRITE_TAC [IDEAL_POW_SUC] THEN TRANS_TAC SUBSET_TRANS (← q r"ideal_prod (ring_of_integers k)
          (ideal_pow (ring_of_integers k) P e) (P:A->bool)") THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_PROD_MONO THEN ASM_REWRITE_TAC [SUBSET_REFL], MATCH_MP_TAC r3 THEN MATCH_MP_TAC IDEAL_PROD_COMM THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW]], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(Q = {ring_0 k:A})") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"~({ring_0 k:A} SUBSET P)") THEN REWRITE_TAC [SING_SUBSET] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool")] IN_RING_IDEAL_0) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_setadd (ring_of_integers k) (ideal_pow (ring_of_integers k) P e) Q =
      ring_carrier(ring_of_integers k) /\
      ideal_pow (ring_of_integers k) P e INTER Q = (q:A->bool)") STRIP_ASSUME_TAC THENL [MATCH_MP_TAC r2 THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"Q:A->bool"), (← q r"e:num"), (← q r"1:num")] COMAXIMAL_IDEAL_POW) THEN ASM_SIMP_TAC [IDEAL_POW_1, MAXIMAL_IDEAL_COMAXIMAL], DISCH_TAC THEN USE_THEN "pq" (SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC IDEAL_PROD_COMAXIMAL THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"p:num"), (← q r"P:A->bool"), (← q r"Q:A->bool"), (← q r"e:num")] ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW_DIVIDES) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"!x:A. x IN Q ==> x IN ring_carrier(ring_of_integers k) /\
                       x IN ring_carrier k") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET, RING_OF_INTEGERS_SUBSET], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"!x:A. x IN Q
            ==> !d. d IN number_field_different
                           (subfield_generated k {ring_0 k},k) I
                    ==> ring_mul k x d IN (q:A->bool)") THEN CONJ_TAC THENL [EQ_TAC THENL [DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN X_GEN_TAC (← q r"d:A") THEN DISCH_TAC THEN USE_THEN "pq" (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"(d:A) IN ring_carrier(ring_of_integers k)") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET, RING_IDEAL_NUMBER_FIELD_DIFFERENT], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul k x d = ring_mul (ring_of_integers k) d (x:A)") SUBST1_TAC THENL [REWRITE_TAC [RING_OF_INTEGERS] THEN MATCH_MP_TAC RING_MUL_SYM THEN ASM_MESON_TAC [RING_OF_INTEGERS_SUBSET, SUBSET], ALL_TAC] THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_SIMP_TAC [] THEN ASM SET_TAC [], DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"Q:A->bool"), (← q r"number_field_different
                          (subfield_generated k {ring_0 k},k) I:A->bool"), (← q r"ideal_pow (ring_of_integers k) P e:A->bool")] DEDEKIND_IDEAL_PROD_SUBSET_CANCEL) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_POW, RING_IDEAL_NUMBER_FIELD_DIFFERENT, RING_OF_INTEGERS] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN SUBGOAL_THEN (← q r"ideal_prod (ring_of_integers k) Q
            (ideal_pow (ring_of_integers k) P e) = (q:A->bool)") SUBST1_TAC THENL [USE_THEN "pq" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IDEAL_PROD_COMM THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_POW], ALL_TAC] THEN MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN ASM_SIMP_TAC []], ALL_TAC] THEN TRANS_TAC EQ_TRANS (← q r"!x:A. x IN Q
            ==> !y. y IN ring_carrier(ring_of_integers k)
                    ==> &p divides
                        algebra_trace (integer_ring,ring_of_integers k)
                          (ring_of_int k) (ring_mul k x y)") THEN CONJ_TAC THENL [AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC r1 THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"w:num->A"), (← q r"p:num"), (← q r"x:A")] NUMBER_FIELD_CODIFFERENT_DIV_NUM) THEN ASM_SIMP_TAC [PRIME_IMP_NZ] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC (← ISPECL [(← q r"subfield_generated k {ring_0 k}:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"ring_of_num k p:A"), (← q r"x:A")] NUMBER_FIELD_CODIFFERENT_DIV) THEN ANTS_TAC THENL [FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN ASM_SIMP_TAC [IN_SUBRING_NUM, RING_OF_INTEGERS_SUBRING, RING_OF_NUM_EQ_0, DIVIDES_ZERO, PRIME_IMP_NZ, FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION], DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [(← ASSUME (← q r"ideal_generated (ring_of_integers k) {ring_of_num k p:A} = q"))]], ALL_TAC] THEN EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THENL [FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"x:A"))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"ring_1 k:A"))) THEN ASM_SIMP_TAC [IN_SUBRING_1, RING_OF_INTEGERS_SUBRING, RING_MUL_RID], X_GEN_TAC (← q r"y:A") THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"Q:A->bool"), (← q r"x:A"), (← q r"y:A")] IN_RING_IDEAL_RMUL) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS]])

  let NUMBER_FIELD_DIFFERENT_TAME ← prove
    r"!k:A ring P p.
        number_field k /\ prime_ideal (ring_of_integers k) P /\
        prime p /\ ring_of_num k p IN P /\
        ~(p divides ramification_index (integer_ring,ring_of_integers k)
                                        (ring_of_int k) P)
        ==> ~(number_field_different (subfield_generated k {ring_0 k},k) I
              SUBSET
              ideal_pow (ring_of_integers k) P
               (ramification_index (integer_ring,ring_of_integers k)
                                   (ring_of_int k) P))"
    (MESON_TAC [NUMBER_FIELD_DIFFERENT_WILD])

  let (NUMBER_FIELD_DIFFERENT_VALUATION_TAME_Q, NUMBER_FIELD_DIFFERENT_VALUATION_WILD_Q) ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"p divides ramification_index (integer_ring,ring_of_integers k)
                (ring_of_int k) (P:A->bool)"
    let q2 ← q r"number_field_different
                    (subfield_generated k {ring_0 k},k) I:A->bool"
    let q3 ← q r"P:A->bool"
    let q4 ← q r"ring_of_integers k:A ring"
    let v5 ← ISPECL [q4, q3, q2] DEDEKIND_IDEAL_SUBSET_POW_VALUATION
    let q6 ← q r"p:num"
    let q7 ← q r"P:A->bool"
    let q8 ← q r"k:A ring"
    let v9 ← ISPECL [q8, q7, q6] NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q
    let q10 ← q r"P:A->bool"
    let q11 ← q r"I:A->A"
    let q12 ← q r"k:A ring"
    let q13 ← q r"subfield_generated k {ring_0 k}:A ring"
    let v14 ← ISPECL [q13, q12, q11, q10] NUMBER_FIELD_DIFFERENT_SUBSET_RAMIFICATION
    let q15 ← q r"number_field_different (subfield_generated k {ring_0 k},k) I SUBSET
    ideal_pow (ring_of_integers k) P
      (ramification_index (integer_ring,ring_of_integers k)
         (ring_of_int k) (P:A->bool) - 1)"
    let q16 ← q r"p:num"
    let q17 ← q r"P:A->bool"
    let q18 ← q r"k:A ring"
    let v19 ← ISPECL [q18, q17, q16] NUMBER_FIELD_DIFFERENT_WILD
    let q20 ← q r"ring_of_num k p IN {ring_0 k:A}"
    let q21 ← q r"~(P = {ring_0 k:A})"
    let q22 ← q r"(p ==> q /\ r) ==> (p ==> q) /\ (p ==> r)"
    let r23 ← TAUT q22
    let p24 ← prove r"(!k:A ring P p.
        number_field k /\ prime_ideal (ring_of_integers k) P /\
        prime p /\ ring_of_num k p IN P
        ==> ramification_index (integer_ring,ring_of_integers k)
              (ring_of_int k) P - 1 <=
            ideal_valuation (ring_of_integers k) P
              (number_field_different (subfield_generated k {ring_0 k},k) I) /\
            (ideal_valuation (ring_of_integers k) P
               (number_field_different (subfield_generated k {ring_0 k},k) I) =
             ramification_index (integer_ring,ring_of_integers k)
               (ring_of_int k) P - 1 <=>
             ~(p divides ramification_index (integer_ring,ring_of_integers k)
                           (ring_of_int k) P))) /\
   (!k:A ring P p.
        number_field k /\ prime_ideal (ring_of_integers k) P /\
        prime p /\ ring_of_num k p IN P
        ==> (ramification_index (integer_ring,ring_of_integers k)
               (ring_of_int k) P <=
             ideal_valuation (ring_of_integers k) P
               (number_field_different
                  (subfield_generated k {ring_0 k},k) I) <=>
             p divides ramification_index (integer_ring,ring_of_integers k)
                         (ring_of_int k) P))" (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC r23 THEN STRIP_TAC THEN SUBGOAL_THEN q21 ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC q20 THEN REWRITE_TAC [IN_SING, RING_OF_NUM_EQ_0] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SIMP_TAC [DIVIDES_ZERO] THEN ASM_MESON_TAC [PRIME_IMP_NZ], ALL_TAC] THEN MP_TAC v19 THEN SUBGOAL_THEN q15 MP_TAC THENL [MP_TAC v14 THEN ASM_SIMP_TAC [RAMIFICATION_INDEX_PRIME_SUBFIELD, FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, PRIME_IMP_RING_IDEAL], ALL_TAC] THEN MP_TAC v9 THEN ASM_REWRITE_TAC [] THEN MP_TAC v5 THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, RING_IDEAL_NUMBER_FIELD_DIFFERENT, NUMBER_FIELD_DIFFERENT_NONZERO, FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION, RING_OF_INTEGERS] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN ASM_CASES_TAC q1 THEN ASM_REWRITE_TAC [] THEN ARITH_TAC)
    CONJ_PAIR p24

  let NUMBER_FIELD_IDEAL_NORM_PRIME_EXPONENT ← prove
    r"!k:A ring j p.
        number_field k /\ ring_ideal (ring_of_integers k) j /\
        ~(j = {ring_0 k}) /\ prime p
        ==> index p (ideal_norm (ring_of_integers k) j) =
            nsum {P | prime_ideal (ring_of_integers k) P /\
                      ring_of_num k p IN P}
                 (\P. residue_degree (integer_ring,ring_of_integers k)
                        (ring_of_int k) P *
                      ideal_valuation (ring_of_integers k) P j)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_RING_OF_INTEGERS)) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool")] IDEAL_NORM_FACTORIZATION) THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_FACTORIZATION) THEN ASM_SIMP_TAC [RING_OF_INTEGERS, RING_OF_INTEGERS_FINITE_QUOTIENT] THEN ABBREV_TAC (← q r"S = {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
             (j:A->bool) SUBSET P}") THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"!P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k:A})
        ==> ~(ideal_norm (ring_of_integers k) P = 0) /\
            index p (ideal_norm (ring_of_integers k) P) =
            if ring_of_num k p IN P
            then residue_degree (integer_ring,ring_of_integers k)
                   (ring_of_int k) P
            else 0") ASSUME_TAC THENL [X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool")] RING_OF_INTEGERS_PRIME_IDEAL_ABOVE) THEN ASM_REWRITE_TAC [EXISTS_UNIQUE_THM] THEN DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q r"q:num") STRIP_ASSUME_TAC) (LABEL_TAC "uniq")) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool"), (← q r"q:num")] RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [EXP_EQ_0, PRIME_IMP_NZ, INDEX_EXP, INDEX_PRIME] THEN COND_CASES_TAC THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES], COND_CASES_TAC THEN REWRITE_TAC [MULT_CLAUSES] THEN USE_THEN "uniq" (MP_TAC o (SPECL [(← q r"p:num"), (← q r"q:num")])) THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC []], ALL_TAC] THEN SUBGOAL_THEN (← q r"!P. P IN S ==> prime_ideal (ring_of_integers k) P /\
                   ~(P = {ring_0 k:A}) /\ (j:A->bool) SUBSET P") ASSUME_TAC THENL [EXPAND_TAC "S" THEN SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN wPart lhand (lhand o rand) INDEX_NPRODUCT THEN ANTS_TAC THENL [ASM_REWRITE_TAC [EXP_EQ_0] THEN ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN ASM_SIMP_TAC [INDEX_EXP] THEN ABBREV_TAC (← q r"U = {P | P IN S /\ ring_of_num k p IN (P:A->bool)}") THEN TRANS_TAC EQ_TRANS (← q r"nsum U (\P. residue_degree (integer_ring,ring_of_integers k)
                  (ring_of_int k) P *
                ideal_valuation (ring_of_integers k) P (j:A->bool))") THEN CONJ_TAC THENL [MATCH_MP_TAC NSUM_EQ_SUPERSET THEN EXPAND_TAC "U" THEN REWRITE_TAC [IN_ELIM_THM, SUBSET] THEN ASM_SIMP_TAC [FINITE_RESTRICT] THEN CONJ_TAC THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THENL [ASM_SIMP_TAC [MULT_CLAUSES] THEN ARITH_TAC, ASM_CASES_TAC (← q r"ring_of_num k p IN (P:A->bool)") THENL [ASM_MESON_TAC [], ASM_SIMP_TAC [MULT_CLAUSES]]], ALL_TAC] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN EXPAND_TAC "U" THEN EXPAND_TAC "S" THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ring_of_num k p IN {ring_0 k:A}") THEN REWRITE_TAC [IN_SING, RING_OF_NUM_EQ_0] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SIMP_TAC [DIVIDES_ZERO] THEN ASM_MESON_TAC [PRIME_IMP_NZ], ALL_TAC] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN REWRITE_TAC [MULT_EQ_0] THEN DISJ2_TAC THEN SUBGOAL_THEN (← q r"~(P = {ring_0 k:A})") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"ring_of_num k p IN {ring_0 k:A}") THEN REWRITE_TAC [IN_SING, RING_OF_NUM_EQ_0] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [number_field]))) THEN SIMP_TAC [DIVIDES_ZERO] THEN ASM_MESON_TAC [PRIME_IMP_NZ], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"P:A->bool"), (← q r"j:A->bool")] IDEAL_VALUATION_EQ_0) THEN ASM_REWRITE_TAC [RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC [SUBSET])

  let NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT ← prove
    r"!k:A ring p.
        number_field k /\ prime p
        ==> index p (num_of_int(abs(number_field_discriminant k))) =
            nsum {P | prime_ideal (ring_of_integers k) P /\
                      ring_of_num k p IN P}
                 (\P. residue_degree (integer_ring,ring_of_integers k)
                        (ring_of_int k) P *
                      ideal_valuation (ring_of_integers k) P
                        (number_field_different
                           (subfield_generated k {ring_0 k},k) I))"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [(← GSYM NUMBER_FIELD_IDEAL_NORM_DIFFERENT)] THEN MATCH_MP_TAC NUMBER_FIELD_IDEAL_NORM_PRIME_EXPONENT THEN ASM_SIMP_TAC [RING_IDEAL_NUMBER_FIELD_DIFFERENT, NUMBER_FIELD_DIFFERENT_NONZERO, FIELD_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD, RING_HOMOMORPHISM_SUBFIELD_INCLUSION])

  let NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT_TAME ← prove
    r"!k:A ring p.
        number_field k /\ prime p /\
        (!P. prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P
             ==> ~(p divides ramification_index
                               (integer_ring,ring_of_integers k)
                               (ring_of_int k) P))
        ==> index p (num_of_int(abs(number_field_discriminant k))) =
            nsum {P | prime_ideal (ring_of_integers k) P /\
                      ring_of_num k p IN P}
                 (\P. residue_degree (integer_ring,ring_of_integers k)
                        (ring_of_int k) P *
                      (ramification_index (integer_ring,ring_of_integers k)
                         (ring_of_int k) P - 1))"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT] THEN MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC [NUMBER_FIELD_DIFFERENT_VALUATION_TAME_Q])

  let NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT_GE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"a < b ==> ~(a = b:num)")
    prove
      r"!k:A ring p.
          number_field k /\ prime p
          ==> nsum {P | prime_ideal (ring_of_integers k) P /\
                        ring_of_num k p IN P}
                   (\P. residue_degree (integer_ring,ring_of_integers k)
                          (ring_of_int k) P *
                        (ramification_index (integer_ring,ring_of_integers k)
                           (ring_of_int k) P - 1))
              <= index p (num_of_int(abs(number_field_discriminant k))) /\
              (nsum {P | prime_ideal (ring_of_integers k) P /\
                         ring_of_num k p IN P}
                    (\P. residue_degree (integer_ring,ring_of_integers k)
                           (ring_of_int k) P *
                         (ramification_index (integer_ring,ring_of_integers k)
                            (ring_of_int k) P - 1)) =
               index p (num_of_int(abs(number_field_discriminant k))) <=>
               !P. prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P
                   ==> ~(p divides ramification_index
                                     (integer_ring,ring_of_integers k)
                                     (ring_of_int k) P))"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"p:num")] RING_OF_INTEGERS_IDEAL_GENERATED_PRIME) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ABBREV_TAC (← q r"ps = {P | prime_ideal (ring_of_integers k) P /\
               ring_of_num k p IN (P:A->bool)}") THEN SUBGOAL_THEN (← q r"!P:A->bool. P IN ps
          ==> 1 <= residue_degree (integer_ring,ring_of_integers k)
                     (ring_of_int k) P /\
              ramification_index (integer_ring,ring_of_integers k)
                (ring_of_int k) P - 1 <=
              ideal_valuation (ring_of_integers k) P
                (number_field_different (subfield_generated k {ring_0 k},k) I) /\
              (ideal_valuation (ring_of_integers k) P
                 (number_field_different (subfield_generated k {ring_0 k},k) I) =
               ramification_index (integer_ring,ring_of_integers k)
                 (ring_of_int k) P - 1 <=>
               ~(p divides ramification_index (integer_ring,ring_of_integers k)
                             (ring_of_int k) P))") ASSUME_TAC THENL [EXPAND_TAC "ps" THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"P:A->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] NUMBER_FIELD_DIFFERENT_VALUATION_TAME_Q) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"P:A->bool"), (← q r"p:num")] NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q) THEN ASM_SIMP_TAC [], ALL_TAC] THEN CONJ_TAC THENL [MATCH_MP_TAC NSUM_LE THEN ASM_SIMP_TAC [LE_MULT_LCANCEL], ALL_TAC] THEN EQ_TAC THENL [ONCE_REWRITE_TAC [(← GSYM CONTRAPOS_THM)] THEN REWRITE_TAC [NOT_FORALL_THM, NOT_IMP] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"P:A->bool") STRIP_ASSUME_TAC) THEN MATCH_MP_TAC r1 THEN MATCH_MP_TAC NSUM_LT THEN ASM_SIMP_TAC [LE_MULT_LCANCEL] THEN EXISTS_TAC (← q r"P:A->bool") THEN SUBGOAL_THEN (← q r"(P:A->bool) IN ps") ASSUME_TAC THENL [EXPAND_TAC "ps" THEN ASM_REWRITE_TAC [IN_ELIM_THM], ALL_TAC] THEN ASM_REWRITE_TAC [LT_MULT_LCANCEL] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"P:A->bool"))) THEN ASM_REWRITE_TAC [] THEN ARITH_TAC, DISCH_TAC THEN MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"P:A->bool") THEN DISCH_TAC THEN REWRITE_TAC [] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN SUBGOAL_THEN (← q r"prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN (P:A->bool)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"(P:A->bool) IN ps") THEN EXPAND_TAC "ps" THEN SIMP_TAC [IN_ELIM_THM], ASM_MESON_TAC []]])

  -- @@RETURN BEGIN
  return { ALGEBRA_TRACE_INTEGER_MOD_SPLIT,
           ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW_DIVIDES,
           ALGEBRA_TRACE_INTEGER_MOD_COMAXIMAL_POW, NUMBER_FIELD_DIFFERENT_WILD,
           NUMBER_FIELD_DIFFERENT_TAME, NUMBER_FIELD_DIFFERENT_VALUATION_TAME_Q,
           NUMBER_FIELD_DIFFERENT_VALUATION_WILD_Q,
           NUMBER_FIELD_IDEAL_NORM_PRIME_EXPONENT,
           NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT,
           NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT_TAME,
           NUMBER_FIELD_DISCRIMINANT_PRIME_EXPONENT_GE }
  -- @@RETURN END

end HolANT.DifferentExponent
