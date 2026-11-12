/- ========================================================================= -/
/- ANT: Quadratic Gauss sums and the quadratic subfield of a ...           -/
/- ========================================================================= -/
/- File: HolANT/GaussSum.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/gauss_sum.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antgausssumdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/isum.ml, Library/integer.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/jacobi.ml, Library/frag.ml, Library/grouptheory.ml, Library/modmul_group.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/quadratic.ml, ANT/prime_split.ml, ANT/trace_form.ml, ANT/finite_field_trace.ml, ANT/ramification.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/dedekind_kummer.ml, ANT/quadratic_split.ml, Library/symmetric_group.ml, Library/galois.ml, Library/ring_groups.ml, Library/finite_fields.ml, ANT/cyclotomic_poly.ml, ANT/power_basis.ml, ANT/cyclotomic_field.ml, ANT/cyclotomic_integers.ml, Library/cyclotomic.ml, ANT/cyclotomic_galois.ml, ANT/cyclotomic_subfields.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.GaussSum fills them).

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
import HolLibrary.Isum
import HolLibrary.Integer
import HolLibrary.Products
import HolLibrary.Multiplicative
import HolLibrary.Primitive
import HolLibrary.Jacobi
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.ModmulGroup
import HolANT.Algmisc
import HolANT.Integral
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.IdealArith
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.Discriminant
import HolANT.Quadratic
import HolANT.PrimeSplit
import HolANT.TraceForm
import HolANT.FiniteFieldTrace
import HolANT.Ramification
import HolANT.DedekindLocal
import HolANT.DedekindValuation
import HolANT.Classgroup
import HolANT.RelativeSplit
import HolANT.RelativeDegree
import HolANT.NfValuation
import HolANT.Integrality
import HolANT.DedekindKummer
import HolANT.QuadraticSplit
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.RingGroups
import HolLibrary.FiniteFields
import HolANT.CyclotomicPoly
import HolANT.PowerBasis
import HolANT.CyclotomicField
import HolANT.CyclotomicIntegers
import HolLibrary.Cyclotomic
import HolANT.CyclotomicGalois
import HolANT.CyclotomicSubfields

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
open HolANT.Discriminant
open HolANT.Quadratic
open HolANT.PrimeSplit
open HolANT.TraceForm
open HolANT.FiniteFieldTrace
open HolANT.Ramification
open HolANT.DedekindLocal
open HolANT.DedekindValuation
open HolANT.Classgroup
open HolANT.RelativeSplit
open HolANT.RelativeDegree
open HolANT.NfValuation
open HolANT.Integrality
open HolANT.DedekindKummer
open HolANT.QuadraticSplit
open HolANT.CyclotomicPoly
open HolANT.PowerBasis
open HolANT.CyclotomicField
open HolANT.CyclotomicIntegers
open HolANT.CyclotomicGalois
open HolANT.CyclotomicSubfields

namespace HolANT.GaussSum

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (COPRIME_0 COPRIME_SYM CYCLIC_MODMUL_GROUP CYCLOTOMIC_FIELD_SUBFIELD_UNIQUE
   DIVIDES_LE DIVIDES_REFL EQ_TRANS EXP_1 EXP_2 EXTENSION_DEGREE_SIMPLE
   FIELD_EXTENSION_IMP_HOMOMORPHISM FIELD_EXTENSION_SUBFIELD_GENERATED
   FIELD_IMP_INTEGRAL_DOMAIN FIELD_IMP_NONTRIVIAL_RING FIELD_SUBFIELD_GENERATED
   FINITE_NUMSEG_LT IMAGE_I INT_ABS_MUL INT_ABS_NEG INT_ABS_NUM INT_ABS_POW
   INT_MUL_LID INT_OF_NUM_EQ INT_POW_ONE IN_ELIM_THM IRREDUCIBLE_IMP_POLY_DEG_NZ
   I_THM JACOBI_EQ_0 JACOBI_LMUL JACOBI_MINUS1 JACOBI_MOD JACOBI_PRIME
   JACOBI_SQUARED JACOBI_SUM_RESIDUES MINIMAL_POLYNOMIAL_DEG_EQ_1
   MINIMAL_POLYNOMIAL_DEG_LE MINIMAL_POLYNOMIAL_IRREDUCIBLE MULT_CLAUSES
   NUMBER_FIELD_ALGEBRAIC NUMBER_FIELD_IMP_FIELD NUM_OF_INT_OF_NUM POLY_DEG_0
   PRIME_1 PRIME_COPRIME_EQ PRIME_GE_2 PRIME_IMP_NZ PRIME_IMP_SQUAREFREE
   PRIME_ODD QUADRATIC_POLY_DEG QUADRATIC_POLY_EXTEND QUADRATIC_POLY_IN_CARRIER
   RING_0 RING_1 RING_ADD_LZERO RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_POW
   RING_HOMOMORPHISM_RING_OF_INT RING_HOMOMORPHISM_SUM RING_MUL RING_MUL_ASSOC
   RING_MUL_LID RING_MUL_LZERO RING_MUL_RID RING_MUL_RZERO RING_OF_INT
   RING_OF_INT_0 RING_OF_INT_1 RING_OF_INT_IN_SUBFIELD_GENERATED
   RING_OF_INT_ISUM RING_OF_INT_MUL RING_OF_INT_OF_NUM RING_OF_NUM RING_POW
   RING_POW_2 RING_POW_ADD RING_POW_MOD_ORDER RING_POW_POW RING_SUB_REFL
   RING_SUM RING_SUM_DELTA RING_SUM_EQ RING_SUM_LMUL RING_SUM_MOD_MULT_REINDEX
   RING_SUM_RMUL RING_SUM_ROOT_OF_UNITY_POWERS RING_SUM_SWAP
   SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD SUBFIELD_GENERATED
   SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED SUBFIELD_GENERATED_SING_ALGEBRAIC
   SUBFIELD_SUBFIELD_GENERATED SUBFIELD_SUBFIELD_GENERATED_EQ number_field o_THM
   ring_pow : thm)
  deriving Inhabited

/-- What gauss_sum.ml uses from Session besides theorems. -/
structure GaussSumDeps where
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
/- gauss_sum.ml phrases from line 63 to 395                               -/
/- ---------------------------------------------------------------------- -/

structure GaussSum where
  -- @@FIELDS
  QUADRATIC_GAUSS_SUM : thm
  QUADRATIC_GAUSS_SUM_HOMOMORPHISM : thm
  NUMBER_FIELD_SQRT_DEGREE : thm
  CYCLOTOMIC_FIELD_QUADRATIC_SUBFIELD : thm
  CYCLOTOMIC_FIELD_QUADRATIC_SUBFIELD_GAUSS_SUM : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupGaussSum [HolBase] (D : GaussSumDeps) :
    ExceptT String IO GaussSum := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INT_ARITH_TAC, RING_RULE,
        TAUT, .. } := D
  let { COPRIME_0, COPRIME_SYM, CYCLIC_MODMUL_GROUP, CYCLOTOMIC_FIELD_SUBFIELD_UNIQUE,
        DIVIDES_LE, DIVIDES_REFL, EQ_TRANS, EXP_1, EXP_2, EXTENSION_DEGREE_SIMPLE,
        FIELD_EXTENSION_IMP_HOMOMORPHISM, FIELD_EXTENSION_SUBFIELD_GENERATED,
        FIELD_IMP_INTEGRAL_DOMAIN, FIELD_IMP_NONTRIVIAL_RING, FIELD_SUBFIELD_GENERATED,
        FINITE_NUMSEG_LT, IMAGE_I, INT_ABS_MUL, INT_ABS_NEG, INT_ABS_NUM, INT_ABS_POW,
        INT_MUL_LID, INT_OF_NUM_EQ, INT_POW_ONE, IN_ELIM_THM,
        IRREDUCIBLE_IMP_POLY_DEG_NZ, I_THM, JACOBI_EQ_0, JACOBI_LMUL, JACOBI_MINUS1,
        JACOBI_MOD, JACOBI_PRIME, JACOBI_SQUARED, JACOBI_SUM_RESIDUES,
        MINIMAL_POLYNOMIAL_DEG_EQ_1, MINIMAL_POLYNOMIAL_DEG_LE,
        MINIMAL_POLYNOMIAL_IRREDUCIBLE, MULT_CLAUSES, NUMBER_FIELD_ALGEBRAIC,
        NUMBER_FIELD_IMP_FIELD, NUM_OF_INT_OF_NUM, POLY_DEG_0, PRIME_1,
        PRIME_COPRIME_EQ, PRIME_GE_2, PRIME_IMP_NZ, PRIME_IMP_SQUAREFREE, PRIME_ODD,
        QUADRATIC_POLY_DEG, QUADRATIC_POLY_EXTEND, QUADRATIC_POLY_IN_CARRIER, RING_0,
        RING_1, RING_ADD_LZERO, RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_POW,
        RING_HOMOMORPHISM_RING_OF_INT, RING_HOMOMORPHISM_SUM, RING_MUL, RING_MUL_ASSOC,
        RING_MUL_LID, RING_MUL_LZERO, RING_MUL_RID, RING_MUL_RZERO, RING_OF_INT,
        RING_OF_INT_0, RING_OF_INT_1, RING_OF_INT_IN_SUBFIELD_GENERATED,
        RING_OF_INT_ISUM, RING_OF_INT_MUL, RING_OF_INT_OF_NUM, RING_OF_NUM, RING_POW,
        RING_POW_2, RING_POW_ADD, RING_POW_MOD_ORDER, RING_POW_POW, RING_SUB_REFL,
        RING_SUM, RING_SUM_DELTA, RING_SUM_EQ, RING_SUM_LMUL,
        RING_SUM_MOD_MULT_REINDEX, RING_SUM_RMUL, RING_SUM_ROOT_OF_UNITY_POWERS,
        RING_SUM_SWAP, SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD, SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED, SUBFIELD_GENERATED_SING_ALGEBRAIC,
        SUBFIELD_SUBFIELD_GENERATED, SUBFIELD_SUBFIELD_GENERATED_EQ, number_field,
        o_THM, ring_pow, .. } := D.core1
  -- @@SCOPE END

  let QUADRATIC_GAUSS_SUM ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"~(p = 0) ==> p - 1 < p")
    let r2 ← ARITH_RULE (← q r"~(p = 0) ==> 1 + (p - 1) = p")
    let r3 ← RING_RULE (← q r"!r u v x y:A.
        u IN ring_carrier r /\ v IN ring_carrier r /\
        x IN ring_carrier r /\ y IN ring_carrier r /\
        ring_mul r u u = ring_1 r
        ==> ring_mul r (ring_mul r u x) (ring_mul r (ring_mul r u v) y) =
            ring_mul r v (ring_mul r x y)")
    prove
      r"!(r:A ring) z p.
          integral_domain r /\ prime p /\ ~(p = 2) /\
          z IN ring_carrier r /\ ring_order r z = p
          ==> ring_pow r (ring_sum r {a | a < p}
                            (\a. ring_mul r (ring_of_int r (jacobi(a,p)))
                                            (ring_pow r z a))) 2 =
              ring_of_int r (--(&1) pow ((p - 1) DIV 2) * &p)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_NZ)) THEN ABBREV_TAC (← q r"g = ring_sum r {a | a < p}
            (\a. ring_mul r (ring_of_int r (jacobi(a,p)))
                            (ring_pow r (z:A) a))") THEN SUBGOAL_THEN (← q r"(g:A) IN ring_carrier r") ASSUME_TAC THENL [EXPAND_TAC "g" THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN SUBGOAL_THEN (← q r"!a. a < p
          ==> ring_mul r (ring_mul r (ring_of_int r (jacobi(a,p)))
                                     (ring_pow r z a)) g =
              ring_sum r {t | t < p}
                (\t. ring_mul r (ring_of_int r (jacobi(t,p)))
                                (ring_pow r (z:A) ((1 + t) * a)))") ASSUME_TAC THENL [X_GEN_TAC (← q r"a:num") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"a = 0") THENL [ASM_REWRITE_TAC [MULT_CLAUSES, ring_pow] THEN SUBGOAL_THEN (← q r"jacobi(0,p) = &0") SUBST1_TAC THENL [REWRITE_TAC [JACOBI_EQ_0, COPRIME_0] THEN ASM_MESON_TAC [PRIME_1], ALL_TAC] THEN ASM_SIMP_TAC [RING_OF_INT_0, RING_MUL_LZERO, RING_1] THEN SIMP_TAC [RING_MUL_RID, RING_OF_INT] THEN ASM_SIMP_TAC [(← GSYM RING_OF_INT_ISUM), FINITE_NUMSEG_LT, JACOBI_SUM_RESIDUES, RING_OF_INT_0], ALL_TAC] THEN SUBGOAL_THEN (← q r"coprime((a:num),p)") ASSUME_TAC THENL [ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_SIMP_TAC [PRIME_COPRIME_EQ] THEN DISCH_THEN (MP_TAC o (MATCH_MP DIVIDES_LE)) THEN ASM_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"g = ring_sum r {t | t < p}
              (\t. ring_mul r
                     (ring_mul r (ring_of_int r (jacobi(a,p)))
                                 (ring_of_int r (jacobi(t,p))))
                     (ring_pow r (z:A) (a * t)))") SUBST1_TAC THENL [EXPAND_TAC "g" THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:num"), (← q r"a:num"), (← q r"\b. ring_mul r (ring_of_int r (jacobi(b,p))) (ring_pow r (z:A) b)")] RING_SUM_MOD_MULT_REINDEX) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"t:num") THEN DISCH_TAC THEN REWRITE_TAC [JACOBI_MOD, JACOBI_LMUL, RING_OF_INT_MUL] THEN AP_TERM_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"z:A"), (← q r"a * t:num")] RING_POW_MOD_ORDER) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul r (ring_of_int r (jacobi(a,p))) (ring_of_int r (jacobi(a,p))) =
        ring_1 (r:A ring)") ASSUME_TAC THENL [REWRITE_TAC [(← GSYM RING_OF_INT_MUL), (← GSYM JACOBI_LMUL)] THEN REWRITE_TAC [(← GSYM EXP_2), JACOBI_SQUARED] THEN ASM_REWRITE_TAC [RING_OF_INT_1], ALL_TAC] THEN SIMP_TAC [(← GSYM RING_SUM_LMUL), FINITE_NUMSEG_LT, RING_MUL, RING_OF_INT, RING_POW, (← ASSUME (← q r"(z:A) IN ring_carrier r"))] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"t:num") THEN DISCH_TAC THEN REWRITE_TAC [] THEN SUBGOAL_THEN (← q r"ring_pow r (z:A) ((1 + t) * a) =
        ring_mul r (ring_pow r z a) (ring_pow r z (a * t))") SUBST1_TAC THENL [ASM_SIMP_TAC [(← GSYM RING_POW_ADD)] THEN AP_TERM_TAC THEN ARITH_TAC, ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_of_int r (jacobi(a,p)):A"), (← q r"ring_of_int r (jacobi(t,p)):A"), (← q r"ring_pow r (z:A) a"), (← q r"ring_pow r (z:A) (a * t)")] r3) THEN ASM_SIMP_TAC [RING_OF_INT, RING_POW], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow r g 2 =
      ring_sum r {t | t < p}
        (\t. ring_mul r (ring_of_int r (jacobi(t,p)))
               (ring_sum r {a | a < p} (\a. ring_pow r (z:A) ((1 + t) * a))))") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_POW_2] THEN FIRST_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [(← SYM th)])) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"\a. ring_mul r (ring_of_int r (jacobi(a,p))) (ring_pow r (z:A) a)"), (← q r"g:A"), (← q r"{a:num | a < p}")] RING_SUM_RMUL) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, RING_MUL, RING_OF_INT, RING_POW] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN TRANS_TAC EQ_TRANS (← q r"ring_sum r {a | a < p}
          (\a. ring_sum r {t | t < p}
                 (\t. ring_mul r (ring_of_int r (jacobi(t,p)))
                                 (ring_pow r (z:A) ((1 + t) * a))))") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM], ALL_TAC] THEN wPart lhand (lhand o rand) RING_SUM_SWAP THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, RING_MUL, RING_OF_INT, RING_POW] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"t:num") THEN DISCH_TAC THEN REWRITE_TAC [] THEN MATCH_MP_TAC RING_SUM_LMUL THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, RING_OF_INT, RING_POW], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"z:A"), (← q r"p:num")] RING_SUM_ROOT_OF_UNITY_POWERS) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN TRANS_TAC EQ_TRANS (← q r"ring_sum r {t | t < p}
        (\t. if t = p - 1
             then ring_mul r (ring_of_int r (jacobi(p - 1,p))) (ring_of_num r p)
             else ring_0 (r:A ring))") THEN CONJ_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"t:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(p:num) divides (1 + t) <=> t = p - 1") SUBST1_TAC THENL [EQ_TAC THENL [DISCH_THEN (MP_TAC o (MATCH_MP DIVIDES_LE)) THEN ASM_ARITH_TAC, DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [r2, DIVIDES_REFL]], COND_CASES_TAC THEN ASM_SIMP_TAC [RING_MUL_RZERO, RING_OF_INT]], ALL_TAC] THEN REWRITE_TAC [RING_SUM_DELTA, IN_ELIM_THM] THEN ASM_SIMP_TAC [r1, RING_MUL, RING_OF_INT, RING_OF_NUM] THEN MP_TAC (← SPEC (← q r"p:num") JACOBI_MINUS1) THEN ANTS_TAC THENL [ASM_MESON_TAC [PRIME_ODD], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [RING_OF_INT_MUL, RING_OF_INT_OF_NUM])

  let QUADRATIC_GAUSS_SUM_HOMOMORPHISM ← prove
    r"!(r:A ring) s z p c.
        prime p /\ z IN ring_carrier r /\ ring_order r z = p /\
        ring_homomorphism(r,r) s /\ s z = ring_pow r z c /\ coprime(c,p)
        ==> s(ring_sum r {a | a < p}
               (\a. ring_mul r (ring_of_int r (jacobi(a,p)))
                               (ring_pow r z a))) =
            ring_mul r (ring_of_int r (jacobi(c,p)))
              (ring_sum r {a | a < p}
                (\a. ring_mul r (ring_of_int r (jacobi(a,p)))
                                (ring_pow r z a)))"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_NZ)) THEN SUBGOAL_THEN (← q r"(s:A->A) (ring_sum r {a | a < p}
                (\a. ring_mul r (ring_of_int r (jacobi(a,p)))
                                (ring_pow r z a))) =
    ring_sum r {a | a < p}
      (\a. ring_mul r (ring_of_int r (jacobi(a,p))) (ring_pow r z (c * a)))") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"r:A ring"), (← q r"s:A->A")] (← INST_TYPE [((← qty r"num"), (← qty r"K"))] RING_HOMOMORPHISM_SUM)) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o (SPECL [(← q r"\a. ring_mul (r:A ring) (ring_of_int r (jacobi(a,p)))
                               (ring_pow r z a)"), (← q r"{a:num | a < p}")])) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, RING_MUL, RING_OF_INT, RING_POW] THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"a:num") THEN DISCH_TAC THEN REWRITE_TAC [o_THM] THEN FIRST_ASSUM (fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th), (← MATCH_MP RING_HOMOMORPHISM_POW th), RING_OF_INT, RING_POW])) THEN FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_RING_OF_INT th)])) THEN ASM_SIMP_TAC [RING_POW_POW], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul r (ring_of_int r (jacobi(c,p)))
      (ring_sum r {a | a < p}
        (\a. ring_mul r (ring_of_int r (jacobi(a,p)))
                        (ring_pow r z (c * a)))) =
    ring_sum (r:A ring) {a | a < p}
      (\a. ring_mul r (ring_of_int r (jacobi(a,p))) (ring_pow r z a))") MP_TAC THENL [ASM_SIMP_TAC [(← GSYM RING_SUM_LMUL), RING_OF_INT, RING_MUL, RING_POW, FINITE_NUMSEG_LT] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:num"), (← q r"c:num"), (← q r"\t. ring_mul (r:A ring) (ring_of_int r (jacobi(t,p)))
                                 (ring_pow r z t)")] RING_SUM_MOD_MULT_REINDEX) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"a:num") THEN DISCH_TAC THEN REWRITE_TAC [JACOBI_MOD] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"z:A"), (← q r"c * a:num")] RING_POW_MOD_ORDER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [RING_MUL_ASSOC, RING_OF_INT, RING_POW] THEN REWRITE_TAC [(← GSYM RING_OF_INT_MUL), JACOBI_LMUL], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul r (ring_of_int r (jacobi(c,p))) (ring_of_int r (jacobi(c,p))) =
    ring_1 (r:A ring)") MP_TAC THENL [REWRITE_TAC [(← GSYM RING_OF_INT_MUL), (← GSYM RING_OF_INT_1)] THEN AP_TERM_TAC THEN ASM_SIMP_TAC [JACOBI_PRIME] THEN COND_CASES_TAC THENL [ASM_MESON_TAC [PRIME_COPRIME_EQ, COPRIME_SYM], ALL_TAC] THEN COND_CASES_TAC THEN INT_ARITH_TAC, ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sum r {a | a < p}
      (\a. ring_mul r (ring_of_int r (jacobi(a,p)))
                      (ring_pow r z (c * a))) IN ring_carrier (r:A ring) /\
    ring_of_int r (jacobi(c,p)) IN ring_carrier r") MP_TAC THENL [REWRITE_TAC [RING_SUM, RING_OF_INT], ALL_TAC] THEN SPEC_TAC ((← q r"ring_sum r {a | a < p}
             (\a. ring_mul r (ring_of_int r (jacobi(a,p)))
                             (ring_pow r z a)):A"), (← q r"g:A")) THEN SPEC_TAC ((← q r"ring_of_int r (jacobi(c,p)):A"), (← q r"e:A")) THEN SPEC_TAC ((← q r"ring_sum r {a | a < p}
             (\a. ring_mul r (ring_of_int r (jacobi(a,p)))
                             (ring_pow r z (c * a))):A"), (← q r"u:A")) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [RING_MUL_ASSOC, RING_MUL_LID])

  let NUMBER_FIELD_SQRT_DEGREE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"d <= 2 ==> ~(d = 0) ==> ~(d = 1) ==> d = 2")
    prove
      r"!k:A ring x.
          number_field k /\ x IN ring_carrier k /\
          ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
          ring_pow k x 2 IN ring_carrier(subfield_generated k {ring_0 k})
          ==> extension_degree (subfield_generated k {ring_0 k},
                                subfield_generated k {x}) I = 2"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] NUMBER_FIELD_ALGEBRAIC) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ABBREV_TAC (← q r"q = subfield_generated (k:A ring) {ring_0 k}") THEN SUBGOAL_THEN (← q r"field(q:A ring) /\ field_extension(q,k) (I:A->A)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "q" THEN ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, FIELD_EXTENSION_SUBFIELD_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"poly_deg q (minimal_polynomial (q,k) (I:A->A) x) = 2") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"k:A ring"), (← q r"x:A"), (← q r"ring_sub (poly_ring q (:1))
           (ring_pow (poly_ring q (:1)) (poly_var q one) 2)
           (ring_add (poly_ring q (:1))
             (ring_mul (poly_ring q (:1)) (poly_const q (ring_0 q))
               (poly_var q one))
             (poly_const q (ring_pow k x 2:A)))")] MINIMAL_POLYNOMIAL_DEG_LE) THEN MP_TAC (← ISPECL [(← q r"q:A ring"), (← q r"ring_0 q:A"), (← q r"ring_pow k x 2:A")] QUADRATIC_POLY_DEG) THEN MP_TAC (← ISPECL [(← q r"q:A ring"), (← q r"ring_0 q:A"), (← q r"ring_pow k x 2:A")] QUADRATIC_POLY_IN_CARRIER) THEN MP_TAC (← ISPECL [(← q r"q:A ring"), (← q r"k:A ring"), (← q r"I:A->A"), (← q r"x:A"), (← q r"ring_0 q:A"), (← q r"ring_pow k x 2:A")] QUADRATIC_POLY_EXTEND) THEN ASM_SIMP_TAC [RING_0, FIELD_IMP_NONTRIVIAL_RING, FIELD_EXTENSION_IMP_HOMOMORPHISM] THEN REPEAT DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"k:A ring"), (← q r"x:A")] MINIMAL_POLYNOMIAL_DEG_EQ_1) THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"k:A ring"), (← q r"x:A")] MINIMAL_POLYNOMIAL_IRREDUCIBLE) THEN ASM_SIMP_TAC [IMAGE_I] THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o ((MATCH_MP IRREDUCIBLE_IMP_POLY_DEG_NZ) o (CONJ (← ASSUME (← q r"field(q:A ring)"))))) THEN MATCH_MP_TAC r1 THEN FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL [DISCH_THEN (MP_TAC o (AP_TERM (← q r"poly_deg (q:A ring):((1->num)->A)->num"))) THEN ASM_REWRITE_TAC [POLY_DEG_0] THEN ARITH_TAC, EXPAND_TAC "q" THEN REWRITE_TAC [I_THM, (← CONJUNCT2 SUBFIELD_GENERATED)] THEN ASM_SIMP_TAC [RING_MUL_LZERO, RING_ADD_LZERO, RING_POW, RING_SUB_REFL]], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"q:A ring"), (← q r"k:A ring"), (← q r"x:A")] EXTENSION_DEGREE_SIMPLE) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"x:A")] SUBFIELD_GENERATED_SING_ALGEBRAIC) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [IMAGE_I])

  let CYCLOTOMIC_FIELD_QUADRATIC_SUBFIELD ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    let r2 ← TAUT (← q r"p ==> (p ==> q) ==> q")
    prove
      r"!(k:A ring) z p y.
          number_field k /\ z IN ring_carrier k /\ ring_order k z = p /\
          prime p /\ ~(p = 2) /\ subfield_generated k {z} = k /\
          y IN ring_carrier k /\
          ring_pow k y 2 = ring_of_int k (--(&1) pow ((p - 1) DIV 2) * &p)
          ==> extension_degree (subfield_generated k {ring_0 k},
                                subfield_generated k {y}) I = 2 /\
              !s. s subfield_of k /\
                  extension_degree (subfield_generated k {ring_0 k},
                                    subfield_generated k s) I = 2
                  ==> s = ring_carrier(subfield_generated k {y})"
      (REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_NZ)) THEN SUBGOAL_THEN (← q r"~((y:A) IN ring_carrier(subfield_generated k {ring_0 k}))") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"y:A"), (← q r"--(&1) pow ((p - 1) DIV 2) * &p:int")] SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD) THEN MATCH_MP_TAC r2 THEN ASM_REWRITE_TAC [INT_ABS_MUL, INT_ABS_POW, INT_ABS_NEG, INT_ABS_NUM, INT_POW_ONE, INT_MUL_LID, NUM_OF_INT_OF_NUM] THEN ASM_SIMP_TAC [PRIME_IMP_SQUAREFREE] THEN CONJ_TAC THENL [ASM_MESON_TAC [number_field], ALL_TAC] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"abs:int->int"))) THEN REWRITE_TAC [INT_ABS_MUL, INT_ABS_POW, INT_ABS_NEG, INT_ABS_NUM, INT_POW_ONE, INT_MUL_LID, INT_OF_NUM_EQ] THEN ASM_MESON_TAC [PRIME_1], ALL_TAC] THEN MATCH_MP_TAC r1 THEN CONJ_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_SQRT_DEGREE THEN ASM_REWRITE_TAC [RING_OF_INT_IN_SUBFIELD_GENERATED], DISCH_TAC] THEN X_GEN_TAC (← q r"s:A->bool") THEN STRIP_TAC THEN MATCH_MP_TAC CYCLOTOMIC_FIELD_SUBFIELD_UNIQUE THEN MAP_EVERY EXISTS_TAC [(← q r"k:A ring"), (← q r"z:A"), (← q r"p:num")] THEN ASM_REWRITE_TAC [SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED_EQ, FIELD_SUBFIELD_GENERATED] THEN REWRITE_TAC [CYCLIC_MODMUL_GROUP] THEN REPEAT DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"p:num"), (← q r"1")] THEN ASM_REWRITE_TAC [EXP_1] THEN MP_TAC (← SPEC (← q r"p:num") PRIME_GE_2) THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC)

  let CYCLOTOMIC_FIELD_QUADRATIC_SUBFIELD_GAUSS_SUM ← prove
    r"!(k:A ring) z p s.
        number_field k /\ z IN ring_carrier k /\ ring_order k z = p /\
        prime p /\ ~(p = 2) /\ subfield_generated k {z} = k
        ==> (s subfield_of k /\
             extension_degree (subfield_generated k {ring_0 k},
                               subfield_generated k s) I = 2 <=>
             s = ring_carrier
                   (subfield_generated k
                     {ring_sum k {a | a < p}
                        (\a. ring_mul k (ring_of_int k (jacobi(a,p)))
                                        (ring_pow k z a))}))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN ABBREV_TAC (← q r"g = ring_sum (k:A ring) {a | a < p}
                    (\a. ring_mul k (ring_of_int k (jacobi(a,p)))
                                    (ring_pow k z a))") THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NUMBER_FIELD_IMP_FIELD)) THEN SUBGOAL_THEN (← q r"(g:A) IN ring_carrier k") ASSUME_TAC THENL [EXPAND_TAC "g" THEN REWRITE_TAC [RING_SUM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"p:num")] QUADRATIC_GAUSS_SUM) THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"p:num"), (← q r"g:A")] CYCLOTOMIC_FIELD_QUADRATIC_SUBFIELD) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN EQ_TAC THENL [ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [SUBFIELD_SUBFIELD_GENERATED, SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED]])

  -- @@RETURN BEGIN
  return { QUADRATIC_GAUSS_SUM, QUADRATIC_GAUSS_SUM_HOMOMORPHISM,
           NUMBER_FIELD_SQRT_DEGREE, CYCLOTOMIC_FIELD_QUADRATIC_SUBFIELD,
           CYCLOTOMIC_FIELD_QUADRATIC_SUBFIELD_GAUSS_SUM }
  -- @@RETURN END

end HolANT.GaussSum
