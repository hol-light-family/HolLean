/- ========================================================================= -/
/- ANT: Characterizations of Dedekind domains, and Dedekind domains ...    -/
/- ========================================================================= -/
/- File: HolANT/DedekindCriteria.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/dedekind_criteria.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antdedekindcriteriadiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/integral.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/dedekind_local.ml, Library/frag.ml, Library/grouptheory.ml, Library/ring_groups.ml, ANT/dedekind_valuation.ml, Library/isum.ml, ANT/ideal_norm.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/classgroup.ml, ANT/classgroup_group.ml, ANT/fractional_ideals.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.DedekindCriteria fills them).

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
import HolANT.Integral
import HolANT.IdealArith
import HolLibrary.Products
import HolANT.Algmisc
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolANT.DedekindLocal
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.RingGroups
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
import HolANT.FractionalIdeals

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Integral
open HolANT.IdealArith
open HolANT.Algmisc
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
open HolANT.FractionalIdeals

namespace HolANT.DedekindCriteria

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (DEDEKIND_FRACTIONAL_IDEAL_MUL_INV DEDEKIND_IDEAL_EQ_VALUATION
   DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE DEDEKIND_IMP_INTEGRAL_DOMAIN
   DEDEKIND_IMP_NOETHERIAN DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL
   DEDEKIND_WEAK_APPROXIMATION DVR DVR_IMP_DEDEKIND DVR_LOCALIZATION EMPTY_GSPEC
   EMPTY_SUBSET EQ_TRANS FIELD_OF_FRACTIONS_IMP_MONOMORPHISM FINITE_EMPTY
   FINITE_IMAGE FINITE_NUMSEG_LT FINITE_SUBSET FORALL_IN_IMAGE
   FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV FRACTIONAL_IDEAL_SCALED_IDEAL
   FRACTIONAL_IDEAL_SCALED_IDEAL_MUL FUN_IN_IMAGE IDEAL_GENERATED_EMPTY
   IDEAL_GENERATED_EQ_0 IDEAL_GENERATED_INC IDEAL_GENERATED_MINIMAL
   IDEAL_GENERATED_SING IDEAL_GENERATED_SUBSET IDEAL_PROD_AC IDEAL_PROD_CARRIER
   IDEAL_PROD_COMM IDEAL_PROD_EXPLICIT IDEAL_PROD_MONO
   IDEAL_PROD_PRINCIPAL_CANCEL IDEAL_PROD_SCALE IDEAL_PROD_SUBSET_LEFT
   IDEAL_PROD_SUBSET_PRIME_IDEAL IMAGE_HOMOMORPHISM_MUL IMAGE_o IMP_IMP
   INTEGRALLY_CLOSED_ALT INTEGRAL_DOMAIN_MUL_EQ_0 INTEGRAL_DOMAIN_MUL_LCANCEL
   INTEGRAL_DOMAIN_MUL_RCANCEL INTEGRAL_DOMAIN_NONTRIVIAL
   INTEGRAL_DOMAIN_POW_EQ_0 INTEGRAL_DOMAIN_REGULAR
   INTEGRAL_HOMOGENEOUS_HOMOMORPHIC_IMAGE IN_DIFF IN_ELIM_THM
   IN_IDEAL_GENERATED_SELF IN_IMAGE IN_RING_IDEAL_0 IN_RING_IDEAL_ADD
   IN_RING_IDEAL_LMUL IN_RING_IDEAL_NEG IN_RING_IDEAL_SUM LEFT_AND_EXISTS_THM
   LEFT_IMP_EXISTS_THM LE_0 LT MAXIMAL_IDEAL_IMP_SUBSET MAXIMAL_IMP_PRIME_IDEAL
   MAXIMAL_IMP_PROPER_IDEAL MAXIMAL_IMP_RING_IDEAL MAXIMAL_SUPERIDEAL_EXISTS
   NOT_EXISTS_THM PID PID_IMP_INTEGRALLY_CLOSED PRIME_IDEAL_LOCALIZATION
   PRIME_IMP_PROPER_IDEAL PRIME_IMP_RING_IDEAL PRINCIPAL_IDEAL_0
   PROPER_IDEAL_ALT PSUBSET RIGHT_EXISTS_IMP_THM RING_0 RING_1 RING_ADD
   RING_ADD_LDISTRIB RING_ADD_RDISTRIB RING_ADD_RZERO RING_DIVIDES_0
   RING_DIVIDES_ADD RING_DIVIDES_LMUL RING_DIVIDES_REFL RING_DIVIDES_RMUL
   RING_FRACTIONATE_IN_CARRIER RING_HOMOMORPHISM_0 RING_HOMOMORPHISM_1
   RING_HOMOMORPHISM_IN_CARRIER RING_IDEAL RING_IDEAL_CARRIER
   RING_IDEAL_IDEAL_GENERATED RING_IDEAL_IDEAL_PROD
   RING_IDEAL_IMP_FRACTIONAL_IDEAL RING_IDEAL_IMP_SUBSET RING_LOCALEQUIV
   RING_LOCALEQUIV_EQUIV RING_LOCALEQUIV_IN_LOCALIZED_IDEAL
   RING_LOCALIZATION_CARRIER RING_LOCALIZATION_MUL RING_MONOMORPHISM_EQ_0
   RING_MONOMORPHISM_FRACTIONATE_GEN RING_MONOMORPHISM_IMP_HOMOMORPHISM
   RING_MONOMORPHISM_INJECTIVE_EQ RING_MUL RING_MULTSYS_NONPRIME RING_MUL_ASSOC
   RING_MUL_IN_IDEAL_PROD RING_MUL_LID RING_MUL_LZERO RING_MUL_RID
   RING_MUL_RZERO RING_MUL_SYM RING_POW RING_SUB RING_SUB_EQ_0 RING_SUM
   RING_SUM_CLAUSES RING_SUM_EQ RING_SUM_LMUL RING_SUM_RMUL SKOLEM_THM SUBSET
   SUBSET_ANTISYM SUBSET_REFL SUBSET_TRANS SUB_0 SUB_REFL dedekind_domain
   finitely_generated_ideal ideal_prod maximal_ideal noetherian_ring num_CASES
   o_DEF principal_ideal ring_divides ring_fractionate ring_multsys ring_pow : thm)
  deriving Inhabited

/-- What dedekind_criteria.ml uses from Session besides theorems. -/
structure DedekindCriteriaDeps where
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
/- dedekind_criteria.ml phrases from line 48 to 647                       -/
/- ---------------------------------------------------------------------- -/

structure DedekindCriteria01 where
  -- @@FIELDS
  DEDEKIND_SEMILOCAL_IMP_PID : thm
  INVERTIBLE_IDEAL_DIVIDES : thm
  RING_HOMOGENEOUS_RELATION_IDEAL : thm
  INVERTIBLE_IDEALS_IMP_INTEGRALLY_CLOSED : thm
  INVERTIBLE_IDEALS_IMP_NOETHERIAN : thm
  INVERTIBLE_IDEAL_PROD_CANCEL : thm
  INVERTIBLE_IDEALS_PRIME_IMP_MAXIMAL : thm
  DEDEKIND_EQ_IDEALS_INVERTIBLE : thm
  DEDEKIND_EQ_FRACTIONAL_IDEALS_INVERTIBLE : thm
  INTEGRAL_DOMAIN_FRACTIONATE_PRIME_MONOMORPHISM : thm
  LOCALLY_DVR_PRIME_IMP_MAXIMAL : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekindCriteria01 [HolBase] (D : DedekindCriteriaDeps) :
    ExceptT String IO DedekindCriteria01 := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, RING_RULE, SET_RULE, SET_TAC,
        TAUT, .. } := D
  let { DEDEKIND_FRACTIONAL_IDEAL_MUL_INV, DEDEKIND_IDEAL_EQ_VALUATION,
        DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE, DEDEKIND_IMP_INTEGRAL_DOMAIN,
        DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL, DEDEKIND_WEAK_APPROXIMATION,
        DVR_IMP_DEDEKIND, EMPTY_GSPEC, EMPTY_SUBSET, EQ_TRANS,
        FIELD_OF_FRACTIONS_IMP_MONOMORPHISM, FINITE_EMPTY, FINITE_IMAGE,
        FINITE_NUMSEG_LT, FINITE_SUBSET, FORALL_IN_IMAGE,
        FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV, FRACTIONAL_IDEAL_SCALED_IDEAL,
        FRACTIONAL_IDEAL_SCALED_IDEAL_MUL, FUN_IN_IMAGE, IDEAL_GENERATED_EMPTY,
        IDEAL_GENERATED_EQ_0, IDEAL_GENERATED_INC, IDEAL_GENERATED_MINIMAL,
        IDEAL_GENERATED_SING, IDEAL_GENERATED_SUBSET, IDEAL_PROD_AC,
        IDEAL_PROD_CARRIER, IDEAL_PROD_COMM, IDEAL_PROD_EXPLICIT, IDEAL_PROD_MONO,
        IDEAL_PROD_PRINCIPAL_CANCEL, IDEAL_PROD_SCALE, IDEAL_PROD_SUBSET_LEFT,
        IDEAL_PROD_SUBSET_PRIME_IDEAL, IMAGE_HOMOMORPHISM_MUL, IMAGE_o, IMP_IMP,
        INTEGRALLY_CLOSED_ALT, INTEGRAL_DOMAIN_MUL_LCANCEL,
        INTEGRAL_DOMAIN_MUL_RCANCEL, INTEGRAL_DOMAIN_NONTRIVIAL,
        INTEGRAL_DOMAIN_POW_EQ_0, INTEGRAL_DOMAIN_REGULAR, IN_DIFF, IN_ELIM_THM,
        IN_IDEAL_GENERATED_SELF, IN_IMAGE, IN_RING_IDEAL_0, IN_RING_IDEAL_ADD,
        IN_RING_IDEAL_LMUL, IN_RING_IDEAL_NEG, IN_RING_IDEAL_SUM, LEFT_IMP_EXISTS_THM,
        LE_0, LT, MAXIMAL_IDEAL_IMP_SUBSET, MAXIMAL_IMP_PRIME_IDEAL,
        MAXIMAL_IMP_PROPER_IDEAL, MAXIMAL_IMP_RING_IDEAL, MAXIMAL_SUPERIDEAL_EXISTS,
        NOT_EXISTS_THM, PID, PRIME_IDEAL_LOCALIZATION, PRIME_IMP_PROPER_IDEAL,
        PRIME_IMP_RING_IDEAL, PRINCIPAL_IDEAL_0, PROPER_IDEAL_ALT, PSUBSET,
        RIGHT_EXISTS_IMP_THM, RING_0, RING_1, RING_ADD, RING_ADD_LDISTRIB,
        RING_ADD_RZERO, RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_IN_CARRIER, RING_IDEAL,
        RING_IDEAL_CARRIER, RING_IDEAL_IDEAL_GENERATED, RING_IDEAL_IDEAL_PROD,
        RING_IDEAL_IMP_FRACTIONAL_IDEAL, RING_IDEAL_IMP_SUBSET,
        RING_LOCALEQUIV_IN_LOCALIZED_IDEAL, RING_MONOMORPHISM_EQ_0,
        RING_MONOMORPHISM_FRACTIONATE_GEN, RING_MONOMORPHISM_INJECTIVE_EQ, RING_MUL,
        RING_MULTSYS_NONPRIME, RING_MUL_ASSOC, RING_MUL_IN_IDEAL_PROD, RING_MUL_LID,
        RING_MUL_RID, RING_MUL_RZERO, RING_POW, RING_SUM, RING_SUM_CLAUSES,
        RING_SUM_EQ, RING_SUM_LMUL, RING_SUM_RMUL, SKOLEM_THM, SUBSET, SUBSET_ANTISYM,
        SUBSET_REFL, SUBSET_TRANS, SUB_0, SUB_REFL, dedekind_domain,
        finitely_generated_ideal, ideal_prod, maximal_ideal, noetherian_ring,
        num_CASES, o_DEF, principal_ideal, ring_divides, ring_fractionate,
        ring_multsys, ring_pow, .. } := D.core1
  -- @@SCOPE END

  let DEDEKIND_SEMILOCAL_IMP_PID ← prove
    r"!r:A ring.
        dedekind_domain r /\ FINITE {m | maximal_ideal r m} ==> PID r"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN ASM_REWRITE_TAC [PID] THEN X_GEN_TAC (← q r"j:A->bool") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"j = {ring_0 r:A}") THEN ASM_REWRITE_TAC [PRINCIPAL_IDEAL_0] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"{p:A->bool | prime_ideal r p /\ ~(p = {ring_0 r})}"), (← q r"\p. ideal_valuation r p (j:A->bool)")] DEDEKIND_WEAK_APPROXIMATION) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [IN_ELIM_THM] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{m:A->bool | maximal_ideal r m}") THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL], REWRITE_TAC [IN_ELIM_THM]] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:A") STRIP_ASSUME_TAC) THEN REWRITE_TAC [principal_ideal] THEN EXISTS_TAC (← q r"a:A") THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r {a:A}"), (← q r"j:A->bool")] DEDEKIND_IDEAL_EQ_VALUATION) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0])

  let INVERTIBLE_IDEAL_DIVIDES ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul r b (ring_mul r s t) = ring_mul r (ring_mul r b t) (s:A)")
    prove
      r"!r j k (a:A) b e.
          integral_domain r /\ ring_ideal r j /\ ring_ideal r k /\
          e IN ring_carrier r /\ ~(e = ring_0 r) /\
          ideal_prod r j k = ideal_generated r {e} /\
          a IN ring_carrier r /\ b IN ring_carrier r /\
          IMAGE (ring_mul r a) j SUBSET IMAGE (ring_mul r b) j
          ==> ring_divides r b a"
      (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(e:A) IN ideal_prod r j k") MP_TAC THENL [ASM_SIMP_TAC [IN_IDEAL_GENERATED_SELF], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"k:A->bool")] IDEAL_PROD_EXPLICIT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"u:num->A"), (← q r"v:num->A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!i. i < n ==> (u:num->A) i IN ring_carrier r /\
       (v:num->A) i IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. ?w. i < n ==> w IN j /\ ring_mul r a ((u:num->A) i) = ring_mul r b w") MP_TAC THENL [X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_mul r a ((u:num->A) i) IN IMAGE (ring_mul r b) j") MP_TAC THENL [FIRST_X_ASSUM (MATCH_MP_TAC o (REWRITE_RULE [SUBSET])) THEN ASM_SIMP_TAC [FUN_IN_IMAGE], REWRITE_TAC [IN_IMAGE] THEN MESON_TAC []], REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"w:num->A") THEN DISCH_TAC] THEN SUBGOAL_THEN (← q r"ring_sum r {i | i < n} (\i. ring_mul r ((w:num->A) i) (v i)) IN
      ideal_generated r {e:A}") MP_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z9 ← (q r"ideal_prod r j (k:A->bool)"); let z8 ← (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); liftExcept (lhand z6)); pure (z8 == z9)))))) THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN REWRITE_TAC [RING_IDEAL_IDEAL_PROD, IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ASM_SIMP_TAC [IDEAL_GENERATED_SING, IN_ELIM_THM, ring_divides]] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"t:A") STRIP_ASSUME_TAC) o CONJUNCT2) THEN REWRITE_TAC [ring_divides] THEN ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"t:A") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_RCANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"r:A ring"), (← q r"e:A")] THEN ASM_SIMP_TAC [RING_MUL] THEN TRANS_TAC EQ_TRANS (← q r"ring_mul r b (ring_sum r {i | i < n}
                     (\i. ring_mul r ((w:num->A) i) (v i)))") THEN CONJ_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do let z5 ← (q r"e:A"); let z4 ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); liftExcept (lhand z2)); pure (z4 == z5))))) THEN SUBGOAL_THEN (← q r"!i. i < n ==> (w:num->A) i IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM RING_SUM_LMUL), FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL, RING_SUM] THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN ASM_SIMP_TAC [RING_MUL_ASSOC], ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_SUM, r1]])

  let RING_HOMOGENEOUS_RELATION_IDEAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_add r x (ring_mul r b s) = ring_0 r
    ==> x = ring_mul r b (ring_neg r (s:A))")
    let r2 ← RING_RULE (← q r"ring_mul r c (ring_mul r x (ring_mul r b y)) =
      ring_mul r b (ring_mul r c (ring_mul r x (y:A)))")
    let r9 ← RING_RULE (← q r"ring_mul r a (ring_mul r x (ring_mul r b y)) =
        ring_mul r b (ring_mul r (ring_mul r a x) (y:A))")
    let r10 ← RING_RULE (← q r"ring_mul r a (ring_mul r x y) = ring_mul r x (ring_mul r a (y:A))")
    prove
      r"!r (a:A) b c m.
          a IN ring_carrier r /\ b IN ring_carrier r /\
          (!i. i < SUC m ==> c i IN ring_carrier r) /\
          ring_add r (ring_pow r a (SUC m))
            (ring_sum r {i | i < SUC m}
               (\i. ring_mul r (c i)
                      (ring_mul r (ring_pow r a i) (ring_pow r b (SUC m - i))))) =
          ring_0 r
          ==> IMAGE (ring_mul r a)
                (ideal_generated r
                   (IMAGE (\i. ring_mul r (ring_pow r a i) (ring_pow r b (m - i)))
                          {i | i <= m})) SUBSET
              IMAGE (ring_mul r b)
                (ideal_generated r
                   (IMAGE (\i. ring_mul r (ring_pow r a i) (ring_pow r b (m - i)))
                          {i | i <= m}))"
      (REPEAT STRIP_TAC THEN ABBREV_TAC (← q r"j = ideal_generated r
           (IMAGE (\i. ring_mul r (ring_pow r (a:A) i) (ring_pow r b (m - i)))
                  {i | i <= m})") THEN SUBGOAL_THEN (← q r"ring_ideal r (j:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "j" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i <= m
          ==> ring_mul r (ring_pow r (a:A) i) (ring_pow r b (m - i)) IN j") ASSUME_TAC THENL [REPEAT STRIP_TAC THEN EXPAND_TAC "j" THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_IMAGE, IN_ELIM_THM] THEN ASM_SIMP_TAC [RING_MUL, RING_POW] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_ideal r (IMAGE (ring_mul r b) (j:A->bool))") ASSUME_TAC THENL [ASM_SIMP_TAC [(← GSYM IDEAL_PROD_SCALE), RING_IDEAL_IDEAL_PROD], ALL_TAC] THEN SUBGOAL_THEN (← q r"j SUBSET {x:A | x IN ring_carrier r /\
                      ring_mul r a x IN IMAGE (ring_mul r b) j}") MP_TAC THENL [ALL_TAC, REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN MESON_TAC []] THEN FIRST_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [(← SYM th)])) o (checkM (fun th => (do let z14 ← (q r"j:A->bool"); let z13 ← (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); liftExcept (rand z11)); pure (z13 == z14))))) THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [RING_IDEAL, SUBSET, IN_ELIM_THM] THEN SIMP_TAC [] THEN ASM_SIMP_TAC [RING_0, RING_MUL_RZERO, IN_RING_IDEAL_0, RING_ADD, RING_MUL, RING_ADD_LDISTRIB, IN_RING_IDEAL_ADD] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_mul r a (ring_mul r x y) = ring_mul r x (ring_mul r a (y:A))") SUBST1_TAC THENL [MATCH_MP_TAC r10 THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [IN_RING_IDEAL_LMUL]]] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN X_GEN_TAC (← q r"p:num") THEN DISCH_TAC THEN ASM_SIMP_TAC [RING_MUL, RING_POW] THEN REWRITE_TAC [IN_IMAGE] THEN ASM_CASES_TAC (← q r"p:num = m") THENL [ALL_TAC, EXISTS_TAC (← q r"ring_mul r (ring_pow r (a:A) (SUC p)) (ring_pow r b (m - SUC p))") THEN CONJ_TAC THENL [SUBGOAL_THEN (← q r"m - p = SUC(m - SUC p)") SUBST1_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [ring_pow]] THEN MATCH_MP_TAC r9 THEN ASM_SIMP_TAC [RING_POW], FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]] THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC (← q r"ring_neg r (ring_sum r {i | i < SUC m}
        (\i. ring_mul r ((c:num->A) i)
               (ring_mul r (ring_pow r a i) (ring_pow r b (m - i)))))") THEN CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC IN_RING_IDEAL_NEG THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IN_RING_IDEAL_SUM THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"q:num") THEN DISCH_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_SIMP_TAC [] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC] THEN REWRITE_TAC [SUB_REFL, ring_pow] THEN ASM_SIMP_TAC [RING_MUL_RID, RING_POW] THEN FIRST_X_ASSUM (MP_TAC o (checkM (fun th => (do if ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); pure (is_eq z3)) then (do let z8 ← (q r"ring_0 r:A"); let z7 ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); liftExcept (rand z5)); pure (z7 == z8)) else pure false)))) THEN REWRITE_TAC [ring_pow] THEN SUBGOAL_THEN (← q r"ring_sum r {i | i < SUC m}
        (\i. ring_mul r ((c:num->A) i)
               (ring_mul r (ring_pow r a i) (ring_pow r b (SUC m - i)))) =
      ring_mul r b (ring_sum r {i | i < SUC m}
        (\i. ring_mul r (c i)
               (ring_mul r (ring_pow r a i) (ring_pow r b (m - i)))))") SUBST1_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"\i. ring_mul r ((c:num->A) i)
                       (ring_mul r (ring_pow r a i) (ring_pow r b (m - i)))"), (← q r"b:A"), (← q r"{i:num | i < SUC m}")] RING_SUM_LMUL) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL, RING_POW], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"q:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"SUC m - q = SUC(m - q)") SUBST1_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [ring_pow]] THEN MATCH_MP_TAC r2 THEN ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN MATCH_MP_TAC r1 THEN ASM_SIMP_TAC [RING_MUL, RING_POW, RING_SUM])

  let INVERTIBLE_IDEALS_IMP_INTEGRALLY_CLOSED ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"c:num->A"
    let q2 ← q r"e:A"
    let q3 ← q r"k:A->bool"
    let q4 ← q r"j:A->bool"
    let q5 ← q r"e:A"
    let q6 ← q r"k:A->bool"
    let q7 ← q r"j:A->bool"
    let q8 ← q r"0"
    let q9 ← q r"ring_pow r (b:A) m"
    let q10 ← q r"!x:A. x IN j /\ ~(x = z) ==> ~(j = {z})"
    let r11 ← SET_RULE q10
    let q12 ← q r"ring_ideal r (j:A->bool) /\ ~(j = {ring_0 r})"
    let q13 ← q r"j = ideal_generated r
         (IMAGE (\i. ring_mul r (ring_pow r (a:A) i) (ring_pow r b (m - i)))
                {i | i <= m})"
    let q14 ← q r"~(n = 0) ==> ?m. n = SUC m"
    let r15 ← MESON [num_CASES] q14
    let q16 ← q r"m:num"
    let q17 ← q r"ring_add r (ring_pow r a n)
       (ring_sum r {i | i < n}
         (\i. ring_mul r (c i) (ring_mul r (ring_pow r (a:A) i)
                                           (ring_pow r b (n - i))))) =
      ring_0 r"
    let q18 ← q r"n = 0"
    let q19 ← q r"n:num"
    let q20 ← q r"c:num->A"
    let q21 ← q r"b:A"
    let q22 ← q r"a:A"
    prove
      r"!r:A ring.
          integral_domain r /\
          (!j. ring_ideal r j /\ ~(j = {ring_0 r})
               ==> ?k e. ring_ideal r k /\ e IN ring_carrier r /\
                         ~(e = ring_0 r) /\
                         ideal_prod r j k = ideal_generated r {e})
          ==> integrally_closed r"
      (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [INTEGRALLY_CLOSED_ALT] THEN MAP_EVERY X_GEN_TAC [q22, q21, q20, q19] THEN STRIP_TAC THEN ASM_CASES_TAC q18 THENL [UNDISCH_TAC q17 THEN ASM_REWRITE_TAC [ring_pow, LT, EMPTY_GSPEC, RING_SUM_CLAUSES] THEN ASM_SIMP_TAC [RING_ADD_RZERO, RING_1, INTEGRAL_DOMAIN_NONTRIVIAL], FIRST_X_ASSUM ((X_CHOOSE_THEN q16 SUBST_ALL_TAC) o (MATCH_MP r15))] THEN ABBREV_TAC q13 THEN SUBGOAL_THEN q12 STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [EXPAND_TAC "j" THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], MATCH_MP_TAC r11 THEN EXISTS_TAC q9 THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_POW_EQ_0] THEN EXPAND_TAC "j" THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_IMAGE, IN_ELIM_THM] THEN ASM_SIMP_TAC [RING_MUL, RING_POW] THEN EXISTS_TAC q8 THEN ASM_SIMP_TAC [LE_0, ring_pow, SUB_0, RING_MUL_LID, RING_POW]], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC q7)) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [q6, q5] THEN STRIP_TAC THEN MATCH_MP_TAC INVERTIBLE_IDEAL_DIVIDES THEN MAP_EVERY EXISTS_TAC [q4, q3, q2] THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "j" THEN MATCH_MP_TAC RING_HOMOGENEOUS_RELATION_IDEAL THEN EXISTS_TAC q1 THEN ASM_REWRITE_TAC [])

  let INVERTIBLE_IDEALS_IMP_NOETHERIAN ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul r x v = ring_mul r e t
        ==> ring_mul r (ring_mul r u v) x =
            ring_mul r e (ring_mul r t (u:A))")
    prove
      r"!r:A ring.
          integral_domain r /\
          (!j. ring_ideal r j /\ ~(j = {ring_0 r})
               ==> ?k e. ring_ideal r k /\ e IN ring_carrier r /\
                         ~(e = ring_0 r) /\
                         ideal_prod r j k = ideal_generated r {e})
          ==> noetherian_ring r"
      (REPEAT STRIP_TAC THEN REWRITE_TAC [noetherian_ring, finitely_generated_ideal] THEN X_GEN_TAC (← q r"j:A->bool") THEN DISCH_TAC THEN ASM_CASES_TAC (← q r"j = {ring_0 r:A}") THENL [EXISTS_TAC (← q r"{}:A->bool") THEN ASM_REWRITE_TAC [FINITE_EMPTY, EMPTY_SUBSET, IDEAL_GENERATED_EMPTY], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"j:A->bool"))) THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"k:A->bool"), (← q r"e:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"(e:A) IN ideal_prod r j k") MP_TAC THENL [ASM_SIMP_TAC [IN_IDEAL_GENERATED_SELF], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"k:A->bool")] IDEAL_PROD_EXPLICIT) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"u:num->A"), (← q r"v:num->A")] THEN STRIP_TAC THEN FIRST_X_ASSUM (ASSUME_TAC o (SYM o (checkM (fun th => (do let z9 ← (q r"e:A"); let z8 ← (do let z6 ← (do let z7 ← (pure th); pure (concl z7)); liftExcept (lhand z6)); pure (z8 == z9)))))) THEN SUBGOAL_THEN (← q r"!i. i < n ==> (u:num->A) i IN ring_carrier r /\
       (v:num->A) i IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN EXISTS_TAC (← q r"IMAGE (u:num->A) {i | i < n}") THEN SIMP_TAC [FINITE_IMAGE, FINITE_NUMSEG_LT] THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [], REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC] THEN SUBGOAL_THEN (← q r"(x:A) IN ring_carrier r") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. ?t. i < n ==> t IN ring_carrier r /\
                       ring_mul r x ((v:num->A) i) = ring_mul r e t") MP_TAC THENL [X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_mul r x ((v:num->A) i) IN ideal_generated r {e:A}") MP_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z5 ← (q r"ideal_prod r j (k:A->bool)"); let z4 ← (do let z2 ← (do let z3 ← (pure th); pure (concl z3)); liftExcept (lhand z2)); pure (z4 == z5)))))) THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_PROD THEN ASM_SIMP_TAC [], ASM_SIMP_TAC [IDEAL_GENERATED_SING, IN_ELIM_THM, ring_divides] THEN MESON_TAC []], REWRITE_TAC [SKOLEM_THM, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"t:num->A") THEN DISCH_TAC] THEN SUBGOAL_THEN (← q r"x = ring_sum r {i | i < n} (\i. ring_mul r ((t:num->A) i) (u i))") SUBST1_TAC THENL [MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"r:A ring"), (← q r"e:A")] THEN ASM_SIMP_TAC [RING_SUM] THEN TRANS_TAC EQ_TRANS (← q r"ring_sum r {i | i < n}
          (\i. ring_mul r (ring_mul r ((u:num->A) i) (v i)) x)") THEN CONJ_TAC THENL [MP_TAC (← BETA_RULE (← ISPECL [(← q r"r:A ring"), (← q r"\i. ring_mul r ((u:num->A) i) (v i)"), (← q r"x:A"), (← q r"{i:num | i < n}")] RING_SUM_RMUL)) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL], DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC []], MP_TAC (← BETA_RULE (← ISPECL [(← q r"r:A ring"), (← q r"\i. ring_mul r ((t:num->A) i) (u i)"), (← q r"e:A"), (← q r"{i:num | i < n}")] RING_SUM_LMUL)) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL], DISCH_THEN (SUBST1_TAC o SYM)] THEN MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_IMP] r1) THEN ASM_SIMP_TAC []], MATCH_MP_TAC IN_RING_IDEAL_SUM THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED, IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED] THEN ASM_SIMP_TAC [] THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN CONJ_TAC THENL [ASM_MESON_TAC [], MATCH_MP_TAC FUN_IN_IMAGE] THEN ASM_REWRITE_TAC [IN_ELIM_THM]])

  let INVERTIBLE_IDEAL_PROD_CANCEL ← prove
    r"!r j k (e:A) x y.
        integral_domain r /\ ring_ideal r j /\ ring_ideal r k /\
        e IN ring_carrier r /\ ~(e = ring_0 r) /\
        ideal_prod r j k = ideal_generated r {e} /\
        ring_ideal r x /\ ring_ideal r y /\
        ideal_prod r j x = ideal_prod r j y
        ==> x = y"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"e:A"), (← q r"x:A->bool"), (← q r"y:A->bool")] IDEAL_PROD_PRINCIPAL_CANCEL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z4 ← (q r"ideal_prod r j (k:A->bool)"); let z3 ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); liftExcept (lhand z1)); pure (z3 == z4)))))) THEN TRANS_TAC EQ_TRANS (← q r"ideal_prod r k (ideal_prod r j (x:A->bool))") THEN CONJ_TAC THENL [SIMP_TAC [IDEAL_PROD_AC, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD, (← ASSUME (← q r"ring_ideal r (j:A->bool)")), (← ASSUME (← q r"ring_ideal r (k:A->bool)")), (← ASSUME (← q r"ring_ideal r (x:A->bool)"))], ASM_REWRITE_TAC [] THEN SIMP_TAC [IDEAL_PROD_AC, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD, (← ASSUME (← q r"ring_ideal r (j:A->bool)")), (← ASSUME (← q r"ring_ideal r (k:A->bool)")), (← ASSUME (← q r"ring_ideal r (y:A->bool)"))]])

  let INVERTIBLE_IDEALS_PRIME_IMP_MAXIMAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r8 ← RING_RULE (← q r"ring_mul r a (ring_mul r x y) = ring_mul r x (ring_mul r a (y:A))")
    let r9 ← SET_RULE (← q r"(z:A) IN p /\ p SUBSET {z} ==> p = {z}")
    prove
      r"!r p:A->bool.
          integral_domain r /\
          (!j. ring_ideal r j /\ ~(j = {ring_0 r})
               ==> ?k e. ring_ideal r k /\ e IN ring_carrier r /\
                         ~(e = ring_0 r) /\
                         ideal_prod r j k = ideal_generated r {e}) /\
          prime_ideal r p /\ ~(p = {ring_0 r})
          ==> maximal_ideal r p"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP PRIME_IMP_RING_IDEAL)) THEN FIRST_X_ASSUM ((LABEL_TAC "inv") o (checkM (fun z10 => (do let z11 ← (do let z12 ← (pure z10); pure (concl z12)); pure (is_forall z11))))) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool")] MAXIMAL_SUPERIDEAL_EXISTS) THEN ASM_SIMP_TAC [PRIME_IMP_PROPER_IDEAL, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"m:A->bool") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"p:A->bool = m") (fun th => ASM_REWRITE_TAC [th]) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_RING_IDEAL)) THEN SUBGOAL_THEN (← q r"~(m = {ring_0 r:A})") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC [IN_RING_IDEAL_0, r9], ALL_TAC] THEN USE_THEN "inv" (MP_TAC o (SPEC (← q r"m:A->bool"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN MAP_EVERY X_GEN_TAC [(← q r"k:A->bool"), (← q r"a:A")] THEN STRIP_TAC THEN ABBREV_TAC (← q r"L = {t:A | t IN ring_carrier r /\
                 ring_mul r a t IN ideal_prod r p k}") THEN SUBGOAL_THEN (← q r"ring_ideal r (L:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "L" THEN REWRITE_TAC [RING_IDEAL, SUBSET, IN_ELIM_THM] THEN SIMP_TAC [] THEN ASM_SIMP_TAC [RING_0, RING_MUL_RZERO, IN_RING_IDEAL_0, RING_IDEAL_IDEAL_PROD, RING_ADD, RING_MUL, RING_ADD_LDISTRIB, IN_RING_IDEAL_ADD] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"ring_mul r a (ring_mul r x y) = ring_mul r x (ring_mul r a (y:A))") SUBST1_TAC THENL [MATCH_MP_TAC r8 THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [IN_RING_IDEAL_LMUL, RING_IDEAL_IDEAL_PROD]], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_prod r (ideal_generated r {a}) L = ideal_prod r p (k:A->bool)") ASSUME_TAC THENL [ASM_SIMP_TAC [IDEAL_PROD_SCALE] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [EXPAND_TAC "L" THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN SIMP_TAC [], REWRITE_TAC [SUBSET, IN_IMAGE] THEN X_GEN_TAC (← q r"y:A") THEN DISCH_TAC] THEN SUBGOAL_THEN (← q r"(y:A) IN ideal_generated r {a}") MP_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z7 ← (q r"ideal_prod r m (k:A->bool)"); let z6 ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (lhand z4)); pure (z6 == z7)))))) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"m:A->bool"), (← q r"k:A->bool"), (← q r"k:A->bool")] IDEAL_PROD_MONO) THEN ASM SET_TAC [], ASM_SIMP_TAC [IDEAL_GENERATED_SING, IN_ELIM_THM, ring_divides]] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"t:A") STRIP_ASSUME_TAC) o CONJUNCT2) THEN EXISTS_TAC (← q r"t:A") THEN ASM_REWRITE_TAC [] THEN EXPAND_TAC "L" THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_prod r m (L:A->bool) = p") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"a:A"), (← q r"ideal_prod r m (L:A->bool)"), (← q r"p:A->bool")] IDEAL_PROD_PRINCIPAL_CANCEL) THEN ASM_REWRITE_TAC [RING_IDEAL_IDEAL_PROD] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN TRANS_TAC EQ_TRANS (← q r"ideal_prod r m (ideal_prod r (ideal_generated r {a:A}) L)") THEN CONJ_TAC THENL [SIMP_TAC [IDEAL_PROD_AC, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD, RING_IDEAL_IDEAL_GENERATED, (← ASSUME (← q r"ring_ideal r (m:A->bool)")), (← ASSUME (← q r"ring_ideal r (L:A->bool)"))], ASM_REWRITE_TAC []] THEN TRANS_TAC EQ_TRANS (← q r"ideal_prod r p (ideal_prod r m (k:A->bool))") THEN CONJ_TAC THENL [SIMP_TAC [IDEAL_PROD_AC, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD, (← ASSUME (← q r"ring_ideal r (m:A->bool)")), (← ASSUME (← q r"ring_ideal r (p:A->bool)")), (← ASSUME (← q r"ring_ideal r (k:A->bool)"))], ASM_REWRITE_TAC []] THEN SIMP_TAC [IDEAL_PROD_AC, RING_IDEAL_IMP_SUBSET, RING_IDEAL_IDEAL_PROD, RING_IDEAL_IDEAL_GENERATED, (← ASSUME (← q r"ring_ideal r (p:A->bool)"))], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"m:A->bool"), (← q r"L:A->bool")] IDEAL_PROD_SUBSET_PRIME_IDEAL) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, SUBSET_REFL] THEN STRIP_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ideal_prod r p m = ideal_prod r p (ring_carrier r:A->bool)") MP_TAC THENL [ASM_SIMP_TAC [IDEAL_PROD_CARRIER] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_PROD_SUBSET_LEFT THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], FIRST_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [(← SYM th)])) o (checkM (fun th => (do let z3 ← (q r"ideal_prod r m (L:A->bool) = p"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3))))) THEN TRANS_TAC SUBSET_TRANS (← q r"ideal_prod r m (p:A->bool)") THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_PROD_MONO THEN ASM_REWRITE_TAC [SUBSET_REFL], MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool"), (← q r"p:A->bool")] IDEAL_PROD_COMM) THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, SUBSET_REFL]]], DISCH_TAC] THEN USE_THEN "inv" (MP_TAC o (SPEC (← q r"p:A->bool"))) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN MAP_EVERY X_GEN_TAC [(← q r"k':A->bool"), (← q r"e:A")] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"m = ring_carrier r:A->bool") MP_TAC THENL [MATCH_MP_TAC INVERTIBLE_IDEAL_PROD_CANCEL THEN MAP_EVERY EXISTS_TAC [(← q r"r:A ring"), (← q r"p:A->bool"), (← q r"k':A->bool"), (← q r"e:A")] THEN ASM_REWRITE_TAC [RING_IDEAL_CARRIER], ASM_MESON_TAC [MAXIMAL_IMP_PROPER_IDEAL, PROPER_IDEAL_ALT]])

  let DEDEKIND_EQ_IDEALS_INVERTIBLE ← prove
    r"!r:A ring.
        dedekind_domain r <=>
        integral_domain r /\
        !j. ring_ideal r j /\ ~(j = {ring_0 r})
            ==> ?k e. ring_ideal r k /\ e IN ring_carrier r /\
                      ~(e = ring_0 r) /\
                      ideal_prod r j k = ideal_generated r {e}"
    (GEN_TAC THEN EQ_TAC THENL [DISCH_TAC THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN] THEN REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool")] DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [], STRIP_TAC THEN ASM_REWRITE_TAC [dedekind_domain] THEN ASM_SIMP_TAC [INVERTIBLE_IDEALS_IMP_NOETHERIAN, INVERTIBLE_IDEALS_IMP_INTEGRALLY_CLOSED] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC INVERTIBLE_IDEALS_PRIME_IMP_MAXIMAL THEN ASM_REWRITE_TAC []])

  let DEDEKIND_EQ_FRACTIONAL_IDEALS_INVERTIBLE ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"!(f:A->B) u. (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\
                 s SUBSET u /\ t SUBSET u
                 ==> IMAGE f t = IMAGE f s ==> s = t")
    let r2 ← SET_RULE (← q r"(!x:A. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE (g:A->B) s")
    prove
      r"!r k (h:A->B).
          field_of_fractions (r,k) h
          ==> (dedekind_domain r <=>
               !J. fractional_ideal (r,k) h J
                   ==> ring_span (r,k) h
                         (ring_setmul k J (fractional_ideal_inv (r,k) h J)) =
                       IMAGE h (ring_carrier r))"
      (REPEAT STRIP_TAC THEN EQ_TAC THENL [MESON_TAC [DEDEKIND_FRACTIONAL_IDEAL_MUL_INV], DISCH_TAC] THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP FIELD_OF_FRACTIONS_IMP_MONOMORPHISM)) THEN REWRITE_TAC [DEDEKIND_EQ_IDEALS_INVERTIBLE] THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"j:A->bool") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"fractional_ideal (r,k) (h:A->B) (IMAGE h j)") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IMP_FRACTIONAL_IDEAL], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"fractional_ideal_inv (r,k) (h:A->B) (IMAGE h j)")] FRACTIONAL_IDEAL_SCALED_IDEAL) THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"d:A"), (← q r"m:A->bool")] THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"m:A->bool"), (← q r"d:A")] THEN ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"IMAGE (h:A->B) j"), (← q r"fractional_ideal_inv (r,k) (h:A->B) (IMAGE h j)"), (← q r"ring_1 r:A"), (← q r"j:A->bool"), (← q r"d:A"), (← q r"m:A->bool")] FRACTIONAL_IDEAL_SCALED_IDEAL_MUL) THEN ASM_SIMP_TAC [FRACTIONAL_IDEAL_FRACTIONAL_IDEAL_INV, RING_1] THEN ANTS_TAC THENL [FIRST_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [(← MATCH_MP RING_HOMOMORPHISM_1 th)])) THEN REWRITE_TAC [(← GSYM IMAGE_o), o_DEF] THEN MATCH_MP_TAC r2 THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC RING_MUL_LID THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_IDEAL_IMP_SUBSET, SUBSET], ALL_TAC] THEN ASM_SIMP_TAC [RING_MUL_LID, (← GSYM IMAGE_HOMOMORPHISM_MUL), SUBSET_REFL] THEN SUBGOAL_THEN (← q r"IMAGE (ring_mul r d) (ring_carrier r) = ideal_generated r {d:A}") SUBST1_TAC THENL [ASM_SIMP_TAC [(← GSYM IDEAL_PROD_SCALE), RING_IDEAL_CARRIER] THEN MATCH_MP_TAC IDEAL_PROD_CARRIER THEN REWRITE_TAC [RING_IDEAL_IDEAL_GENERATED], ALL_TAC] THEN MATCH_MP_TAC r1 THEN EXISTS_TAC (← q r"ring_carrier r:A->bool") THEN REWRITE_TAC [ideal_prod, IDEAL_GENERATED_SUBSET] THEN ASM_MESON_TAC [RING_MONOMORPHISM_INJECTIVE_EQ])

  let INTEGRAL_DOMAIN_FRACTIONATE_PRIME_MONOMORPHISM ← prove
    r"!r p:A->bool.
        integral_domain r /\ prime_ideal r p
        ==> ring_monomorphism
             (r,ring_localization r (ring_carrier r DIFF p))
             (ring_fractionate r (ring_carrier r DIFF p))"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [RING_MONOMORPHISM_FRACTIONATE_GEN, RING_MULTSYS_NONPRIME] THEN ASM_SIMP_TAC [SUBSET, IN_DIFF, IN_ELIM_THM, INTEGRAL_DOMAIN_REGULAR] THEN ASM_MESON_TAC [IN_RING_IDEAL_0, PRIME_IMP_RING_IDEAL])

  let LOCALLY_DVR_PRIME_IMP_MAXIMAL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"p ==> ~(p /\ ~q) ==> q")
    let r2 ← SET_RULE (← q r"!x:A#A->bool. x IN s /\ ~(x = z) ==> ~(s = {z})")
    let r3 ← SET_RULE (← q r"(z:A) IN s /\ ~(s = {z}) ==> ?a. a IN s /\ ~(a = z)")
    let r4 ← SET_RULE (← q r"(z:A) IN p /\ p SUBSET {z} ==> p = {z}")
    prove
      r"!r p:A->bool.
          integral_domain r /\
          (!q. prime_ideal r q /\ ~(q = {ring_0 r})
               ==> DVR(ring_localization r (ring_carrier r DIFF q))) /\
          prime_ideal r p /\ ~(p = {ring_0 r})
          ==> maximal_ideal r p"
      (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"p:A->bool")] MAXIMAL_SUPERIDEAL_EXISTS) THEN ASM_SIMP_TAC [PRIME_IMP_PROPER_IDEAL, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"m:A->bool") THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"p:A->bool = m") (fun th => ASM_REWRITE_TAC [th]) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_PRIME_IDEAL)) THEN SUBGOAL_THEN (← q r"~(m = {ring_0 r:A})") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC [IN_RING_IDEAL_0, PRIME_IMP_RING_IDEAL, r4], ALL_TAC] THEN ABBREV_TAC (← q r"s = ring_carrier r DIFF (m:A->bool)") THEN SUBGOAL_THEN (← q r"ring_multsys r (s:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "s" THEN ASM_SIMP_TAC [RING_MULTSYS_NONPRIME], ALL_TAC] THEN SUBGOAL_THEN (← q r"p INTER s = {} /\ m INTER (s:A->bool) = {}") STRIP_ASSUME_TAC THENL [EXPAND_TAC "s" THEN ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"DVR(ring_localization r (s:A->bool))") ASSUME_TAC THENL [EXPAND_TAC "s" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ABBREV_TAC (← q r"P' = {ring_localequiv r s (a,b) | a,b | (a:A) IN p /\ b IN s}") THEN SUBGOAL_THEN (← q r"prime_ideal (ring_localization r s) (P':(A#A->bool)->bool) /\
      prime_ideal (ring_localization r s)
       {ring_localequiv r s (a,b) | a,b | (a:A) IN m /\ b IN s}") STRIP_ASSUME_TAC THENL [EXPAND_TAC "P'" THEN ASM_SIMP_TAC [PRIME_IDEAL_LOCALIZATION], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(P' = {ring_0(ring_localization r (s:A->bool))})") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"?a:A. a IN p /\ ~(a = ring_0 r)") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [IN_RING_IDEAL_0, PRIME_IMP_RING_IDEAL, r3], ALL_TAC] THEN MATCH_MP_TAC r2 THEN EXISTS_TAC (← q r"ring_fractionate r s (a:A)") THEN CONJ_TAC THENL [EXPAND_TAC "P'" THEN REWRITE_TAC [ring_fractionate, IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [(← q r"a:A"), (← q r"ring_1 r:A")] THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [ring_multsys], MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"m:A->bool")] INTEGRAL_DOMAIN_FRACTIONATE_PRIME_MONOMORPHISM) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_localization r (s:A->bool)"), (← q r"ring_fractionate r (s:A->bool)"), (← q r"a:A")] RING_MONOMORPHISM_EQ_0) THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [PRIME_IMP_RING_IDEAL, RING_IDEAL_IMP_SUBSET, SUBSET]], ALL_TAC] THEN SUBGOAL_THEN (← q r"(P':(A#A->bool)->bool) =
      {ring_localequiv r s (a,b) | a,b | (a:A) IN m /\ b IN s}") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"ring_localization r (s:A->bool)"), (← q r"P':(A#A->bool)->bool")] DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL) THEN ASM_SIMP_TAC [DVR_IMP_DEDEKIND, maximal_ideal] THEN REWRITE_TAC [NOT_EXISTS_THM] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"{ring_localequiv r s (a,b) | a,b | (a:A) IN m /\ b IN s}")) o CONJUNCT2)) THEN ASM_SIMP_TAC [PRIME_IMP_PROPER_IDEAL, PSUBSET] THEN MATCH_MP_TAC r1 THEN EXPAND_TAC "P'" THEN ASM SET_TAC [], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:A") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"s:A->bool"), (← q r"p:A->bool"), (← q r"x:A"), (← q r"ring_1 r:A")] RING_LOCALEQUIV_IN_LOCALIZED_IDEAL) THEN ANTS_TAC THENL [ASM_MESON_TAC [ring_multsys, MAXIMAL_IDEAL_IMP_SUBSET, SUBSET], DISCH_THEN (SUBST1_TAC o SYM)] THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [(← q r"x:A"), (← q r"ring_1 r:A")] THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [ring_multsys])

  -- @@RETURN BEGIN
  return { DEDEKIND_SEMILOCAL_IMP_PID, INVERTIBLE_IDEAL_DIVIDES,
           RING_HOMOGENEOUS_RELATION_IDEAL, INVERTIBLE_IDEALS_IMP_INTEGRALLY_CLOSED,
           INVERTIBLE_IDEALS_IMP_NOETHERIAN, INVERTIBLE_IDEAL_PROD_CANCEL,
           INVERTIBLE_IDEALS_PRIME_IMP_MAXIMAL, DEDEKIND_EQ_IDEALS_INVERTIBLE,
           DEDEKIND_EQ_FRACTIONAL_IDEALS_INVERTIBLE,
           INTEGRAL_DOMAIN_FRACTIONATE_PRIME_MONOMORPHISM, LOCALLY_DVR_PRIME_IMP_MAXIMAL }
  -- @@RETURN END



/- ---------------------------------------------------------------------- -/
/- dedekind_criteria.ml phrases from line 733 to 852                      -/
/- ---------------------------------------------------------------------- -/

structure DedekindCriteria02 where
  -- @@FIELDS
  LOCALLY_DVR_IMP_INTEGRALLY_CLOSED : thm
  DEDEKIND_EQ_LOCALIZATIONS_DVR : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekindCriteria02 [HolBase] (D : DedekindCriteriaDeps) (BDedekindCriteria01 : DedekindCriteria01) :
    ExceptT String IO DedekindCriteria02 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, SET_TAC, TAUT, .. } := D
  let { DEDEKIND_IMP_INTEGRAL_DOMAIN, DEDEKIND_IMP_NOETHERIAN, DVR, DVR_LOCALIZATION,
        INTEGRALLY_CLOSED_ALT, INTEGRAL_DOMAIN_MUL_EQ_0,
        INTEGRAL_HOMOGENEOUS_HOMOMORPHIC_IMAGE, IN_DIFF, IN_ELIM_THM, IN_RING_IDEAL_0,
        LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, MAXIMAL_IMP_PRIME_IDEAL,
        MAXIMAL_IMP_RING_IDEAL, MAXIMAL_SUPERIDEAL_EXISTS, PID_IMP_INTEGRALLY_CLOSED,
        PROPER_IDEAL_ALT, RING_0, RING_1, RING_ADD, RING_ADD_RDISTRIB, RING_DIVIDES_0,
        RING_DIVIDES_ADD, RING_DIVIDES_LMUL, RING_DIVIDES_REFL, RING_DIVIDES_RMUL,
        RING_FRACTIONATE_IN_CARRIER, RING_HOMOMORPHISM_0, RING_IDEAL, RING_LOCALEQUIV,
        RING_LOCALEQUIV_EQUIV, RING_LOCALIZATION_CARRIER, RING_LOCALIZATION_MUL,
        RING_MONOMORPHISM_EQ_0, RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL,
        RING_MULTSYS_NONPRIME, RING_MUL_ASSOC, RING_MUL_LID, RING_MUL_LZERO,
        RING_MUL_RID, RING_MUL_SYM, RING_SUB, RING_SUB_EQ_0, SUBSET, dedekind_domain,
        ring_divides, ring_fractionate, ring_multsys, .. } := D.core1
  let { INTEGRAL_DOMAIN_FRACTIONATE_PRIME_MONOMORPHISM, LOCALLY_DVR_PRIME_IMP_MAXIMAL, .. } := BDedekindCriteria01
  -- @@SCOPE END

  let LOCALLY_DVR_IMP_INTEGRALLY_CLOSED ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"q ==> ~q ==> p")
    prove
      r"!r:A ring.
          integral_domain r /\
          (!q. prime_ideal r q /\ ~(q = {ring_0 r})
               ==> DVR(ring_localization r (ring_carrier r DIFF q)))
          ==> integrally_closed r"
      (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [INTEGRALLY_CLOSED_ALT] THEN MAP_EVERY X_GEN_TAC [(← q r"a:A"), (← q r"b:A"), (← q r"c:num->A"), (← q r"n:num")] THEN STRIP_TAC THEN ABBREV_TAC (← q r"L = {y:A | y IN ring_carrier r /\ ring_divides r b (ring_mul r y a)}") THEN SUBGOAL_THEN (← q r"ring_ideal r (L:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "L" THEN REWRITE_TAC [RING_IDEAL, SUBSET, IN_ELIM_THM] THEN SIMP_TAC [] THEN ASM_SIMP_TAC [RING_0, RING_MUL_LZERO, RING_DIVIDES_0] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC [RING_ADD, RING_MUL] THENL [ASM_SIMP_TAC [RING_ADD_RDISTRIB] THEN MATCH_MP_TAC RING_DIVIDES_ADD THEN ASM_REWRITE_TAC [], ASM_SIMP_TAC [(← GSYM RING_MUL_ASSOC)] THEN MATCH_MP_TAC RING_DIVIDES_LMUL THEN ASM_REWRITE_TAC []], ALL_TAC] THEN ASM_CASES_TAC (← q r"ring_1 r:A IN L") THENL [UNDISCH_TAC (← q r"ring_1 r:A IN L") THEN EXPAND_TAC "L" THEN ASM_SIMP_TAC [IN_ELIM_THM, RING_MUL_LID], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"L:A->bool")] MAXIMAL_SUPERIDEAL_EXISTS) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [PROPER_IDEAL_ALT] THEN ASM_MESON_TAC [RING_1], DISCH_THEN (X_CHOOSE_THEN (← q r"m:A->bool") STRIP_ASSUME_TAC)] THEN SUBGOAL_THEN (← q r"(b:A) IN L") ASSUME_TAC THENL [EXPAND_TAC "L" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC RING_DIVIDES_RMUL THEN ASM_SIMP_TAC [RING_DIVIDES_REFL], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(m = {ring_0 r:A})") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN ASM SET_TAC [], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP MAXIMAL_IMP_PRIME_IDEAL)) THEN ABBREV_TAC (← q r"s = ring_carrier r DIFF (m:A->bool)") THEN SUBGOAL_THEN (← q r"ring_multsys r (s:A->bool)") ASSUME_TAC THENL [EXPAND_TAC "s" THEN ASM_SIMP_TAC [RING_MULTSYS_NONPRIME], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_monomorphism (r,ring_localization r s)
                        (ring_fractionate r (s:A->bool))") ASSUME_TAC THENL [EXPAND_TAC "s" THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_FRACTIONATE_PRIME_MONOMORPHISM], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"integrally_closed (ring_localization r (s:A->bool))") MP_TAC THENL [MATCH_MP_TAC PID_IMP_INTEGRALLY_CLOSED THEN SUBGOAL_THEN (← q r"DVR(ring_localization r (s:A->bool))") MP_TAC THENL [EXPAND_TAC "s" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [], SIMP_TAC [DVR]], ALL_TAC] THEN REWRITE_TAC [INTEGRALLY_CLOSED_ALT] THEN DISCH_THEN (MP_TAC o ((SPECL [(← q r"ring_fractionate r s (a:A)"), (← q r"ring_fractionate r s (b:A)"), (← q r"\i. ring_fractionate r s ((c:num->A) i)"), (← q r"n:num")]) o CONJUNCT2)) THEN ANTS_TAC THENL [ASM_SIMP_TAC [RING_FRACTIONATE_IN_CARRIER] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_localization r (s:A->bool)"), (← q r"ring_fractionate r (s:A->bool)"), (← q r"b:A")] RING_MONOMORPHISM_EQ_0) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ring_localization r (s:A->bool)"), (← q r"ring_fractionate r (s:A->bool)"), (← q r"a:A"), (← q r"b:A"), (← q r"c:num->A"), (← q r"n:num")] INTEGRAL_HOMOGENEOUS_HOMOMORPHIC_IMAGE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (SUBST1_TAC o SYM)] THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do if ← (do let z8 ← (do let z9 ← (pure th); pure (concl z9)); pure (is_eq z8)) then (do let z13 ← (q r"ring_0 r:A"); let z12 ← (do let z10 ← (do let z11 ← (pure th); pure (concl z11)); liftExcept (rand z10)); pure (z12 == z13)) else pure false)))) THEN MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [ring_divides, RING_FRACTIONATE_IN_CARRIER] THEN ASM_SIMP_TAC [RING_LOCALIZATION_CARRIER, IN_ELIM_THM] THEN REWRITE_TAC [LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"z:A#A->bool"), (← q r"t:A"), (← q r"u:A")] THEN DISCH_THEN (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) MP_TAC) THEN FIRST_X_ASSUM (SUBST1_TAC o (checkM (fun th => (do let z7 ← (q r"z:A#A->bool"); let z6 ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (lhand z4)); pure (z6 == z7))))) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [ring_multsys])) THEN SUBGOAL_THEN (← q r"(u:A) IN ring_carrier r /\ ~(u IN m)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"(u:A) IN s") THEN EXPAND_TAC "s" THEN SIMP_TAC [IN_DIFF], ALL_TAC] THEN ASM_SIMP_TAC [ring_fractionate, RING_LOCALIZATION_MUL] THEN ASM_SIMP_TAC [(← GSYM RING_LOCALEQUIV_EQUIV), RING_MUL, RING_LOCALEQUIV] THEN DISCH_THEN (fun z2 => tactic_of do pure (X_CHOOSE_THEN (← q r"v:A") STRIP_ASSUME_TAC (← (do let z3 ← (pure (CONJUNCTS z2)); liftExcept (last z3))))) THEN SUBGOAL_THEN (← q r"(v:A) IN ring_carrier r /\ ~(v = ring_0 r)") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"(v:A) IN s") THEN EXPAND_TAC "s" THEN REWRITE_TAC [IN_DIFF] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC [IN_RING_IDEAL_0, MAXIMAL_IMP_RING_IDEAL], ALL_TAC] THEN UNDISCH_TAC (← q r"~((u:A) IN m)") THEN MATCH_MP_TAC r1 THEN FIRST_X_ASSUM (MATCH_MP_TAC o (REWRITE_RULE [SUBSET])) THEN EXPAND_TAC "L" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [ring_divides] THEN ASM_SIMP_TAC [RING_MUL] THEN EXISTS_TAC (← q r"t:A") THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"ring_mul r v (ring_sub r (ring_mul r a (ring_mul r (ring_1 r) u))
                               (ring_mul r (ring_mul r b t) (ring_1 r))) =
      ring_0 r:A") THEN ASM_SIMP_TAC [RING_MUL_LID, RING_MUL_RID] THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"ring_sub r (ring_mul r a u) (ring_mul r b t) = ring_0 r:A") MP_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"v:A"), (← q r"ring_sub r (ring_mul r a u) (ring_mul r b t):A")] INTEGRAL_DOMAIN_MUL_EQ_0) THEN ASM_SIMP_TAC [RING_SUB, RING_MUL] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN UNDISCH_TAC (← q r"ring_mul r v (ring_sub r (ring_mul r a u)
                                 (ring_mul r (ring_mul r b t) (ring_1 r))) =
        ring_0 r:A") THEN ASM_SIMP_TAC [RING_MUL, RING_MUL_RID], ASM_SIMP_TAC [RING_SUB_EQ_0, RING_MUL] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_MUL_SYM THEN ASM_REWRITE_TAC []])

  let DEDEKIND_EQ_LOCALIZATIONS_DVR ← prove
    r"!r:A ring.
        dedekind_domain r <=>
        integral_domain r /\ noetherian_ring r /\
        !p. prime_ideal r p /\ ~(p = {ring_0 r})
            ==> DVR(ring_localization r (ring_carrier r DIFF p))"
    (GEN_TAC THEN EQ_TAC THENL [SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN, DEDEKIND_IMP_NOETHERIAN, DVR_LOCALIZATION], STRIP_TAC THEN ASM_REWRITE_TAC [dedekind_domain] THEN ASM_SIMP_TAC [LOCALLY_DVR_IMP_INTEGRALLY_CLOSED] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC LOCALLY_DVR_PRIME_IMP_MAXIMAL THEN ASM_REWRITE_TAC []])

  -- @@RETURN BEGIN
  return { LOCALLY_DVR_IMP_INTEGRALLY_CLOSED, DEDEKIND_EQ_LOCALIZATIONS_DVR }
  -- @@RETURN END

end HolANT.DedekindCriteria
