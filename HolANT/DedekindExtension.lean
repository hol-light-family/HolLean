/- ========================================================================= -/
/- ANT: The integral closure of a Dedekind domain in a finite ...          -/
/- ========================================================================= -/
/- File: HolANT/DedekindExtension.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/dedekind_extension.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antdedekindextensiondiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, ANT/integral.ml, ANT/integral_primes.ml, Library/products.ml, ANT/algmisc.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.DedekindExtension fills them).

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
import HolANT.IntegralPrimes
import HolLibrary.Products
import HolANT.Algmisc
import HolANT.IdealArith
import HolANT.Dedekind
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP INST_TYPE
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax
open HolANT.Prelude
open HolANT.Integral
open HolANT.IntegralPrimes
open HolANT.Algmisc
open HolANT.IdealArith
open HolANT.Dedekind
open HolANT.Zlattice
open HolANT.Numfield

namespace HolANT.DedekindExtension

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRA_TRACE_SURJECTIVE BASIS_COORDINATES_EXPAND
   BASIS_COORDINATES_IN_CARRIER BASIS_DISCRIMINANT_EQ_0
   BASIS_DISCRIMINANT_TIMES_COORD CARRIER_SUBRING_GENERATED_SUBRING
   DEDEKIND_IMP_NOETHERIAN ETA_AX EXTENSION FIELD_IMP_INTEGRAL_DOMAIN
   FIELD_MUL_LINV FIELD_MUL_RINV FIELD_NONTRIVIAL FINITE_EXTENSION_FREE_BASIS
   FINITE_IMAGE FINITE_IMP_ALGEBRAIC_EXTENSION FINITE_IMP_FIELD_EXTENSION
   FINITE_NUMSEG_LT FORALL_IN_IMAGE FRACTION_FIELD_COMMON_DENOMINATOR
   FREE_BASIS_IN_CARRIER FREE_BASIS_SCALE IDEAL_GENERATED_MINIMAL
   IDEAL_GENERATED_SUBSET_CARRIER_SUBSET IMP_IMP
   INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM INTEGRALLY_CLOSED_INTEGRAL_CLOSURE
   INTEGRAL_CLOSURE_SUBRING INTEGRAL_CLOSURE_SUPSET_IMAGE
   INTEGRAL_DOMAIN_SUBRING_GENERATED INTEGRAL_ELEMENT_FROM_RELATION
   INTEGRAL_ELEMENT_IMAGE INTEGRAL_ELEMENT_IN_CARRIER INTEGRAL_ELEMENT_MUL
   INTEGRAL_ELEMENT_RELATION INTEGRAL_ELEMENT_SUBRING_GENERATED
   INTEGRAL_EXTENSION_MAXIMAL_IDEAL INTEGRAL_EXTENSION_PRIME_NONZERO
   INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC IN_ELIM_THM IN_IMAGE IN_RING_IDEAL_0
   IN_RING_IDEAL_ADD IN_RING_IDEAL_LMUL I_DEF I_THM LEFT_IMP_EXISTS_THM
   MONO_EXISTS NOETHERIAN_RING_SPAN_SUBMODULE NOT_EXISTS_THM
   PRIME_IDEAL_HOMOMORPHIC_PREIMAGE RIGHT_IMP_EXISTS_THM RING_1
   RING_ADD_LDISTRIB RING_DET RING_HOMOMORPHISM_COMPOSE
   RING_HOMOMORPHISM_INTO_SUBRING_EQ RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_POW RING_IDEAL_IDEAL_GENERATED
   RING_IDEAL_IMP_SUBSET RING_INV RING_MONOMORPHISM_COMPOSE
   RING_MONOMORPHISM_EQ_0 RING_MONOMORPHISM_IMP_HOMOMORPHISM
   RING_MONOMORPHISM_INCLUSION RING_MONOMORPHISM_INTO_SUBRING RING_MUL
   RING_MUL_ASSOC RING_MUL_LID RING_MUL_POW RING_MUL_RZERO RING_POW RING_POW_1
   RING_POW_ADD RING_SPAN_INC RING_SPAN_MUL RING_SPAN_SUM RING_SUM RING_SUM_EQ
   RING_SUM_LMUL SKOLEM_THM SUBRING_GENERATED SUBRING_RING_IMAGE SUBSET
   SUBSET_ANTISYM algebraic_extension basis_discriminant dedekind_domain
   field_extension field_of_fractions finitely_generated_ideal noetherian_ring
   o_THM ring_homomorphism ring_image ring_span_INDUCT : thm)
  deriving Inhabited

/-- What dedekind_extension.ml uses from Session besides theorems. -/
structure DedekindExtensionDeps where
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
/- dedekind_extension.ml phrases from line 53 to 363                      -/
/- ---------------------------------------------------------------------- -/

structure DedekindExtension where
  -- @@FIELDS
  INTEGRAL_ELEMENT_DENOMINATOR : thm
  INTEGRAL_CLOSURE_SUBSET_SPAN : thm
  FIELD_OF_FRACTIONS_INTEGRAL_CLOSURE : thm
  DEDEKIND_INTEGRAL_CLOSURE : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupDedekindExtension [HolBase] (D : DedekindExtensionDeps) :
    ExceptT String IO DedekindExtension := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, RING_RULE, SET_TAC, .. } := D
  let { ALGEBRA_TRACE_SURJECTIVE, BASIS_COORDINATES_EXPAND,
        BASIS_COORDINATES_IN_CARRIER, BASIS_DISCRIMINANT_EQ_0,
        BASIS_DISCRIMINANT_TIMES_COORD, CARRIER_SUBRING_GENERATED_SUBRING,
        DEDEKIND_IMP_NOETHERIAN, ETA_AX, EXTENSION, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_MUL_LINV, FIELD_MUL_RINV, FIELD_NONTRIVIAL, FINITE_EXTENSION_FREE_BASIS,
        FINITE_IMAGE, FINITE_IMP_ALGEBRAIC_EXTENSION, FINITE_IMP_FIELD_EXTENSION,
        FINITE_NUMSEG_LT, FORALL_IN_IMAGE, FRACTION_FIELD_COMMON_DENOMINATOR,
        FREE_BASIS_IN_CARRIER, FREE_BASIS_SCALE, IDEAL_GENERATED_MINIMAL,
        IDEAL_GENERATED_SUBSET_CARRIER_SUBSET, IMP_IMP,
        INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM, INTEGRALLY_CLOSED_INTEGRAL_CLOSURE,
        INTEGRAL_CLOSURE_SUBRING, INTEGRAL_CLOSURE_SUPSET_IMAGE,
        INTEGRAL_DOMAIN_SUBRING_GENERATED, INTEGRAL_ELEMENT_FROM_RELATION,
        INTEGRAL_ELEMENT_IMAGE, INTEGRAL_ELEMENT_IN_CARRIER, INTEGRAL_ELEMENT_MUL,
        INTEGRAL_ELEMENT_RELATION, INTEGRAL_ELEMENT_SUBRING_GENERATED,
        INTEGRAL_EXTENSION_MAXIMAL_IDEAL, INTEGRAL_EXTENSION_PRIME_NONZERO,
        INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC, IN_ELIM_THM, IN_IMAGE, IN_RING_IDEAL_0,
        IN_RING_IDEAL_ADD, IN_RING_IDEAL_LMUL, I_DEF, I_THM, LEFT_IMP_EXISTS_THM,
        MONO_EXISTS, NOETHERIAN_RING_SPAN_SUBMODULE, NOT_EXISTS_THM,
        PRIME_IDEAL_HOMOMORPHIC_PREIMAGE, RIGHT_IMP_EXISTS_THM, RING_1,
        RING_ADD_LDISTRIB, RING_DET, RING_HOMOMORPHISM_COMPOSE,
        RING_HOMOMORPHISM_INTO_SUBRING_EQ, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_POW, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IMP_SUBSET, RING_INV, RING_MONOMORPHISM_COMPOSE,
        RING_MONOMORPHISM_EQ_0, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
        RING_MONOMORPHISM_INCLUSION, RING_MONOMORPHISM_INTO_SUBRING, RING_MUL,
        RING_MUL_ASSOC, RING_MUL_LID, RING_MUL_POW, RING_MUL_RZERO, RING_POW,
        RING_POW_1, RING_POW_ADD, RING_SPAN_INC, RING_SPAN_MUL, RING_SPAN_SUM,
        RING_SUM, RING_SUM_EQ, RING_SUM_LMUL, SKOLEM_THM, SUBRING_GENERATED,
        SUBRING_RING_IMAGE, SUBSET, SUBSET_ANTISYM, algebraic_extension,
        basis_discriminant, dedekind_domain, field_extension, field_of_fractions,
        finitely_generated_ideal, noetherian_ring, o_THM, ring_homomorphism,
        ring_image, ring_span_INDUCT, .. } := D.core1
  -- @@SCOPE END

  let INTEGRAL_ELEMENT_DENOMINATOR ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul l (ring_mul l p (ring_mul l e c))
                 (ring_mul l q y) =
      ring_mul l (ring_mul l p (ring_mul l e q)) (ring_mul l c (y:C))")
    prove
      r"!r k l (h:A->B) (g:B->C) x.
          field_of_fractions (r,k) h /\ ring_homomorphism(k,l) g /\
          integral_element (k,l) g x
          ==> ?d. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                  integral_element (r,l) (g o h) (ring_mul l (g(h d)) x)"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"(x:C) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [INTEGRAL_ELEMENT_IN_CARRIER], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:B ring"), (← q r"l:C ring"), (← q r"g:B->C"), (← q r"x:C")] INTEGRAL_ELEMENT_RELATION) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"n:num"), (← q r"a:num->B")] THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"h:A->B"), (← q r"a:num->B"), (← q r"{i:num | i < n}")] FRACTION_FIELD_COMMON_DENOMINATOR) THEN ASM_SIMP_TAC [FINITE_NUMSEG_LT, IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"d:A") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN REWRITE_TAC [SKOLEM_THM] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"b:num->A")) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [SUBSET, FORALL_IN_IMAGE]) o ((GEN_REWRITE_RULE id [ring_homomorphism]) o (checkM (fun th => (do let z13 ← (q r"ring_homomorphism(r:A ring,k:B ring) h"); let z12 ← (do let z11 ← (pure th); pure (concl z11)); pure (z12 == z13))))))) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((REWRITE_RULE [SUBSET, FORALL_IN_IMAGE]) o ((GEN_REWRITE_RULE id [ring_homomorphism]) o (checkM (fun th => (do let z10 ← (q r"ring_homomorphism(k:B ring,l:C ring) g"); let z9 ← (do let z8 ← (pure th); pure (concl z8)); pure (z9 == z10))))))) THEN ABBREV_TAC (← q r"D = (g:B->C)((h:A->B) d)") THEN SUBGOAL_THEN (← q r"(D:C) IN ring_carrier l") ASSUME_TAC THENL [EXPAND_TAC "D" THEN ASM_SIMP_TAC [], ALL_TAC] THEN MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN MAP_EVERY EXISTS_TAC [(← q r"n:num"), (← q r"\i. ring_mul r (ring_pow r d (n - 1 - i)) ((b:num->A) i)")] THEN ASM_SIMP_TAC [RING_MUL, RING_POW] THEN CONJ_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"k:B ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(h:A->B) d IN ring_carrier k") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i < n ==> (g:B->C)((a:num->B) i) IN ring_carrier l") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_sum l {i | i < n}
        (\i. ring_mul l (((g:B->C) o (h:A->B))
                           (ring_mul r (ring_pow r d (n - 1 - i)) (b i)))
                        (ring_pow l (ring_mul l D x) i)) =
      ring_sum l {i | i < n}
        (\i. ring_mul l (ring_pow l D n)
                        (ring_mul l (g((a:num->B) i)) (ring_pow l x i)))") SUBST1_TAC THENL [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(b:num->A) i IN ring_carrier r /\
        ring_mul k ((h:A->B) d) ((a:num->B) i) = h(b i) /\
        a i IN ring_carrier k") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN REWRITE_TAC [o_THM] THEN SUBGOAL_THEN (← q r"(h:A->B)(ring_mul r (ring_pow r d (n - 1 - i)) ((b:num->A) i)) =
        ring_mul k (ring_pow k (h d) (n - 1 - i))
                   (ring_mul k (h d) ((a:num->B) i))") SUBST1_TAC THENL [ASM_SIMP_TAC [RING_POW] THEN FIRST_ASSUM ((fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_POW th)])) o (checkM (fun th => (do let z7 ← (q r"ring_homomorphism(r:A ring,k:B ring) h"); let z6 ← (do let z5 ← (pure th); pure (concl z5)); pure (z6 == z7))))), ALL_TAC] THEN ASM_SIMP_TAC [RING_POW, RING_MUL] THEN FIRST_ASSUM ((fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_POW th)])) o (checkM (fun th => (do let z4 ← (q r"ring_homomorphism(k:B ring,l:C ring) g"); let z3 ← (do let z2 ← (pure th); pure (concl z2)); pure (z3 == z4))))) THEN SUBGOAL_THEN (← q r"n = (n - 1 - i) + (1 + i)") (fun th => GEN_REWRITE_TAC (RAND_CONV o (LAND_CONV o RAND_CONV)) [th]) THENL [ASM_ARITH_TAC, ALL_TAC] THEN ASM_SIMP_TAC [RING_POW_ADD, RING_POW_1, RING_MUL_POW] THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_IMP] r1) THEN ASM_SIMP_TAC [RING_POW], ALL_TAC] THEN ASM_SIMP_TAC [RING_SUM_LMUL, FINITE_NUMSEG_LT, IN_ELIM_THM, RING_MUL, RING_POW, RING_MUL_POW] THEN ASM_SIMP_TAC [(← GSYM RING_ADD_LDISTRIB), RING_POW, RING_SUM, RING_MUL_RZERO])

  let INTEGRAL_CLOSURE_SUBSET_SPAN ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← RING_RULE (← q r"ring_mul l (ring_mul l u (ring_mul l p q)) w =
      ring_mul l (ring_mul l p q) (ring_mul l u (w:C))")
    prove
      r"!r k l (h:A->B) (g:B->C).
          integrally_closed r /\ field_of_fractions (r,k) h /\
          finite_extension (k,l) g /\ separable_extension (k,l) g
          ==> ?t. FINITE t /\ t SUBSET ring_carrier l /\
                  {y | integral_element (r,l) (g o h) y} SUBSET
                  ring_span (r,l) (g o h) t"
      (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((GEN_REWRITE_RULE id [field_extension]) o (MATCH_MP FINITE_IMP_FIELD_EXTENSION))) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) o (checkM (fun th => (do let z25 ← (q r"ring_monomorphism(k:B ring,l:C ring) g"); let z24 ← (do let z23 ← (pure th); pure (concl z23)); pure (z24 == z25)))))) THEN SUBGOAL_THEN (← q r"ring_homomorphism(r,l) ((g:B->C) o (h:A->B))") ASSUME_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"k:B ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_ASSUM ((X_CHOOSE_TAC (← q r"b0:num->C")) o (MATCH_MP FINITE_EXTENSION_FREE_BASIS)) THEN ABBREV_TAC (← q r"n = extension_degree (k,l) (g:B->C)") THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP FREE_BASIS_IN_CARRIER)) THEN SUBGOAL_THEN (← q r"!i. i < n
          ==> ?d. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                  integral_element (r,l) ((g:B->C) o (h:A->B))
                    (ring_mul l (g(h d)) ((b0:num->C) i))") MP_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_ELEMENT_DENOMINATOR THEN EXISTS_TAC (← q r"k:B ring") THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC, FINITE_IMP_FIELD_EXTENSION] THEN ASM_MESON_TAC [algebraic_extension], GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN REWRITE_TAC [SKOLEM_THM] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"d:num->A"))] THEN ABBREV_TAC (← q r"b = \i. ring_mul l ((g:B->C)((h:A->B)((d:num->A) i))) ((b0:num->C) i)") THEN SUBGOAL_THEN (← q r"free_basis (k,l) (g:B->C) n b") ASSUME_TAC THENL [EXPAND_TAC "b" THEN MATCH_MP_TAC FREE_BASIS_SCALE THEN ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(d:num->A) i IN ring_carrier r /\ ~(d i = ring_0 r)") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0]], ALL_TAC] THEN SUBGOAL_THEN (← q r"!i. i < n ==> integral_element (r,l) ((g:B->C) o (h:A->B)) ((b:num->C) i)") ASSUME_TAC THENL [EXPAND_TAC "b" THEN ASM_SIMP_TAC [], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP FREE_BASIS_IN_CARRIER) o (checkM (fun th => (do let z22 ← (q r"free_basis (k,l) (g:B->C) n b"); let z21 ← (do let z20 ← (pure th); pure (concl z20)); pure (z21 == z22)))))) THEN ABBREV_TAC (← q r"D = basis_discriminant (k,l) (g:B->C) n b") THEN SUBGOAL_THEN (← q r"(D:B) IN ring_carrier k /\ ~(D = ring_0 k)") STRIP_ASSUME_TAC THENL [CONJ_TAC THENL [EXPAND_TAC "D" THEN REWRITE_TAC [basis_discriminant, RING_DET], ALL_TAC] THEN EXPAND_TAC "D" THEN MP_TAC (← ISPECL [(← q r"g:B->C"), (← q r"k:B ring"), (← q r"l:C ring"), (← q r"n:num"), (← q r"b:num->C")] BASIS_DISCRIMINANT_EQ_0) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"?z:C. z IN ring_carrier l /\ algebra_trace (k,l) (g:B->C) z = ring_1 k") STRIP_ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"g:B->C"), (← q r"k:B ring"), (← q r"l:C ring")] ALGEBRA_TRACE_SURJECTIVE) THEN ASM_REWRITE_TAC [EXTENSION, IN_IMAGE] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"ring_1 k:B"))) THEN REWRITE_TAC [RING_1] THEN MESON_TAC [], ALL_TAC] THEN REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"x:C") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"ring_mul l (ring_inv l x) (z:C)"))) THEN ASM_SIMP_TAC [RING_MUL, RING_INV, RING_MUL_ASSOC, FIELD_MUL_RINV, RING_MUL_LID] THEN ASM_MESON_TAC [FIELD_NONTRIVIAL], ALL_TAC] THEN EXISTS_TAC (← q r"IMAGE (\i. ring_mul l ((g:B->C)(ring_inv k D)) ((b:num->C) i))
            {i | i < n}") THEN ASM_SIMP_TAC [FINITE_IMAGE, FINITE_NUMSEG_LT] THEN CONJ_TAC THENL [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [RING_MUL, RING_INV, RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"x:C") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(x:C) IN ring_carrier l") ASSUME_TAC THENL [ASM_MESON_TAC [INTEGRAL_ELEMENT_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y:C. integral_element (r,l) ((g:B->C) o (h:A->B)) y
            ==> algebra_trace (k,l) g y IN IMAGE h (ring_carrier r)") ASSUME_TAC THENL [ASM_MESON_TAC [INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"g:B->C"), (← q r"k:B ring"), (← q r"l:C ring"), (← q r"n:num"), (← q r"b:num->C"), (← q r"IMAGE (h:A->B) (ring_carrier r)"), (← q r"x:C")] BASIS_DISCRIMINANT_TIMES_COORD) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MATCH_MP_TAC (← REWRITE_RULE [ring_image] SUBRING_RING_IMAGE) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o (checkM (fun th => (do if ← (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); canM (fun z13 => (do let z14 ← (pure z13); find_termM (fun z15 => (do let z17 ← (pure z15); let z16 ← (q r"algebra_trace (k,l) (g:B->C)"); pure (z16 == z17))) z14)) z11) then (do let z18 ← (do let z19 ← (pure th); pure (concl z19)); pure (is_forall z18)) else pure false)))) THEN MATCH_MP_TAC INTEGRAL_ELEMENT_MUL THEN ASM_SIMP_TAC [], ALL_TAC] THEN REWRITE_TAC [IN_IMAGE] THEN GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN REWRITE_TAC [SKOLEM_THM] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"a:num->A")) THEN MP_TAC (← ISPECL [(← q r"g:B->C"), (← q r"k:B ring"), (← q r"l:C ring"), (← q r"n:num"), (← q r"b:num->C"), (← q r"x:C")] BASIS_COORDINATES_EXPAND) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_SPAN_SUM THEN X_GEN_TAC (← q r"i:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"i:num"))) THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ABBREV_TAC (← q r"c = basis_coordinates (k,l) (g:B->C) n b x i") THEN SUBGOAL_THEN (← q r"(c:B) IN ring_carrier k") ASSUME_TAC THENL [EXPAND_TAC "c" THEN ASM_SIMP_TAC [BASIS_COORDINATES_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_mul l ((g:B->C) c) (b i) =
      ring_mul l (((g:B->C) o (h:A->B)) ((a:num->A) i))
                 (ring_mul l (g(ring_inv k D)) (b i))") SUBST1_TAC THENL [REWRITE_TAC [o_THM] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z5 ← (do let z6 ← (pure th); pure (concl z6)); pure (is_eq z5)) then (do let z10 ← (q r"ring_mul k D (c:B)"); let z9 ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); liftExcept (lhand z7)); pure (z9 == z10)) else pure false))))) THEN SUBGOAL_THEN (← q r"c = ring_mul k (ring_inv k D) (ring_mul k D (c:B))") (fun th => GEN_REWRITE_TAC (LAND_CONV o (LAND_CONV o RAND_CONV)) [th]) THENL [ASM_SIMP_TAC [RING_MUL_ASSOC, RING_INV, FIELD_MUL_LINV, RING_MUL_LID], ALL_TAC] THEN FIRST_ASSUM ((fun th => tactic_of do pure (ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_MUL th), RING_MUL, RING_INV])) o (checkM (fun th => (do let z4 ← (q r"ring_homomorphism(k:B ring,l:C ring) g"); let z3 ← (do let z2 ← (pure th); pure (concl z2)); pure (z3 == z4))))) THEN SUBGOAL_THEN (← q r"(g:B->C)(ring_inv k D) IN ring_carrier l /\
        (g:B->C) D IN ring_carrier l /\ (g:B->C) c IN ring_carrier l /\
        (b:num->C) i IN ring_carrier l") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, RING_INV], ALL_TAC] THEN MATCH_MP_TAC (← REWRITE_RULE [IMP_IMP] r1) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN MATCH_MP_TAC RING_SPAN_MUL THEN ASM_SIMP_TAC [RING_HOMOMORPHISM_IN_CARRIER] THEN CONJ_TAC THENL [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN MATCH_MP_TAC RING_SPAN_INC THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN ASM_MESON_TAC [RING_MUL, RING_INV, RING_HOMOMORPHISM_IN_CARRIER])

  let FIELD_OF_FRACTIONS_INTEGRAL_CLOSURE ← prove
    r"!r k l (h:A->B) (g:B->C).
        field_of_fractions (r,k) h /\ algebraic_extension (k,l) g
        ==> field_of_fractions
             (subring_generated l {y | integral_element (r,l) (g o h) y},l)
             I"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN FIRST_ASSUM (ASSUME_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [algebraic_extension]))) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_extension])) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) o (checkM (fun th => (do let z3 ← (q r"ring_monomorphism(k:B ring,l:C ring) g"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3)))))) THEN SUBGOAL_THEN (← q r"ring_homomorphism(r,l) ((g:B->C) o (h:A->B))") ASSUME_TAC THENL [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"k:B ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"{y | integral_element (r,l) ((g:B->C) o (h:A->B)) y} subring_of l") ASSUME_TAC THENL [ASM_SIMP_TAC [INTEGRAL_CLOSURE_SUBRING], ALL_TAC] THEN REWRITE_TAC [field_of_fractions] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [REWRITE_TAC [I_DEF, RING_MONOMORPHISM_INCLUSION], ALL_TAC] THEN ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING, IN_ELIM_THM, I_THM, (← CONJUNCT2 SUBRING_GENERATED)] THEN X_GEN_TAC (← q r"x:C") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"l:C ring"), (← q r"h:A->B"), (← q r"g:B->C"), (← q r"x:C")] INTEGRAL_ELEMENT_DENOMINATOR) THEN ASM_SIMP_TAC [INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC] THEN ANTS_TAC THENL [ASM_MESON_TAC [algebraic_extension], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"d:A") STRIP_ASSUME_TAC) THEN MAP_EVERY EXISTS_TAC [(← q r"ring_mul l ((g:B->C)((h:A->B) d)) x"), (← q r"(g:B->C)((h:A->B) d)")] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"l:C ring"), (← q r"(g:B->C) o (h:A->B)"), (← q r"d:A")] INTEGRAL_ELEMENT_IMAGE) THEN ASM_REWRITE_TAC [o_THM], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_monomorphism(r,l) ((g:B->C) o (h:A->B))") MP_TAC THENL [MATCH_MP_TAC RING_MONOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"k:B ring") THEN ASM_REWRITE_TAC [], ASM_MESON_TAC [RING_MONOMORPHISM_EQ_0, o_THM]])

  let DEDEKIND_INTEGRAL_CLOSURE ← prove
    r"!r k l (h:A->B) (g:B->C).
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        finite_extension (k,l) g /\ separable_extension (k,l) g
        ==> dedekind_domain
              (subring_generated l {y | integral_element (r,l) (g o h) y})"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_of_fractions])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o ((GEN_REWRITE_RULE id [field_extension]) o (MATCH_MP FINITE_IMP_FIELD_EXTENSION))) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) o (checkM (fun th => (do let z22 ← (q r"ring_monomorphism(k:B ring,l:C ring) g"); let z21 ← (do let z20 ← (pure th); pure (concl z20)); pure (z21 == z22)))))) THEN SUBGOAL_THEN (← q r"ring_monomorphism(r,l) ((g:B->C) o (h:A->B))") ASSUME_TAC THENL [MATCH_MP_TAC RING_MONOMORPHISM_COMPOSE THEN EXISTS_TAC (← q r"k:B ring") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) o (checkM (fun th => (do let z19 ← (q r"ring_monomorphism(r:A ring,l:C ring) ((g:B->C) o (h:A->B))"); let z18 ← (do let z17 ← (pure th); pure (concl z17)); pure (z18 == z19)))))) THEN ABBREV_TAC (← q r"S = {y | integral_element (r,l) ((g:B->C) o (h:A->B)) y}") THEN SUBGOAL_THEN (← q r"(!y. y IN S <=> integral_element (r,l) ((g:B->C) o (h:A->B)) y) /\
    S subring_of l /\ IMAGE ((g:B->C) o (h:A->B)) (ring_carrier r) SUBSET S /\
    integrally_closed(subring_generated l S)") STRIP_ASSUME_TAC THENL [EXPAND_TAC "S" THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_SIMP_TAC [INTEGRAL_CLOSURE_SUBRING, INTEGRAL_CLOSURE_SUPSET_IMAGE, INTEGRALLY_CLOSED_INTEGRAL_CLOSURE], FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o (checkM (fun th => (do if ← (do let z11 ← (do let z12 ← (pure th); pure (concl z12)); pure (is_eq z11)) then (do let z16 ← (q r"S:C->bool"); let z15 ← (do let z13 ← (do let z14 ← (pure th); pure (concl z14)); liftExcept (rand z13)); pure (z15 == z16)) else pure false))))] THEN SUBGOAL_THEN (← q r"ring_carrier(subring_generated l S) = (S:C->bool)") ASSUME_TAC THENL [ASM_SIMP_TAC [CARRIER_SUBRING_GENERATED_SUBRING], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_homomorphism(r,subring_generated l S) ((g:B->C) o (h:A->B))") ASSUME_TAC THENL [ASM_SIMP_TAC [RING_HOMOMORPHISM_INTO_SUBRING_EQ], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_monomorphism(r,subring_generated l S) ((g:B->C) o (h:A->B))") ASSUME_TAC THENL [MATCH_MP_TAC RING_MONOMORPHISM_INTO_SUBRING THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y. y IN S
        ==> integral_element (r,subring_generated l S)
                             ((g:B->C) o (h:A->B)) y") ASSUME_TAC THENL [ASM_SIMP_TAC [INTEGRAL_ELEMENT_SUBRING_GENERATED], ALL_TAC] THEN SUBGOAL_THEN (← q r"!y. integral_element (r,l) ((g:B->C) o (h:A->B)) y
        ==> integral_element (r,subring_generated l S) (g o h) y") ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"integral_domain(subring_generated l (S:C->bool))") ASSUME_TAC THENL [MATCH_MP_TAC INTEGRAL_DOMAIN_SUBRING_GENERATED THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN REWRITE_TAC [dedekind_domain] THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [REWRITE_TAC [noetherian_ring, finitely_generated_ideal] THEN X_GEN_TAC (← q r"J:C->bool") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"k:B ring"), (← q r"l:C ring"), (← q r"h:A->B"), (← q r"g:B->C")] INTEGRAL_CLOSURE_SUBSET_SPAN) THEN ANTS_TAC THENL [ASM_MESON_TAC [dedekind_domain], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"t:C->bool") STRIP_ASSUME_TAC) THEN SUBGOAL_THEN (← q r"(J:C->bool) SUBSET S") ASSUME_TAC THENL [ASM_MESON_TAC [RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"l:C ring"), (← q r"(g:B->C) o (h:A->B)"), (← q r"t:C->bool"), (← q r"J:C->bool")] NOETHERIAN_RING_SPAN_SUBMODULE) THEN ANTS_TAC THENL [ASM_SIMP_TAC [DEDEKIND_IMP_NOETHERIAN] THEN MP_TAC (← ISPECL [(← q r"subring_generated l (S:C->bool)"), (← q r"J:C->bool")] IN_RING_IDEAL_0) THEN MP_TAC (← ISPECL [(← q r"subring_generated l (S:C->bool)"), (← q r"J:C->bool")] IN_RING_IDEAL_ADD) THEN MP_TAC (← ISPECL [(← q r"subring_generated l (S:C->bool)"), (← q r"J:C->bool")] IN_RING_IDEAL_LMUL) THEN ASM_REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED)] THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC [] THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"{y | integral_element (r,l) ((g:B->C) o (h:A->B)) y} SUBSET
          ring_span (r,l) (g o h) t") THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [SUBSET], REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC []], DISCH_THEN (X_CHOOSE_THEN (← q r"u:C->bool") STRIP_ASSUME_TAC)] THEN EXISTS_TAC (← q r"u:C->bool") THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_X_ASSUM ((fun th => tactic_of do pure (GEN_REWRITE_TAC LAND_CONV [(← SYM th)])) o (checkM (fun th => (do let z10 ← (q r"ring_span (r,l) ((g:B->C) o (h:A->B)) u"); let z9 ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); liftExcept (lhand z7)); pure (z9 == z10))))) THEN MP_TAC (← ISPECL [(← q r"subring_generated l (S:C->bool)"), (← q r"u:C->bool")] RING_IDEAL_IDEAL_GENERATED) THEN ABBREV_TAC (← q r"m = ideal_generated (subring_generated l S) (u:C->bool)") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"(u:C->bool) SUBSET m") ASSUME_TAC THENL [EXPAND_TAC "m" THEN MATCH_MP_TAC IDEAL_GENERATED_SUBSET_CARRIER_SUBSET THEN ASM SET_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"subring_generated l (S:C->bool)"), (← q r"m:C->bool")] IN_RING_IDEAL_0) THEN MP_TAC (← ISPECL [(← q r"subring_generated l (S:C->bool)"), (← q r"m:C->bool")] IN_RING_IDEAL_ADD) THEN MP_TAC (← ISPECL [(← q r"subring_generated l (S:C->bool)"), (← q r"m:C->bool")] IN_RING_IDEAL_LMUL) THEN ASM_REWRITE_TAC [(← CONJUNCT2 SUBRING_GENERATED)] THEN REPEAT DISCH_TAC THEN REWRITE_TAC [SUBSET] THEN MATCH_MP_TAC ring_span_INDUCT THEN ASM_SIMP_TAC [] THEN CONJ_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN ASM SET_TAC [], X_GEN_TAC (← q r"q:C->bool") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"subring_generated l (S:C->bool)"), (← q r"(g:B->C) o (h:A->B)"), (← q r"q:C->bool")] INTEGRAL_EXTENSION_MAXIMAL_IDEAL) THEN ANTS_TAC THENL [ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN FIRST_ASSUM (fun z1 => tactic_of do pure (MATCH_MP_TAC (← (do let z2 ← (do pure (CONJUNCTS (← GEN_REWRITE_RULE id [dedekind_domain] (← (do let z3 ← (pure z1); checkM (fun th => (do let z6 ← (q r"dedekind_domain(r:A ring)"); let z5 ← (do let z4 ← (pure th); pure (concl z4)); pure (z5 == z6))) z3))))); liftExcept (last z2))))) THEN CONJ_TAC THENL [MATCH_MP_TAC PRIME_IDEAL_HOMOMORPHIC_PREIMAGE THEN EXISTS_TAC (← q r"subring_generated l (S:C->bool)") THEN ASM_REWRITE_TAC [ETA_AX], MATCH_MP_TAC INTEGRAL_EXTENSION_PRIME_NONZERO THEN EXISTS_TAC (← q r"subring_generated l (S:C->bool)") THEN ASM_SIMP_TAC [ETA_AX]]])

  -- @@RETURN BEGIN
  return { INTEGRAL_ELEMENT_DENOMINATOR, INTEGRAL_CLOSURE_SUBSET_SPAN,
           FIELD_OF_FRACTIONS_INTEGRAL_CLOSURE, DEDEKIND_INTEGRAL_CLOSURE }
  -- @@RETURN END

end HolANT.DedekindExtension
