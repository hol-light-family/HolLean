/- ========================================================================= -/
/- ANT: The Galois group of a cyclotomic field                             -/
/- ========================================================================= -/
/- File: HolANT/CyclotomicGalois.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/cyclotomic_galois.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antcyclotomicgaloisdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/symmetric_group.ml, Library/galois.ml, Library/integer.ml, Library/isum.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/modmul_group.ml, Library/cyclotomic.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, Library/ring_groups.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/dedekind_kummer.ml, Library/finite_fields.ml, ANT/cyclotomic_poly.ml, ANT/power_basis.ml, ANT/cyclotomic_field.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.CyclotomicGalois fills them).

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
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.SymmetricGroup
import HolLibrary.Galois
import HolLibrary.Integer
import HolLibrary.Isum
import HolLibrary.Products
import HolLibrary.Multiplicative
import HolLibrary.Primitive
import HolLibrary.ModmulGroup
import HolLibrary.Cyclotomic
import HolANT.Algmisc
import HolANT.Integral
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolLibrary.RingGroups
import HolANT.IdealArith
import HolANT.Dedekind
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
import HolLibrary.FiniteFields
import HolANT.CyclotomicPoly
import HolANT.PowerBasis
import HolANT.CyclotomicField

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
open HolANT.CyclotomicPoly
open HolANT.PowerBasis
open HolANT.CyclotomicField

namespace HolANT.CyclotomicGalois

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ABELIAN_UNIT_GROUP COPRIME_1 COPRIME_LMOD CYCLOTOMIC_EXTENSION_ABELIAN
   CYCLOTOMIC_FIELD_DEGREE CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM
   DIVIDES_REFL EXTENSION FIELD_EXTENSION_SUBFIELD_GENERATED FORALL_IN_IMAGE
   FORALL_UNWIND_THM2 GALOIS_GROUP_EQ_ON_GENERATORS GROUP_HOMOMORPHISM
   GROUP_ISOMORPHISM GROUP_ISOMORPHISMS_SYM GROUP_ISOMORPHISM_COMPOSE
   GROUP_ISOMORPHISM_IMP_ISOMORPHIC HAS_SIZE_MODMUL_GROUP IMAGE_I
   INTEGER_MOD_RING_CLAUSES INTEGER_MOD_RING_UNIT INT_OF_NUM_EQ INT_OF_NUM_LT
   INT_OF_NUM_MUL INT_OF_NUM_OF_INT INT_OF_NUM_REM INT_POS IN_ELIM_THM IN_IMAGE
   IN_INSERT IN_INTEGER_MOD_RING_CARRIER IN_INTER IN_SING IN_SUBFIELD_0
   ISOMORPHIC_GROUP_ABELIANNESS ISOMORPHIC_GROUP_HAS_ORDER ISOMORPHIC_GROUP_SYM
   LEFT_IMP_EXISTS_THM MODMUL_GROUP MOD_1 MOD_LT MOD_LT_EQ MOD_MOD_REFL
   MOD_MULT_MOD2 NOT_IN_EMPTY NUMBER_FIELD_IMP_FIELD NUM_OF_INT_OF_NUM RING_0
   RING_POW_EQ_1 RING_POW_MOD_ORDER SUBFIELDS_GENERATED_EQ
   SUBFIELD_GENERATED_INSERT SUBSET SUBSET_REFL UNIT_GROUP group_isomorphism
   group_isomorphisms num_coprime o_THM : thm)
  deriving Inhabited

/-- What cyclotomic_galois.ml uses from Session besides theorems. -/
structure CyclotomicGaloisDeps where
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
/- cyclotomic_galois.ml phrases from line 63 to 266                       -/
/- ---------------------------------------------------------------------- -/

structure CyclotomicGalois where
  -- @@FIELDS
  UNIT_GROUP_INTEGER_MOD_RING : thm
  GROUP_ISOMORPHISM_MODMUL_UNIT_GROUP : thm
  SUBFIELD_GENERATED_INSERT_PRIME_SUBFIELD : thm
  CYCLOTOMIC_FIELD_GALOIS_EXTENSION : thm
  CYCLOTOMIC_FIELD_GALOIS_GROUP_MODMUL : thm
  CYCLOTOMIC_FIELD_GALOIS_GROUP_HAS_SIZE : thm
  CYCLOTOMIC_FIELD_GALOIS_GROUP : thm
  CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS : thm
  CYCLOTOMIC_FIELD_GALOIS_GROUP_ROOT : thm
  CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ : thm
  CYCLOTOMIC_FIELD_GALOIS_GROUP_ISOMORPHIC : thm
  CYCLOTOMIC_FIELD_GALOIS_GROUP_ABELIAN : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupCyclotomicGalois [HolBase] (D : CyclotomicGaloisDeps) :
    ExceptT String IO CyclotomicGalois := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, .. } := D
  let { ABELIAN_UNIT_GROUP, COPRIME_1, COPRIME_LMOD, CYCLOTOMIC_EXTENSION_ABELIAN,
        CYCLOTOMIC_FIELD_DEGREE, CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM,
        DIVIDES_REFL, EXTENSION, FIELD_EXTENSION_SUBFIELD_GENERATED, FORALL_IN_IMAGE,
        FORALL_UNWIND_THM2, GALOIS_GROUP_EQ_ON_GENERATORS, GROUP_HOMOMORPHISM,
        GROUP_ISOMORPHISM, GROUP_ISOMORPHISMS_SYM, GROUP_ISOMORPHISM_COMPOSE,
        GROUP_ISOMORPHISM_IMP_ISOMORPHIC, HAS_SIZE_MODMUL_GROUP, IMAGE_I,
        INTEGER_MOD_RING_CLAUSES, INTEGER_MOD_RING_UNIT, INT_OF_NUM_EQ, INT_OF_NUM_LT,
        INT_OF_NUM_MUL, INT_OF_NUM_OF_INT, INT_OF_NUM_REM, INT_POS, IN_ELIM_THM,
        IN_IMAGE, IN_INSERT, IN_INTEGER_MOD_RING_CARRIER, IN_INTER, IN_SING,
        IN_SUBFIELD_0, ISOMORPHIC_GROUP_ABELIANNESS, ISOMORPHIC_GROUP_HAS_ORDER,
        ISOMORPHIC_GROUP_SYM, LEFT_IMP_EXISTS_THM, MODMUL_GROUP, MOD_1, MOD_LT,
        MOD_LT_EQ, MOD_MOD_REFL, MOD_MULT_MOD2, NOT_IN_EMPTY, NUMBER_FIELD_IMP_FIELD,
        NUM_OF_INT_OF_NUM, RING_0, RING_POW_EQ_1, RING_POW_MOD_ORDER,
        SUBFIELDS_GENERATED_EQ, SUBFIELD_GENERATED_INSERT, SUBSET, SUBSET_REFL,
        UNIT_GROUP, group_isomorphism, group_isomorphisms, num_coprime, o_THM, .. } := D.core1
  -- @@SCOPE END

  let UNIT_GROUP_INTEGER_MOD_RING ← prove
    r"!n. ~(n = 0)
       ==> group_carrier(unit_group(integer_mod_ring n)) =
           IMAGE (&) {a | a < n /\ coprime(a,n)}"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM, UNIT_GROUP, INTEGER_MOD_RING_UNIT, IN_INTEGER_MOD_RING_CARRIER] THEN ASM_REWRITE_TAC [INT_OF_NUM_EQ] THEN X_GEN_TAC (← q r"c:int") THEN EQ_TAC THENL [STRIP_TAC THEN EXISTS_TAC (← q r"num_of_int c") THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT, (← GSYM INT_OF_NUM_LT), num_coprime], STRIP_TAC THEN ASM_REWRITE_TAC [INT_POS, INT_OF_NUM_LT, (← GSYM num_coprime)]])

  let GROUP_ISOMORPHISM_MODMUL_UNIT_GROUP ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← ARITH_RULE (← q r"a < 1 <=> a = 0")
    prove
      r"!n. ~(n = 0)
         ==> group_isomorphism(modmul_group n,unit_group(integer_mod_ring n))
                              (\a. &a rem &n)"
      (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [GROUP_ISOMORPHISM, GROUP_HOMOMORPHISM, UNIT_GROUP_INTEGER_MOD_RING, UNIT_GROUP, INTEGER_MOD_RING_CLAUSES, INT_OF_NUM_REM, INT_OF_NUM_MUL, MOD_MULT_MOD2, INT_OF_NUM_EQ, MODMUL_GROUP] THEN COND_CASES_TAC THENL [SUBGOAL_THEN (← q r"n = 1") SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN REWRITE_TAC [MOD_1, IN_SING, r1, COPRIME_1] THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE (\a. &(a MOD n)) {m | m < n /\ coprime(m,n)} =
      IMAGE ((&):num->int) {a | a < n /\ coprime(a,n)}") SUBST1_TAC THENL [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN MESON_TAC [MOD_LT], SIMP_TAC [SUBSET_REFL, IN_ELIM_THM, MOD_MOD_REFL] THEN MESON_TAC [MOD_LT]])

  let SUBFIELD_GENERATED_INSERT_PRIME_SUBFIELD ← prove
    r"!(k:A ring) z.
        subfield_generated k
          (z INSERT IMAGE I (ring_carrier(subfield_generated k {ring_0 k}))) =
        subfield_generated k {z}"
    (REWRITE_TAC [IMAGE_I, SUBFIELD_GENERATED_INSERT] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC SUBFIELDS_GENERATED_EQ THEN REWRITE_TAC [SUBSET, IN_INTER, IN_INSERT, NOT_IN_EMPTY] THEN MESON_TAC [IN_SUBFIELD_0, RING_0])

  let CYCLOTOMIC_FIELD_GALOIS_EXTENSION ← prove
    r"!(k:A ring) z n.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k
        ==> galois_extension (subfield_generated k {ring_0 k},k) I"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_EXTENSION_ABELIAN) THEN ASM_SIMP_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD, SUBFIELD_GENERATED_INSERT_PRIME_SUBFIELD, RING_POW_EQ_1, DIVIDES_REFL])

  let CYCLOTOMIC_FIELD_GALOIS_GROUP_MODMUL ← prove
    r"!(k:A ring) z n.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k
        ==> ?e. group_isomorphism
                  (galois_group (subfield_generated k {ring_0 k},k) I,
                   modmul_group n) e /\
                !f. f IN
                    group_carrier(galois_group
                                    (subfield_generated k {ring_0 k},k) I)
                    ==> f z = ring_pow k z (e f)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated k {ring_0 k:A}"), (← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM) THEN ASM_SIMP_TAC [FIELD_EXTENSION_SUBFIELD_GENERATED, NUMBER_FIELD_IMP_FIELD, SUBFIELD_GENERATED_INSERT_PRIME_SUBFIELD] THEN DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC [CYCLOTOMIC_FIELD_DEGREE])

  let CYCLOTOMIC_FIELD_GALOIS_GROUP_HAS_SIZE ← prove
    r"!(k:A ring) z n.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k
        ==> group_carrier(galois_group (subfield_generated k {ring_0 k},k) I)
            HAS_SIZE phi n"
    (REPEAT STRIP_TAC THEN MP_TAC (← SPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_GALOIS_GROUP_MODMUL) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CHOOSE_THEN (MP_TAC o ((MATCH_MP GROUP_ISOMORPHISM_IMP_ISOMORPHIC) o CONJUNCT1))) THEN ASM_MESON_TAC [ISOMORPHIC_GROUP_HAS_ORDER, HAS_SIZE_MODMUL_GROUP])

  let CYCLOTOMIC_FIELD_GALOIS_GROUP ← prove
    r"!(k:A ring) z n.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k
        ==> ?f. group_isomorphism
                  (unit_group(integer_mod_ring n),
                   galois_group (subfield_generated k {ring_0 k},k) I) f /\
                !c. c IN group_carrier(unit_group(integer_mod_ring n))
                    ==> f c z = ring_pow k z (num_of_int c)"
    (REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"n:num") GROUP_ISOMORPHISM_MODMUL_UNIT_GROUP) THEN MP_TAC (← SPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_GALOIS_GROUP_MODMUL) THEN ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"e:(A->A)->num") THEN DISCH_THEN (CONJUNCTS_THEN2 (fun th => DISCH_THEN (MP_TAC o ((MATCH_MP GROUP_ISOMORPHISM_COMPOSE) o (CONJ th)))) ASSUME_TAC) THEN REWRITE_TAC [group_isomorphism, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"f:int->A->A") THEN GEN_REWRITE_TAC LAND_CONV [GROUP_ISOMORPHISMS_SYM] THEN DISCH_TAC THEN EXISTS_TAC (← q r"f:int->A->A") THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [group_isomorphisms])) THEN RULE_ASSUM_TAC (REWRITE_RULE [GROUP_HOMOMORPHISM, SUBSET, FORALL_IN_IMAGE, o_THM]) THEN X_GEN_TAC (← q r"c:int") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"num_of_int c = (e:(A->A)->num) (f c) MOD n") SUBST1_TAC THENL [FIRST_X_ASSUM (MP_TAC o (SPEC (← q r"c:int"))) THEN ASM_REWRITE_TAC [INT_OF_NUM_REM] THEN DISCH_THEN (MP_TAC o (AP_TERM (← q r"num_of_int"))) THEN REWRITE_TAC [NUM_OF_INT_OF_NUM] THEN DISCH_THEN (ACCEPT_TAC o SYM), ALL_TAC] THEN SUBGOAL_THEN (← q r"(f:int->A->A) c IN
    group_carrier(galois_group (subfield_generated k {ring_0 k},k) I)") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN UNDISCH_TAC (← q r"ring_order k (z:A) = n") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [RING_POW_MOD_ORDER] THEN ASM_MESON_TAC [])

  let CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS ← prove
    r"!(k:A ring) z n c.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k /\
        coprime(c,n)
        ==> ?sigma. sigma IN
                    group_carrier(galois_group
                                    (subfield_generated k {ring_0 k},k) I) /\
                    sigma z = ring_pow k z c"
    (REPEAT STRIP_TAC THEN MP_TAC (← SPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_GALOIS_GROUP) THEN ASM_SIMP_TAC [GROUP_ISOMORPHISM, GROUP_HOMOMORPHISM, SUBSET, FORALL_IN_IMAGE, UNIT_GROUP_INTEGER_MOD_RING, IN_ELIM_THM, NUM_OF_INT_OF_NUM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"f:int->A->A") STRIP_ASSUME_TAC) THEN EXISTS_TAC (← q r"(f:int->A->A)(&(c MOD n))") THEN ASM_SIMP_TAC [MOD_LT_EQ, COPRIME_LMOD] THEN UNDISCH_TAC (← q r"ring_order k (z:A) = n") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [RING_POW_MOD_ORDER])

  let CYCLOTOMIC_FIELD_GALOIS_GROUP_ROOT ← prove
    r"!(k:A ring) z n sigma.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k /\
        sigma IN
        group_carrier(galois_group (subfield_generated k {ring_0 k},k) I)
        ==> ?c. c < n /\ coprime(c,n) /\ sigma z = ring_pow k z c"
    (MAP_EVERY X_GEN_TAC [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num"), (← q r"g:A->A")] THEN STRIP_TAC THEN MP_TAC (← SPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_GALOIS_GROUP) THEN ASM_SIMP_TAC [GROUP_ISOMORPHISM, UNIT_GROUP_INTEGER_MOD_RING] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"f:int->A->A") (CONJUNCTS_THEN2 (MP_TAC o (CONJUNCT1 o CONJUNCT2)) MP_TAC)) THEN REWRITE_TAC [FORALL_IN_IMAGE, IN_ELIM_THM, NUM_OF_INT_OF_NUM] THEN DISCH_TAC THEN REWRITE_TAC [EXTENSION] THEN DISCH_THEN (MP_TAC o (SPEC (← q r"g:A->A"))) THEN ASM_REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN STRIP_TAC THEN ASM_MESON_TAC [])

  let CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← SET_RULE (← q r"(s:A->bool) UNION {a} = a INSERT s")
    prove
      r"!(k:A ring) z sigma tau.
          field k /\ z IN ring_carrier k /\ subfield_generated k {z} = k /\
          sigma IN
          group_carrier(galois_group (subfield_generated k {ring_0 k},k) I) /\
          tau IN
          group_carrier(galois_group (subfield_generated k {ring_0 k},k) I) /\
          sigma z = tau z
          ==> sigma = tau"
      (REPEAT STRIP_TAC THEN MATCH_MP_TAC GALOIS_GROUP_EQ_ON_GENERATORS THEN MAP_EVERY EXISTS_TAC [(← q r"I:A->A"), (← q r"subfield_generated (k:A ring) {ring_0 k}"), (← q r"k:A ring"), (← q r"{z:A}")] THEN ASM_REWRITE_TAC [IN_SING, FORALL_UNWIND_THM2, r1, SUBFIELD_GENERATED_INSERT_PRIME_SUBFIELD])

  let CYCLOTOMIC_FIELD_GALOIS_GROUP_ISOMORPHIC ← prove
    r"!(k:A ring) z n.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k
        ==> galois_group (subfield_generated k {ring_0 k},k) I
            isomorphic_group unit_group(integer_mod_ring n)"
    (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o (MATCH_MP CYCLOTOMIC_FIELD_GALOIS_GROUP)) THEN MESON_TAC [GROUP_ISOMORPHISM_IMP_ISOMORPHIC, ISOMORPHIC_GROUP_SYM])

  let CYCLOTOMIC_FIELD_GALOIS_GROUP_ABELIAN ← prove
    r"!(k:A ring) z n.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k
        ==> abelian_group(galois_group (subfield_generated k {ring_0 k},k) I)"
    (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o (MATCH_MP CYCLOTOMIC_FIELD_GALOIS_GROUP_ISOMORPHIC)) THEN MESON_TAC [ISOMORPHIC_GROUP_ABELIANNESS, ABELIAN_UNIT_GROUP])

  -- @@RETURN BEGIN
  return { UNIT_GROUP_INTEGER_MOD_RING, GROUP_ISOMORPHISM_MODMUL_UNIT_GROUP,
           SUBFIELD_GENERATED_INSERT_PRIME_SUBFIELD, CYCLOTOMIC_FIELD_GALOIS_EXTENSION,
           CYCLOTOMIC_FIELD_GALOIS_GROUP_MODMUL, CYCLOTOMIC_FIELD_GALOIS_GROUP_HAS_SIZE,
           CYCLOTOMIC_FIELD_GALOIS_GROUP, CYCLOTOMIC_FIELD_GALOIS_GROUP_EXISTS,
           CYCLOTOMIC_FIELD_GALOIS_GROUP_ROOT, CYCLOTOMIC_FIELD_GALOIS_GROUP_EQ,
           CYCLOTOMIC_FIELD_GALOIS_GROUP_ISOMORPHIC,
           CYCLOTOMIC_FIELD_GALOIS_GROUP_ABELIAN }
  -- @@RETURN END

end HolANT.CyclotomicGalois
