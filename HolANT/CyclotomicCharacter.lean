/- ========================================================================= -/
/- ANT: The cyclotomic character                                           -/
/- ========================================================================= -/
/- File: HolANT/CyclotomicCharacter.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/cyclotomic_character.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antcyclotomiccharacterdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/matroids.ml, Library/permutations.ml, Library/ring_det.ml, Library/fieldtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/ring_groups.ml, Library/symmetric_group.ml, Library/galois.ml, Library/integer.ml, Library/isum.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/modmul_group.ml, Library/cyclotomic.ml, ANT/algmisc.ml, ANT/integral.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/norm_index.ml, ANT/discriminant.ml, ANT/dedekind_local.ml, ANT/dedekind_valuation.ml, ANT/classgroup.ml, ANT/trace_form.ml, ANT/relative_split.ml, ANT/relative_degree.ml, ANT/nf_valuation.ml, ANT/integrality.ml, ANT/dedekind_kummer.ml, Library/finite_fields.ml, ANT/cyclotomic_poly.ml, ANT/power_basis.ml, ANT/cyclotomic_field.ml, ANT/cyclotomic_galois.ml, Multivariate/misc.ml, Multivariate/metric.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.CyclotomicCharacter fills them).

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
import HolLibrary.RingGroups
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
import HolANT.CyclotomicGalois
import HolMultiLib.Misc
import HolMultiLib.Metric

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
open HolANT.CyclotomicGalois

namespace HolANT.CyclotomicCharacter

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD
   ALGEBRAICALLY_CLOSED_FIELD_PRIMITIVE_ROOT_OF_UNITY
   ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION CONG CONG_IMP_EQ
   CONTINUOUS_MAP_INTO_DISCRETE_TOPOLOGY_FIBRES COPRIME_LMOD
   CYCLOTOMIC_EXTENSION_ABELIAN CYCLOTOMIC_FIELD_DEGREE
   CYCLOTOMIC_GALOIS_GROUP_MODMUL CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM
   DE_MORGAN_THM DIVIDES_ZERO DIV_MULT EQ_TRANS EXTENSION
   FIELD_EXTENSION_INTO_SUBFIELD_GENERATED FIELD_IMP_INTEGRAL_DOMAIN
   FIELD_SUBFIELD_GENERATED FINITE_SING FORALL_IN_IMAGE FORALL_IN_INSERT
   FORALL_UNWIND_THM2 GALOIS_GROUP GALOIS_GROUP_COMPOSE GALOIS_GROUP_RESTRICTION
   GALOIS_GROUP_RING_AUTOMORPHISM GALOIS_GROUP_RING_HOMOMORPHISM
   GALOIS_IMP_NORMAL_EXTENSION GROUP_EPIMORPHISM_ALT GROUP_HOMOMORPHISM GROUP_ID
   GROUP_ISOMORPHISM GROUP_ISOMORPHISM_MODMUL_UNIT_GROUP
   GROUP_MONOMORPHISM_EPIMORPHISM GROUP_MONOMORPHISM_IMP_HOMOMORPHISM GROUP_MUL
   INTEGER_MOD_RING INT_OF_NUM_EQ INT_OF_NUM_MUL INT_OF_NUM_REM IN_ELIM_THM
   IN_GALOIS_GROUP IN_GALOIS_GROUP_SUBFIELD_GENERATED IN_IMAGE IN_INSERT IN_SING
   LEFT_IMP_EXISTS_THM MODMUL_GROUP MOD_LT MOD_LT_EQ MONO_EXISTS MULT_EQ_0
   MULT_SYM NORMAL_IMP_FIELD_EXTENSION NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC
   NUM_OF_INT_OF_NUM OPEN_IN_POINTWISE_TOPOLOGY_POINT
   PRIME_SUBFIELD_SUBFIELD_GENERATED RING_ENDOMORPHISM_ROOT_OF_UNITY
   RING_HOMOMORPHISM_IN_CARRIER RING_HOMOMORPHISM_POW
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_OF_INTEGERS_ALGEBRAIC RING_ORDER_POW
   RING_ORDER_SUBFIELD_GENERATED RING_POW RING_POW_1 RING_POW_EQ_GEN
   RING_POW_MOD_ORDER RING_POW_ONE RING_POW_POW RING_POW_RING_ORDER
   RING_POW_SUBFIELD_GENERATED ROOTS_OF_UNITY_RING_ORDER
   ROOT_OF_UNITY_IN_RING_OF_INTEGERS SING_SUBSET SUBFIELD_GENERATED
   SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED SUBFIELD_GENERATED_IDEMPOT_GEN
   SUBFIELD_GENERATED_INC_GEN SUBFIELD_GENERATED_INSERT_PRIME_SUBFIELD
   SUBFIELD_SUBFIELD_GENERATED SUBSET SUBSET_ANTISYM TOPSPACE_POINTWISE_TOPOLOGY
   UNIT_GROUP UNIT_GROUP_INTEGER_MOD_RING divides field_extension
   group_epimorphism group_homomorphism group_image group_kernel
   group_monomorphism o_THM ring_automorphism ring_endomorphism ring_isomorphism
   ring_isomorphisms : thm)
  deriving Inhabited

/-- What cyclotomic_character.ml uses from Session besides theorems. -/
structure CyclotomicCharacterDeps where
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
  MOD_DOWN_CONV : ioconv
  SELECT_CONV : ioconv
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
/- cyclotomic_character.ml phrases from line 64 to 623                    -/
/- ---------------------------------------------------------------------- -/

structure CyclotomicCharacter where
  -- @@FIELDS
  cyclotomic_character : thm
  CYCLOTOMIC_CHARACTER : thm
  CYCLOTOMIC_CHARACTER_UNIQUE : thm
  CYCLOTOMIC_CHARACTER_DIVIDES : thm
  CYCLOTOMIC_CHARACTER_HOMOMORPHISM : thm
  CYCLOTOMIC_CHARACTER_KERNEL : thm
  CYCLOTOMIC_CHARACTER_CONTINUOUS : thm
  CYCLOTOMIC_CHARACTER_EPIMORPHISM_EQ : thm
  CYCLOTOMIC_CHARACTER_EPIMORPHISM : thm
  ALGEBRAIC_CLOSURE_CYCLOTOMIC_CHARACTER : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupCyclotomicCharacter [HolBase] (D : CyclotomicCharacterDeps) :
    ExceptT String IO CyclotomicCharacter := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, MOD_DOWN_CONV, NUMBER_RULE, SELECT_CONV, SET_TAC,
        TAUT, new_definition, .. } := D
  let { ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD,
        ALGEBRAICALLY_CLOSED_FIELD_PRIMITIVE_ROOT_OF_UNITY,
        ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION, CONG, CONG_IMP_EQ,
        CONTINUOUS_MAP_INTO_DISCRETE_TOPOLOGY_FIBRES, COPRIME_LMOD,
        CYCLOTOMIC_EXTENSION_ABELIAN, CYCLOTOMIC_FIELD_DEGREE,
        CYCLOTOMIC_GALOIS_GROUP_MODMUL, CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM,
        DE_MORGAN_THM, DIVIDES_ZERO, DIV_MULT, EQ_TRANS, EXTENSION,
        FIELD_EXTENSION_INTO_SUBFIELD_GENERATED, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_SUBFIELD_GENERATED, FINITE_SING, FORALL_IN_IMAGE, FORALL_IN_INSERT,
        FORALL_UNWIND_THM2, GALOIS_GROUP, GALOIS_GROUP_COMPOSE,
        GALOIS_GROUP_RESTRICTION, GALOIS_GROUP_RING_AUTOMORPHISM,
        GALOIS_GROUP_RING_HOMOMORPHISM, GALOIS_IMP_NORMAL_EXTENSION,
        GROUP_EPIMORPHISM_ALT, GROUP_HOMOMORPHISM, GROUP_ID, GROUP_ISOMORPHISM,
        GROUP_ISOMORPHISM_MODMUL_UNIT_GROUP, GROUP_MONOMORPHISM_EPIMORPHISM,
        GROUP_MONOMORPHISM_IMP_HOMOMORPHISM, GROUP_MUL, INTEGER_MOD_RING,
        INT_OF_NUM_EQ, INT_OF_NUM_MUL, INT_OF_NUM_REM, IN_ELIM_THM, IN_GALOIS_GROUP,
        IN_GALOIS_GROUP_SUBFIELD_GENERATED, IN_IMAGE, IN_INSERT, IN_SING,
        LEFT_IMP_EXISTS_THM, MODMUL_GROUP, MOD_LT, MOD_LT_EQ, MONO_EXISTS, MULT_EQ_0,
        MULT_SYM, NORMAL_IMP_FIELD_EXTENSION,
        NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC, NUM_OF_INT_OF_NUM,
        OPEN_IN_POINTWISE_TOPOLOGY_POINT, PRIME_SUBFIELD_SUBFIELD_GENERATED,
        RING_ENDOMORPHISM_ROOT_OF_UNITY, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_POW, RING_MONOMORPHISM_IMP_HOMOMORPHISM,
        RING_OF_INTEGERS_ALGEBRAIC, RING_ORDER_POW, RING_ORDER_SUBFIELD_GENERATED,
        RING_POW, RING_POW_1, RING_POW_EQ_GEN, RING_POW_MOD_ORDER, RING_POW_ONE,
        RING_POW_POW, RING_POW_RING_ORDER, RING_POW_SUBFIELD_GENERATED,
        ROOTS_OF_UNITY_RING_ORDER, ROOT_OF_UNITY_IN_RING_OF_INTEGERS, SING_SUBSET,
        SUBFIELD_GENERATED, SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED,
        SUBFIELD_GENERATED_IDEMPOT_GEN, SUBFIELD_GENERATED_INC_GEN,
        SUBFIELD_GENERATED_INSERT_PRIME_SUBFIELD, SUBFIELD_SUBFIELD_GENERATED, SUBSET,
        SUBSET_ANTISYM, TOPSPACE_POINTWISE_TOPOLOGY, UNIT_GROUP,
        UNIT_GROUP_INTEGER_MOD_RING, divides, field_extension, group_epimorphism,
        group_homomorphism, group_image, group_kernel, group_monomorphism, o_THM,
        ring_automorphism, ring_endomorphism, ring_isomorphism, ring_isomorphisms, .. } := D.core1
  -- @@SCOPE END

  let cyclotomic_character ← new_definition
    r"cyclotomic_character (k:A ring) n (f:A->A) =
        @c. c IN group_carrier(unit_group(integer_mod_ring n)) /\
            !x. x IN ring_carrier k /\ ring_pow k x n = ring_1 k
                ==> f x = ring_pow k x (num_of_int c)"

  let CYCLOTOMIC_CHARACTER ← prove
    r"!(k:A ring) n z f.
        integral_domain k /\ z IN ring_carrier k /\ ring_order k z = n /\
        ~(n = 0) /\ ring_automorphism k f
        ==> cyclotomic_character k n f IN
            group_carrier(unit_group(integer_mod_ring n)) /\
            !x. x IN ring_carrier k /\ ring_pow k x n = ring_1 k
                ==> f x = ring_pow k x
                  (num_of_int(cyclotomic_character k n f))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [cyclotomic_character] THEN CONV_TAC SELECT_CONV THEN FIRST_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [ring_automorphism])) THEN REWRITE_TAC [ring_isomorphism, ring_isomorphisms, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"g:A->A") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"f:A->A"), (← q r"z:A")] RING_ENDOMORPHISM_ROOT_OF_UNITY) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"g:A->A"), (← q r"z:A")] RING_ENDOMORPHISM_ROOT_OF_UNITY) THEN ASM_REWRITE_TAC [ring_endomorphism] THEN DISCH_THEN (X_CHOOSE_TAC (← q r"i:num")) THEN DISCH_THEN (X_CHOOSE_TAC (← q r"j:num")) THEN SUBGOAL_THEN (← q r"coprime(j:num,n)") ASSUME_TAC THENL [SUBGOAL_THEN (← q r"ring_pow k (z:A) (j * i) = ring_pow k z 1") MP_TAC THENL [ASM_SIMP_TAC [RING_POW_1, (← GSYM RING_POW_POW)] THEN UNDISCH_TAC (← q r"(f:A->A) z = ring_pow k z j") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [(← GSYM (← MATCH_MP RING_HOMOMORPHISM_POW (← ASSUME (← q r"ring_homomorphism(k,k) (f:A->A)"))))] THEN UNDISCH_TAC (← q r"(g:A->A) z = ring_pow k z i") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [], ASM_SIMP_TAC [RING_POW_EQ_GEN] THEN CONV_TAC NUMBER_RULE], ALL_TAC] THEN EXISTS_TAC (← q r"&(j MOD n):int") THEN CONJ_TAC THENL [ASM_SIMP_TAC [UNIT_GROUP_INTEGER_MOD_RING] THEN REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN EXISTS_TAC (← q r"j MOD n") THEN ASM_SIMP_TAC [MOD_LT_EQ, COPRIME_LMOD], ALL_TAC] THEN REWRITE_TAC [NUM_OF_INT_OF_NUM] THEN X_GEN_TAC (← q r"x:A") THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A"), (← q r"n:num")] ROOTS_OF_UNITY_RING_ORDER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"x:A")) o ((GEN_REWRITE_RULE id [EXTENSION]) o CONJUNCT1))) THEN ASM_REWRITE_TAC [IN_ELIM_THM, IN_IMAGE] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:num") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_POW (← ASSUME (← q r"ring_homomorphism(k,k) (f:A->A)")))] THEN ASM_SIMP_TAC [RING_POW_POW, RING_POW_EQ_GEN] THEN REWRITE_TAC [CONG] THEN CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC [MULT_SYM])

  let CYCLOTOMIC_CHARACTER_UNIQUE ← prove
    r"!(k:A ring) n z f c.
        integral_domain k /\ z IN ring_carrier k /\ ring_order k z = n /\
        ~(n = 0) /\ ring_automorphism k f /\
        c IN group_carrier(unit_group(integer_mod_ring n))
        ==> (cyclotomic_character k n f = c <=>
             f z = ring_pow k z (num_of_int c))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"z:A"), (← q r"f:A->A")] CYCLOTOMIC_CHARACTER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o (SPEC (← q r"z:A")))) THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A")] RING_POW_RING_ORDER) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN EQ_TAC THENL [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [], ALL_TAC] THEN ASM_SIMP_TAC [RING_POW_EQ_GEN] THEN MAP_EVERY UNDISCH_TAC [(← q r"c IN group_carrier(unit_group(integer_mod_ring n))"), (← q r"cyclotomic_character (k:A ring) n f IN
     group_carrier(unit_group(integer_mod_ring n))")] THEN ASM_SIMP_TAC [UNIT_GROUP_INTEGER_MOD_RING, IN_IMAGE, IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:num") STRIP_ASSUME_TAC) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"b:num") STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [NUM_OF_INT_OF_NUM, INT_OF_NUM_EQ] THEN REWRITE_TAC [CONG] THEN ASM_SIMP_TAC [MOD_LT])

  let CYCLOTOMIC_CHARACTER_DIVIDES ← prove
    r"!(k:A ring) m n z f.
        integral_domain k /\ z IN ring_carrier k /\ ring_order k z = n /\
        ~(n = 0) /\ m divides n /\ ring_automorphism k f
        ==> cyclotomic_character k m f = cyclotomic_character k n f rem &m"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"~(m = 0)") ASSUME_TAC THENL [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC (← q r"0 divides (n:num)") THEN ASM_REWRITE_TAC [DIVIDES_ZERO], ALL_TAC] THEN SUBGOAL_THEN (← q r"~(n DIV m = 0) /\ n DIV m divides n /\ n DIV (n DIV m) = m") STRIP_ASSUME_TAC THENL [FIRST_X_ASSUM ((X_CHOOSE_THEN (← q r"q:num") SUBST_ALL_TAC) o ((GEN_REWRITE_RULE id [divides]) o (checkM (fun th => (do let z3 ← (q r"(m:num) divides n"); let z2 ← (do let z1 ← (pure th); pure (concl z1)); pure (z2 == z3)))))) THEN RULE_ASSUM_TAC (REWRITE_RULE [MULT_EQ_0, DE_MORGAN_THM]) THEN ASM_SIMP_TAC [DIV_MULT] THEN CONJ_TAC THENL [CONV_TAC NUMBER_RULE, ALL_TAC] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_SIMP_TAC [DIV_MULT], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow k (ring_pow k (z:A) (n DIV m)) n = ring_1 k") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"z:A")] RING_POW_RING_ORDER) THEN ASM_SIMP_TAC [RING_POW_POW] THEN DISCH_TAC THEN ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_SIMP_TAC [(← GSYM RING_POW_POW), RING_POW_ONE], ALL_TAC] THEN ABBREV_TAC (← q r"w = ring_pow k (z:A) (n DIV m)") THEN SUBGOAL_THEN (← q r"(w:A) IN ring_carrier k /\ ring_order k w = m") STRIP_ASSUME_TAC THENL [EXPAND_TAC "w" THEN ASM_SIMP_TAC [RING_POW, RING_ORDER_POW], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"z:A"), (← q r"f:A->A")] CYCLOTOMIC_CHARACTER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (MP_TAC o (SPEC (← q r"w:A")))) THEN ASM_REWRITE_TAC [] THEN SPEC_TAC ((← q r"cyclotomic_character (k:A ring) n f"), (← q r"c:int")) THEN X_GEN_TAC (← q r"c:int") THEN DISCH_TAC THEN ASM_SIMP_TAC [UNIT_GROUP_INTEGER_MOD_RING, IN_IMAGE, IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:num") (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN RULE_ASSUM_TAC (REWRITE_RULE [NUM_OF_INT_OF_NUM]) THEN REWRITE_TAC [INT_OF_NUM_REM] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"m:num"), (← q r"w:A"), (← q r"f:A->A"), (← q r"&(a MOD m):int")] CYCLOTOMIC_CHARACTER_UNIQUE) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_SIMP_TAC [UNIT_GROUP_INTEGER_MOD_RING, IN_IMAGE, IN_ELIM_THM] THEN EXISTS_TAC (← q r"a MOD m") THEN ASM_SIMP_TAC [MOD_LT_EQ] THEN REWRITE_TAC [COPRIME_LMOD] THEN UNDISCH_TAC (← q r"coprime(a:num,n)") THEN UNDISCH_TAC (← q r"(m:num) divides n") THEN CONV_TAC NUMBER_RULE, DISCH_THEN SUBST1_TAC] THEN ASM_REWRITE_TAC [NUM_OF_INT_OF_NUM] THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"w:A"), (← q r"a:num")] RING_POW_MOD_ORDER) THEN ASM_SIMP_TAC [])

  let CYCLOTOMIC_CHARACTER_HOMOMORPHISM ← prove
    r"!(h:A->B) k l n z.
        integral_domain l /\ z IN ring_carrier l /\ ring_order l z = n /\
        ~(n = 0)
        ==> group_homomorphism
             (galois_group(k,l) h,unit_group(integer_mod_ring n))
             (cyclotomic_character l n)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [GROUP_HOMOMORPHISM] THEN REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"n:num"), (← q r"z:B"), (← q r"f:B->B")] CYCLOTOMIC_CHARACTER) THEN ASM_MESON_TAC [GALOIS_GROUP_RING_AUTOMORPHISM], ALL_TAC] THEN MAP_EVERY X_GEN_TAC [(← q r"f:B->B"), (← q r"g:B->B")] THEN STRIP_TAC THEN REWRITE_TAC [GALOIS_GROUP, UNIT_GROUP] THEN SUBGOAL_THEN (← q r"ring_automorphism l (f:B->B) /\ ring_automorphism l (g:B->B) /\
    ring_automorphism l (f o g) /\ ring_homomorphism(l,l) f") STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_RING_AUTOMORPHISM, GALOIS_GROUP_COMPOSE, GALOIS_GROUP_RING_HOMOMORPHISM], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"z:B")] RING_POW_RING_ORDER) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"n:num"), (← q r"z:B"), (← q r"f:B->B")] CYCLOTOMIC_CHARACTER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o (SPEC (← q r"z:B")))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"n:num"), (← q r"z:B"), (← q r"g:B->B")] CYCLOTOMIC_CHARACTER) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o (SPEC (← q r"z:B")))) THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"n:num"), (← q r"z:B"), (← q r"(f:B->B) o (g:B->B)"), (← q r"ring_mul (integer_mod_ring n)
                   (cyclotomic_character (l:B ring) n (f:B->B))
                   (cyclotomic_character (l:B ring) n (g:B->B))")] CYCLOTOMIC_CHARACTER_UNIQUE) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN MP_TAC (← ISPECL [(← q r"unit_group(integer_mod_ring n)"), (← q r"cyclotomic_character (l:B ring) n f"), (← q r"cyclotomic_character (l:B ring) n g")] GROUP_MUL) THEN ASM_REWRITE_TAC [(← CONJUNCT2 (← CONJUNCT2 (← CONJUNCT2 UNIT_GROUP)))], DISCH_THEN SUBST1_TAC] THEN MAP_EVERY UNDISCH_TAC [(← q r"(f:B->B) z = ring_pow l z (num_of_int(cyclotomic_character l n f))"), (← q r"(g:B->B) z = ring_pow l z (num_of_int(cyclotomic_character l n g))"), (← q r"cyclotomic_character (l:B ring) n f IN
     group_carrier(unit_group(integer_mod_ring n))"), (← q r"cyclotomic_character (l:B ring) n g IN
     group_carrier(unit_group(integer_mod_ring n))")] THEN SPEC_TAC ((← q r"cyclotomic_character (l:B ring) n (f:B->B)"), (← q r"c:int")) THEN SPEC_TAC ((← q r"cyclotomic_character (l:B ring) n (g:B->B)"), (← q r"d:int")) THEN ASM_SIMP_TAC [UNIT_GROUP_INTEGER_MOD_RING, IN_IMAGE, IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [(← q r"d:int"), (← q r"c:int")] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"b:num") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:num") (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN REWRITE_TAC [NUM_OF_INT_OF_NUM, INTEGER_MOD_RING, INT_OF_NUM_MUL, INT_OF_NUM_REM] THEN DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC [o_THM] THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [(← MATCH_MP RING_HOMOMORPHISM_POW (← ASSUME (← q r"ring_homomorphism(l,l) (f:B->B)")))] THEN ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [RING_POW_POW, RING_POW_EQ_GEN] THEN REWRITE_TAC [CONG] THEN CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC [])

  let CYCLOTOMIC_CHARACTER_KERNEL ← do
    -- the rules of the tactics, in OCaml's order (right to left)
    let r1 ← TAUT (← q r"(p /\ q ==> (r <=> s)) ==> ((p /\ q /\ t) /\ r <=> p /\ q /\ s /\ t)")
    prove
      r"!(h:A->B) k l n z.
          field l /\ z IN ring_carrier l /\ ring_order l z = n /\ ~(n = 0)
          ==> group_kernel
               (galois_group(k,l) h,unit_group(integer_mod_ring n))
               (cyclotomic_character l n) =
              group_carrier
               (galois_group
                 (subfield_generated l (z INSERT IMAGE h (ring_carrier k)),l)
                 I)"
      (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"f:B->B") THEN ASM_SIMP_TAC [IN_GALOIS_GROUP_SUBFIELD_GENERATED] THEN REWRITE_TAC [group_kernel, IN_ELIM_THM, UNIT_GROUP, FORALL_IN_INSERT, FORALL_IN_IMAGE, IN_GALOIS_GROUP] THEN MATCH_MP_TAC r1 THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"n:num"), (← q r"z:B"), (← q r"f:B->B"), (← q r"ring_1(integer_mod_ring n)")] CYCLOTOMIC_CHARACTER_UNIQUE) THEN ANTS_TAC THENL [ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN MP_TAC (← ISPEC (← q r"unit_group(integer_mod_ring n)") GROUP_ID) THEN REWRITE_TAC [(← CONJUNCT1 (← CONJUNCT2 UNIT_GROUP))], DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC [INTEGER_MOD_RING, INT_OF_NUM_REM, NUM_OF_INT_OF_NUM] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"z:B"), (← q r"1:num")] RING_POW_MOD_ORDER) THEN ASM_SIMP_TAC [RING_POW_1])

  let CYCLOTOMIC_CHARACTER_CONTINUOUS ← prove
    r"!(h:A->B) k l n z.
        integral_domain l /\ z IN ring_carrier l /\ ring_order l z = n /\
        ~(n = 0)
        ==> continuous_map
             (pointwise_topology(group_carrier(galois_group(k,l) h)),
              discrete_topology(group_carrier(unit_group(integer_mod_ring n))))
             (cyclotomic_character l n)"
    (REPEAT STRIP_TAC THEN REWRITE_TAC [CONTINUOUS_MAP_INTO_DISCRETE_TOPOLOGY_FIBRES] THEN REWRITE_TAC [TOPSPACE_POINTWISE_TOPOLOGY] THEN CONJ_TAC THENL [X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"n:num"), (← q r"z:B"), (← q r"f:B->B")] CYCLOTOMIC_CHARACTER) THEN ASM_MESON_TAC [GALOIS_GROUP_RING_AUTOMORPHISM], ALL_TAC] THEN X_GEN_TAC (← q r"c:int") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"{f | f IN group_carrier(galois_group(k,l) (h:A->B)) /\
         cyclotomic_character l n f = c} =
    {f | f IN group_carrier(galois_group(k,l) h) /\
         f z = ring_pow l z (num_of_int c)}") SUBST1_TAC THENL [GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC (← q r"f:B->B") THEN REWRITE_TAC [IN_ELIM_THM] THEN ASM_CASES_TAC (← q r"(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))") THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC CYCLOTOMIC_CHARACTER_UNIQUE THEN ASM_MESON_TAC [GALOIS_GROUP_RING_AUTOMORPHISM], REWRITE_TAC [OPEN_IN_POINTWISE_TOPOLOGY_POINT]])

  let CYCLOTOMIC_CHARACTER_EPIMORPHISM_EQ ← prove
    r"!(h:A->B) k l n z.
        normal_extension(k,l) h /\ z IN ring_carrier l /\
        ring_order l z = n /\ ~(n = 0)
        ==> (group_epimorphism
              (galois_group(k,l) h,unit_group(integer_mod_ring n))
              (cyclotomic_character l n) <=>
             extension_degree
              (k,subfield_generated l (z INSERT IMAGE h (ring_carrier k))) h =
             phi n)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NORMAL_IMP_FIELD_EXTENSION)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (GEN_REWRITE_RULE id [field_extension])) THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN SUBGOAL_THEN (← q r"(z INSERT IMAGE (h:A->B) (ring_carrier k)) SUBSET
    ring_carrier(subfield_generated l (z INSERT IMAGE h (ring_carrier k)))") ASSUME_TAC THENL [REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"x:B") THEN DISCH_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC (← q r"(x:B) IN z INSERT IMAGE (h:A->B) (ring_carrier k)") THEN REWRITE_TAC [IN_INSERT, IN_IMAGE] THEN STRIP_TAC THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN SUBGOAL_THEN (← q r"field_extension
     (k,subfield_generated l (z INSERT IMAGE h (ring_carrier k))) (h:A->B)") ASSUME_TAC THENL [MATCH_MP_TAC FIELD_EXTENSION_INTO_SUBFIELD_GENERATED THEN ASM_REWRITE_TAC [] THEN SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_order (subfield_generated l (z INSERT IMAGE h (ring_carrier k))) z =
    n /\
    subfield_generated
     (subfield_generated l (z INSERT IMAGE h (ring_carrier k)))
     (z INSERT IMAGE (h:A->B) (ring_carrier k)) =
    subfield_generated l (z INSERT IMAGE h (ring_carrier k)) /\
    field(subfield_generated l (z INSERT IMAGE h (ring_carrier k))) /\
    ring_pow (subfield_generated l (z INSERT IMAGE h (ring_carrier k))) =
    ring_pow l /\
    ring_carrier(subfield_generated l (z INSERT IMAGE h (ring_carrier k)))
    subfield_of l /\
    subfield_generated l
     (ring_carrier(subfield_generated l (z INSERT IMAGE h (ring_carrier k)))) =
    subfield_generated l (z INSERT IMAGE h (ring_carrier k))") STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_SUBFIELD_GENERATED, RING_POW_SUBFIELD_GENERATED, SUBFIELD_SUBFIELD_GENERATED, SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN CONJ_TAC THENL [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"ring_order l (z:B)") THEN CONJ_TAC THENL [ALL_TAC, ASM_REWRITE_TAC []] THEN MATCH_MP_TAC RING_ORDER_SUBFIELD_GENERATED THEN ASM SET_TAC [], MATCH_MP_TAC SUBFIELD_GENERATED_IDEMPOT_GEN THEN ASM_REWRITE_TAC []], ALL_TAC] THEN ABBREV_TAC (← q r"m = subfield_generated l (z INSERT IMAGE (h:A->B) (ring_carrier k))") THEN SUBGOAL_THEN (← q r"(z:B) IN ring_carrier m") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"IMAGE (h:A->B) (ring_carrier k) SUBSET ring_carrier m") ASSUME_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"ring_pow m (z:B) n = ring_1 m") ASSUME_TAC THENL [ASM_REWRITE_TAC [] THEN EXPAND_TAC "m" THEN REWRITE_TAC [(← CONJUNCT2 SUBFIELD_GENERATED)] THEN UNDISCH_TAC (← q r"ring_order l (z:B) = n") THEN DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [RING_POW_RING_ORDER], ALL_TAC] THEN SUBGOAL_THEN (← q r"group_epimorphism (galois_group(k,l) h,galois_group(k,m) (h:A->B))
     (\f x. if x IN ring_carrier m then f x else x)") ASSUME_TAC THENL [MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"l:B ring"), (← q r"ring_carrier m:B->bool")] GALOIS_GROUP_RESTRICTION) THEN ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN MATCH_MP_TAC GALOIS_IMP_NORMAL_EXTENSION THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"m:B ring"), (← q r"z:B"), (← q r"n:num")] CYCLOTOMIC_EXTENSION_ABELIAN) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!f. f IN group_carrier(galois_group(k,l) h)
        ==> (\x. if x IN ring_carrier m then f x else x) IN
            group_carrier(galois_group(k,m) (h:A->B)) /\
            (\x. if x IN ring_carrier m then f x else x) z = f z") ASSUME_TAC THENL [ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MP_TAC o (CONJUNCT1 o (CONJUNCT1 o ((REWRITE_RULE [group_epimorphism, group_homomorphism, SUBSET, FORALL_IN_IMAGE]) o (checkM (fun th => (do let z75 ← (do let z76 ← (pure th); pure (concl z76)); let z74 ← (pure "group_epimorphism"); pure (is_binary z74 z75)))))))) THEN SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"!a b. a IN group_carrier(modmul_group n) /\
          b IN group_carrier(modmul_group n) /\ (a == b) (mod n)
          ==> a = b") (LABEL_TAC "res") THENL [REWRITE_TAC [MODMUL_GROUP] THEN COND_CASES_TAC THEN REWRITE_TAC [IN_SING, IN_ELIM_THM] THEN MESON_TAC [CONG_IMP_EQ], ALL_TAC] THEN MP_TAC (← ISPEC (← q r"n:num") GROUP_ISOMORPHISM_MODMUL_UNIT_GROUP) THEN ASM_REWRITE_TAC [GROUP_ISOMORPHISM] THEN STRIP_TAC THEN SUBGOAL_THEN (← q r"!a. ring_pow l (z:B) (num_of_int(&a rem &n)) = ring_pow l z a") ASSUME_TAC THENL [REWRITE_TAC [INT_OF_NUM_REM, NUM_OF_INT_OF_NUM] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"z:B")] RING_POW_MOD_ORDER) THEN ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"integral_domain(l:B ring)") ASSUME_TAC THENL [ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"m:B ring"), (← q r"z:B"), (← q r"n:num")] CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN EQ_TAC THENL [DISCH_TAC THEN MP_TAC (← ISPECL [(← q r"h:A->B"), (← q r"k:A ring"), (← q r"m:B ring"), (← q r"z:B"), (← q r"n:num")] CYCLOTOMIC_GALOIS_GROUP_MODMUL) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"e:(B->B)->num") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [(← GSYM GROUP_MONOMORPHISM_EPIMORPHISM)] THEN ASM_REWRITE_TAC [group_epimorphism] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP GROUP_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [FIRST_X_ASSUM (ACCEPT_TAC o (CONJUNCT1 o (GEN_REWRITE_RULE id [group_homomorphism]))), ALL_TAC] THEN REWRITE_TAC [SUBSET, IN_IMAGE] THEN X_GEN_TAC (← q r"b:num") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"&b rem &n IN group_carrier(unit_group(integer_mod_ring n))") ASSUME_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z68 ← (do let z69 ← (pure th); pure (concl z69)); pure (is_eq z68)) then (do let z73 ← (q r"group_carrier(unit_group(integer_mod_ring n))"); let z72 ← (do let z70 ← (do let z71 ← (pure th); pure (concl z71)); liftExcept (rhs z70)); pure (z72 == z73)) else pure false))))) THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC (← q r"b:num") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN UNDISCH_TAC (← q r"group_epimorphism
       (galois_group(k,l) (h:A->B),unit_group(integer_mod_ring n))
       (cyclotomic_character l n)") THEN REWRITE_TAC [group_epimorphism, EXTENSION, IN_IMAGE] THEN DISCH_THEN (fun z67 => tactic_of do pure (MP_TAC (← (do pure (Prod.snd (← (do pure (← EQ_IMP_RULE (← SPEC (← q r"&b rem &n:int") (← CONJUNCT2 z67)))))))))) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"f:B->B") (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN SUBGOAL_THEN (← q r"(f:B->B) z = ring_pow l z b") ASSUME_TAC THENL [FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP GALOIS_GROUP_RING_AUTOMORPHISM) o (checkM (fun th => (do let z66 ← (q r"(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))"); let z65 ← (do let z64 ← (pure th); pure (concl z64)); pure (z65 == z66)))))) THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"n:num"), (← q r"z:B"), (← q r"f:B->B"), (← q r"&b rem &n:int")] CYCLOTOMIC_CHARACTER_UNIQUE) THEN ASM_SIMP_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"f:B->B")) o (checkM (fun th => (do if ← (do if ← (do let z52 ← (do let z53 ← (pure th); pure (concl z53)); pure (is_forall z52)) then (do let z54 ← (do let z55 ← (pure th); pure (concl z55)); canM (fun z56 => (do let z57 ← (pure z56); find_termM (fun z58 => (do let z60 ← (pure z58); let z59 ← (q r"ring_carrier(m:B ring)"); pure (z59 == z60))) z57)) z54) else pure false) then (do let z61 ← (do pure (Prod.snd (← (do let z62 ← (do let z63 ← (pure th); pure (concl z63)); liftExcept (dest_forall z62))))); pure (is_imp z61)) else pure false))))) THEN ASM_REWRITE_TAC [] THEN ABBREV_TAC (← q r"g = \x. if x IN ring_carrier m then (f:B->B) x else x") THEN STRIP_TAC THEN EXISTS_TAC (← q r"g:B->B") THEN ASM_REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN USE_THEN "res" MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [UNDISCH_TAC (← q r"group_monomorphism (galois_group(k,m) (h:A->B),
                                       modmul_group n) e") THEN REWRITE_TAC [group_monomorphism, group_homomorphism, SUBSET, FORALL_IN_IMAGE] THEN ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"z:B")] RING_POW_EQ_GEN) THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [(← GSYM th)])) THEN SUBGOAL_THEN (← q r"(g:B->B) z = ring_pow l z (e g)") (SUBST1_TAC o SYM) THENL [FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"g:B->B")) o (checkM (fun th => (do if ← (do if ← (do let z40 ← (do let z41 ← (pure th); pure (concl z41)); pure (is_forall z40)) then (do let z42 ← (do let z43 ← (pure th); pure (concl z43)); canM (fun z44 => (do let z45 ← (pure z44); find_termM (fun z46 => (do let z48 ← (pure z46); let z47 ← (q r"e:(B->B)->num"); pure (z47 == z48))) z45)) z42) else pure false) then (do let z49 ← (do pure (Prod.snd (← (do let z50 ← (do let z51 ← (pure th); pure (concl z51)); liftExcept (dest_forall z50))))); pure (is_imp z49)) else pure false))))) THEN ASM_REWRITE_TAC [], EXPAND_TAC "g" THEN REWRITE_TAC [] THEN ASM_REWRITE_TAC []], ALL_TAC] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"e:(B->B)->num") (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN REWRITE_TAC [GROUP_ISOMORPHISM] THEN STRIP_TAC THEN REWRITE_TAC [GROUP_EPIMORPHISM_ALT] THEN CONJ_TAC THENL [MATCH_MP_TAC CYCLOTOMIC_CHARACTER_HOMOMORPHISM THEN EXISTS_TAC (← q r"z:B") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN REWRITE_TAC [group_image, SUBSET, IN_IMAGE] THEN X_GEN_TAC (← q r"c:int") THEN DISCH_TAC THEN SUBGOAL_THEN (← q r"?b. b IN group_carrier(modmul_group n) /\ &b rem &n = c") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"c IN group_carrier(unit_group(integer_mod_ring n))") THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z34 ← (do let z35 ← (pure th); pure (concl z35)); pure (is_eq z34)) then (do let z39 ← (q r"group_carrier(unit_group(integer_mod_ring n))"); let z38 ← (do let z36 ← (do let z37 ← (pure th); pure (concl z37)); liftExcept (rhs z36)); pure (z38 == z39)) else pure false))))) THEN REWRITE_TAC [IN_IMAGE] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"?g. g IN group_carrier(galois_group(k,m) (h:A->B)) /\
        (e:(B->B)->num) g = b") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"b IN group_carrier(modmul_group n)") THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z28 ← (do let z29 ← (pure th); pure (concl z29)); pure (is_eq z28)) then (do let z33 ← (q r"group_carrier(modmul_group n)"); let z32 ← (do let z30 ← (do let z31 ← (pure th); pure (concl z31)); liftExcept (rhs z30)); pure (z32 == z33)) else pure false))))) THEN REWRITE_TAC [IN_IMAGE] THEN MESON_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"?f. f IN group_carrier(galois_group(k,l) (h:A->B)) /\
        (\x. if x IN ring_carrier m then f x else x) = g") STRIP_ASSUME_TAC THENL [UNDISCH_TAC (← q r"group_epimorphism (galois_group(k,l) h,galois_group(k,m) (h:A->B))
       (\f x. if x IN ring_carrier m then f x else x)") THEN REWRITE_TAC [group_epimorphism, EXTENSION, IN_IMAGE] THEN DISCH_THEN (MP_TAC o ((SPEC (← q r"g:B->B")) o CONJUNCT2)) THEN ASM_REWRITE_TAC [] THEN MESON_TAC [], ALL_TAC] THEN EXISTS_TAC (← q r"f:B->B") THEN ASM_REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP GALOIS_GROUP_RING_AUTOMORPHISM) o (checkM (fun th => (do let z27 ← (q r"(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))"); let z26 ← (do let z25 ← (pure th); pure (concl z25)); pure (z26 == z27)))))) THEN MP_TAC (← ISPECL [(← q r"l:B ring"), (← q r"n:num"), (← q r"z:B"), (← q r"f:B->B"), (← q r"c:int")] CYCLOTOMIC_CHARACTER_UNIQUE) THEN ASM_SIMP_TAC [] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"(f:B->B) z = g z") SUBST1_TAC THENL [FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z19 ← (do let z20 ← (pure th); pure (concl z20)); pure (is_eq z19)) then (do let z24 ← (q r"g:B->B"); let z23 ← (do let z21 ← (do let z22 ← (pure th); pure (concl z22)); liftExcept (rhs z21)); pure (z23 == z24)) else pure false))))) THEN REWRITE_TAC [] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN (← q r"(g:B->B) z = ring_pow l z (e g)") SUBST1_TAC THENL [FIRST_X_ASSUM (MP_TAC o ((SPEC (← q r"g:B->B")) o (checkM (fun th => (do if ← (do if ← (do let z7 ← (do let z8 ← (pure th); pure (concl z8)); pure (is_forall z7)) then (do let z9 ← (do let z10 ← (pure th); pure (concl z10)); canM (fun z11 => (do let z12 ← (pure z11); find_termM (fun z13 => (do let z15 ← (pure z13); let z14 ← (q r"e:(B->B)->num"); pure (z14 == z15))) z12)) z9) else pure false) then (do let z16 ← (do pure (Prod.snd (← (do let z17 ← (do let z18 ← (pure th); pure (concl z18)); liftExcept (dest_forall z17))))); pure (is_imp z16)) else pure false))))) THEN ASM_REWRITE_TAC [], ALL_TAC] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do if ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); pure (is_eq z1)) then (do let z6 ← (q r"c:int"); let z5 ← (do let z3 ← (do let z4 ← (pure th); pure (concl z4)); liftExcept (rhs z3)); pure (z5 == z6)) else pure false))))) THEN ASM_REWRITE_TAC [])

  let CYCLOTOMIC_CHARACTER_EPIMORPHISM ← prove
    r"!(l:A ring) n z.
        ring_char l = 0 /\
        normal_extension(subfield_generated l {ring_0 l},l) I /\
        z IN ring_carrier l /\ ring_order l z = n /\ ~(n = 0)
        ==> group_epimorphism
             (galois_group(subfield_generated l {ring_0 l},l) I,
              unit_group(integer_mod_ring n))
             (cyclotomic_character l n)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NORMAL_IMP_FIELD_EXTENSION)) THEN SUBGOAL_THEN (← q r"field(l:A ring)") ASSUME_TAC THENL [ASM_MESON_TAC [field_extension], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"I:A->A"), (← q r"subfield_generated l {ring_0 l}:A ring"), (← q r"l:A ring"), (← q r"n:num"), (← q r"z:A")] CYCLOTOMIC_CHARACTER_EPIMORPHISM_EQ) THEN ASM_REWRITE_TAC [SUBFIELD_GENERATED_INSERT_PRIME_SUBFIELD] THEN DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN (← q r"number_field(subfield_generated l {z:A})") ASSUME_TAC THENL [MATCH_MP_TAC NUMBER_FIELD_SUBFIELD_GENERATED_ALGEBRAIC THEN ASM_REWRITE_TAC [FINITE_SING, IN_SING, FORALL_UNWIND_THM2] THEN MATCH_MP_TAC RING_OF_INTEGERS_ALGEBRAIC THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC ROOT_OF_UNITY_IN_RING_OF_INTEGERS THEN EXISTS_TAC (← q r"n:num") THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [RING_POW_RING_ORDER], ALL_TAC] THEN SUBGOAL_THEN (← q r"(z:A) IN ring_carrier(subfield_generated l {z})") ASSUME_TAC THENL [MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN ASM_REWRITE_TAC [IN_SING], ALL_TAC] THEN MP_TAC (← ISPECL [(← q r"subfield_generated l {z:A}"), (← q r"z:A"), (← q r"n:num")] CYCLOTOMIC_FIELD_DEGREE) THEN ASM_SIMP_TAC [RING_ORDER_SUBFIELD_GENERATED, PRIME_SUBFIELD_SUBFIELD_GENERATED, SUBFIELD_GENERATED_IDEMPOT_GEN, SING_SUBSET])

  let ALGEBRAIC_CLOSURE_CYCLOTOMIC_CHARACTER ← prove
    r"!(k:A ring) n.
        algebraically_closed_field k /\ ring_char k = 0 /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I /\ ~(n = 0)
        ==> group_epimorphism
             (galois_group(subfield_generated k {ring_0 k},k) I,
              unit_group(integer_mod_ring n))
             (cyclotomic_character k n) /\
            continuous_map
             (pointwise_topology
               (group_carrier
                 (galois_group(subfield_generated k {ring_0 k},k) I)),
              discrete_topology(group_carrier(unit_group(integer_mod_ring n))))
             (cyclotomic_character k n) /\
            !f x. f IN group_carrier
                        (galois_group(subfield_generated k {ring_0 k},k) I) /\
                  x IN ring_carrier k /\ ring_pow k x n = ring_1 k
                  ==> f x = ring_pow k x
                    (num_of_int(cyclotomic_character k n f))"
    (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num")] ALGEBRAICALLY_CLOSED_FIELD_PRIMITIVE_ROOT_OF_UNITY) THEN ASM_REWRITE_TAC [(← ExceptT.mk (NUMBER_RULE (← q r"((0:num) divides n) <=> n = 0")))] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"z:A") STRIP_ASSUME_TAC) o CONJUNCT2) THEN SUBGOAL_THEN (← q r"field(k:A ring)") ASSUME_TAC THENL [ASM_SIMP_TAC [ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD], ALL_TAC] THEN REPEAT CONJ_TAC THENL [MATCH_MP_TAC CYCLOTOMIC_CHARACTER_EPIMORPHISM THEN EXISTS_TAC (← q r"z:A") THEN ASM_SIMP_TAC [ALGEBRAICALLY_CLOSED_IMP_NORMAL_EXTENSION], MATCH_MP_TAC CYCLOTOMIC_CHARACTER_CONTINUOUS THEN EXISTS_TAC (← q r"z:A") THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN], REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"k:A ring"), (← q r"n:num"), (← q r"z:A"), (← q r"f:A->A")] CYCLOTOMIC_CHARACTER) THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN] THEN ANTS_TAC THENL [FIRST_ASSUM (MATCH_ACCEPT_TAC o (MATCH_MP GALOIS_GROUP_RING_AUTOMORPHISM)), DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC []]])

  -- @@RETURN BEGIN
  return { cyclotomic_character, CYCLOTOMIC_CHARACTER, CYCLOTOMIC_CHARACTER_UNIQUE,
           CYCLOTOMIC_CHARACTER_DIVIDES, CYCLOTOMIC_CHARACTER_HOMOMORPHISM,
           CYCLOTOMIC_CHARACTER_KERNEL, CYCLOTOMIC_CHARACTER_CONTINUOUS,
           CYCLOTOMIC_CHARACTER_EPIMORPHISM_EQ, CYCLOTOMIC_CHARACTER_EPIMORPHISM,
           ALGEBRAIC_CLOSURE_CYCLOTOMIC_CHARACTER }
  -- @@RETURN END

end HolANT.CyclotomicCharacter
