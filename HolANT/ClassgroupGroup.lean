/- ========================================================================= -/
/- ANT: The ideal class group of a Dedekind domain as a group, in ...      -/
/- ========================================================================= -/
/- File: HolANT/ClassgroupGroup.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `ANT/classgroup_group.ml` (078839e), in file order, one Lean
  `let` per OCaml `let`.  The theorem phrases were converted by
  gxwork/ant/ml2lean.py (disclosed; the user agreed to a converter for ANT/,
  2026-11-11) and checked against the .ml (quotations and tokens) and by
  tools/antclassgroupgroupdiff; the rest is by hand.  Its `needs` closure is
  Library/binomial.ml, Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/wo.ml, Library/card.ml, Library/ringtheory.ml, Library/frag.ml, Library/grouptheory.ml, Library/permutations.ml, Library/ring_det.ml, ANT/ideal_arith.ml, Library/products.ml, ANT/algmisc.ml, Library/matroids.ml, Library/fieldtheory.ml, ANT/integral.ml, ANT/dedekind.ml, ANT/dedekind_struct.ml, Library/isum.ml, ANT/zlattice.ml, Library/floor.ml, ANT/numfield.ml, ANT/ideal_norm.ml, ANT/ring_of_integers.ml, ANT/norm_index.ml, ANT/classgroup.ml;
  the theorems it uses from them and from the core library are supplied via
  the CoreThms structures (SessionANT.ClassgroupGroup fills them).

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
import HolLibrary.Frag
import HolLibrary.GroupTheory
import HolLibrary.Permutations
import HolLibrary.RingDet
import HolANT.IdealArith
import HolLibrary.Products
import HolANT.Algmisc
import HolLibrary.Matroids
import HolLibrary.FieldTheory
import HolANT.Integral
import HolANT.Dedekind
import HolANT.DedekindStruct
import HolLibrary.Isum
import HolANT.Zlattice
import HolLibrary.Floor
import HolANT.Numfield
import HolANT.IdealNorm
import HolANT.RingOfIntegers
import HolANT.NormIndex
import HolANT.Classgroup

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
open HolANT.Zlattice
open HolANT.Numfield
open HolANT.IdealNorm
open HolANT.RingOfIntegers
open HolANT.NormIndex
open HolANT.Classgroup

namespace HolANT.ClassgroupGroup

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (AND_FORALL_THM DEDEKIND_IDEAL_CLASS_INVERSE DEDEKIND_IDEAL_COPRIME_PROD_POW
   DEDEKIND_IMP_INTEGRAL_DOMAIN DEDEKIND_PID_EQ_CLASS_NUMBER_1
   DEDEKIND_RING_OF_INTEGERS DE_MORGAN_THM EXTENSION FORALL_IN_GSPEC
   FORALL_IN_IMAGE GROUP_ELEMENT_ORDER_EQ_1 GROUP_HOMOMORPHISM GROUP_LINV_EQ
   GROUP_POW_EQ_ID GROUP_POW_GROUP_ORDER HAS_SIZE IDEALS_GENERATED_SING_EQ
   IDEAL_CLASS_EQ IDEAL_CLASS_MUL IDEAL_CLASS_PRINCIPAL IDEAL_CLASS_REFL
   IDEAL_CLASS_SYM IDEAL_CLASS_TRANS IDEAL_GENERATED_0 IDEAL_GENERATED_EQ_0
   IDEAL_GENERATED_IMAGE_IDEAL_GENERATED IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0
   IDEAL_POW_0 IDEAL_POW_EQ_ZERO IDEAL_POW_PRINCIPAL IDEAL_PROD_AC
   IDEAL_PROD_ASSOC IDEAL_PROD_CARRIER IDEAL_PROD_CARRIER_LEFT IDEAL_PROD_COMM
   IDEAL_PROD_EQ_ZERO IDEAL_PROD_HOMOMORPHIC_IMAGE IDEAL_PROD_PRINCIPAL
   IDEAL_PROD_RZERO IMAGE_CLAUSES IMP_CONJ INTEGRAL_DOMAIN_ASSOCIATES
   INTEGRAL_DOMAIN_UNIT_IDEAL IN_ELIM_THM IN_IDEAL_CLASS LEFT_IMP_EXISTS_THM
   MONO_EXISTS NUMBER_FIELD_CLASS_GROUP_FINITE PRINCIPAL_IDEAL_0
   PRINCIPAL_IDEAL_CARRIER PRINCIPAL_IDEAL_CLASS RIGHT_FORALL_IMP_THM
   RIGHT_IMP_EXISTS_THM RING_HOMOMORPHISM_IN_CARRIER RING_IDEAL_IDEAL_GENERATED
   RING_IDEAL_IDEAL_POW RING_IDEAL_IDEAL_PROD RING_IDEAL_IMP_SUBSET
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL_SYM RING_OF_INTEGERS RING_POW
   RING_UNIT_IN_CARRIER SING_SUBSET SKOLEM_THM SUBSET TRIVIAL_GROUP_HAS_SIZE_1
   abelian_group class_number coprime group_carrier group_id group_inv group_mul
   group_pow group_tybij ideal_classes ideal_pow principal_ideal : thm)
  deriving Inhabited

/-- What classgroup_group.ml uses from Session besides theorems. -/
structure ClassgroupGroupDeps where
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
/- classgroup_group.ml phrases from line 64 to 566                        -/
/- ---------------------------------------------------------------------- -/

structure ClassgroupGroup where
  -- @@FIELDS
  class_group : thm
  CLASS_GROUP : thm
  IDEAL_CLASS_IN_CLASS_GROUP : thm
  CLASS_GROUP_MUL : thm
  IDEAL_CLASS_EQ_ID : thm
  CLASS_GROUP_INV : thm
  CLASS_GROUP_POW : thm
  CLASS_GROUP_POW_EQ_ID : thm
  ABELIAN_CLASS_GROUP : thm
  TRIVIAL_CLASS_GROUP : thm
  DEDEKIND_PRINCIPAL_IDEAL_POW_CLASS_NUMBER : thm
  FINITE_CLASS_GROUP : thm
  HAS_SIZE_CLASS_GROUP : thm
  NUMBER_FIELD_PRINCIPAL_IDEAL_POW_CLASS_NUMBER : thm
  DEDEKIND_PRINCIPAL_IDEAL_POW_COPRIME : thm
  NUMBER_FIELD_PRINCIPAL_IDEAL_POW_COPRIME : thm
  DEDEKIND_COPRIME_MUL_POW : thm
  NUMBER_FIELD_COPRIME_MUL_POW : thm
  CLASS_GROUP_HOMOMORPHISM_IDEAL_MAP : thm
  DEDEKIND_CLASS_GROUP_EXTENSION : thm
  deriving Inhabited

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 16384 in
@[nospecialize]
def setupClassgroupGroup [HolBase] (D : ClassgroupGroupDeps) :
    ExceptT String IO ClassgroupGroup := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, SELECT_CONV, TAUT, new_definition, .. } := D
  let { AND_FORALL_THM, DEDEKIND_IDEAL_CLASS_INVERSE, DEDEKIND_IDEAL_COPRIME_PROD_POW,
        DEDEKIND_IMP_INTEGRAL_DOMAIN, DEDEKIND_PID_EQ_CLASS_NUMBER_1,
        DEDEKIND_RING_OF_INTEGERS, DE_MORGAN_THM, EXTENSION, FORALL_IN_GSPEC,
        FORALL_IN_IMAGE, GROUP_ELEMENT_ORDER_EQ_1, GROUP_HOMOMORPHISM, GROUP_LINV_EQ,
        GROUP_POW_EQ_ID, GROUP_POW_GROUP_ORDER, HAS_SIZE, IDEALS_GENERATED_SING_EQ,
        IDEAL_CLASS_EQ, IDEAL_CLASS_MUL, IDEAL_CLASS_PRINCIPAL, IDEAL_CLASS_REFL,
        IDEAL_CLASS_SYM, IDEAL_CLASS_TRANS, IDEAL_GENERATED_0, IDEAL_GENERATED_EQ_0,
        IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0,
        IDEAL_POW_0, IDEAL_POW_EQ_ZERO, IDEAL_POW_PRINCIPAL, IDEAL_PROD_AC,
        IDEAL_PROD_ASSOC, IDEAL_PROD_CARRIER, IDEAL_PROD_CARRIER_LEFT, IDEAL_PROD_COMM,
        IDEAL_PROD_EQ_ZERO, IDEAL_PROD_HOMOMORPHIC_IMAGE, IDEAL_PROD_PRINCIPAL,
        IDEAL_PROD_RZERO, IMAGE_CLAUSES, IMP_CONJ, INTEGRAL_DOMAIN_ASSOCIATES,
        INTEGRAL_DOMAIN_UNIT_IDEAL, IN_ELIM_THM, IN_IDEAL_CLASS, LEFT_IMP_EXISTS_THM,
        MONO_EXISTS, NUMBER_FIELD_CLASS_GROUP_FINITE, PRINCIPAL_IDEAL_0,
        PRINCIPAL_IDEAL_CARRIER, PRINCIPAL_IDEAL_CLASS, RIGHT_FORALL_IMP_THM,
        RIGHT_IMP_EXISTS_THM, RING_HOMOMORPHISM_IN_CARRIER, RING_IDEAL_IDEAL_GENERATED,
        RING_IDEAL_IDEAL_POW, RING_IDEAL_IDEAL_PROD, RING_IDEAL_IMP_SUBSET,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL_SYM, RING_OF_INTEGERS, RING_POW,
        RING_UNIT_IN_CARRIER, SING_SUBSET, SKOLEM_THM, SUBSET,
        TRIVIAL_GROUP_HAS_SIZE_1, abelian_group, class_number, coprime, group_carrier,
        group_id, group_inv, group_mul, group_pow, group_tybij, ideal_classes,
        ideal_pow, principal_ideal, .. } := D.core1
  -- @@SCOPE END

  let class_group ← new_definition
    r"class_group (r:A ring) =
    group(ideal_classes r,
          ideal_class r (ring_carrier r),
          (\c. {k | ring_ideal r k /\
                    ?j. j IN c /\
                        ring_carrier r IN ideal_class r (ideal_prod r j k)}),
          (\c d. {l | ?j k. j IN c /\ k IN d /\
                            l IN ideal_class r (ideal_prod r j k)}))"

  let CLASS_GROUP ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"ideal_prod r j k:A->bool"
    let q2 ← q r"j:A->bool"
    let q3 ← q r"l:A->bool"
    let q4 ← q r"ring_carrier r:A->bool"
    let q5 ← q r"l:A->bool"
    let q6 ← q r"ideal_prod r j k:A->bool"
    let q7 ← q r"r:A ring"
    let v8 ← ISPECL [q7, q6, q5, q4, q3] IDEAL_CLASS_MUL
    let q9 ← q r"ideal_prod r j l:A->bool"
    let q10 ← q r"k:A->bool"
    let q11 ← q r"ring_carrier r:A->bool"
    let q12 ← q r"k:A->bool"
    let q13 ← q r"r:A ring"
    let v14 ← ISPECL [q13, q12, q11, q10, q9] IDEAL_CLASS_MUL
    let q15 ← q r"ideal_prod r m l:A->bool"
    let q16 ← q r"(ideal_prod r j l:A->bool) IN ideal_class r (ring_carrier r)"
    let q17 ← q r"ideal_prod r (ideal_prod r j k) l:A->bool"
    let q18 ← q r"~(ideal_prod r m l = {ring_0 r:A})"
    let q19 ← q r"(m:A->bool) IN ideal_class r j"
    let q20 ← q r"(ring_carrier r:A->bool) IN ideal_class r (ideal_prod r m l)"
    let q21 ← q r"ring_ideal r m /\ ~(l = {ring_0 r:A})"
    let q22 ← q r"m:A->bool"
    let q23 ← q r"l:A->bool"
    let q24 ← q r"k:A->bool"
    let q25 ← q r"j:A->bool"
    let q26 ← q r"r:A ring"
    let v27 ← ISPECL [q26, q25] DEDEKIND_IDEAL_CLASS_INVERSE
    let p28 ← prove r"!r j:A->bool.
          dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r})
          ==> ?k. ring_ideal r k /\ ~(k = {ring_0 r}) /\
                  ring_carrier r IN ideal_class r (ideal_prod r j k) /\
                  {l | ring_ideal r l /\
                       ?m. m IN ideal_class r j /\
                           ring_carrier r IN ideal_class r (ideal_prod r m l)} =
                  ideal_class r k" (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN MP_TAC v27 THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC q24 THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC q23 THEN EQ_TAC THENL [DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN q22 STRIP_ASSUME_TAC)) THEN SUBGOAL_THEN q21 STRIP_ASSUME_TAC THENL [UNDISCH_TAC q20 THEN UNDISCH_TAC q19 THEN REWRITE_TAC [IN_IDEAL_CLASS] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN UNDISCH_TAC q18 THEN ASM_SIMP_TAC [IDEAL_PROD_RZERO, RING_IDEAL_IMP_SUBSET], ALL_TAC] THEN MATCH_MP_TAC IDEAL_CLASS_TRANS THEN EXISTS_TAC q17 THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [SUBGOAL_THEN q16 ASSUME_TAC THENL [MATCH_MP_TAC IDEAL_CLASS_SYM THEN MATCH_MP_TAC IDEAL_CLASS_TRANS THEN EXISTS_TAC q15 THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IDEAL_CLASS_MUL THEN ASM_SIMP_TAC [IDEAL_CLASS_REFL], ALL_TAC] THEN MP_TAC v14 THEN ASM_SIMP_TAC [IDEAL_CLASS_REFL, IDEAL_PROD_CARRIER] THEN ASM_SIMP_TAC [IDEAL_PROD_AC, RING_IDEAL_IMP_SUBSET], MP_TAC v8 THEN ASM_SIMP_TAC [IDEAL_CLASS_REFL, IDEAL_PROD_CARRIER_LEFT]], DISCH_TAC THEN CONJ_TAC THENL [FIRST_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [IN_IDEAL_CLASS])) THEN SIMP_TAC [], ALL_TAC] THEN EXISTS_TAC q2 THEN ASM_SIMP_TAC [IDEAL_CLASS_REFL] THEN MATCH_MP_TAC IDEAL_CLASS_TRANS THEN EXISTS_TAC q1 THEN ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IDEAL_CLASS_MUL THEN ASM_SIMP_TAC [IDEAL_CLASS_REFL, IDEAL_CLASS_SYM]])
    let lemma := p28
    let q29 ← q r"j:A->bool"
    let q30 ← q r"iv(j:A->bool):A->bool"
    let q31 ← q r"r:A ring"
    let v32 ← ISPECL [q31, q30, q29] IDEAL_PROD_COMM
    let q33 ← q r"!j. ring_ideal r j /\ ~(j = {ring_0 r})
          ==> ideal_class r j IN
              {ideal_class r j | j | ring_ideal r j /\ ~(j = {ring_0 r:A})}"
    let q34 ← q r"iv:(A->bool)->A->bool"
    let q35 ← q r"r:A ring"
    let v36 ← ISPEC q35 lemma
    let q37 ← q r"k:A->bool"
    let q38 ← q r"j:A->bool"
    let q39 ← q r"l:A->bool"
    let q40 ← q r"!j k. ring_ideal r j /\ ring_ideal r k
            ==> {l | ?j' k'. j' IN ideal_class r j /\ k' IN ideal_class r k /\
                             l IN ideal_class r (ideal_prod r j' k')} =
                ideal_class r (ideal_prod r j k:A->bool)"
    let v41 ← GSYM class_group
    let q46 ← q r"r:A ring"
    let q47 ← q r"(p ==> q) /\ (p ==> r) <=> p ==> q /\ r"
    let r48 ← TAUT q47
    prove
      r"(!r:A ring.
            dedekind_domain r
            ==> group_carrier(class_group r) = ideal_classes r) /\
       (!r:A ring.
            dedekind_domain r
            ==> group_id(class_group r) = ideal_class r (ring_carrier r)) /\
       (!r:A ring.
            dedekind_domain r
            ==> group_inv(class_group r) =
                \c. {k | ring_ideal r k /\
                         ?j. j IN c /\
                             ring_carrier r IN
                             ideal_class r (ideal_prod r j k)}) /\
       (!r:A ring.
            dedekind_domain r
            ==> group_mul(class_group r) =
                \c d. {l | ?j k. j IN c /\ k IN d /\
                                 l IN ideal_class r (ideal_prod r j k)})"
      (REWRITE_TAC [AND_FORALL_THM, r48] THEN X_GEN_TAC q46 THEN DISCH_TAC THEN MP_TAC (← (do pure (Prod.fst (← (do pure (← EQ_IMP_RULE (← ISPEC (← (do let z42 ← (do let z43 ← (do pure (Prod.snd (← (do let z44 ← (do let z45 ← (pure class_group); pure (concl z45)); pure (strip_forall z44))))); liftExcept (rand z43)); liftExcept (rand z42))) (← CONJUNCT2 group_tybij)))))))) THEN REWRITE_TAC [v41] THEN ANTS_TAC THENL [ALL_TAC, SIMP_TAC [group_carrier, group_id, group_inv, group_mul]] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP INTEGRAL_DOMAIN_UNIT_IDEAL)) THEN SUBGOAL_THEN q40 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC q39 THEN EQ_TAC THENL [ASM_MESON_TAC [IDEAL_CLASS_MUL, IDEAL_CLASS_TRANS], DISCH_TAC THEN MAP_EVERY EXISTS_TAC [q38, q37] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (CONJUNCT2 o (CONJUNCT2 o (GEN_REWRITE_RULE id [IN_IDEAL_CLASS]))))) THEN ASM_SIMP_TAC [IDEAL_PROD_EQ_ZERO, DE_MORGAN_THM, IDEAL_CLASS_REFL]], ALL_TAC] THEN MP_TAC v36 THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN DISCH_THEN (X_CHOOSE_TAC q34) THEN REWRITE_TAC [ideal_classes, RIGHT_FORALL_IMP_THM, IMP_CONJ, FORALL_IN_GSPEC] THEN SUBGOAL_THEN q33 ASSUME_TAC THENL [REWRITE_TAC [IN_ELIM_THM] THEN MESON_TAC [], ALL_TAC] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_PROD, IDEAL_PROD_EQ_ZERO, IDEAL_PROD_CARRIER, IDEAL_PROD_CARRIER_LEFT] THENL [REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC IDEAL_PROD_ASSOC THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], MP_TAC v32 THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET, IDEAL_CLASS_EQ]])

  let IDEAL_CLASS_IN_CLASS_GROUP ← prove
    r"!r j:A->bool.
        dedekind_domain r
        ==> (ideal_class r j IN group_carrier(class_group r) <=>
             ring_ideal r j /\ ~(j = {ring_0 r}))"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [CLASS_GROUP, ideal_classes, IN_ELIM_THM] THEN EQ_TAC THENL [ALL_TAC, MESON_TAC []] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"k:A->bool") STRIP_ASSUME_TAC) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"k:A->bool")] IDEAL_CLASS_EQ) THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN, IN_IDEAL_CLASS])

  let CLASS_GROUP_MUL ← prove
    r"!r j k:A->bool.
        dedekind_domain r /\ ring_ideal r j /\ ring_ideal r k
        ==> group_mul (class_group r) (ideal_class r j) (ideal_class r k) =
            ideal_class r (ideal_prod r j k)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN ASM_SIMP_TAC [CLASS_GROUP] THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"l:A->bool") THEN EQ_TAC THENL [ASM_MESON_TAC [IDEAL_CLASS_MUL, IDEAL_CLASS_TRANS], DISCH_TAC THEN MAP_EVERY EXISTS_TAC [(← q r"j:A->bool"), (← q r"k:A->bool")] THEN FIRST_ASSUM (MP_TAC o (CONJUNCT1 o (CONJUNCT2 o (CONJUNCT2 o (GEN_REWRITE_RULE id [IN_IDEAL_CLASS]))))) THEN ASM_SIMP_TAC [IDEAL_PROD_EQ_ZERO, DE_MORGAN_THM, IDEAL_CLASS_REFL]])

  let IDEAL_CLASS_EQ_ID ← prove
    r"!r j:A->bool.
        dedekind_domain r /\ ~(j = {ring_0 r})
        ==> (ideal_class r j = group_id(class_group r) <=>
             principal_ideal r j)"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [CLASS_GROUP] THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN FIRST_ASSUM (STRIP_ASSUME_TAC o (MATCH_MP INTEGRAL_DOMAIN_UNIT_IDEAL)) THEN ASM_SIMP_TAC [IDEAL_CLASS_EQ] THEN ASM_MESON_TAC [IDEAL_CLASS_PRINCIPAL, PRINCIPAL_IDEAL_CLASS])

  let CLASS_GROUP_INV ← prove
    r"!r j k:A->bool.
        dedekind_domain r /\
        ring_ideal r j /\ ~(j = {ring_0 r}) /\
        ring_ideal r k /\ ~(k = {ring_0 r})
        ==> (group_inv (class_group r) (ideal_class r j) = ideal_class r k <=>
             principal_ideal r (ideal_prod r j k))"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [GROUP_LINV_EQ, IDEAL_CLASS_IN_CLASS_GROUP, CLASS_GROUP_MUL] THEN MATCH_MP_TAC IDEAL_CLASS_EQ_ID THEN ASM_SIMP_TAC [IDEAL_PROD_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN])

  let CLASS_GROUP_POW ← prove
    r"!r (j:A->bool) n.
        dedekind_domain r /\ ring_ideal r j
        ==> group_pow (class_group r) (ideal_class r j) n =
            ideal_class r (ideal_pow r j n)"
    (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC [group_pow, ideal_pow, CLASS_GROUP_MUL, RING_IDEAL_IDEAL_POW] THEN ASM_SIMP_TAC [CLASS_GROUP])

  let CLASS_GROUP_POW_EQ_ID ← prove
    r"!r (j:A->bool) n.
        dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r})
        ==> (group_pow (class_group r) (ideal_class r j) n =
             group_id(class_group r) <=>
             principal_ideal r (ideal_pow r j n))"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [CLASS_GROUP_POW] THEN MATCH_MP_TAC IDEAL_CLASS_EQ_ID THEN ASM_SIMP_TAC [IDEAL_POW_EQ_ZERO, DEDEKIND_IMP_INTEGRAL_DOMAIN])

  let ABELIAN_CLASS_GROUP ← prove
    r"!r:A ring. dedekind_domain r ==> abelian_group(class_group r)"
    (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [abelian_group, (← CONJUNCT1 CLASS_GROUP), ideal_classes, IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN ASM_SIMP_TAC [CLASS_GROUP_MUL] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC IDEAL_PROD_COMM THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET])

  let TRIVIAL_CLASS_GROUP ← prove
    r"!r:A ring. dedekind_domain r ==> (trivial_group(class_group r) <=> PID r)"
    (SIMP_TAC [TRIVIAL_GROUP_HAS_SIZE_1, CLASS_GROUP, DEDEKIND_PID_EQ_CLASS_NUMBER_1])

  let DEDEKIND_PRINCIPAL_IDEAL_POW_CLASS_NUMBER ← prove
    r"!r j:A->bool.
        dedekind_domain r /\ FINITE(ideal_classes r) /\ ring_ideal r j
        ==> principal_ideal r (ideal_pow r j (class_number r))"
    (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"j = {ring_0 r:A}") THENL [ASM_CASES_TAC (← q r"class_number(r:A ring) = 0") THEN ASM_SIMP_TAC [IDEAL_POW_0, PRINCIPAL_IDEAL_CARRIER] THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"j:A->bool"), (← q r"class_number(r:A ring)")] IDEAL_POW_EQ_ZERO) THEN ASM_SIMP_TAC [DEDEKIND_IMP_INTEGRAL_DOMAIN, PRINCIPAL_IDEAL_0], ASM_SIMP_TAC [(← GSYM CLASS_GROUP_POW_EQ_ID)] THEN MP_TAC (← ISPECL [(← q r"class_group r:((A->bool)->bool)group"), (← q r"ideal_class r (j:A->bool)")] GROUP_POW_GROUP_ORDER) THEN ASM_SIMP_TAC [IDEAL_CLASS_IN_CLASS_GROUP, CLASS_GROUP, class_number]])

  let FINITE_CLASS_GROUP ← prove
    r"!k:A ring.
        number_field k
        ==> FINITE(group_carrier(class_group(ring_of_integers k)))"
    (SIMP_TAC [CLASS_GROUP, DEDEKIND_RING_OF_INTEGERS, NUMBER_FIELD_CLASS_GROUP_FINITE])

  let HAS_SIZE_CLASS_GROUP ← prove
    r"!k:A ring.
        number_field k
        ==> group_carrier(class_group(ring_of_integers k)) HAS_SIZE
            class_number(ring_of_integers k)"
    (SIMP_TAC [HAS_SIZE, class_number, CLASS_GROUP, DEDEKIND_RING_OF_INTEGERS, NUMBER_FIELD_CLASS_GROUP_FINITE])

  let NUMBER_FIELD_PRINCIPAL_IDEAL_POW_CLASS_NUMBER ← prove
    r"!k j:A->bool.
        number_field k /\ ring_ideal (ring_of_integers k) j
        ==> principal_ideal (ring_of_integers k)
              (ideal_pow (ring_of_integers k) j
                 (class_number(ring_of_integers k)))"
    (SIMP_TAC [DEDEKIND_PRINCIPAL_IDEAL_POW_CLASS_NUMBER, DEDEKIND_RING_OF_INTEGERS, NUMBER_FIELD_CLASS_GROUP_FINITE])

  let DEDEKIND_PRINCIPAL_IDEAL_POW_COPRIME ← prove
    r"!r j:A->bool n.
        dedekind_domain r /\ FINITE(ideal_classes r) /\ ring_ideal r j /\
        coprime(n,class_number r) /\ principal_ideal r (ideal_pow r j n)
        ==> principal_ideal r j"
    (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"j = {ring_0 r:A}") THEN ASM_REWRITE_TAC [PRINCIPAL_IDEAL_0] THEN ASM_SIMP_TAC [(← GSYM IDEAL_CLASS_EQ_ID)] THEN SUBGOAL_THEN (← q r"ideal_class r (j:A->bool) IN group_carrier(class_group r)") ASSUME_TAC THENL [ASM_SIMP_TAC [IDEAL_CLASS_IN_CLASS_GROUP], ALL_TAC] THEN ASM_SIMP_TAC [(← GSYM GROUP_ELEMENT_ORDER_EQ_1)] THEN FIRST_X_ASSUM (MATCH_MP_TAC o (GEN_REWRITE_RULE id [coprime])) THEN ASM_SIMP_TAC [(← GSYM GROUP_POW_EQ_ID)] THEN CONJ_TAC THENL [ASM_SIMP_TAC [CLASS_GROUP_POW_EQ_ID], MP_TAC (← ISPECL [(← q r"class_group r:((A->bool)->bool)group"), (← q r"ideal_class r (j:A->bool)")] GROUP_POW_GROUP_ORDER) THEN ASM_SIMP_TAC [CLASS_GROUP, class_number]])

  let NUMBER_FIELD_PRINCIPAL_IDEAL_POW_COPRIME ← prove
    r"!k j:A->bool n.
        number_field k /\ ring_ideal (ring_of_integers k) j /\
        coprime(n,class_number(ring_of_integers k)) /\
        principal_ideal (ring_of_integers k)
                        (ideal_pow (ring_of_integers k) j n)
        ==> principal_ideal (ring_of_integers k) j"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC DEDEKIND_PRINCIPAL_IDEAL_POW_COPRIME THEN EXISTS_TAC (← q r"n:num") THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, NUMBER_FIELD_CLASS_GROUP_FINITE])

  let DEDEKIND_COPRIME_MUL_POW ← prove
    r"!r x y z:A n.
        dedekind_domain r /\ FINITE(ideal_classes r) /\
        coprime(n,class_number r) /\ ~(n = 0) /\
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r /\
        ring_setadd r (ideal_generated r {x}) (ideal_generated r {y}) =
        ring_carrier r /\
        ring_mul r x y = ring_pow r z n
        ==> ?u w. ring_unit r u /\ w IN ring_carrier r /\
                  x = ring_mul r u (ring_pow r w n)"
    (REPEAT STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"ideal_generated r {x:A}"), (← q r"ideal_generated r {y:A}"), (← q r"ideal_generated r {z:A}"), (← q r"n:num")] DEDEKIND_IDEAL_COPRIME_PROD_POW) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_PROD_PRINCIPAL, IDEAL_POW_PRINCIPAL] THEN DISCH_THEN (X_CHOOSE_THEN (← q r"a:A->bool") (X_CHOOSE_THEN (← q r"b:A->bool") STRIP_ASSUME_TAC)) THEN MP_TAC (← ISPECL [(← q r"r:A ring"), (← q r"a:A->bool"), (← q r"n:num")] DEDEKIND_PRINCIPAL_IDEAL_POW_COPRIME) THEN ANTS_TAC THENL [ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z4 ← (q r"ideal_pow r (a:A->bool) n"); let z3 ← (do let z1 ← (do let z2 ← (pure th); pure (concl z2)); liftExcept (rand z1)); pure (z3 == z4)))))) THEN REWRITE_TAC [principal_ideal] THEN ASM_MESON_TAC [], REWRITE_TAC [principal_ideal, LEFT_IMP_EXISTS_THM]] THEN X_GEN_TAC (← q r"w:A") THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN UNDISCH_TAC (← q r"ideal_generated r {x:A} = ideal_pow r (ideal_generated r {w}) n") THEN ASM_SIMP_TAC [IDEAL_POW_PRINCIPAL, IDEALS_GENERATED_SING_EQ, RING_POW] THEN ASM_SIMP_TAC [INTEGRAL_DOMAIN_ASSOCIATES] THEN DISCH_THEN ((X_CHOOSE_THEN (← q r"u:A") STRIP_ASSUME_TAC) o CONJUNCT2) THEN MAP_EVERY EXISTS_TAC [(← q r"u:A"), (← q r"w:A")] THEN ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN ASM_MESON_TAC [RING_MUL_SYM, RING_POW, RING_UNIT_IN_CARRIER])

  let NUMBER_FIELD_COPRIME_MUL_POW ← prove
    r"!k x y z:A n.
        number_field k /\ coprime(n,class_number(ring_of_integers k)) /\
        ~(n = 0) /\
        x IN ring_carrier(ring_of_integers k) /\
        y IN ring_carrier(ring_of_integers k) /\
        z IN ring_carrier(ring_of_integers k) /\
        ring_setadd (ring_of_integers k)
          (ideal_generated (ring_of_integers k) {x})
          (ideal_generated (ring_of_integers k) {y}) =
        ring_carrier(ring_of_integers k) /\
        ring_mul k x y = ring_pow k z n
        ==> ?u w. ring_unit (ring_of_integers k) u /\
                  w IN ring_carrier(ring_of_integers k) /\
                  x = ring_mul k u (ring_pow k w n)"
    (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL [(← q r"ring_of_integers k:A ring"), (← q r"x:A"), (← q r"y:A"), (← q r"z:A"), (← q r"n:num")] DEDEKIND_COPRIME_MUL_POW) THEN ASM_SIMP_TAC [DEDEKIND_RING_OF_INTEGERS, NUMBER_FIELD_CLASS_GROUP_FINITE, RING_OF_INTEGERS])

  let CLASS_GROUP_HOMOMORPHISM_IDEAL_MAP ← do
    -- every quotation and rule built with the tactics, in OCaml's order
    let q1 ← q r"ideal_prod s ((g:(A->bool)->(B->bool)) (ideal_generated r {a})) (g j) =
      g(ideal_prod r (ideal_generated r {a}) j) /\
      ideal_prod s (g (ideal_generated r {b})) (g j') =
      g(ideal_prod r (ideal_generated r {b}) j')"
    let q2 ← q r"ideal_generated s {d:B}"
    let q3 ← q r"ideal_generated s {c:B}"
    let q8 ← q r"d:B"
    let q9 ← q r"c:B"
    let q10 ← q r"d:B"
    let q11 ← q r"?d. d IN ring_carrier s /\ ~(d = ring_0 s) /\
          (g:(A->bool)->(B->bool))(ideal_generated r {b:A}) =
          ideal_generated s {d:B}"
    let q12 ← q r"c:B"
    let q13 ← q r"?c. c IN ring_carrier s /\ ~(c = ring_0 s) /\
          (g:(A->bool)->(B->bool))(ideal_generated r {a:A}) =
          ideal_generated s {c:B}"
    let q14 ← q r"b:A"
    let q15 ← q r"a:A"
    let p16 ← prove r"!r:A ring s:B ring g j j'.
          integral_domain r /\ integral_domain s /\
          (!j. ring_ideal r j /\ ~(j = {ring_0 r})
               ==> ring_ideal s (g j) /\ ~(g j = {ring_0 s})) /\
          (!j k. ring_ideal r j /\ ~(j = {ring_0 r}) /\
                 ring_ideal r k /\ ~(k = {ring_0 r})
                 ==> g(ideal_prod r j k) = ideal_prod s (g j) (g k)) /\
          (!a. a IN ring_carrier r /\ ~(a = ring_0 r)
               ==> ?c. c IN ring_carrier s /\ ~(c = ring_0 s) /\
                       g(ideal_generated r {a}) = ideal_generated s {c}) /\
          j' IN ideal_class r j
          ==> g j' IN ideal_class s (g j)" (REPEAT GEN_TAC THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN FIRST_ASSUM (MP_TAC o (GEN_REWRITE_RULE id [IN_IDEAL_CLASS])) THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN q15 (X_CHOOSE_THEN q14 STRIP_ASSUME_TAC)))))) THEN REWRITE_TAC [IN_IDEAL_CLASS] THEN ASM_SIMP_TAC [] THEN SUBGOAL_THEN q13 (X_CHOOSE_THEN q12 STRIP_ASSUME_TAC) THENL [ASM_SIMP_TAC [], ALL_TAC] THEN SUBGOAL_THEN q11 (X_CHOOSE_THEN q10 STRIP_ASSUME_TAC) THENL [ASM_SIMP_TAC [], ALL_TAC] THEN MAP_EVERY EXISTS_TAC [q9, q8] THEN ASM_REWRITE_TAC [] THEN MAP_EVERY (fun t => tactic_of do pure (FIRST_X_ASSUM (SUBST1_TAC o (SYM o (checkM (fun th => (do let z7 ← (pure t); let z6 ← (do let z4 ← (do let z5 ← (pure th); pure (concl z5)); liftExcept (rand z4)); pure (z6 == z7)))))))) [q3, q2] THEN SUBGOAL_THEN q1 (CONJUNCTS_THEN SUBST1_TAC) THENL [CONJ_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0], ASM_REWRITE_TAC []])
    let lemma := p16
    let q17 ← q r"k:A->bool"
    let q18 ← q r"j:A->bool"
    let q19 ← q r"(g:(A->bool)->(B->bool)) j"
    let q20 ← q r"j:A->bool"
    let v21 ← CONJUNCT1 CLASS_GROUP
    let q22 ← q r"f:((A->bool)->bool)->((B->bool)->bool)"
    let q23 ← q r"(g:(A->bool)->(B->bool)) j'"
    let q24 ← q r"(g:(A->bool)->(B->bool)) j"
    let q25 ← q r"s:B ring"
    let v26 ← ISPECL [q25, q24, q23] IDEAL_CLASS_EQ
    let q27 ← q r"ring_ideal s ((g:(A->bool)->(B->bool)) j') /\ ~(g j' = {ring_0 s})"
    let v28 ← GSYM IDEAL_CLASS_EQ
    let q29 ← q r"(j':A->bool) IN ideal_class r j"
    let q30 ← q r"j:A->bool"
    let q31 ← q r"ring_ideal r j' /\ ~(j' = {ring_0 r}) /\
        ideal_class r j = ideal_class r (j':A->bool)"
    let q32 ← q r"j' = @j'. ring_ideal r j' /\ ~(j' = {ring_0 r}) /\
                            ideal_class r j = ideal_class r (j':A->bool)"
    let q33 ← q r"j:A->bool"
    let q34 ← q r"\c. ideal_class s ((g:(A->bool)->(B->bool))
                             (@j. ring_ideal r j /\ ~(j = {ring_0 r}) /\
                                  c = ideal_class r (j:A->bool)))"
    let q35 ← q r"?f. !j. ring_ideal r j /\ ~(j = {ring_0 r})
              ==> f(ideal_class r j) =
                  ideal_class s ((g:(A->bool)->(B->bool)) j)"
    let q36 ← q r"r:A ring"
    let q37 ← q r"!j j'. j' IN ideal_class r j
             ==> (g:(A->bool)->(B->bool)) j' IN ideal_class s (g j)"
    let q38 ← q r"c:B"
    let q39 ← q r"c:B"
    let q40 ← q r"ring_ideal s ((g:(A->bool)->(B->bool))(ideal_generated r {a:A})) /\
        ~(g(ideal_generated r {a}) = {ring_0 s}) /\
        principal_ideal s (g(ideal_generated r {a}))"
    let q41 ← q r"a:A"
    let q42 ← q r"!a. a IN ring_carrier r /\ ~(a = ring_0 r)
          ==> ?c. c IN ring_carrier s /\ ~(c = ring_0 s) /\
                  (g:(A->bool)->(B->bool))(ideal_generated r {a:A}) =
                  ideal_generated s {c:B}"
    prove
      r"!r:A ring s:B ring g.
            dedekind_domain r /\ dedekind_domain s /\
            (!j. ring_ideal r j /\ ~(j = {ring_0 r})
                 ==> ring_ideal s (g j) /\ ~(g j = {ring_0 s})) /\
            (!j k. ring_ideal r j /\ ~(j = {ring_0 r}) /\
                   ring_ideal r k /\ ~(k = {ring_0 r})
                   ==> g(ideal_prod r j k) = ideal_prod s (g j) (g k)) /\
            (!a. a IN ring_carrier r /\ ~(a = ring_0 r)
                 ==> principal_ideal s (g(ideal_generated r {a})))
            ==> ?f. group_homomorphism(class_group r,class_group s) f /\
                    !j. ring_ideal r j /\ ~(j = {ring_0 r})
                        ==> f(ideal_class r j) = ideal_class s (g j)"
      (REPEAT GEN_TAC THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN) o (checkM (fun th => (do let z48 ← (q r"dedekind_domain(r:A ring)"); let z47 ← (do let z46 ← (pure th); pure (concl z46)); pure (z47 == z48)))))) THEN FIRST_ASSUM (ASSUME_TAC o ((MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN) o (checkM (fun th => (do let z45 ← (q r"dedekind_domain(s:B ring)"); let z44 ← (do let z43 ← (pure th); pure (concl z43)); pure (z44 == z45)))))) THEN SUBGOAL_THEN q42 ASSUME_TAC THENL [X_GEN_TAC q41 THEN STRIP_TAC THEN SUBGOAL_THEN q40 MP_TAC THENL [ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_EQ_0], ALL_TAC] THEN REWRITE_TAC [principal_ideal] THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN q39 STRIP_ASSUME_TAC))) THEN EXISTS_TAC q38 THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC [IDEAL_GENERATED_0], ALL_TAC] THEN SUBGOAL_THEN q37 ASSUME_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN EXISTS_TAC q36 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q35 MP_TAC THENL [EXISTS_TAC q34 THEN X_GEN_TAC q33 THEN STRIP_TAC THEN REWRITE_TAC [] THEN ABBREV_TAC q32 THEN SUBGOAL_THEN q31 STRIP_ASSUME_TAC THENL [EXPAND_TAC "j'" THEN CONV_TAC SELECT_CONV THEN EXISTS_TAC q30 THEN ASM_REWRITE_TAC [], ALL_TAC] THEN SUBGOAL_THEN q29 ASSUME_TAC THENL [ASM_SIMP_TAC [v28], ALL_TAC] THEN SUBGOAL_THEN q27 STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN MP_TAC v26 THEN ASM_SIMP_TAC [], MATCH_MP_TAC MONO_EXISTS] THEN X_GEN_TAC q22 THEN DISCH_TAC THEN ASM_REWRITE_TAC [GROUP_HOMOMORPHISM] THEN ASM_SIMP_TAC [v21, ideal_classes, SUBSET, FORALL_IN_IMAGE, IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN CONJ_TAC THENL [X_GEN_TAC q20 THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC [IN_ELIM_THM] THEN EXISTS_TAC q19 THEN ASM_SIMP_TAC [], ALL_TAC] THEN X_GEN_TAC q18 THEN REPEAT DISCH_TAC THEN X_GEN_TAC q17 THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC [CLASS_GROUP_MUL] THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_PROD, IDEAL_PROD_EQ_ZERO])

  let DEDEKIND_CLASS_GROUP_EXTENSION ← prove
    r"!r:A ring s:B ring h.
        dedekind_domain r /\ dedekind_domain s /\ ring_monomorphism(r,s) h
        ==> ?f. group_homomorphism(class_group r,class_group s) f /\
                !j. ring_ideal r j /\ ~(j = {ring_0 r})
                    ==> f(ideal_class r j) =
                        ideal_class s (ideal_generated s (IMAGE h j))"
    (REPEAT STRIP_TAC THEN MATCH_MP_TAC CLASS_GROUP_HOMOMORPHISM_IDEAL_MAP THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM)) THEN ASM_SIMP_TAC [RING_IDEAL_IDEAL_GENERATED, IDEAL_GENERATED_MONOMORPHIC_IMAGE_EQ_0] THEN CONJ_TAC THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_PROD_HOMOMORPHIC_IMAGE THEN ASM_SIMP_TAC [RING_IDEAL_IMP_SUBSET], REPEAT STRIP_TAC THEN ASM_SIMP_TAC [IDEAL_GENERATED_IMAGE_IDEAL_GENERATED, SING_SUBSET] THEN REWRITE_TAC [principal_ideal, IMAGE_CLAUSES] THEN EXISTS_TAC (← q r"(h:A->B) a") THEN ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER]])

  -- @@RETURN BEGIN
  return { class_group, CLASS_GROUP, IDEAL_CLASS_IN_CLASS_GROUP, CLASS_GROUP_MUL,
           IDEAL_CLASS_EQ_ID, CLASS_GROUP_INV, CLASS_GROUP_POW, CLASS_GROUP_POW_EQ_ID,
           ABELIAN_CLASS_GROUP, TRIVIAL_CLASS_GROUP,
           DEDEKIND_PRINCIPAL_IDEAL_POW_CLASS_NUMBER, FINITE_CLASS_GROUP,
           HAS_SIZE_CLASS_GROUP, NUMBER_FIELD_PRINCIPAL_IDEAL_POW_CLASS_NUMBER,
           DEDEKIND_PRINCIPAL_IDEAL_POW_COPRIME,
           NUMBER_FIELD_PRINCIPAL_IDEAL_POW_COPRIME, DEDEKIND_COPRIME_MUL_POW,
           NUMBER_FIELD_COPRIME_MUL_POW, CLASS_GROUP_HOMOMORPHISM_IDEAL_MAP,
           DEDEKIND_CLASS_GROUP_EXTENSION }
  -- @@RETURN END

end HolANT.ClassgroupGroup
