/- ========================================================================= -/
/- Cyclotomic extensions: the Galois group of k(z), for z of order n, as a   -/
/- subgroup of the multiplicative group of units modulo n, and all of it     -/
/- exactly when [k(z):k] = phi(n).                                           -/
/- ========================================================================= -/
/- File: HolLibrary/Cyclotomic.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/cyclotomic.ml`, by hand, in file
  order, in the style of HolLibrary/Galois.lean (see there and
  HolMath/Base.lean for the conventions).  cyclotomic.ml begins with
  `needs "Library/galois.ml"` and `needs "Library/modmul_group.ml"`, then
  `prioritize_num()` (run at the start of the bundle); the theorems it uses
  from them (and from the files they need) and from the core library are
  supplied via the CoreThms structures (SessionLibrary.Cyclotomic fills
  them).  SessionLibrary/Cyclotomic.lean builds the bundle and exports every
  name under its HOL Light name.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, SET_RULE, RING_RULE, ARITH_RULE, TAUT) they are bound
  first, in OCaml's order.
-/

import HolLibrary.Galois
import HolLibrary.ModmulGroup

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.Cyclotomic

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (COPRIME_LMOD CYCLOTOMIC_EXTENSION_ABELIAN DIVIDES_REFL
   FIELD_IMP_INTEGRAL_DOMAIN FINITE_GALOIS_GROUP FINITE_MODMUL_GROUP
   FORALL_IN_IMAGE FORALL_UNWIND_THM2 GALOIS_EXTENSION_EQ_CARD GALOIS_GROUP
   GALOIS_GROUP_COMPOSE GALOIS_GROUP_EQ_ON_GENERATORS GALOIS_GROUP_INVERSE
   GALOIS_GROUP_PERMUTES GALOIS_GROUP_RING_HOMOMORPHISM GROUP_HOMOMORPHISM
   GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE GROUP_ISOMORPHISM_IMP_ISOMORPHIC
   HAS_SIZE HAS_SIZE_MODMUL_GROUP IN_ELIM_THM IN_SING ISOMORPHIC_GROUP_ORDER
   MODMUL_GROUP MOD_LT_EQ MONO_EXISTS PERMUTES_INVERSES RIGHT_IMP_EXISTS_THM
   RING_1 RING_ENDOMORPHISM_ROOT_OF_UNITY RING_HOMOMORPHISM_1
   RING_HOMOMORPHISM_POW RING_ORDER_EQ_1 RING_POW_1 RING_POW_EQ_1
   RING_POW_EQ_GEN RING_POW_EQ_LT RING_POW_MOD_ORDER RING_POW_POW SKOLEM_THM
   SUBSET field_extension group_monomorphism o_THM ring_endomorphism : thm)
  deriving Inhabited

/-- What cyclotomic.ml uses from Session besides theorems. -/
structure CyclotomicDeps where
  new_definition : String → ExceptT String IO thm
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  TAUT : term → ExceptT String IO thm
  INDUCT_TAC : tactic
  RING_RULE : term → ExceptT String IO thm  -- ringtheory.ml's RING_RULE
  FIELD_TAC : tactic  -- ringtheory.ml's FIELD_TAC
  GROUP_TAC : tactic  -- grouptheory.ml's GROUP_TAC
  NUM_REDUCE_CONV : ioconv  -- calc_num.ml's NUM_REDUCE_CONV
  HAS_SIZE_CONV : ioconv  -- card.ml's HAS_SIZE_CONV
  EXPAND_CASES_CONV : ioconv  -- calc_num.ml's EXPAND_CASES_CONV
  DIVIDES_CONV : ioconv  -- prime.ml's DIVIDES_CONV
  prioritize_num : IO Unit  -- prioritize_num ()
  NUMBER_RULE : ioconv  -- ints.ml's NUMBER_RULE
  num_CONV : ioconv  -- calc_num.ml's num_CONV
  core1 : CoreThms1

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)

/- ------------------------------------------------------------------------- -/
/- For l generated over the image of k by an element z of finite order n,    -/
/- every element f of the Galois group sends z to a power z^e with e a unit  -/
/- mod n, and f |-> e is a monomorphism from the Galois group into the       -/
/- multiplicative group modmul_group n of the units mod n. The monomorphism  -/
/- is an isomorphism exactly when [l:k] = phi(n).                            -/
/- ------------------------------------------------------------------------- -/

structure CyclotomicGalois where
  -- @@FIELDS
  CYCLOTOMIC_GALOIS_GROUP_MODMUL : thm
  CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM : thm
  deriving Inhabited

@[nospecialize]
def setupCyclotomicGalois [HolBase] (D : CyclotomicDeps) :
    ExceptT String IO CyclotomicGalois := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, NUMBER_RULE, SET_RULE, prioritize_num, .. } := D
  let { COPRIME_LMOD, CYCLOTOMIC_EXTENSION_ABELIAN, DIVIDES_REFL,
        FIELD_IMP_INTEGRAL_DOMAIN, FINITE_GALOIS_GROUP, FINITE_MODMUL_GROUP,
        FORALL_IN_IMAGE, FORALL_UNWIND_THM2, GALOIS_EXTENSION_EQ_CARD, GALOIS_GROUP,
        GALOIS_GROUP_COMPOSE, GALOIS_GROUP_EQ_ON_GENERATORS, GALOIS_GROUP_INVERSE,
        GALOIS_GROUP_PERMUTES, GALOIS_GROUP_RING_HOMOMORPHISM, GROUP_HOMOMORPHISM,
        GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE, GROUP_ISOMORPHISM_IMP_ISOMORPHIC,
        HAS_SIZE, HAS_SIZE_MODMUL_GROUP, IN_ELIM_THM, IN_SING, ISOMORPHIC_GROUP_ORDER,
        MODMUL_GROUP, MOD_LT_EQ, MONO_EXISTS, PERMUTES_INVERSES, RIGHT_IMP_EXISTS_THM,
        RING_1, RING_ENDOMORPHISM_ROOT_OF_UNITY, RING_HOMOMORPHISM_1,
        RING_HOMOMORPHISM_POW, RING_ORDER_EQ_1, RING_POW_1, RING_POW_EQ_1,
        RING_POW_EQ_GEN, RING_POW_EQ_LT, RING_POW_MOD_ORDER, RING_POW_POW, SKOLEM_THM,
        SUBSET, field_extension, group_monomorphism, o_THM, ring_endomorphism, .. } := D.core1
  -- @@SCOPE END
  prioritize_num

  /- For l generated over the image of k by an element z of finite order n,    -/
  /- every element f of the Galois group sends z to a power z^e with e a unit  -/
  /- mod n, and f |-> e is a monomorphism from the Galois group into the       -/
  /- multiplicative group modmul_group n of the units mod n.                   -/

  let CYCLOTOMIC_GALOIS_GROUP_MODMUL ← prove
   r"!(h:A->B) k l z n.
        field l /\ z IN ring_carrier l /\ ring_order l z = n /\ ~(n = 0) /\
        subfield_generated l (z INSERT IMAGE h (ring_carrier k)) = l
        ==> ?e. group_monomorphism(galois_group(k,l) h,modmul_group n) e /\
                !f. f IN group_carrier(galois_group(k,l) h)
                    ==> f z = ring_pow l z (e f)"
   (← do
    -- right to left: the SET_RULE, then the ARITH_RULE
    let s1 ← SET_RULE (← q r"(s:B->bool) UNION {a} = a INSERT s")
    let a1 ← ARITH_RULE (← q r"n <= 1 /\ ~(n = 0) ==> n = 1")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
    SUBGOAL_THEN
     (← q r"!f. f IN group_carrier(galois_group(k,l) (h:A->B))
          ==> ?j. j IN group_carrier(modmul_group n) /\ f z = ring_pow l z j")
    MP_TAC THENL
     [X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM) THEN
      REWRITE_TAC [MODMUL_GROUP] THEN COND_CASES_TAC THENL
       [EXISTS_TAC (← q r"1") THEN REWRITE_TAC [IN_SING] THEN
        SUBGOAL_THEN (← q r"z = ring_1(l:B ring)") SUBST1_TAC THENL
         [ASM_MESON_TAC [RING_ORDER_EQ_1, a1],
          ASM_MESON_TAC [RING_POW_1, RING_1, RING_HOMOMORPHISM_1]],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"l:B ring", ← q r"f:B->B", ← q r"z:B"]
        RING_ENDOMORPHISM_ROOT_OF_UNITY) THEN
      ASM_REWRITE_TAC [ring_endomorphism] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q r"j:num")) THEN
      MP_TAC (← ISPECL [← q r"l:B ring", ← q r"inverse(f:B->B)", ← q r"z:B"]
        RING_ENDOMORPHISM_ROOT_OF_UNITY) THEN
      ASM_REWRITE_TAC [ring_endomorphism] THEN ANTS_TAC THENL
       [ASM_MESON_TAC [GALOIS_GROUP_INVERSE, GALOIS_GROUP_RING_HOMOMORPHISM],
        DISCH_THEN (X_CHOOSE_TAC (← q r"i:num"))] THEN
      EXISTS_TAC (← q r"j MOD n") THEN REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_SIMP_TAC [MOD_LT_EQ, COPRIME_LMOD] THEN CONJ_TAC THENL
       [SUBGOAL_THEN (← q r"ring_pow l (z:B) (j * i) = ring_pow l z 1") MP_TAC THENL
         [ASM_SIMP_TAC [RING_POW_1, ← GSYM RING_POW_POW] THEN
          UNDISCH_TAC (← q r"(f:B->B) z = ring_pow l z j") THEN
          DISCH_THEN (SUBST1_TAC o SYM) THEN
          ASM_SIMP_TAC [← GSYM (← MATCH_MP RING_HOMOMORPHISM_POW
            (← ASSUME (← q r"ring_homomorphism(l,l) (f:B->B)")))] THEN
          UNDISCH_TAC (← q r"inverse(f:B->B) z = ring_pow l z i") THEN
          DISCH_THEN (SUBST1_TAC o SYM) THEN
          ASM_MESON_TAC [PERMUTES_INVERSES, GALOIS_GROUP_PERMUTES],
          ASM_SIMP_TAC [RING_POW_EQ_GEN] THEN CONV_TAC NUMBER_RULE],
        ASM_REWRITE_TAC [] THEN
        UNDISCH_TAC (← q r"ring_order l (z:B) = n") THEN
        DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [RING_POW_MOD_ORDER]],
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"e:(B->B)->num") THEN DISCH_THEN (LABEL_TAC "e") THEN
    CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
    REWRITE_TAC [group_monomorphism, GROUP_HOMOMORPHISM, SUBSET,
                FORALL_IN_IMAGE] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [],
      ALL_TAC,
      MAP_EVERY X_GEN_TAC [← q r"f:B->B", ← q r"g:B->B"] THEN STRIP_TAC THEN
      MATCH_MP_TAC GALOIS_GROUP_EQ_ON_GENERATORS THEN
      MAP_EVERY EXISTS_TAC [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"{z:B}"] THEN
      ASM_REWRITE_TAC [s1, IN_SING,
                      FORALL_UNWIND_THM2] THEN
      ASM_MESON_TAC []] THEN
    MAP_EVERY X_GEN_TAC [← q r"f:B->B", ← q r"g:B->B"] THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"(f:B->B) o g IN group_carrier(galois_group(k,l) (h:A->B))")
    ASSUME_TAC THENL [ASM_SIMP_TAC [GALOIS_GROUP_COMPOSE], ALL_TAC] THEN
    REWRITE_TAC [← CONJUNCT2 (← CONJUNCT2 (← CONJUNCT2 GALOIS_GROUP))] THEN
    REWRITE_TAC [MODMUL_GROUP] THEN COND_CASES_TAC THEN BETA_TAC THENL
     [USE_THEN "e" (fun th => tactic_of do
        pure (MP_TAC (← CONJUNCT1 (← MATCH_MP th
          (← ASSUME (← q r"(f:B->B) o g IN group_carrier(galois_group(k,l) (h:A->B))")))))) THEN
      ASM_REWRITE_TAC [MODMUL_GROUP, IN_SING],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!f. f IN group_carrier(galois_group(k,l) (h:A->B))
          ==> (e:(B->B)->num) f < n")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"f':B->B") THEN DISCH_TAC THEN
      USE_THEN "e" (fun th => tactic_of do
        pure (MP_TAC (← CONJUNCT1 (← MATCH_MP th
          (← ASSUME (← q r"(f':B->B) IN group_carrier(galois_group(k,l) (h:A->B))")))))) THEN
      ASM_REWRITE_TAC [MODMUL_GROUP, IN_ELIM_THM] THEN SIMP_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC (← ISPECL [← q r"l:B ring", ← q r"z:B"] RING_POW_EQ_LT) THEN
    ASM_SIMP_TAC [MOD_LT_EQ] THEN
    USE_THEN "e" (fun th => tactic_of do
      pure (MP_TAC (← CONJUNCT2 (← MATCH_MP th
        (← ASSUME (← q r"(f:B->B) o g IN group_carrier(galois_group(k,l) (h:A->B))")))))) THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    UNDISCH_TAC (← q r"ring_order l (z:B) = n") THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC [RING_POW_MOD_ORDER] THEN
    REWRITE_TAC [o_THM] THEN
    SUBGOAL_THEN
     (← q r"(g:B->B) z = ring_pow l z (e g) /\ (f:B->B) z = ring_pow l z (e f)")
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    ASSUME_TAC (← MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM
     (← ASSUME (← q r"(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))"))) THEN
    ASM_SIMP_TAC [← MATCH_MP RING_HOMOMORPHISM_POW
      (← ASSUME (← q r"ring_homomorphism(l,l) (f:B->B)"))] THEN
    ASM_SIMP_TAC [RING_POW_POW]))

  /- The monomorphism e is an isomorphism exactly when [l:k] = phi(n): the     -/
  /- extension is finite and Galois (CYCLOTOMIC_EXTENSION_ABELIAN), so its     -/
  /- group has [l:k] elements (GALOIS_EXTENSION_EQ_CARD), modmul_group n has   -/
  /- phi(n) elements (HAS_SIZE_MODMUL_GROUP), and a monomorphism between       -/
  /- finite groups of the same size is onto                                    -/
  /- (GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE).                               -/
  let CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM ← prove
   r"!(h:A->B) k l z n.
        field_extension(k,l) h /\
        z IN ring_carrier l /\ ring_order l z = n /\ ~(n = 0) /\
        subfield_generated l (z INSERT IMAGE h (ring_carrier k)) = l
        ==> ((?e. group_isomorphism(galois_group(k,l) h,modmul_group n) e /\
                  !f. f IN group_carrier(galois_group(k,l) h)
                      ==> f z = ring_pow l z (e f)) <=>
             extension_degree(k,l) h = phi n)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"z:B", ← q r"n:num"]
      CYCLOTOMIC_EXTENSION_ABELIAN) THEN
    ASM_SIMP_TAC [RING_POW_EQ_1, DIVIDES_REFL] THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"]
      GALOIS_EXTENSION_EQ_CARD) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    MP_TAC (← SPEC (← q r"n:num") HAS_SIZE_MODMUL_GROUP) THEN
    ASM_REWRITE_TAC [HAS_SIZE] THEN DISCH_THEN (SUBST1_TAC o SYM o CONJUNCT2) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP FINITE_GALOIS_GROUP) THEN EQ_TAC THENL
     [DISCH_THEN (CHOOSE_THEN (MP_TAC o MATCH_MP GROUP_ISOMORPHISM_IMP_ISOMORPHIC o
        CONJUNCT1)) THEN
      ASM_MESON_TAC [ISOMORPHIC_GROUP_ORDER],
      DISCH_TAC] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"z:B", ← q r"n:num"]
      CYCLOTOMIC_GALOIS_GROUP_MODMUL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [field_extension], ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"e:(B->B)->num") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE, FINITE_MODMUL_GROUP])

  -- @@RETURN BEGIN
  return { CYCLOTOMIC_GALOIS_GROUP_MODMUL, CYCLOTOMIC_GALOIS_GROUP_MODMUL_ISOMORPHISM }
  -- @@RETURN END

end HolLibrary.Cyclotomic
