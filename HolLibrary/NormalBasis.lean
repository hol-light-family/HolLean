/- ========================================================================= -/
/- The normal basis theorem: for a finite Galois extension (k,l) h with      -/
/- Galois group G, the conjugates f x, f IN G, of some x form a basis of l   -/
/- over k.                                                                    -/
/- ========================================================================= -/
/- File: HolLibrary/NormalBasis.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/normal_basis.ml` (e7fbefd), by hand,
  in file order, in the style of HolLibrary/Galois.lean (see there and
  HolMath/Base.lean for the conventions).  normal_basis.ml begins with
  `needs "Library/galois.ml"`; the theorems it uses from galois.ml (and the
  files it needs) and from the core library are supplied via the CoreThms
  structures (SessionLibrary.NormalBasis fills them).
  SessionLibrary/NormalBasis.lean builds the bundles and exports every name
  under its HOL Light name.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (TAUT, NUMBER_RULE) they are bound first, in OCaml's order.
-/

import HolLibrary.Galois

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.NormalBasis

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (BIJ CARD_EQ_0 CARD_IMAGE_INJ CONG_IMP_EQ CONTRAPOS_THM
   CYCLIC_GALOIS_GROUP_FINITE_FIELD CYCLIC_VECTOR_EXISTS EQ_IMP EQ_SYM_EQ
   EQ_TRANS EXTENSION FIELD_IMP_INTEGRAL_DOMAIN FIELD_NONTRIVIAL
   FINITE_CYCLIC_GROUP_POWERS FINITE_DELETE FINITE_EXTENSION_RING_MATROID
   FINITE_FIELD_GALOIS_EXTENSION FINITE_FINITE_FIELD_EXTENSION
   FINITE_GALOIS_GROUP FINITE_IMAGE FINITE_IMP_FIELD_EXTENSION FINITE_SUBSET
   FORALL_IN_IMAGE FREE_BASIS_FIELD FUN_EQ_THM GALOIS_EXTENSION_EQ_CARD
   GALOIS_GROUP GALOIS_GROUP_COMPOSE GALOIS_GROUP_FINITE_FIELD
   GALOIS_GROUP_FIXES GALOIS_GROUP_I GALOIS_GROUP_INDEPENDENT
   GALOIS_GROUP_INVERSE GALOIS_GROUP_IN_CARRIER GALOIS_GROUP_PERMUTES
   GALOIS_GROUP_POW_RING_POW GALOIS_GROUP_RING_HOMOMORPHISM
   GALOIS_IMP_SEPARABLE_EXTENSION GROUP_POW INFINITE INFINITE_IMAGE INJ
   INTEGRAL_DOMAIN_PRODUCT_EQ_0 IN_DELETE IN_ELIM_THM IN_IMAGE IN_INSERT ITER
   I_O_ID I_THM LE_REFL LT_NZ MATROID_BASIS_LARGE_INDEPENDENT MEMBER_NOT_EMPTY
   MONO_EXISTS NOT_EXISTS_THM NOT_FORALL_THM NOT_IMP PERMUTES_EQ
   PERMUTES_INVERSES_o PERMUTES_INVERSE_INVERSE POLY_CLAUSES POLY_CONST
   POLY_EVAL_0 POLY_EVAL_CONST POLY_EVAL_RING_PRODUCT POLY_EVAL_SUB
   POLY_EVAL_VAR POLY_RING_CLAUSES POLY_ROOT_BOUND POLY_VAR_UNIV
   PRIMITIVE_ELEMENT_THEOREM RING_0 RING_1 RING_ADD_LZERO RING_ADD_RNEG
   RING_ADD_RZERO RING_DET RING_DET_DEPENDENT_COLUMNS RING_DET_DIAGONAL
   RING_DET_EQ RING_DET_EQ_0_ROWS RING_DET_HOMOMORPHISM
   RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED RING_HOMOMORPHISM_0
   RING_HOMOMORPHISM_1 RING_HOMOMORPHISM_ADD RING_HOMOMORPHISM_IN_CARRIER
   RING_HOMOMORPHISM_MUL RING_HOMOMORPHISM_NEG RING_HOMOMORPHISM_POLY_EVAL
   RING_HOMOMORPHISM_PRODUCT RING_HOMOMORPHISM_SUB RING_HOMOMORPHISM_SUM
   RING_INDEPENDENT_FINITE RING_MATROID_BASIS RING_MATROID_INDEPENDENT
   RING_MONOMORPHISM_IMP_HOMOMORPHISM RING_MUL RING_MUL_LID RING_MUL_LNEG
   RING_MUL_LZERO RING_MUL_RZERO RING_MUL_SYM RING_NEG RING_POLYNOMIAL_CONST
   RING_POLYNOMIAL_VAR RING_PRODUCT RING_PRODUCT_EQ
   RING_PRODUCT_EQ_GENERAL_INVERSES RING_PRODUCT_ZERO RING_SPAN_FINITE RING_SUB
   RING_SUB_EQ_0 RING_SUB_REFL RING_SUM_ADD RING_SUM_CYCLIC_GROUP RING_SUM_DELTA
   RING_SUM_EQ RING_SUM_EQ_0 RING_SUM_EQ_GENERAL_INVERSES RING_SUM_IMAGE
   RING_SUM_LMUL RING_SUM_SWAP SUBSET SURJ cyclic_group extension_degree
   field_extension group_pow o_ASSOC o_DEF o_THM ring_basis ring_monomorphism
   ring_spanning : thm)
  deriving Inhabited

/-- What normal_basis.ml uses from Session besides theorems. -/
structure NormalBasisDeps where
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  TAUT : term → ExceptT String IO thm
  INDUCT_TAC : tactic
  SELECT_CONV : ioconv  -- class.ml's SELECT_CONV
  NUMBER_RULE : ioconv  -- ints.ml's NUMBER_RULE
  RING_TAC : tactic  -- ringtheory.ml's RING_TAC
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
/- Normal elements. For a finite Galois extension the conjugates f x,        -/
/- f IN G, are [l:k] = |G| many, so they form a basis as soon as they are    -/
/- independent over k (then they are distinct). They are independent         -/
/- exactly when the determinant of the (inverse f o g) x is nonzero: a       -/
/- dependency over k gives a column dependency, and conversely a row         -/
/- dependency e gives the combination of the inverse f with coefficients     -/
/- e(f), which vanishes on the span of the f x, so on l, against Dedekind.   -/
/- ------------------------------------------------------------------------- -/

structure NormalElements where
  -- @@FIELDS
  NORMAL_BASIS_INDEPENDENT : thm
  NORMAL_BASIS_DET_INDEPENDENT : thm
  NORMAL_BASIS_DETERMINANT : thm
  deriving Inhabited

@[nospecialize]
def setupNormalElements [HolBase] (D : NormalBasisDeps) :
    ExceptT String IO NormalElements := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, RING_TAC, TAUT, .. } := D
  let { CARD_IMAGE_INJ, CONTRAPOS_THM, EQ_TRANS, EXTENSION, FIELD_IMP_INTEGRAL_DOMAIN,
        FIELD_NONTRIVIAL, FINITE_EXTENSION_RING_MATROID, FINITE_GALOIS_GROUP,
        FINITE_IMAGE, FINITE_IMP_FIELD_EXTENSION, FORALL_IN_IMAGE,
        GALOIS_EXTENSION_EQ_CARD, GALOIS_GROUP_COMPOSE, GALOIS_GROUP_FIXES,
        GALOIS_GROUP_INDEPENDENT, GALOIS_GROUP_INVERSE, GALOIS_GROUP_IN_CARRIER,
        GALOIS_GROUP_PERMUTES, GALOIS_GROUP_RING_HOMOMORPHISM, IN_ELIM_THM, LE_REFL,
        MATROID_BASIS_LARGE_INDEPENDENT, NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP,
        PERMUTES_INVERSE_INVERSE, RING_0, RING_1, RING_ADD_LZERO, RING_ADD_RNEG,
        RING_ADD_RZERO, RING_DET_DEPENDENT_COLUMNS, RING_DET_EQ_0_ROWS,
        RING_HOMOMORPHISM_0, RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_MUL, RING_HOMOMORPHISM_NEG, RING_HOMOMORPHISM_SUM,
        RING_INDEPENDENT_FINITE, RING_MATROID_BASIS, RING_MATROID_INDEPENDENT,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL, RING_MUL_LID, RING_MUL_LNEG,
        RING_MUL_LZERO, RING_MUL_RZERO, RING_MUL_SYM, RING_NEG, RING_SPAN_FINITE,
        RING_SUM_ADD, RING_SUM_DELTA, RING_SUM_EQ, RING_SUM_EQ_0,
        RING_SUM_EQ_GENERAL_INVERSES, RING_SUM_IMAGE, RING_SUM_LMUL, RING_SUM_SWAP,
        SUBSET, extension_degree, field_extension, o_DEF, o_THM, ring_basis,
        ring_monomorphism, ring_spanning, .. } := D.core1
  -- @@SCOPE END

  let NORMAL_BASIS_INDEPENDENT ← prove
   r"!(h:A->B) k l x.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        x IN ring_carrier l /\
        (!c. (!f. f IN group_carrier(galois_group(k,l) h)
                  ==> c f IN ring_carrier k) /\
             ring_sum l (group_carrier(galois_group(k,l) h))
               (\f. ring_mul l (h(c f)) (f x)) = ring_0 l
             ==> !f. f IN group_carrier(galois_group(k,l) h)
                     ==> c f = ring_0 k)
        ==> (!f g. f IN group_carrier(galois_group(k,l) h) /\
                   g IN group_carrier(galois_group(k,l) h) /\ f x = g x
                   ==> f = g) /\
            ring_basis (k,l) h
              (IMAGE (\f. f x) (group_carrier(galois_group(k,l) h))) /\
            (!y. y IN ring_carrier l
                 ==> ?c. (!f. f IN group_carrier(galois_group(k,l) h)
                              ==> c f IN ring_carrier k) /\
                         y = ring_sum l (group_carrier(galois_group(k,l) h))
                               (\f. ring_mul l (h(c f)) (f x)))"
   (← do
    let t1 ← TAUT (← q r"(~p ==> F) ==> p")
    pure (REPEAT GEN_TAC THEN
    ABBREV_TAC (← q r"G = group_carrier(galois_group(k,l) (h:A->B))") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ind")))) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_0) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_1) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_NEG) THEN
    SUBGOAL_THEN
     (← q r"FINITE(G:(B->B)->bool) /\ CARD G = extension_degree(k,l) (h:A->B)")
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "G" THEN ASM_SIMP_TAC [FINITE_GALOIS_GROUP] THEN
      ASM_MESON_TAC [GALOIS_EXTENSION_EQ_CARD],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"(!f y. f IN G /\ y IN ring_carrier l ==> (f:B->B) y IN ring_carrier l) /\
      (!c. c IN ring_carrier k ==> (h:A->B) c IN ring_carrier l)")
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "G" THEN REWRITE_TAC [GALOIS_GROUP_IN_CARRIER] THEN
      ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!f g. f IN G /\ g IN G /\ (f:B->B) x = g x ==> f = g")
    ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q r"f:B->B", ← q r"g:B->B"] THEN STRIP_TAC THEN
      MATCH_MP_TAC t1 THEN DISCH_TAC THEN
      USE_THEN "ind" (MP_TAC o SPEC
       (← q r"\u:B->B. if u = f then ring_1 k
                 else if u = g then ring_neg k (ring_1 k) else ring_0 k:A")) THEN
      REWRITE_TAC [NOT_IMP] THEN REPEAT CONJ_TAC THENL
       [GEN_TAC THEN REPEAT COND_CASES_TAC THEN
        SIMP_TAC [RING_1, RING_NEG, RING_0],
        ALL_TAC,
        DISCH_THEN (MP_TAC o SPEC (← q r"f:B->B")) THEN ASM_REWRITE_TAC [] THEN
        ASM_MESON_TAC [FIELD_NONTRIVIAL]] THEN
      TRANS_TAC EQ_TRANS
       (← q r"ring_sum l G
          (\u. ring_add l (if u = f then (f:B->B) x else ring_0 l)
                          (if u = g then ring_neg l (g x) else ring_0 l))") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"u:B->B") THEN DISCH_TAC THEN
        REWRITE_TAC [] THEN
        ASM_CASES_TAC (← q r"u:B->B = f") THEN ASM_REWRITE_TAC [] THENL
         [ASM_SIMP_TAC [RING_MUL_LID, RING_ADD_RZERO, RING_1],
          ALL_TAC] THEN
        ASM_CASES_TAC (← q r"u:B->B = g") THEN ASM_REWRITE_TAC [] THENL
         [ASM_SIMP_TAC [RING_1, RING_MUL_LNEG, RING_MUL_LID,
                        RING_ADD_LZERO, RING_NEG],
          ASM_SIMP_TAC [RING_MUL_LZERO, RING_ADD_LZERO, RING_0]],
        ALL_TAC] THEN
      wPart lhand (fun t => do lhand (← rand t)) RING_SUM_ADD THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN GEN_TAC THEN DISCH_TAC THEN
        REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC [RING_0, RING_NEG],
        DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC [RING_SUM_DELTA] THEN
      ASM_SIMP_TAC [RING_ADD_RNEG, RING_NEG],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN
     (← q r"ring_independent (k,l) (h:A->B) (IMAGE (\f:B->B. f x) G)")
    ASSUME_TAC THENL
     [ASM_SIMP_TAC [RING_INDEPENDENT_FINITE, FINITE_IMAGE] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC [SUBSET, FORALL_IN_IMAGE], ALL_TAC] THEN
      X_GEN_TAC (← q r"c:B->A") THEN REWRITE_TAC [FORALL_IN_IMAGE] THEN STRIP_TAC THEN
      USE_THEN "ind" (MP_TAC o BETA_RULE o SPEC (← q r"\f:B->B. (c:B->A)(f x)")) THEN
      ANTS_TAC THENL [ALL_TAC, SIMP_TAC []] THEN
      ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC
       (← q r"ring_sum l (IMAGE (\f:B->B. f x) G) (\y. ring_mul l (h((c:B->A) y)) y) =
        ring_0 l") THEN
      wPart (fun t => do lhand (← lhand t)) (fun t => do lhand (← rand t)) RING_SUM_IMAGE THEN
      ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC [o_DEF],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"ring_basis (k,l) (h:A->B) (IMAGE (\f:B->B. f x) G)")
    ASSUME_TAC THENL
     [ASM_SIMP_TAC [← GSYM RING_MATROID_BASIS] THEN
      MATCH_MP_TAC MATROID_BASIS_LARGE_INDEPENDENT THEN
      ASM_SIMP_TAC [RING_MATROID_INDEPENDENT] THEN CONJ_TAC THENL
       [ASM_MESON_TAC [FINITE_EXTENSION_RING_MATROID], ALL_TAC] THEN
      MP_TAC (← ISPECL [← q r"\f:B->B. f x", ← q r"G:(B->B)->bool"] CARD_IMAGE_INJ) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN
       (← q r"matroid_finite_dimensional (ring_matroid (k,l) (h:A->B))")
      MP_TAC THENL
       [ASM_MESON_TAC [FINITE_EXTENSION_RING_MATROID], ALL_TAC] THEN
      SIMP_TAC [extension_degree, LE_REFL],
      ASM_REWRITE_TAC []] THEN
    X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN
    MP_TAC (← ASSUME (← q r"ring_basis (k,l) (h:A->B) (IMAGE (\f:B->B. f x) G)")) THEN
    REWRITE_TAC [ring_basis, ring_spanning] THEN
    DISCH_THEN (MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring",
                      ← q r"IMAGE (\f:B->B. f x) G"] RING_SPAN_FINITE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [FINITE_IMAGE, SUBSET, FORALL_IN_IMAGE],
      DISCH_THEN SUBST1_TAC] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"y:B") o GEN_REWRITE_RULE I [EXTENSION]) THEN
    ASM_REWRITE_TAC [IN_ELIM_THM, FORALL_IN_IMAGE] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c:B->A") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"\f:B->B. (c:B->A)(f x)") THEN ASM_REWRITE_TAC [] THEN
    wPart lhand (fun t => do lhand (← rand t)) RING_SUM_IMAGE THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC [o_DEF]))

  let NORMAL_BASIS_DET_INDEPENDENT ← prove
   r"!(h:A->B) k l x.
        finite_extension(k,l) h /\ x IN ring_carrier l /\
        ~(ring_det l (group_carrier(galois_group(k,l) h))
                     (\f g. (inverse f o g) x) = ring_0 l)
        ==> !c. (!f. f IN group_carrier(galois_group(k,l) h)
                     ==> c f IN ring_carrier k) /\
                ring_sum l (group_carrier(galois_group(k,l) h))
                  (\f. ring_mul l (h(c f)) (f x)) = ring_0 l
                ==> !f. f IN group_carrier(galois_group(k,l) h)
                        ==> c f = ring_0 k"
   (← do
    let t1 ← TAUT (← q r"(~p ==> F) ==> p")
    pure (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_0) THEN
    SUBGOAL_THEN (← q r"FINITE(group_carrier(galois_group(k,l) (h:A->B)))")
    ASSUME_TAC THENL [ASM_SIMP_TAC [FINITE_GALOIS_GROUP], ALL_TAC] THEN
    ABBREV_TAC (← q r"G = group_carrier(galois_group(k,l) (h:A->B))") THEN
    SUBGOAL_THEN
     (← q r"(!f y. f IN G /\ y IN ring_carrier l ==> (f:B->B) y IN ring_carrier l) /\
      (!f. f IN G ==> inverse f IN G) /\
      (!f. f IN G ==> ring_homomorphism(l,l) (f:B->B)) /\
      (!f c. f IN G /\ c IN ring_carrier k ==> f((h:A->B) c) = h c) /\
      (!c. c IN ring_carrier k ==> h c IN ring_carrier l)")
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "G" THEN
      REWRITE_TAC [GALOIS_GROUP_IN_CARRIER, GALOIS_GROUP_INVERSE,
                   GALOIS_GROUP_RING_HOMOMORPHISM, GALOIS_GROUP_FIXES] THEN
      ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER],
      ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC (← q r"c:(B->B)->A") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sum")) THEN
    MATCH_MP_TAC t1 THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"g:B->B") STRIP_ASSUME_TAC o
      REWRITE_RULE [NOT_FORALL_THM, NOT_IMP]) THEN
    UNDISCH_TAC
     (← q r"~(ring_det l G (\f g:B->B. (inverse f o g) (x:B)) = ring_0 l)") THEN
    REWRITE_TAC [] THEN MATCH_MP_TAC RING_DET_DEPENDENT_COLUMNS THEN
    EXISTS_TAC (← q r"\f:B->B. (h:A->B)(c f)") THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, o_THM] THEN CONJ_TAC THENL
     [EXISTS_TAC (← q r"g:B->B") THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC (← q r"~((c:(B->B)->A) g = ring_0 k)") THEN
      REWRITE_TAC [CONTRAPOS_THM] THEN
      UNDISCH_TAC (← q r"(h:A->B)(ring_0 k) = ring_0 l") THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_TAC THEN
      FIRST_ASSUM (MATCH_MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I
        [ring_monomorphism]) THEN
      ASM_SIMP_TAC [RING_0],
      ALL_TAC] THEN
    X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"ring_homomorphism(l,l) (inverse f:B->B)") ASSUME_TAC THENL
     [ASM_SIMP_TAC [], ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     (← q r"inverse f (ring_sum l G (\g:B->B. ring_mul l ((h:A->B)(c g)) (g (x:B)))):B")
    THEN CONJ_TAC THENL
     [MP_TAC (← ISPECL
       [← q r"\g:B->B. ring_mul l ((h:A->B)(c g)) (g (x:B))", ← q r"G:(B->B)->bool"]
       (← MATCH_MP RING_HOMOMORPHISM_SUM
         (← ASSUME (← q r"ring_homomorphism(l,l) (inverse f:B->B)")))) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC [RING_MUL], DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"u:B->B") THEN DISCH_TAC THEN
      REWRITE_TAC [o_THM] THEN
      ASM_SIMP_TAC [← MATCH_MP RING_HOMOMORPHISM_MUL
       (← ASSUME (← q r"ring_homomorphism(l,l) (inverse f:B->B)"))] THEN
      MATCH_MP_TAC RING_MUL_SYM THEN ASM_SIMP_TAC [],
      USE_THEN "sum" SUBST1_TAC THEN
      MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN ASM_REWRITE_TAC []]))

  let NORMAL_BASIS_DETERMINANT ← prove
   r"!(h:A->B) k l x.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        x IN ring_carrier l
        ==> ((!c. (!f. f IN group_carrier(galois_group(k,l) h)
                       ==> c f IN ring_carrier k) /\
                  ring_sum l (group_carrier(galois_group(k,l) h))
                    (\f. ring_mul l (h(c f)) (f x)) = ring_0 l
                  ==> !f. f IN group_carrier(galois_group(k,l) h)
                          ==> c f = ring_0 k) <=>
             ~(ring_det l (group_carrier(galois_group(k,l) h))
                          (\f g. (inverse f o g) x) = ring_0 l))"
   (← do
    pure (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_TAC, ASM_MESON_TAC [NORMAL_BASIS_DET_INDEPENDENT]] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"x:B"]
      NORMAL_BASIS_INDEPENDENT) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (LABEL_TAC "span" o CONJUNCT2 o CONJUNCT2) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    SUBGOAL_THEN (← q r"FINITE(group_carrier(galois_group(k,l) (h:A->B)))")
    ASSUME_TAC THENL [ASM_SIMP_TAC [FINITE_GALOIS_GROUP], ALL_TAC] THEN
    ABBREV_TAC (← q r"G = group_carrier(galois_group(k,l) (h:A->B))") THEN
    SUBGOAL_THEN
     (← q r"(!f y. f IN G /\ y IN ring_carrier l ==> (f:B->B) y IN ring_carrier l) /\
      (!f g. f IN G /\ g IN G ==> f o g IN G) /\
      (!f. f IN G ==> inverse f IN G) /\
      (!f. f IN G ==> ring_homomorphism(l,l) (f:B->B)) /\
      (!f c. f IN G /\ c IN ring_carrier k ==> f((h:A->B) c) = h c) /\
      (!f. f IN G ==> inverse(inverse f) = f) /\
      (!c. c IN ring_carrier k ==> h c IN ring_carrier l)")
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "G" THEN
      REWRITE_TAC [GALOIS_GROUP_IN_CARRIER, GALOIS_GROUP_INVERSE,
                   GALOIS_GROUP_RING_HOMOMORPHISM, GALOIS_GROUP_FIXES,
                   GALOIS_GROUP_COMPOSE] THEN
      ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER, PERMUTES_INVERSE_INVERSE,
                     GALOIS_GROUP_PERMUTES],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!f y. f IN G /\ y IN ring_carrier l ==> (f:B->B) y IN ring_carrier l")
    (LABEL_TAC "gin") THENL [ASM_SIMP_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC [RING_DET_EQ_0_ROWS, FIELD_IMP_INTEGRAL_DOMAIN, o_THM] THEN
    REWRITE_TAC [NOT_EXISTS_THM] THEN X_GEN_TAC (← q r"e:(B->B)->B") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN (← q r"s0:B->B") STRIP_ASSUME_TAC) (LABEL_TAC "rows"))) THEN
    SUBGOAL_THEN
     (← q r"!y. y IN ring_carrier l
          ==> ring_sum l G (\s. ring_mul l ((e:(B->B)->B) s) (inverse s y)) =
              ring_0 l")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN
      USE_THEN "span" (MP_TAC o SPEC (← q r"y:B")) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC [], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"c:(B->B)->A")
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
      TRANS_TAC EQ_TRANS
       (← q r"ring_sum l G
          (\s. ring_sum l G
                 (\t:B->B. ring_mul l ((h:A->B)(c t))
                     (ring_mul l ((e:(B->B)->B) s) (inverse s (t (x:B))))))") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"s:B->B") THEN DISCH_TAC THEN
        REWRITE_TAC [] THEN
        SUBGOAL_THEN (← q r"ring_homomorphism(l,l) (inverse s:B->B)") ASSUME_TAC THENL
         [ASM_SIMP_TAC [], ALL_TAC] THEN
        MP_TAC (← ISPECL
         [← q r"\f:B->B. ring_mul l ((h:A->B)(c f)) (f (x:B))", ← q r"G:(B->B)->bool"]
         (← MATCH_MP RING_HOMOMORPHISM_SUM
           (← ASSUME (← q r"ring_homomorphism(l,l) (inverse s:B->B)")))) THEN
        ANTS_TAC THENL [ASM_SIMP_TAC [RING_MUL], DISCH_THEN SUBST1_TAC] THEN
        wPart lhand (fun t => do rand (← rand t)) RING_SUM_LMUL THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC [o_THM] THEN REPEAT STRIP_TAC THEN
          TRY (USE_THEN "gin" MATCH_MP_TAC) THEN ASM_SIMP_TAC [RING_MUL],
          DISCH_THEN (SUBST1_TAC o SYM)] THEN
        MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"t:B->B") THEN DISCH_TAC THEN
        REWRITE_TAC [o_THM] THEN
        ASM_SIMP_TAC [← MATCH_MP RING_HOMOMORPHISM_MUL
          (← ASSUME (← q r"ring_homomorphism(l,l) (inverse s:B->B)"))] THEN
        SUBGOAL_THEN
         (← q r"(h:A->B)(c(t:B->B)) IN ring_carrier l /\
          (e:(B->B)->B) s IN ring_carrier l /\
          inverse s (t(x:B)) IN ring_carrier l")
        MP_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN
        SPEC_TAC (← q r"(h:A->B)(c(t:B->B))", ← q r"u:B") THEN
        SPEC_TAC (← q r"(e:(B->B)->B) s", ← q r"v:B") THEN
        SPEC_TAC (← q r"inverse (s:B->B) (t(x:B))", ← q r"z:B") THEN
        RING_TAC,
        ALL_TAC] THEN
      wPart lhand (fun t => do lhand (← rand t)) RING_SUM_SWAP THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
        REPEAT (MATCH_MP_TAC RING_MUL THEN CONJ_TAC) THEN
        TRY (USE_THEN "gin" MATCH_MP_TAC) THEN ASM_SIMP_TAC [],
        DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC RING_SUM_EQ_0 THEN X_GEN_TAC (← q r"t:B->B") THEN
      DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN REWRITE_TAC [] THEN
      wPart lhand (fun t => do lhand (← rand t)) RING_SUM_LMUL THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
        REPEAT (MATCH_MP_TAC RING_MUL THEN CONJ_TAC) THEN
        TRY (USE_THEN "gin" MATCH_MP_TAC) THEN ASM_SIMP_TAC [],
        DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "rows" (fun th => tactic_of do
        pure (REWRITE_TAC [← MATCH_MP th (← ASSUME (← q r"(t:B->B) IN G"))])) THEN
      MATCH_MP_TAC RING_MUL_RZERO THEN ASM_SIMP_TAC [],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring",
                      ← q r"\f:B->B. (e:(B->B)->B) (inverse f)"]
      GALOIS_GROUP_INDEPENDENT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL [ASM_SIMP_TAC [], ALL_TAC] THEN
      X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        pure (GEN_REWRITE_TAC RAND_CONV
          [← SYM (← MATCH_MP th (← ASSUME (← q r"(y:B) IN ring_carrier l")))])) THEN
      MATCH_MP_TAC RING_SUM_EQ_GENERAL_INVERSES THEN
      MAP_EVERY EXISTS_TAC
       [← q r"inverse:(B->B)->(B->B)", ← q r"inverse:(B->B)->(B->B)"] THEN
      ASM_SIMP_TAC [],
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"inverse s0:B->B")) THEN ASM_SIMP_TAC []]))

  -- @@RETURN BEGIN
  return { NORMAL_BASIS_INDEPENDENT, NORMAL_BASIS_DET_INDEPENDENT,
           NORMAL_BASIS_DETERMINANT }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- The two cases of the proof: cyclic Galois groups (any base field, in      -/
/- particular finite fields, through the cyclic vector theorem) and infinite -/
/- base fields (through the determinant of a polynomial array).              -/
/- ------------------------------------------------------------------------- -/

structure NormalBasisCyclic where
  -- @@FIELDS
  NORMAL_BASIS_CYCLIC : thm
  deriving Inhabited

@[nospecialize]
def setupNormalBasisCyclic [HolBase] (D : NormalBasisDeps) (BNormalElements : NormalElements) :
    ExceptT String IO NormalBasisCyclic := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, NUMBER_RULE, SELECT_CONV, .. } := D
  let { CARD_EQ_0, CONG_IMP_EQ, CYCLIC_VECTOR_EXISTS, EQ_TRANS,
        FINITE_CYCLIC_GROUP_POWERS, FINITE_GALOIS_GROUP, FINITE_IMP_FIELD_EXTENSION,
        FORALL_IN_IMAGE, GALOIS_GROUP, GALOIS_GROUP_FIXES, GALOIS_GROUP_I,
        GALOIS_GROUP_INDEPENDENT, GALOIS_GROUP_IN_CARRIER,
        GALOIS_GROUP_RING_HOMOMORPHISM, GROUP_POW, IN_ELIM_THM, IN_IMAGE, ITER, I_THM,
        LT_NZ, MEMBER_NOT_EMPTY, RING_0, RING_1, RING_HOMOMORPHISM_0,
        RING_HOMOMORPHISM_1, RING_HOMOMORPHISM_ADD, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_MUL, RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_MUL_LID,
        RING_MUL_LZERO, RING_SUM_CYCLIC_GROUP, RING_SUM_DELTA, RING_SUM_EQ,
        cyclic_group, field_extension, group_pow, o_THM, ring_monomorphism, .. } := D.core1
  let { NORMAL_BASIS_INDEPENDENT, .. } := BNormalElements
  -- @@SCOPE END

  let NORMAL_BASIS_CYCLIC ← prove
   r"!(h:A->B) k l.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        cyclic_group(galois_group(k,l) h)
        ==> ?x. x IN ring_carrier l /\
                (!y. y IN ring_carrier l
                     ==> ?c. (!f. f IN group_carrier(galois_group(k,l) h)
                                  ==> c f IN ring_carrier k) /\
                             y = ring_sum l (group_carrier(galois_group(k,l) h))
                                   (\f. ring_mul l (h(c f)) (f x))) /\
                (!c. (!f. f IN group_carrier(galois_group(k,l) h)
                          ==> c f IN ring_carrier k) /\
                     ring_sum l (group_carrier(galois_group(k,l) h))
                       (\f. ring_mul l (h(c f)) (f x)) = ring_0 l
                     ==> !f. f IN group_carrier(galois_group(k,l) h)
                             ==> c f = ring_0 k)"
   (← do
    let n1 ← NUMBER_RULE (← q r"(n == 0) (mod n)")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"s:B->B") STRIP_ASSUME_TAC o
      GEN_REWRITE_RULE I [cyclic_group]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_0) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_1) THEN
    SUBGOAL_THEN
     (← q r"!c. c IN ring_carrier k ==> (h:A->B) c IN ring_carrier l")
    (LABEL_TAC "hin") THENL
     [ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"FINITE(group_carrier(galois_group(k,l) (h:A->B)))")
    ASSUME_TAC THENL [ASM_SIMP_TAC [FINITE_GALOIS_GROUP], ALL_TAC] THEN
    ABBREV_TAC (← q r"n = CARD(group_carrier(galois_group(k,l) (h:A->B)))") THEN
    SUBGOAL_THEN (← q r"~(n = 0)") ASSUME_TAC THENL
     [EXPAND_TAC "n" THEN ASM_SIMP_TAC [CARD_EQ_0] THEN
      REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC (← q r"I:B->B") THEN REWRITE_TAC [GALOIS_GROUP_I],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"galois_group(k,l) (h:A->B)", ← q r"s:B->B"]
      FINITE_CYCLIC_GROUP_POWERS) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "img") (LABEL_TAC "pw")) THEN
    SUBGOAL_THEN
     (← q r"!i y. ITER i (s:B->B) y = group_pow (galois_group(k,l) (h:A->B)) s i y")
    ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_REWRITE_TAC [ITER, group_pow, GALOIS_GROUP, I_THM,
                                       o_THM],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!i. group_pow (galois_group(k,l) (h:A->B)) s i IN
          group_carrier(galois_group(k,l) h)")
    ASSUME_TAC THENL [ASM_SIMP_TAC [GROUP_POW], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!i y. y IN ring_carrier l
            ==> group_pow (galois_group(k,l) (h:A->B)) s i y IN ring_carrier l")
    ASSUME_TAC THENL [ASM_MESON_TAC [GALOIS_GROUP_IN_CARRIER], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!i j. i < n /\ j < n /\
            group_pow (galois_group(k,l) (h:A->B)) s i =
            group_pow (galois_group(k,l) h) s j
            ==> i = j")
    (LABEL_TAC "inj") THENL
     [USE_THEN "pw" (fun th => REWRITE_TAC [th]) THEN MESON_TAC [CONG_IMP_EQ],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"group_pow (galois_group(k,l) (h:A->B)) s n = I")
    ASSUME_TAC THENL
     [USE_THEN "pw" (MP_TAC o SPECL [← q r"n:num", ← q r"0"]) THEN
      REWRITE_TAC [n1] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [group_pow, GALOIS_GROUP],
      REMOVE_THEN "pw" (K ALL_TAC : thm → tactic)] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"s:B->B",
                      ← q r"n:num", ← q r"\i. if i = 0 then ring_1 k else ring_0 k:A"]
      CYCLIC_VECTOR_EXISTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC [GALOIS_GROUP_IN_CARRIER],
        ASM_MESON_TAC [GALOIS_GROUP_RING_HOMOMORPHISM, RING_HOMOMORPHISM_ADD],
        MP_TAC (← ISPECL [← q r"h:A->B", ← q r"s:B->B", ← q r"k:A ring", ← q r"l:B ring"]
          GALOIS_GROUP_RING_HOMOMORPHISM) THEN
        ASM_REWRITE_TAC [] THEN
        DISCH_THEN (fun th => tactic_of do
          pure (ASM_SIMP_TAC [← MATCH_MP RING_HOMOMORPHISM_MUL th])) THEN
        REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        ASM_MESON_TAC [GALOIS_GROUP_FIXES],
        GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [RING_0, RING_1],
        X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN ASM_REWRITE_TAC [I_THM] THEN
        CONV_TAC SYM_CONV THEN
        TRANS_TAC EQ_TRANS
         (← q r"ring_sum l {i | i < n} (\i. if i = 0 then y else ring_0 l):B") THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC (← q r"i:num") THEN
          REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
          COND_CASES_TAC THEN
          ASM_REWRITE_TAC [group_pow, GALOIS_GROUP, I_THM] THEN
          ASM_SIMP_TAC [RING_MUL_LID, RING_MUL_LZERO],
          ASM_REWRITE_TAC [RING_SUM_DELTA, IN_ELIM_THM, LT_NZ]],
        X_GEN_TAC (← q r"c:num->A") THEN
        DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "cin") (LABEL_TAC "zero")) THEN
        SUBGOAL_THEN
         (← q r"!f. f IN group_carrier(galois_group(k,l) (h:A->B))
              ==> (@i. i < n /\ group_pow (galois_group(k,l) h) s i = f) < n /\
                  group_pow (galois_group(k,l) h) s
                    (@i. i < n /\ group_pow (galois_group(k,l) h) s i = f) = f")
        (LABEL_TAC "sel") THENL
         [X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN CONV_TAC SELECT_CONV THEN
          UNDISCH_TAC (← q r"(f:B->B) IN group_carrier(galois_group(k,l) (h:A->B))") THEN
          USE_THEN "img"
           (fun th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
          REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN MESON_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN
         (← q r"!i. i < n
              ==> (@j. j < n /\ group_pow (galois_group(k,l) (h:A->B)) s j =
                                group_pow (galois_group(k,l) h) s i) = i")
        (LABEL_TAC "selid") THENL
         [X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
          USE_THEN "sel" (MP_TAC o SPEC
            (← q r"group_pow (galois_group(k,l) (h:A->B)) s i")) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC [], STRIP_TAC] THEN
          USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
          ALL_TAC] THEN
        MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring",
          ← q r"\f. (h:A->B)(c(@i. i < n /\
                           group_pow (galois_group(k,l) (h:A->B)) s i = f))"]
          GALOIS_GROUP_INDEPENDENT) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
           [X_GEN_TAC (← q r"f:B->B") THEN DISCH_TAC THEN
            USE_THEN "hin" MATCH_MP_TAC THEN USE_THEN "cin" MATCH_MP_TAC THEN
            USE_THEN "sel" (MP_TAC o SPEC (← q r"f:B->B")) THEN
            ANTS_TAC THENL [ASM_REWRITE_TAC [], SIMP_TAC []],
            ALL_TAC] THEN
          X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN
          MP_TAC (← ISPECL [← q r"galois_group(k,l) (h:A->B)", ← q r"s:B->B", ← q r"l:B ring"]
            RING_SUM_CYCLIC_GROUP) THEN
          ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
          USE_THEN "zero" (MP_TAC o SPEC (← q r"y:B")) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC [], ASM_REWRITE_TAC []] THEN
          DISCH_THEN (SUBST1_TAC o SYM) THEN
          MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC [IN_ELIM_THM],
          DISCH_TAC] THEN
        X_GEN_TAC (← q r"i:num") THEN DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC
          (← q r"group_pow (galois_group(k,l) (h:A->B)) s i")) THEN
        ASM_SIMP_TAC [] THEN
        UNDISCH_TAC (← q r"(h:A->B)(ring_0 k) = ring_0 l") THEN
        DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_TAC THEN
        FIRST_ASSUM (MATCH_MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I
          [ring_monomorphism]) THEN
        ASM_SIMP_TAC [RING_0]],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"z:B")
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "z"))) THEN
    SUBGOAL_THEN
     (← q r"!c. (!f. f IN group_carrier(galois_group(k,l) (h:A->B))
               ==> c f IN ring_carrier k) /\
          ring_sum l (group_carrier(galois_group(k,l) h))
            (\f. ring_mul l (h(c f)) (f z)) = ring_0 l
          ==> !f. f IN group_carrier(galois_group(k,l) h) ==> c f = ring_0 k")
    ASSUME_TAC THENL
     [X_GEN_TAC (← q r"c:(B->B)->A") THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      MP_TAC (← ISPECL [← q r"galois_group(k,l) (h:A->B)", ← q r"s:B->B", ← q r"l:B ring"]
        RING_SUM_CYCLIC_GROUP) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
      DISCH_TAC THEN
      USE_THEN "z" (MP_TAC o SPEC
        (← q r"\i. (c:(B->B)->A)(group_pow (galois_group(k,l) (h:A->B)) s i)")) THEN
      REWRITE_TAC [] THEN ANTS_TAC THENL
       [ASM_SIMP_TAC [], DISCH_TAC] THEN
      ASM_REWRITE_TAC [FORALL_IN_IMAGE, IN_ELIM_THM],
      ALL_TAC] THEN
    EXISTS_TAC (← q r"z:B") THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"z:B"]
      NORMAL_BASIS_INDEPENDENT) THEN
    ASM_REWRITE_TAC [] THEN SIMP_TAC []))

  -- @@RETURN BEGIN
  return { NORMAL_BASIS_CYCLIC }
  -- @@RETURN END


structure NormalBasisInfinite where
  -- @@FIELDS
  NORMAL_BASIS_INFINITE : thm
  deriving Inhabited

@[nospecialize]
def setupNormalBasisInfinite [HolBase] (D : NormalBasisDeps) (BNormalElements : NormalElements) :
    ExceptT String IO NormalBasisInfinite := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, TAUT, .. } := D
  let { EQ_SYM_EQ, FIELD_IMP_INTEGRAL_DOMAIN, FINITE_DELETE, FINITE_GALOIS_GROUP,
        FINITE_IMP_FIELD_EXTENSION, FINITE_SUBSET, FORALL_IN_IMAGE,
        GALOIS_GROUP_COMPOSE, GALOIS_GROUP_FIXES, GALOIS_GROUP_I, GALOIS_GROUP_INVERSE,
        GALOIS_GROUP_IN_CARRIER, GALOIS_GROUP_PERMUTES, GALOIS_GROUP_RING_HOMOMORPHISM,
        GALOIS_IMP_SEPARABLE_EXTENSION, INFINITE, INFINITE_IMAGE,
        INTEGRAL_DOMAIN_PRODUCT_EQ_0, IN_DELETE, IN_ELIM_THM, IN_IMAGE, IN_INSERT,
        I_O_ID, I_THM, NOT_EXISTS_THM, PERMUTES_EQ, PERMUTES_INVERSES_o, POLY_CLAUSES,
        POLY_CONST, POLY_EVAL_0, POLY_EVAL_CONST, POLY_EVAL_RING_PRODUCT,
        POLY_EVAL_SUB, POLY_EVAL_VAR, POLY_RING_CLAUSES, POLY_ROOT_BOUND,
        POLY_VAR_UNIV, PRIMITIVE_ELEMENT_THEOREM, RING_DET, RING_DET_DIAGONAL,
        RING_DET_EQ, RING_DET_HOMOMORPHISM,
        RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED, RING_HOMOMORPHISM_IN_CARRIER,
        RING_HOMOMORPHISM_POLY_EVAL, RING_HOMOMORPHISM_PRODUCT, RING_HOMOMORPHISM_SUB,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, RING_POLYNOMIAL_CONST, RING_POLYNOMIAL_VAR,
        RING_PRODUCT, RING_PRODUCT_EQ, RING_PRODUCT_EQ_GENERAL_INVERSES,
        RING_PRODUCT_ZERO, RING_SUB, RING_SUB_EQ_0, RING_SUB_REFL, SUBSET,
        field_extension, o_ASSOC, o_THM, ring_monomorphism, .. } := D.core1
  let { NORMAL_BASIS_DET_INDEPENDENT, NORMAL_BASIS_INDEPENDENT, .. } := BNormalElements
  -- @@SCOPE END

  let NORMAL_BASIS_INFINITE ← prove
   r"!(h:A->B) k l.
        finite_extension(k,l) h /\ galois_extension(k,l) h /\
        INFINITE(ring_carrier k)
        ==> ?x. x IN ring_carrier l /\
                (!y. y IN ring_carrier l
                     ==> ?c. (!f. f IN group_carrier(galois_group(k,l) h)
                                  ==> c f IN ring_carrier k) /\
                             y = ring_sum l (group_carrier(galois_group(k,l) h))
                                   (\f. ring_mul l (h(c f)) (f x))) /\
                (!c. (!f. f IN group_carrier(galois_group(k,l) h)
                          ==> c f IN ring_carrier k) /\
                     ring_sum l (group_carrier(galois_group(k,l) h))
                       (\f. ring_mul l (h(c f)) (f x)) = ring_0 l
                     ==> !f. f IN group_carrier(galois_group(k,l) h)
                             ==> c f = ring_0 k)"
   (← do
    -- right to left: the second TAUT, then the first
    let t2 ← TAUT (← q r"~(p /\ ~q) <=> p ==> q")
    let t1 ← TAUT (← q r"(~p ==> F) ==> p")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    SUBGOAL_THEN (← q r"integral_domain(l:B ring)") ASSUME_TAC THENL
     [ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN], ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"]
      PRIMITIVE_ELEMENT_THEOREM) THEN
    ASM_SIMP_TAC [GALOIS_IMP_SEPARABLE_EXTENSION] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"a:B") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"FINITE(group_carrier(galois_group(k,l) (h:A->B)))")
    ASSUME_TAC THENL [ASM_SIMP_TAC [FINITE_GALOIS_GROUP], ALL_TAC] THEN
    ABBREV_TAC (← q r"G = group_carrier(galois_group(k,l) (h:A->B))") THEN
    SUBGOAL_THEN
     (← q r"(!f y. f IN G /\ y IN ring_carrier l ==> (f:B->B) y IN ring_carrier l) /\
      (!f g. f IN G /\ g IN G ==> f o g IN G) /\
      (!f. f IN G ==> inverse f IN G) /\
      (!f. f IN G ==> ring_homomorphism(l,l) (f:B->B)) /\
      (!f c. f IN G /\ c IN ring_carrier k ==> f((h:A->B) c) = h c) /\
      (!f. f IN G ==> f permutes ring_carrier l) /\
      I IN G /\
      (!c. c IN ring_carrier k ==> h c IN ring_carrier l)")
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "G" THEN
      REWRITE_TAC [GALOIS_GROUP_IN_CARRIER, GALOIS_GROUP_INVERSE, GALOIS_GROUP_I,
                   GALOIS_GROUP_RING_HOMOMORPHISM, GALOIS_GROUP_FIXES,
                   GALOIS_GROUP_COMPOSE, GALOIS_GROUP_PERMUTES] THEN
      ASM_MESON_TAC [RING_HOMOMORPHISM_IN_CARRIER],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!f g. f IN G /\ g IN G /\ (f:B->B) a = g a ==> f = g")
    (LABEL_TAC "pinj") THENL
     [MAP_EVERY X_GEN_TAC [← q r"f:B->B", ← q r"g:B->B"] THEN STRIP_TAC THEN
      MATCH_MP_TAC PERMUTES_EQ THEN EXISTS_TAC (← q r"ring_carrier l:B->bool") THEN
      ASM_SIMP_TAC [] THEN
      MP_TAC (← ISPECL [← q r"f:B->B", ← q r"g:B->B", ← q r"l:B ring", ← q r"l:B ring",
                        ← q r"(a:B) INSERT IMAGE (h:A->B) (ring_carrier k)"]
        RING_HOMOMORPHISMS_EQ_FROM_SUBRING_GENERATED) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC [] THEN REWRITE_TAC [IN_INSERT, IN_IMAGE] THEN
        REPEAT STRIP_TAC THEN ASM_SIMP_TAC [],
        ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!f g. f IN G /\ g IN G ==> (inverse f o g = I <=> (f:B->B) = g)")
    ASSUME_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q r"f:B->B", ← q r"g:B->B"] THEN STRIP_TAC THEN
      MP_TAC (← ISPECL [← q r"f:B->B", ← q r"ring_carrier l:B->bool"] PERMUTES_INVERSES_o) THEN
      ASM_SIMP_TAC [] THEN STRIP_TAC THEN EQ_TAC THENL
       [DISCH_THEN (MP_TAC o AP_TERM (← q r"(o) (f:B->B):(B->B)->(B->B)")) THEN
        ASM_REWRITE_TAC [o_ASSOC, I_O_ID] THEN MESON_TAC [],
        DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    ABBREV_TAC
     (← q r"Q = \p:B->B. ring_product (poly_ring l (:1)) (G DELETE p)
                    (\r:B->B. poly_sub l (poly_var l one)
                                        (poly_const l (r a)))") THEN
    SUBGOAL_THEN
     (← q r"!p:B->B. (Q:(B->B)->(1->num)->B) p IN ring_carrier(poly_ring l (:1))")
    ASSUME_TAC THENL
     [EXPAND_TAC "Q" THEN REWRITE_TAC [RING_PRODUCT], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!p y. y IN ring_carrier l
            ==> poly_eval l ((Q:(B->B)->(1->num)->B) p) y =
                ring_product l (G DELETE p) (\r. ring_sub l y (r a))")
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "Q" THEN REWRITE_TAC [] THEN
      wPart lhand (fun t => do lhand (← rand t)) POLY_EVAL_RING_PRODUCT THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC [FINITE_DELETE, POLY_CLAUSES, RING_SUB, POLY_VAR_UNIV,
                      POLY_CONST, IN_DELETE],
        DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC (← q r"r:B->B") THEN
      REWRITE_TAC [IN_DELETE] THEN STRIP_TAC THEN REWRITE_TAC [] THEN
      ASM_SIMP_TAC [POLY_EVAL_SUB, RING_POLYNOMIAL_VAR, RING_POLYNOMIAL_CONST,
                    POLY_EVAL_VAR, POLY_EVAL_CONST],
      ALL_TAC] THEN
    ABBREV_TAC
     (← q r"P = ring_det (poly_ring l (:1)) G
            (\p q:B->B. (Q:(B->B)->(1->num)->B) (inverse p o q))") THEN
    SUBGOAL_THEN (← q r"(P:(1->num)->B) IN ring_carrier(poly_ring l (:1))")
    ASSUME_TAC THENL [EXPAND_TAC "P" THEN REWRITE_TAC [RING_DET], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!y. y IN ring_carrier l
          ==> poly_eval l (P:(1->num)->B) y =
              ring_det l G (\p q. ring_product l (G DELETE (inverse p o q))
                                    (\r. ring_sub l y (r a)))")
    (LABEL_TAC "Peval") THENL
     [X_GEN_TAC (← q r"y:B") THEN DISCH_TAC THEN EXPAND_TAC "P" THEN
      MP_TAC (← ISPECL [← q r"poly_ring l (:1):((1->num)->B)ring", ← q r"l:B ring",
                        ← q r"\p:(1->num)->B. poly_eval l p y", ← q r"G:(B->B)->bool",
                        ← q r"\p q:B->B. (Q:(B->B)->(1->num)->B) (inverse p o q)"]
        RING_DET_HOMOMORPHISM) THEN
      ASM_SIMP_TAC [RING_HOMOMORPHISM_POLY_EVAL] THEN
      DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(poly_eval l (P:(1->num)->B) a = ring_0 l)") ASSUME_TAC THENL
     [ASM_SIMP_TAC [] THEN
      wPart (fun t => do lhand (← rand t)) (fun t => do lhand (← rand t))
        RING_DET_DIAGONAL THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN MAP_EVERY X_GEN_TAC [← q r"p:B->B", ← q r"q:B->B"] THEN
        STRIP_TAC THEN MATCH_MP_TAC RING_PRODUCT_ZERO THEN
        EXISTS_TAC (← q r"I:B->B") THEN
        ASM_SIMP_TAC [FINITE_DELETE, IN_DELETE, I_THM, RING_SUB_REFL] THEN
        ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN ASM_SIMP_TAC [],
        DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC [INTEGRAL_DOMAIN_PRODUCT_EQ_0, NOT_EXISTS_THM] THEN
      X_GEN_TAC (← q r"p:B->B") THEN
      ASM_CASES_TAC (← q r"(p:B->B) IN G") THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"inverse (p:B->B) o p = I") SUBST1_TAC THENL
       [ASM_SIMP_TAC [], ALL_TAC] THEN
      ASM_SIMP_TAC [INTEGRAL_DOMAIN_PRODUCT_EQ_0, FINITE_DELETE, NOT_EXISTS_THM,
                    IN_DELETE, RING_SUB_EQ_0] THEN
      X_GEN_TAC (← q r"r:B->B") THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"(r:B->B) a = I a") ASSUME_TAC THENL
       [REWRITE_TAC [I_THM] THEN CONV_TAC SYM_CONV THEN
        -- `check (fun th -> is_eq(concl th) && rand(concl th) = `ring_0 l:B`)`:
        -- the quotation is parsed only when the first test passes, as `&&`.
        FIRST_X_ASSUM (fun th => tactic_of do
          let ok ← if is_eq (concl th) then do
              let z ← q r"ring_0 l:B"
              pure (match rand (concl th) with | .ok r => r == z | .error _ => false)
            else pure false
          pure (MP_TAC (← liftExcept (check (fun _ => ok) th)))) THEN
        ASM_SIMP_TAC [RING_SUB_EQ_0],
        ALL_TAC] THEN
      UNDISCH_TAC (← q r"~(r = (I:B->B))") THEN REWRITE_TAC [] THEN
      USE_THEN "pinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(P = ring_0(poly_ring l (:1)):(1->num)->B)") ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC (← q r"~(poly_eval l (P:(1->num)->B) a = ring_0 l)") THEN
      ASM_REWRITE_TAC [POLY_RING_CLAUSES, POLY_EVAL_0],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"l:B ring", ← q r"P:(1->num)->B"] POLY_ROOT_BOUND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC [], DISCH_THEN (ASSUME_TAC o CONJUNCT1)] THEN
    SUBGOAL_THEN
     (← q r"?c. c IN ring_carrier k /\
          ~(poly_eval l (P:(1->num)->B) ((h:A->B) c) = ring_0 l)")
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC t1 THEN
      DISCH_THEN (ASSUME_TAC o REWRITE_RULE [NOT_EXISTS_THM, t2]) THEN
      SUBGOAL_THEN (← q r"INFINITE(IMAGE (h:A->B) (ring_carrier k))") MP_TAC THENL
       [MATCH_MP_TAC INFINITE_IMAGE THEN ASM_MESON_TAC [ring_monomorphism],
        ALL_TAC] THEN
      REWRITE_TAC [INFINITE] THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC
       (← q r"{y | y IN ring_carrier l /\
             poly_eval l (P:(1->num)->B) y = ring_0 l}") THEN
      ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
      ASM_SIMP_TAC [],
      ALL_TAC] THEN
    ABBREV_TAC
     (← q r"w = ring_product l (G DELETE I)
            (\r:B->B. ring_sub l ((h:A->B) c) (r a))") THEN
    SUBGOAL_THEN (← q r"(w:B) IN ring_carrier l") ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN REWRITE_TAC [RING_PRODUCT], ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!p. p IN G
          ==> (p:B->B) w =
              ring_product l (G DELETE p) (\r. ring_sub l ((h:A->B) c) (r a))")
    (LABEL_TAC "conj") THENL
     [X_GEN_TAC (← q r"p:B->B") THEN DISCH_TAC THEN EXPAND_TAC "w" THEN
      SUBGOAL_THEN (← q r"ring_homomorphism(l,l) (p:B->B)") ASSUME_TAC THENL
       [ASM_SIMP_TAC [], ALL_TAC] THEN
      MP_TAC (← ISPECL
       [← q r"\r:B->B. ring_sub l ((h:A->B) c) (r a)", ← q r"G DELETE (I:B->B)"]
       (← MATCH_MP RING_HOMOMORPHISM_PRODUCT
         (← ASSUME (← q r"ring_homomorphism(l,l) (p:B->B)")))) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC [FINITE_DELETE, IN_DELETE, RING_SUB],
        DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC RING_PRODUCT_EQ_GENERAL_INVERSES THEN
      MAP_EVERY EXISTS_TAC
       [← q r"\r:B->B. (p:B->B) o r", ← q r"\r:B->B. inverse (p:B->B) o r"] THEN
      SUBGOAL_THEN (← q r"(p:B->B) o inverse p = I /\ inverse p o p = I")
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC [PERMUTES_INVERSES_o], ALL_TAC] THEN
      REWRITE_TAC [IN_DELETE, o_ASSOC] THEN ASM_REWRITE_TAC [I_O_ID] THEN
      CONJ_TAC THENL
       [X_GEN_TAC (← q r"q:B->B") THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN
        ASM_SIMP_TAC [] THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      X_GEN_TAC (← q r"q:B->B") THEN STRIP_TAC THEN ASM_SIMP_TAC [] THEN
      CONJ_TAC THENL
       [DISCH_THEN (MP_TAC o AP_TERM (← q r"(o) (inverse p:B->B):(B->B)->(B->B)")) THEN
        ASM_REWRITE_TAC [o_ASSOC, I_O_ID],
        ALL_TAC] THEN
      REWRITE_TAC [o_THM] THEN
      ASM_SIMP_TAC [← MATCH_MP RING_HOMOMORPHISM_SUB
        (← ASSUME (← q r"ring_homomorphism(l,l) (p:B->B)"))],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"ring_det l G (\f g:B->B. (inverse f o g) w) =
      poly_eval l (P:(1->num)->B) ((h:A->B) c)")
    ASSUME_TAC THENL
     [USE_THEN "Peval" (MP_TAC o SPEC (← q r"(h:A->B) c")) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC [], DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC RING_DET_EQ THEN
      MAP_EVERY X_GEN_TAC [← q r"f:B->B", ← q r"g:B->B"] THEN STRIP_TAC THEN
      USE_THEN "conj" (MP_TAC o SPEC (← q r"inverse (f:B->B) o (g:B->B)")) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [], SIMP_TAC []],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!d. (!f:B->B. f IN G ==> d f IN ring_carrier k) /\
          ring_sum l G (\f:B->B. ring_mul l ((h:A->B)(d f)) (f (w:B))) =
          ring_0 l
          ==> !f. f IN G ==> d f = ring_0 k")
    ASSUME_TAC THENL
     [MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"w:B"]
        NORMAL_BASIS_DET_INDEPENDENT) THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    EXISTS_TAC (← q r"w:B") THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"w:B"]
      NORMAL_BASIS_INDEPENDENT) THEN
    ASM_REWRITE_TAC [] THEN SIMP_TAC []))

  -- @@RETURN BEGIN
  return { NORMAL_BASIS_INFINITE }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- The normal basis theorem and its forms with ring_basis and free_basis;    -/
/- for finite fields the Galois group is generated by the Frobenius map, so  -/
/- the powers x^(q^i), i < [l:k], of a normal element form a free basis.     -/
/- ------------------------------------------------------------------------- -/

structure NormalBasisTheorem where
  -- @@FIELDS
  NORMAL_BASIS_THEOREM : thm
  NORMAL_BASIS_RING_BASIS : thm
  NORMAL_BASIS_FREE_BASIS : thm
  FINITE_FIELD_NORMAL_BASIS : thm
  deriving Inhabited

@[nospecialize]
def setupNormalBasisTheorem [HolBase] (D : NormalBasisDeps) (BNormalElements : NormalElements) (BNormalBasisCyclic : NormalBasisCyclic) (BNormalBasisInfinite : NormalBasisInfinite) :
    ExceptT String IO NormalBasisTheorem := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, .. } := D
  let { BIJ, CONG_IMP_EQ, CYCLIC_GALOIS_GROUP_FINITE_FIELD, EQ_IMP, EXTENSION,
        FINITE_CYCLIC_GROUP_POWERS, FINITE_FIELD_GALOIS_EXTENSION,
        FINITE_FINITE_FIELD_EXTENSION, FINITE_GALOIS_GROUP, FINITE_IMP_FIELD_EXTENSION,
        FREE_BASIS_FIELD, FUN_EQ_THM, GALOIS_GROUP_FINITE_FIELD,
        GALOIS_GROUP_POW_RING_POW, INFINITE, INJ, IN_ELIM_THM, IN_IMAGE, MONO_EXISTS,
        RING_MONOMORPHISM_IMP_HOMOMORPHISM, SURJ, field_extension, .. } := D.core1
  let { NORMAL_BASIS_INDEPENDENT, .. } := BNormalElements
  let { NORMAL_BASIS_CYCLIC, .. } := BNormalBasisCyclic
  let { NORMAL_BASIS_INFINITE, .. } := BNormalBasisInfinite
  -- @@SCOPE END

  let NORMAL_BASIS_THEOREM ← prove
   r"!(h:A->B) k l.
        finite_extension(k,l) h /\ galois_extension(k,l) h
        ==> ?x. x IN ring_carrier l /\
                (!y. y IN ring_carrier l
                     ==> ?c. (!f. f IN group_carrier(galois_group(k,l) h)
                                  ==> c f IN ring_carrier k) /\
                             y = ring_sum l (group_carrier(galois_group(k,l) h))
                                   (\f. ring_mul l (h(c f)) (f x))) /\
                (!c. (!f. f IN group_carrier(galois_group(k,l) h)
                          ==> c f IN ring_carrier k) /\
                     ring_sum l (group_carrier(galois_group(k,l) h))
                       (\f. ring_mul l (h(c f)) (f x)) = ring_0 l
                     ==> !f. f IN group_carrier(galois_group(k,l) h)
                             ==> c f = ring_0 k)"
   (← do
    pure (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"FINITE(ring_carrier(k:A ring))") THENL
     [MATCH_MP_TAC NORMAL_BASIS_CYCLIC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC CYCLIC_GALOIS_GROUP_FINITE_FIELD THEN
      ASM_MESON_TAC [FINITE_FINITE_FIELD_EXTENSION],
      MATCH_MP_TAC NORMAL_BASIS_INFINITE THEN ASM_REWRITE_TAC [INFINITE]]))

  let NORMAL_BASIS_RING_BASIS ← prove
   r"!(h:A->B) k l.
        finite_extension(k,l) h /\ galois_extension(k,l) h
        ==> ?x. x IN ring_carrier l /\
                ring_basis (k,l) h
                  (IMAGE (\f. f x) (group_carrier(galois_group(k,l) h))) /\
                !f g. f IN group_carrier(galois_group(k,l) h) /\
                      g IN group_carrier(galois_group(k,l) h) /\
                      f x = g x
                      ==> f = g"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"] NORMAL_BASIS_THEOREM) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"x:B") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring", ← q r"x:B"]
      NORMAL_BASIS_INDEPENDENT) THEN
    ASM_REWRITE_TAC [] THEN MESON_TAC []))

  let NORMAL_BASIS_FREE_BASIS ← prove
   r"!(h:A->B) k l.
        finite_extension(k,l) h /\ galois_extension(k,l) h
        ==> ?x. x IN ring_carrier l /\
                !n e. BIJ e {i | i < n} (group_carrier(galois_group(k,l) h))
                      ==> free_basis (k,l) h n (\i. e i x)"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"] NORMAL_BASIS_RING_BASIS) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"x:B") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    MAP_EVERY X_GEN_TAC [← q r"n:num", ← q r"e:num->B->B"] THEN DISCH_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
    FIRST_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
    ASM_SIMP_TAC [FREE_BASIS_FIELD] THEN
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [BIJ]) THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [INJ]) THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [SURJ]) THEN
    REWRITE_TAC [IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
     [SUBGOAL_THEN
       (← q r"IMAGE (\i. (e:num->B->B) i x) {i | i < n} =
        IMAGE (\f. f x) (group_carrier(galois_group(k,l) (h:A->B)))")
       (fun th => ASM_REWRITE_TAC [th]) THEN
      REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN ASM_MESON_TAC [],
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC []]))

  let FINITE_FIELD_NORMAL_BASIS ← prove
   r"!(h:A->B) k l.
        field_extension(k,l) h /\ FINITE(ring_carrier l)
        ==> ?x. x IN ring_carrier l /\
                free_basis (k,l) h (extension_degree(k,l) h)
                  (\i. ring_pow l x (CARD(ring_carrier k) EXP i))"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"]
      FINITE_FIELD_GALOIS_EXTENSION) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"]
      GALOIS_GROUP_FINITE_FIELD) THEN
    ASM_REWRITE_TAC [] THEN
    ABBREV_TAC
     (← q r"s = \x. if x IN ring_carrier l
              then ring_pow l x (CARD(ring_carrier k:A->bool)) else x:B") THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"h:A->B", ← q r"k:A ring", ← q r"l:B ring"] NORMAL_BASIS_FREE_BASIS) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"x:B") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
     [← q r"extension_degree(k,l) (h:A->B)",
      ← q r"group_pow (galois_group(k,l) (h:A->B)) s"]) THEN
    ANTS_TAC THENL
     [MP_TAC (← ISPECL [← q r"galois_group(k,l) (h:A->B)", ← q r"s:B->B"]
        FINITE_CYCLIC_GROUP_POWERS) THEN
      ASM_SIMP_TAC [FINITE_GALOIS_GROUP] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [BIJ, INJ, SURJ, IN_ELIM_THM] THEN
      REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN MESON_TAC [CONG_IMP_EQ],
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"i:num") THEN
      EXPAND_TAC "s" THEN REWRITE_TAC [GALOIS_GROUP_POW_RING_POW] THEN
      ASM_REWRITE_TAC []]))

  -- @@RETURN BEGIN
  return { NORMAL_BASIS_THEOREM, NORMAL_BASIS_RING_BASIS, NORMAL_BASIS_FREE_BASIS,
           FINITE_FIELD_NORMAL_BASIS }
  -- @@RETURN END

end HolLibrary.NormalBasis
