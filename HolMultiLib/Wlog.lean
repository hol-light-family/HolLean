/- ========================================================================= -/
/- Geometric "without loss of generality" tactics to pick convenient coords. -/
/- ========================================================================= -/
/- File: HolMultiLib/Wlog.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/wlog.ml`, in the style of
  HolMultiLib/Convex.lean: pure, the proofs, rules and tactics translated by
  hand, one `let` per OCaml `let`, in file order.  The load-time effects
  (`add_translation_invariants`, `add_linear_invariants`) are at their file
  positions.  wlog.ml needs determinants.ml and convex.ml, so it is given
  convex.ml's `ConvexDeps`, the four determinants.ml/vectors.ml procedures it
  calls, and the further theorems in `WlogThms`; SessionMultiLib/Wlog.lean
  supplies them.
-/

import HolMultiLib.Convex

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.Wlog

/-- The theorems wlog.ml uses that convex.ml's deps do not carry. -/
structure WlogThms where
  (AFFINE_HULL_INSERT_SPAN AFFINE_HULL_LINEAR_IMAGE COLLINEAR_LINEAR_IMAGE_EQ
   ORTHOGONAL_TRANSFORMATION_INVERSE ORTHOGONAL_TRANSFORMATION_SURJECTIVE ROTATION_EXISTS
   ROTATION_LOWDIM_HORIZONTAL LTE_ANTISYM COLLINEAR_3 DIM_INJECTIVE_LINEAR_IMAGE DOT_3
   INDEPENDENT_BOUND_GENERAL QUANTIFY_SURJECTION_THM SPAN_BREAKDOWN_EQ SPAN_LINEAR_IMAGE : thm)
  deriving Inhabited

structure WlogDeps where
  cvx : HolMultiLib.Convex.ConvexDeps
  /-- vectors.ml's `EXPAND_QUANTS_CONV`. -/
  EXPAND_QUANTS_CONV : thm → ExceptT String IO ioconv
  /-- determinants.ml's `EXISTS_GENVAR_RULE`. -/
  EXISTS_GENVAR_RULE : thm → ExceptT String IO thm
  /-- determinants.ml's `TRANSLATION_INVARIANTS`. -/
  TRANSLATION_INVARIANTS : term → ExceptT String IO thm
  /-- determinants.ml's `LINEAR_INVARIANTS`. -/
  LINEAR_INVARIANTS : term → List thm → ExceptT String IO thm
  thms : WlogThms

/-- OCaml's `itlist` for a function with effects. -/
def itlistIO {α β : Type} (f : α → β → ExceptT String IO β) :
    List α → β → ExceptT String IO β
  | [], b => pure b
  | h :: t, b => do f h (← itlistIO f t b)

/- ------------------------------------------------------------------------- -/
/- Flyspeck definition of plane, and its invariance theorems; rotating and   -/
/- translating so a given plane in R^3 becomes {x | x$3 = &0}; apply plane   -/
/- rotation to a goal; injection from real^2 -> real^3 plane with zero last  -/
/- coordinate; apply 3D->2D conversion to a goal; rotating so a given line   -/
/- from the origin becomes the x-axis.  (wlog.ml 8-389)                      -/
/- ------------------------------------------------------------------------- -/

structure WLG where
  plane : thm
  PLANE_TRANSLATION_EQ : thm
  PLANE_TRANSLATION : thm
  PLANE_LINEAR_IMAGE_EQ : thm
  PLANE_LINEAR_IMAGE : thm
  ROTATION_PLANE_HORIZONTAL : thm
  ROTATION_HORIZONTAL_PLANE : thm
  GEOM_HORIZONTAL_PLANE_RULE : term → ExceptT String IO thm
  GEOM_HORIZONTAL_PLANE_TAC : term → tactic
  pad2d3d : thm
  FORALL_PAD2D3D_THM : thm
  QUANTIFY_PAD2D3D_THM : thm
  LINEAR_PAD2D3D : thm
  INJECTIVE_PAD2D3D : thm
  NORM_PAD2D3D : thm
  PAD2D3D_QUANTIFY_CONV : ioconv
  PAD2D3D_TAC : tactic
  ROTATION_HORIZONTAL_LINE : thm
  GEOM_HORIZONTAL_LINE_RULE : term → ExceptT String IO thm
  GEOM_HORIZONTAL_LINE_TAC : term → tactic
  deriving Inhabited

@[nospecialize]
def setupWLG [HolBase] (D : WlogDeps) : ExceptT String IO WLG := do
  -- @@SCOPE BEGIN
  let { new_definition, ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC,
        REAL_ARITH_TAC, REAL_RING, SET_RULE, SET_TAC, VECTOR_ARITH, add_linear_invariants,
        add_translation_invariants, GEOM_TRANSLATE_TAC, .. } := D.cvx
  let { EXPAND_QUANTS_CONV, EXISTS_GENVAR_RULE, TRANSLATION_INVARIANTS,
        LINEAR_INVARIANTS, .. } := D
  let { FORALL_SIMP, .. } := HolBase.T
  let { ARITH, CARD_CLAUSES, CART_EQ, CONTRAPOS_THM, DIMINDEX_2, DIMINDEX_3, DIMINDEX_GE_1,
        EQ_IMP, EQ_TRANS, EXISTS_IN_IMAGE, EXISTS_OR_THM, EXTENSION, FINITE_RULES, .. } :=
    D.cvx.core1
  let { IMAGE_CLAUSES, IMAGE_ID, IMAGE_SUBSET, IMAGE_o, INSERT_AC, .. } := D.cvx.core2
  let { IN_ELIM_THM, IN_IMAGE, IN_INSERT, IN_SING, IN_UNIV, LAMBDA_BETA, LEFT_IMP_EXISTS_THM,
        LET_TRANS, LE_REFL, LE_TRANS, LT_IMP_LE, LT_REFL, MONO_EXISTS, MONO_FORALL,
        NOT_IN_EMPTY, .. } := D.cvx.core3
  let { REAL_MUL_RID, REAL_MUL_RZERO, RIGHT_AND_EXISTS_THM, RIGHT_OR_DISTRIB,
        SUBSET_TRANS, .. } := D.cvx.core5
  let { SUBSET_UNIV, UNWIND_THM2, o_DEF, o_THM, .. } := D.cvx.core6
  let { HULL_SUBSET, .. } := D.cvx.misc
  let { BASIS_COMPONENT, COLLINEAR_2, COLLINEAR_LEMMA, DIM_EQ_SPAN, DIM_LE_CARD, DIM_SPAN,
        DIM_UNIV, DOT_2, .. } := D.cvx.vec1
  let { LINEAR_0, MATRIX_COMPOSE, MATRIX_ID, NORM_BASIS, NORM_EQ, .. } := D.cvx.vec2
  let { NORM_MUL, REAL_ABS_NORM, SPAN_EMPTY, SPAN_EQ_SELF, SPAN_INC, SPAN_UNIV, VECTOR_3, .. } :=
    D.cvx.vec3
  let { VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, VECTOR_SUB_EQ, VEC_COMPONENT, dependent,
        independent, linear, subspace, .. } := D.cvx.vec4
  let { DET_I, DET_MUL, ORTHOGONAL_TRANSFORMATION, ORTHOGONAL_TRANSFORMATION_ID,
        ORTHOGONAL_TRANSFORMATION_INJECTIVE, ORTHOGONAL_TRANSFORMATION_LINEAR, .. } := D.cvx.det
  let { AFFINE_HULL_INSERT_SPAN, AFFINE_HULL_LINEAR_IMAGE, COLLINEAR_LINEAR_IMAGE_EQ,
        ORTHOGONAL_TRANSFORMATION_INVERSE, ORTHOGONAL_TRANSFORMATION_SURJECTIVE,
        ROTATION_EXISTS, ROTATION_LOWDIM_HORIZONTAL, LTE_ANTISYM, COLLINEAR_3,
        DIM_INJECTIVE_LINEAR_IMAGE, DOT_3, INDEPENDENT_BOUND_GENERAL, QUANTIFY_SURJECTION_THM,
        SPAN_BREAKDOWN_EQ, SPAN_LINEAR_IMAGE, .. } := D.thms
  -- @@SCOPE END

  -- Flyspeck definition of plane, and its invariance theorems.

  let plane ← new_definition
   r"plane x = (?u v w. ~(collinear {u,v,w}) /\ x = affine hull {u,v,w})"

  let PLANE_TRANSLATION_EQ ← prove
   r"!a:real^N s. plane(IMAGE (\x. a + x) s) <=> plane s"
   (REWRITE_TAC [plane] THEN GEOM_TRANSLATE_TAC [])

  let PLANE_TRANSLATION ← prove
   r"!a:real^N s. plane s ==> plane(IMAGE (\x. a + x) s)"
   (REWRITE_TAC [PLANE_TRANSLATION_EQ])

  add_translation_invariants [PLANE_TRANSLATION_EQ]

  let PLANE_LINEAR_IMAGE_EQ ← prove
   r"!f:real^M->real^N p.
          linear f /\ (!x y. f x = f y ==> x = y)
          ==> (plane(IMAGE f p) <=> plane p)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [plane] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     (← q r"?u. u IN IMAGE f (:real^M) /\
          ?v. v IN IMAGE f (:real^M) /\
              ?w. w IN IMAGE (f:real^M->real^N) (:real^M) /\
                  ~collinear {u, v, w} /\ IMAGE f p = affine hull {u, v, w}") THEN
    CONJ_TAC THENL
     [REWRITE_TAC [RIGHT_AND_EXISTS_THM, IN_IMAGE, IN_UNIV] THEN
      REPEAT (AP_TERM_TAC THEN ABS_TAC) THEN
      EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"{u,v,w} SUBSET IMAGE (f:real^M->real^N) p") MP_TAC THENL
       [ASM_REWRITE_TAC [HULL_SUBSET], SET_TAC []],
      REWRITE_TAC [EXISTS_IN_IMAGE, IN_UNIV] THEN
      REWRITE_TAC [← SET_RULE (← q r"{f a,f b,f c} = IMAGE f {a,b,c}")] THEN
      ASM_SIMP_TAC [AFFINE_HULL_LINEAR_IMAGE] THEN
      REPEAT (AP_TERM_TAC THEN ABS_TAC) THEN BINOP_TAC THENL
       [ASM_MESON_TAC [COLLINEAR_LINEAR_IMAGE_EQ], ASM SET_TAC []]])

  let PLANE_LINEAR_IMAGE ← prove
   r"!f:real^M->real^N p.
          linear f /\ plane p /\ (!x y. f x = f y ==> x = y)
          ==> plane(IMAGE f p)"
   (MESON_TAC [PLANE_LINEAR_IMAGE_EQ])

  add_linear_invariants [PLANE_LINEAR_IMAGE_EQ]

  -- Rotating and translating so a given plane in R^3 becomes {x | x$3 = &0}.

  let ROTATION_PLANE_HORIZONTAL ← do
    let lemma ← prove
     r"span {z:real^3 | z$3 = &0} = {z:real^3 | z$3 = &0}"
     (REWRITE_TAC [SPAN_EQ_SELF, subspace, IN_ELIM_THM] THEN
      SIMP_TAC [VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, VEC_COMPONENT,
                DIMINDEX_3, ARITH] THEN REAL_ARITH_TAC)
    prove
     r"!s. plane s
           ==>  ?a f. orthogonal_transformation f /\ det(matrix f) = &1 /\
                      IMAGE f (IMAGE (\x. a + x) s) = {z:real^3 | z$3 = &0}"
     (REPEAT STRIP_TAC THEN
      FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE id [plane]) THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q r"a:real^3", ← q r"b:real^3", ← q r"c:real^3"] THEN
      MAP_EVERY (fun t =>
        ASM_CASES_TAC t THENL [ASM_REWRITE_TAC [COLLINEAR_2, INSERT_AC],
                               ALL_TAC])
       [← q r"a:real^3 = b", ← q r"a:real^3 = c", ← q r"b:real^3 = c"] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
      ASM_SIMP_TAC [AFFINE_HULL_INSERT_SPAN, IN_INSERT, NOT_IN_EMPTY] THEN
      EXISTS_TAC (← q r"--a:real^3") THEN
      REWRITE_TAC [← SET_RULE (← q r"IMAGE (\x:real^3. --a + x) {a + x | x | x IN s} =
                            IMAGE (\x. --a + a + x) s")] THEN
      REWRITE_TAC [← VECTOR_ARITH (← q r"--a + a + x:real^3 = x"), IMAGE_ID] THEN
      REWRITE_TAC [← SET_RULE (← q r"{x - a:real^x | x = b \/ x = c} = {b - a,c - a}")] THEN
      MP_TAC (← ISPEC (← q r"span{b - a:real^3,c - a}")
        ROTATION_LOWDIM_HORIZONTAL) THEN
      REWRITE_TAC [DIMINDEX_3] THEN ANTS_TAC THENL
       [MATCH_MP_TAC LET_TRANS THEN
        EXISTS_TAC (← q r"CARD{b - a:real^3,c - a}") THEN
        SIMP_TAC [DIM_SPAN, DIM_LE_CARD, FINITE_RULES] THEN
        SIMP_TAC [CARD_CLAUSES, FINITE_RULES] THEN ARITH_TAC,
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"f:real^3->real^3") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
      ASM_SIMP_TAC [← GSYM SPAN_LINEAR_IMAGE] THEN
      GEN_REWRITE_TAC RAND_CONV [← GSYM lemma] THEN
      MATCH_MP_TAC DIM_EQ_SPAN THEN CONJ_TAC THENL
       [ASM_MESON_TAC [IMAGE_SUBSET, SPAN_INC, SUBSET_TRANS], ALL_TAC] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"2") THEN CONJ_TAC THENL
       [MP_TAC (← ISPECL [← q r"{z:real^3 | z$3 = &0}", ← q r"(:real^3)"] DIM_EQ_SPAN) THEN
        REWRITE_TAC [SUBSET_UNIV, DIM_UNIV, DIMINDEX_3, lemma] THEN
        MATCH_MP_TAC (← TAUT (← q r"~r /\ (~p ==> q) ==> (q ==> r) ==> p")) THEN
        REWRITE_TAC [← ARITH_RULE (← q r"~(x <= 2) <=> 3 <= x")] THEN
        REWRITE_TAC [EXTENSION, SPAN_UNIV, IN_ELIM_THM] THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"vector[&0;&0;&1]:real^3")) THEN
        REWRITE_TAC [IN_UNIV, VECTOR_3] THEN REAL_ARITH_TAC,
        ALL_TAC] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"dim {b - a:real^3,c - a}") THEN
      CONJ_TAC THENL
       [ALL_TAC, ASM_MESON_TAC [LE_REFL, DIM_INJECTIVE_LINEAR_IMAGE,
                 ORTHOGONAL_TRANSFORMATION_INJECTIVE]] THEN
      MP_TAC (← ISPEC (← q r"{b - a:real^3,c - a}") INDEPENDENT_BOUND_GENERAL) THEN
      SIMP_TAC [CARD_CLAUSES, FINITE_RULES, IN_SING, NOT_IN_EMPTY] THEN
      ASM_REWRITE_TAC [← VECTOR_ARITH (← q r"b - a:real^3 = c - a <=> b = c"), ARITH] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE (RAND_CONV o RAND_CONV)
        [← SET_RULE (← q r"{a,b,c} = {b,a,c}")]) THEN
      REWRITE_TAC [] THEN ONCE_REWRITE_TAC [COLLINEAR_3] THEN
      REWRITE_TAC [independent, CONTRAPOS_THM, dependent] THEN
      REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, RIGHT_OR_DISTRIB] THEN
      REWRITE_TAC [EXISTS_OR_THM, UNWIND_THM2] THEN
      ASM_SIMP_TAC [← SET_RULE (← q r"~(a = b) ==> {a,b} DELETE b = {a}"),
                    ← SET_RULE (← q r"~(a = b) ==> {a,b} DELETE a = {b}"),
                    ← VECTOR_ARITH (← q r"b - a:real^3 = c - a <=> b = c")] THEN
      REWRITE_TAC [SPAN_BREAKDOWN_EQ, SPAN_EMPTY, IN_SING] THEN
      ONCE_REWRITE_TAC [VECTOR_SUB_EQ] THEN MESON_TAC [COLLINEAR_LEMMA, INSERT_AC])

  let ROTATION_HORIZONTAL_PLANE ← prove
   r"!p. plane p
         ==>  ?a f. orthogonal_transformation f /\ det(matrix f) = &1 /\
                    IMAGE (\x. a + x) (IMAGE f {z:real^3 | z$3 = &0}) = p"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP ROTATION_PLANE_HORIZONTAL) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"a:real^3")
     (X_CHOOSE_THEN (← q r"f:real^3->real^3") STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q r"g:real^3->real^3") STRIP_ASSUME_TAC o MATCH_MP
      ORTHOGONAL_TRANSFORMATION_INVERSE) THEN
    MAP_EVERY EXISTS_TAC [← q r"--a:real^3", ← q r"g:real^3->real^3"] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC [← GSYM IMAGE_o, o_DEF, IMAGE_ID,
                     ← VECTOR_ARITH (← q r"--a + a + x:real^3 = x")] THEN
    MATCH_MP_TAC (← REAL_RING (← q r"!f. f * g = &1 /\ f = &1 ==> g = &1")) THEN
    EXISTS_TAC (← q r"det(matrix(f:real^3->real^3))") THEN
    REWRITE_TAC [← GSYM DET_MUL] THEN
    ASM_SIMP_TAC [← GSYM MATRIX_COMPOSE, ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
    ASM_REWRITE_TAC [o_DEF, MATRIX_ID, DET_I])

  -- Apply plane rotation to a goal.

  let GEOM_HORIZONTAL_PLANE_RULE : term → ExceptT String IO thm ← do
    let ifn := MATCH_MP
     (← TAUT (← q r"(p ==> (x <=> x')) /\ (~p ==> (x <=> T)) ==> (x' ==> x)"))
    let pth ← prove
     r"!a f. orthogonal_transformation (f:real^N->real^N)
             ==> ((!P. (!x. P x) <=> (!x. P (a + f x))) /\
                  (!P. (?x. P x) <=> (?x. P (a + f x))) /\
                  (!Q. (!s. Q s) <=> (!s. Q (IMAGE (\x. a + x) (IMAGE f s)))) /\
                  (!Q. (?s. Q s) <=> (?s. Q (IMAGE (\x. a + x) (IMAGE f s))))) /\
                 (!P. {x | P x} =
                      IMAGE (\x. a + x) (IMAGE f {x | P(a + f x)}))"
     (REPEAT GEN_TAC THEN DISCH_TAC THEN
      MP_TAC (← ISPEC (← q r"(\x. a + x) o (f:real^N->real^N)")
        QUANTIFY_SURJECTION_THM) THEN REWRITE_TAC [o_THM, IMAGE_o] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION_SURJECTIVE,
                     ← VECTOR_ARITH (← q r"a + (x - a:real^N) = x")])
    let cth ← prove
     r"!a f. {} = IMAGE (\x:real^3. a + x) (IMAGE f {})"
     (REWRITE_TAC [IMAGE_CLAUSES])
    let oth ← prove
     r"!f:real^3->real^3.
          orthogonal_transformation f /\ det(matrix f) = &1
          ==> linear f /\
              (!x y. f x = f y ==> x = y) /\
              (!y. ?x. f x = y) /\
              (!x. norm(f x) = norm x) /\
              (2 <= dimindex(:3) ==> det(matrix f) = &1)"
     (GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC [ORTHOGONAL_TRANSFORMATION_LINEAR],
        ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION_INJECTIVE],
        ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION_SURJECTIVE],
        ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION]])
    let fth ← MESON []
     (← q r"(!a f. q a f ==> (p <=> p' a f))
      ==> ((?a f. q a f) ==> (p <=> !a f. q a f ==> p' a f))")
    pure (fun tm => do
      let (x, bod) ← liftExcept (HolCore.Basics.dest_forall tm)
      let th1 ← EXISTS_GENVAR_RULE
        (← UNDISCH (← ISPEC x ROTATION_HORIZONTAL_PLANE))
      let (a, f, tm1) ← match HolCore.Basics.strip_exists (concl th1) with
        | ([a, f], tm1) => pure (a, f, tm1)
        | _ => throw "GEOM_HORIZONTAL_PLANE_RULE: match failure"
      let (th_orth, th_det, th_im) ← match CONJUNCTS (← ASSUME tm1) with
        | [t1, t2, t3] => pure (t1, t2, t3)
        | _ => throw "GEOM_HORIZONTAL_PLANE_RULE: match failure"
      let th2 ← PROVE_HYP th_orth (← UNDISCH (← ISPECL [a, f] pth))
      let th3 ← ExceptT.mk (((← EXPAND_QUANTS_CONV (← ASSUME (concl th2))) THENC
                 SUBS_CONV [← GSYM th_im, ← ISPECL [a, f] cth]) bod)
      let th4 ← PROVE_HYP th2 th3
      let th5 ← TRANSLATION_INVARIANTS a
      let th6 ← GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV)
                  [← ASSUME (concl th5)] th4
      let th7 ← PROVE_HYP th5 th6
      let th8s := CONJUNCTS (← MATCH_MP oth (← CONJ th_orth th_det))
      let th9 ← LINEAR_INVARIANTS f th8s
      let th10 ← GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV) [th9] th7
      let th11 ← if (intersect (frees (concl th10)) [a, f]).isEmpty
                 then do PROVE_HYP th1 (← itlistIO SIMPLE_CHOOSE [a, f] th10)
                 else do MP (← MATCH_MP fth (← GENL [a, f] (← DISCH_ALL th10))) th1
      let h ← match hyp th11 with
        | h :: _ => pure h
        | [] => throw "hd"
      let th12 ← ExceptT.mk (REWRITE_CONV [← ASSUME (← liftExcept (HolCore.Bool.mk_neg h))] bod)
      let th13 ← ifn (← CONJ (← DISCH_ALL th11) (← DISCH_ALL th12))
      let th14 ← MATCH_MP MONO_FORALL (← GEN x th13)
      GEN_REWRITE_RULE (fun c => TRY_CONV (LAND_CONV c)) [FORALL_SIMP] th14)

  let GEOM_HORIZONTAL_PLANE_TAC (p : term) : tactic :=
    W (fun (asl, w) =>
          let (_avs, _bod) := HolCore.Basics.strip_forall w
          let avs' := subtract (frees w) (freesl (asl.map (fun (_, th) => concl th)))
          let (avs, _bod) := HolCore.Basics.strip_forall w
          MAP_EVERY X_GEN_TAC avs THEN
          MAP_EVERY (fun t => SPEC_TAC (t, t)) (subtract (avs ++ avs') [p]).reverse THEN
          SPEC_TAC (p, p) THEN
          W (MATCH_MP_TAC o GEOM_HORIZONTAL_PLANE_RULE o snd))

  -- Injection from real^2 -> real^3 plane with zero last coordinate.

  let pad2d3d ← new_definition
   r"(pad2d3d:real^2->real^3) x = lambda i. if i < 3 then x$i else &0"

  let FORALL_PAD2D3D_THM ← prove
   r"!P. (!y:real^3. y$3 = &0 ==> P y) <=> (!x. P(pad2d3d x))"
   (GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [pad2d3d] THEN
      SIMP_TAC [LAMBDA_BETA, DIMINDEX_3, ARITH, LT_REFL],
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(lambda i. (y:real^3)$i):real^2")) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      SIMP_TAC [CART_EQ, pad2d3d, DIMINDEX_3, ARITH, LAMBDA_BETA, DIMINDEX_2,
                ← ARITH_RULE (← q r"i < 3 <=> i <= 2")] THEN
      REWRITE_TAC [← ARITH_RULE (← q r"i <= 3 <=> i <= 2 \/ i = 3")] THEN
      ASM_MESON_TAC []])

  let QUANTIFY_PAD2D3D_THM ← prove
   r"(!P. (!y:real^3. y$3 = &0 ==> P y) <=> (!x. P(pad2d3d x))) /\
     (!P. (?y:real^3. y$3 = &0 /\ P y) <=> (?x. P(pad2d3d x)))"
   (REWRITE_TAC [← MESON [] (← q r"(?y. P y) <=> ~(!x. ~P x)")] THEN
    REWRITE_TAC [← GSYM FORALL_PAD2D3D_THM] THEN MESON_TAC [])

  let LINEAR_PAD2D3D ← prove
   r"linear pad2d3d"
   (REWRITE_TAC [linear, pad2d3d] THEN
    SIMP_TAC [CART_EQ, VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT,
              LAMBDA_BETA, DIMINDEX_2, DIMINDEX_3, ARITH,
              ← ARITH_RULE (← q r"i < 3 ==> i <= 2")] THEN
    REPEAT STRIP_TAC THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REAL_ARITH_TAC)

  let INJECTIVE_PAD2D3D ← prove
   r"!x y. pad2d3d x = pad2d3d y ==> x = y"
   (SIMP_TAC [CART_EQ, pad2d3d, LAMBDA_BETA, DIMINDEX_3, DIMINDEX_2] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"i < 3 <=> i <= 2")] THEN
    MESON_TAC [← ARITH_RULE (← q r"i <= 2 ==> i <= 3")])

  let NORM_PAD2D3D ← prove
   r"!x. norm(pad2d3d x) = norm x"
   (SIMP_TAC [NORM_EQ, DOT_2, DOT_3, pad2d3d, LAMBDA_BETA,
              DIMINDEX_2, DIMINDEX_3, ARITH] THEN
    REAL_ARITH_TAC)

  -- Apply 3D->2D conversion to a goal. Take care to preserve variable names.

  let PAD2D3D_QUANTIFY_CONV : ioconv ← do
    let gv ← liftM (HolCore.Basics.genvar (← qty "real^2") : IO term)
    let pth ← CONV_RULE (BINOP_CONV (BINDER_CONV (RAND_CONV
                (fun t => pure (HolCore.Equal.GEN_ALPHA_CONV gv t)))))
                QUANTIFY_PAD2D3D_THM
    let conv1 ← GEN_REWRITE_CONV_NET id [pth]
    let dest_quant (tm : term) : Except String (term × term) :=
      match HolCore.Basics.dest_forall tm with
      | .ok r => .ok r
      | .error _ => HolCore.Basics.dest_exists tm
    pure (fun tm => ExceptT.run do
      let th ← ExceptT.mk (conv1 tm)
      let name := (← liftExcept (dest_var (← liftExcept (dest_quant tm)).1)).1
      let ty := (← liftExcept (dest_var
        (← liftExcept (dest_quant (← liftExcept (rand (concl th))))).1)).2
      CONV_RULE (RAND_CONV (fun t => pure (HolCore.Equal.GEN_ALPHA_CONV (mk_var name ty) t)))
        th)

  let PAD2D3D_TAC : tactic ← do
    let pad2d3d_tm ← q r"pad2d3d"
    let pths := [LINEAR_PAD2D3D, INJECTIVE_PAD2D3D, NORM_PAD2D3D]
    let cth ← prove
     r"{} = IMAGE pad2d3d {} /\
       vec 0 = pad2d3d(vec 0)"
     (REWRITE_TAC [IMAGE_CLAUSES] THEN MESON_TAC [LINEAR_PAD2D3D, LINEAR_0])
    let lasttac :=
      GEN_REWRITE_TAC REDEPTH_CONV [← LINEAR_INVARIANTS pad2d3d_tm pths]
    pure (fun gl => (GEN_REWRITE_TAC ONCE_DEPTH_CONV [cth] THEN
                     CONV_TAC (DEPTH_CONV PAD2D3D_QUANTIFY_CONV) THEN
                     lasttac) gl)

  -- Rotating so a given line from the origin becomes the x-axis.

  let ROTATION_HORIZONTAL_LINE ← prove
   r"!a:real^N.
          ?b f. orthogonal_transformation f /\ det(matrix f) = &1 /\ f b = a /\
                (!k. 1 < k /\ k <= dimindex(:N) ==> b$k = &0)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"dimindex(:N) = 1") THENL
     [MAP_EVERY EXISTS_TAC [← q r"a:real^N", ← q r"\x:real^N. x"] THEN
      ASM_SIMP_TAC [DET_I, MATRIX_ID, ORTHOGONAL_TRANSFORMATION_ID, LTE_ANTISYM],
      EXISTS_TAC (← q r"norm(a:real^N) % (basis 1):real^N") THEN
      SIMP_TAC [VECTOR_MUL_COMPONENT, LT_IMP_LE, BASIS_COMPONENT] THEN
      SIMP_TAC [← ARITH_RULE (← q r"1 < k ==> ~(k = 1)"), REAL_MUL_RZERO] THEN
      MATCH_MP_TAC ROTATION_EXISTS THEN
      SIMP_TAC [NORM_MUL, NORM_BASIS, LE_REFL, DIMINDEX_GE_1] THEN
      REWRITE_TAC [REAL_ABS_NORM, REAL_MUL_RID] THEN
      MATCH_MP_TAC (← ARITH_RULE (← q r"~(n = 1) /\ 1 <= n ==> 2 <= n")) THEN
      ASM_REWRITE_TAC [DIMINDEX_GE_1]])

  let GEOM_HORIZONTAL_LINE_RULE : term → ExceptT String IO thm ← do
    let pth ← prove
     r"!f. orthogonal_transformation (f:real^N->real^N)
           ==> (vec 0 = f(vec 0) /\ {} = IMAGE f {}) /\
               ((!P. (!x. P x) <=> (!x. P (f x))) /\
                (!P. (?x. P x) <=> (?x. P (f x))) /\
                (!Q. (!s. Q s) <=> (!s. Q (IMAGE f s))) /\
                (!Q. (?s. Q s) <=> (?s. Q (IMAGE f s)))) /\
               (!P. {x | P x} = IMAGE f {x | P(f x)})"
     (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [IMAGE_CLAUSES] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
        MESON_TAC [LINEAR_0],
        MATCH_MP_TAC QUANTIFY_SURJECTION_THM THEN
        ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION_SURJECTIVE]])
    let oth ← prove
     r"!f:real^N->real^N.
          orthogonal_transformation f /\ det(matrix f) = &1
          ==> linear f /\
              (!x y. f x = f y ==> x = y) /\
              (!y. ?x. f x = y) /\
              (!x. norm(f x) = norm x) /\
              (2 <= dimindex(:N) ==> det(matrix f) = &1)"
     (GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC [ORTHOGONAL_TRANSFORMATION_LINEAR],
        ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION_INJECTIVE],
        ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION_SURJECTIVE],
        ASM_MESON_TAC [ORTHOGONAL_TRANSFORMATION]])
    let sth ← prove
     r"((!k. 1 < k /\ k <= dimindex(:2) ==> b$k = &0) <=> b$2 = &0) /\
       ((!k. 1 < k /\ k <= dimindex(:3) ==> b$k = &0) <=> b$2 = &0 /\ b$3 = &0)"
     (REWRITE_TAC [DIMINDEX_2, DIMINDEX_3,
                   ← ARITH_RULE (← q r"k <= 3 <=> k = 3 \/ k <= 2"),
                   ← ARITH_RULE (← q r"k <= 2 <=> k = 2 \/ ~(1 < k)")] THEN
      MESON_TAC [← ARITH_RULE (← q r"1 < 2 /\ 1 < 3")])
    let sfn := GEN_REWRITE_RULE ONCE_DEPTH_CONV [sth]
    pure (fun tm => do
      let (x, bod) ← liftExcept (HolCore.Basics.dest_forall tm)
      let th1 ← EXISTS_GENVAR_RULE
       (← sfn (← ISPEC x ROTATION_HORIZONTAL_LINE))
      let (a, f, tm1) ← match HolCore.Basics.strip_exists (concl th1) with
        | ([a, f], tm1) => pure (a, f, tm1)
        | _ => throw "GEOM_HORIZONTAL_LINE_RULE: match failure"
      let (th_orth, th2) ← CONJ_PAIR (← ASSUME tm1)
      let (th_det, th2a) ← CONJ_PAIR th2
      let (th_works, th_zero) ← CONJ_PAIR th2a
      let (thc, thq) ← CONJ_PAIR (← PROVE_HYP th2 (← UNDISCH (← ISPEC f pth)))
      let th3 ← CONV_RULE (RAND_CONV (SUBS_CONV ((← GSYM th_works) :: CONJUNCTS thc)))
                 (← ExceptT.mk ((← EXPAND_QUANTS_CONV (← ASSUME (concl thq))) bod))
      let th4 ← PROVE_HYP thq th3
      let thps := CONJUNCTS (← MATCH_MP oth (← CONJ th_orth th_det))
      let th5 ← LINEAR_INVARIANTS f thps
      let th6 ← PROVE_HYP th_orth
       (← GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV) [th5] th4)
      let ntm ← liftExcept (HolCore.Bool.mk_forall a
        (← HolCore.Bool.mk_imp (concl th_zero) (← rand (concl th6))))
      let th7 ← MP (← SPEC a (← ASSUME ntm)) th_zero
      let th8 ← DISCH ntm (← HolLight.EQ_MP (← SYM th6) th7)
      if (intersect (frees (concl th8)) [a, f]).isEmpty then
        let th9 ← PROVE_HYP th1 (← itlistIO SIMPLE_CHOOSE [a, f] th8)
        let th10 ← DISCH ntm (← GEN x (← UNDISCH th9))
        CONV_RULE (LAND_CONV (fun t => pure (HolCore.Equal.GEN_ALPHA_CONV x t))) th10
      else
        let h ← match hyp th8 with
          | h :: _ => pure h
          | [] => throw "hd"
        let mtm ← liftExcept (HolCore.Bool.list_mk_forall [a, f]
          (← HolCore.Bool.mk_imp h (← rand (concl th6))))
        let th9 ← HolLight.EQ_MP (← SYM th6) (← UNDISCH (← SPECL [a, f] (← ASSUME mtm)))
        let th10 ← itlistIO SIMPLE_CHOOSE [a, f] (← DISCH mtm th9)
        let th11 ← GEN x (← PROVE_HYP th1 th10)
        MATCH_MP MONO_FORALL th11)

  let GEOM_HORIZONTAL_LINE_TAC (l : term) : tactic := fun gl =>
    let (asl, w) := gl
    let (avs, _bod) := HolCore.Basics.strip_forall w
    let avs' := subtract (frees w) (freesl (asl.map (fun (_, th) => concl th)))
    (MAP_EVERY X_GEN_TAC avs THEN
     MAP_EVERY (fun t => SPEC_TAC (t, t)) (subtract (avs ++ avs') [l]).reverse THEN
     SPEC_TAC (l, l) THEN
     W (MATCH_MP_TAC o GEOM_HORIZONTAL_LINE_RULE o snd)) gl

  return { plane, PLANE_TRANSLATION_EQ, PLANE_TRANSLATION, PLANE_LINEAR_IMAGE_EQ,
           PLANE_LINEAR_IMAGE, ROTATION_PLANE_HORIZONTAL, ROTATION_HORIZONTAL_PLANE,
           GEOM_HORIZONTAL_PLANE_RULE, GEOM_HORIZONTAL_PLANE_TAC, pad2d3d, FORALL_PAD2D3D_THM,
           QUANTIFY_PAD2D3D_THM, LINEAR_PAD2D3D, INJECTIVE_PAD2D3D, NORM_PAD2D3D,
           PAD2D3D_QUANTIFY_CONV, PAD2D3D_TAC, ROTATION_HORIZONTAL_LINE,
           GEOM_HORIZONTAL_LINE_RULE, GEOM_HORIZONTAL_LINE_TAC }

end HolMultiLib.Wlog
