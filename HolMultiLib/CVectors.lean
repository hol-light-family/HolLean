/- ========================================================================= -/
/- A library for vectors of complex numbers.                                 -/
/- Much inspired from HOL-Light real vector library <"vectors.ml">.          -/
/- ========================================================================= -/
/- File: HolMultiLib/CVectors.lean

  Original (c) Copyright, Sanaz Khan Afshar & Vincent Aravantinos 2011-13,
  Hardware Verification Group, Concordia University.
  Acknowledgements: Harsh Singhal (n-dimensional dot product, utility
  theorems).  Updated for the latest version of HOL Light (July 2014).
  Distributed under the same license as HOL Light.
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/cvectors.ml`, in the style of
  HolMultiLib/Complexes.lean: pure, the proofs translated by hand, one `let`
  per OCaml `let`, in file order.  The load-time effects
  (`prioritize_vector()`, `make_overloadable "%"`, `overload_interface`,
  `prioritize_cvector()`, `parse_as_infix`, `prioritize_complex()`) are at
  their file positions.  What cvectors.ml uses from earlier files is passed
  in `CvectorsDeps`: complexes.ml's deps and bundles, cross.ml's theorems and
  bundle, the extra theorems in `CvecThms`, and the parser procedures.
  SessionMultiLib/CVectors.lean supplies it.
-/

import HolMultiLib.Complexes
import HolMultiLib.Cross

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolMultiLib.CVectors

open HolMultiLib.Complexes (CXA CXB CXC CXD CXE CXF CXG CXH CXI CXJ CXK)

/-- The theorems cvectors.ml uses that the complexes.ml and cross.ml deps do
    not carry: from the core library, vectors.ml and topology.ml. -/
structure CvecThms where
  (FINITE_HAS_SIZE FINITE_INDEX_WORKS HAS_SIZE_NUMSEG_1 I_DEF MULT_2 PASTECART_EQ
   PASTECART_FST_SND REAL_ABS_BOUNDS REAL_ABS_LE REAL_MUL_POS_LE REAL_NEG_GT0
   REAL_NEG_MINUS1 REAL_NEG_RMUL REAL_POW_ZERO SQRT_DIV UNCURRY_DEF finite_index fstcart
   pastecart sndcart
   DOT_SQUARE_NORM NORM_BASIS_1 NORM_EQ_1 NORM_FSTCART NORM_SNDCART PASTECART_VSUM VSUM_3
   CONTINUOUS_AT_SEQUENTIALLY INFSUM_LINEAR LIM_PASTECART_EQ SUMMABLE_LINEAR summable
   sums : thm)
  deriving Inhabited

structure CvectorsDeps where
  cx : HolMultiLib.Complexes.ComplexesDeps
  cxa : CXA
  cxb : CXB
  cxc : CXC
  cxd : CXD
  cxe : CXE
  cxf : CXF
  cxg : CXG
  cxh : CXH
  cxi : CXI
  cxj : CXJ
  cxk : CXK
  crt : HolMultiLib.Cross.CrossThms
  crs : HolMultiLib.Cross.CRS
  prioritize_vector : IO Unit
  make_overloadable : String → hol_type → ExceptT String IO Unit
  thms : CvecThms

/- ------------------------------------------------------------------------- -/
/- Additions to the base library: additional tacticals; additions to the     -/
/- vectors, complex numbers and topology libraries; embedding of reals in    -/
/- complex numbers; vector maps.  (cvectors.ml 23-475)                       -/
/- ------------------------------------------------------------------------- -/

structure CVA where
  SINGLE : (List thm → tactic) → thm → tactic
  distrib : List (thm → tactic) → thm → List tactic
  DISTRIB : List (thm → tactic) → thm → tactic
  REWRITE_TACS : List thm → tactic
  GCONJUNCTS : thm → ExceptT String IO (List thm)
  COMPONENT_LE_NORM_ALT : thm
  RE_IM_NORM : thm
  RE_NORM : thm
  IM_NORM : thm
  ABS_RE_NORM : thm
  ABS_IM_NORM : thm
  NORM_RE : thm
  NORM_RE_ADD : thm
  NORM_RE_SUB : thm
  NORM2_ADD_REAL : thm
  COMPLEX_EQ_RCANCEL_IMP : thm
  COMPLEX_BALANCE_DIV_MUL : thm
  CSQRT_MUL_LCX_LT : thm
  CSQRT_MUL_LCX : thm
  REAL_ADD_POW_2 : thm
  COMPLEX_ADD_POW_2 : thm
  FINITE_INTER_ENUM : thm
  NORM_PASTECART_GE1 : thm
  NORM_PASTECART_GE2 : thm
  SUMS_PASTECART : thm
  LINEAR_SUMS : thm
  real_of_complex : thm
  REAL_OF_COMPLEX : thm
  REAL_OF_COMPLEX_RE : thm
  REAL_OF_COMPLEX_CX : thm
  REAL_OF_COMPLEX_NORM : thm
  REAL_OF_COMPLEX_ADD : thm
  REAL_MUL : thm
  REAL_OF_COMPLEX_MUL : thm
  REAL_OF_COMPLEX_0 : thm
  REAL_COMPLEX_ADD_CNJ : thm
  vector_const : thm
  vector_map : thm
  vector_map2 : thm
  vector_map3 : thm
  FINITE_INDEX_INRANGE_4 : thm
  COMPONENT_TAC : thm → tactic
  VECTOR_CONST_COMPONENT : thm
  VECTOR_MAP_COMPONENT : thm
  VECTOR_MAP2_COMPONENT : thm
  VECTOR_MAP3_COMPONENT : thm
  VECTOR_MAP_VECTOR_CONST : thm
  VECTOR_MAP_VECTOR_MAP : thm
  VECTOR_MAP_VECTOR_MAP2 : thm
  VECTOR_MAP2_LVECTOR_CONST : thm
  VECTOR_MAP2_RVECTOR_CONST : thm
  VECTOR_MAP2_LVECTOR_MAP : thm
  VECTOR_MAP2_RVECTOR_MAP : thm
  VECTOR_MAP2_LVECTOR_MAP2 : thm
  VECTOR_MAP2_RVECTOR_MAP2 : thm
  VECTOR_MAP_SIMP_TAC : tactic
  VECTOR_MAP_PROPERTY_TAC : List thm → thm → tactic
  VECTOR_MAP_PROPERTY : term → List thm → thm → ExceptT String IO thm
  COMPLEX_VECTOR_MAP : thm
  COMPLEX_NEG_IS_A_MAP : thm
  VECTOR_NEG_IS_A_MAP : thm
  VECTOR_MAP_VECTOR_MAP_ALT : thm
  COMPLEX_VECTOR_MAP2 : thm
  VECTOR_MAP2_RVECTOR_MAP_ALT : thm
  COMPLEX_ADD_IS_A_MAP : thm
  VECTOR_ADD_IS_A_MAP : thm
  COMPLEX_SUB_IS_A_MAP : thm
  VECTOR_SUB_IS_A_MAP : thm
  PASTECART_VECTOR_MAP : thm
  PASTECART_VECTOR_MAP2 : thm
  vector_zip : thm
  VECTOR_ZIP_COMPONENT : thm
  vector_unzip : thm
  VECTOR_UNZIP_COMPONENT : thm
  VECTOR_MAP2_AS_VECTOR_MAP : thm
  deriving Inhabited

@[nospecialize]
def setupCVA [HolBase] (D : CvectorsDeps) : ExceptT String IO CVA := do
  -- @@SCOPE BEGIN
  let { new_definition, ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, REAL_ARITH,
        REAL_ARITH_TAC, .. } := D.cx.cvx
  let { CART_EQ, DE_MORGAN_THM, DIMINDEX_2, DIMINDEX_FINITE_SUM, FINITE_INTER, FINITE_NUMSEG,
        .. } := D.cx.cvx.core1
  let { FSTCART_PASTECART, FUN_EQ_THM, .. } := D.cx.cvx.core2
  let { LAMBDA_BETA, REAL_ABS_MUL, REAL_ABS_REFL, REAL_ADD_LDISTRIB, REAL_ADD_LID,
        REAL_ADD_RID, .. } := D.cx.cvx.core3
  let { REAL_ENTIRE, REAL_INV_MUL, REAL_LE_ADD, REAL_LE_LT, REAL_LE_MUL_EQ, REAL_LE_POW_2,
        REAL_LE_TRANS, REAL_LT_IMP_LE, REAL_LT_IMP_NZ, .. } := D.cx.cvx.core4
  let { REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LZERO, REAL_MUL_RINV,
        REAL_MUL_RZERO, REAL_NEG_0, REAL_SUB_LDISTRIB, REAL_SUB_RZERO, SNDCART_PASTECART,
        SQRT_0, SQRT_MUL, SQRT_POW_2, .. } := D.cx.cvx.core5
  let { o_DEF, real_div, .. } := D.cx.cvx.core6
  let { COMPONENT_LE_NORM, .. } := D.cx.cvx.vec1
  let { LINEAR_VSUM, .. } := D.cx.cvx.vec2
  let { NORM_MUL, .. } := D.cx.cvx.vec3
  let { VECTOR_ADD_COMPONENT, VECTOR_NEG_COMPONENT, VECTOR_SUB_COMPONENT, .. } := D.cx.cvx.vec4
  let { LINEAR_CONTINUOUS_AT, .. } := D.cx.cvx.top4
  let { real_sub, FORALL_2, VECTOR_2, .. } := D.cx.cpx
  let { RE_DEF, IM_DEF, complex, CX_DEF, complex_mul, RE, IM, COMPLEX_EQ, complex_neg,
        complex_add, complex_sub, complex_norm, SIMPLE_COMPLEX_ARITH_TAC,
        SIMPLE_COMPLEX_ARITH, .. } := D.cxa
  let { COMPLEX_MUL_LZERO, .. } := D.cxb
  let { COMPLEX_CMUL, COMPLEX_POW_2, CX_INJ, CX_MUL, RE_CX, RE_ADD, IM_CX, IM_ADD, RE_MUL_II,
        IM_MUL_II, .. } := D.cxc
  let { COMPLEX_EQ_MUL_RCANCEL, .. } := D.cxe
  let { COMPLEX_DIV_RMUL, .. } := D.cxf
  let { COMPLEX_ADD_CNJ, .. } := D.cxg
  let { csqrt, CSQRT_0, .. } := D.cxh
  let { real, REAL, REAL_EXISTS, REAL_CX, REAL_ADD, .. } := D.cxi
  let { REAL_NORM, .. } := D.cxj
  let { FINITE_INDEX_WORKS, PASTECART_VSUM, REAL_ABS_LE, REAL_MUL_POS_LE, REAL_NEG_GT0,
        REAL_NEG_RMUL, REAL_POW_ZERO, SQRT_DIV, UNCURRY_DEF, finite_index, pastecart,
        NORM_FSTCART, NORM_SNDCART, CONTINUOUS_AT_SEQUENTIALLY, LIM_PASTECART_EQ, sums,
        .. } := D.thms
  -- @@SCOPE END

  /- ======================================================================= -/
  /- ADDITIONS TO THE BASE LIBRARY                                           -/
  /- ======================================================================= -/

  -- Additional tacticals

  let SINGLE (f : List thm → tactic) (x : thm) : tactic := f [x]

  let distrib (fs : List (thm → tactic)) (x : thm) : List tactic := fs.map (fun f => f x)

  let DISTRIB (ttacs : List (thm → tactic)) (x : thm) : tactic := EVERY (distrib ttacs x)

  let REWRITE_TACS : List thm → tactic := MAP_EVERY (SINGLE REWRITE_TAC)

  let GCONJUNCTS (th : thm) : ExceptT String IO (List thm) := do
    (CONJUNCTS (← SPEC_ALL th)).mapM GEN_ALL

  -- Additions to the vectors library

  let COMPONENT_LE_NORM_ALT ← prove
   r"!x:real^N i. 1 <= i /\ i <= dimindex (:N) ==> x$i <= norm x"
   (MESON_TAC [REAL_ABS_LE, COMPONENT_LE_NORM, REAL_LE_TRANS])

  -- Additions to the library of complex numbers

  -- Lemmas
  let RE_IM_NORM ← prove
   r"!x. Re x <= norm x /\ Im x <= norm x /\ abs(Re x) <= norm x
  /\ abs(Im x) <= norm x"
   (REWRITE_TAC [RE_DEF, IM_DEF] THEN GEN_TAC THEN REPEAT CONJ_TAC
    THEN ((MATCH_MP_TAC COMPONENT_LE_NORM_ALT
    THEN REWRITE_TAC [DIMINDEX_2] THEN ARITH_TAC) ORELSE SIMP_TAC [COMPONENT_LE_NORM]))

  let [RE_NORM, IM_NORM, ABS_RE_NORM, ABS_IM_NORM] ← GCONJUNCTS RE_IM_NORM
    | throw "RE_NORM: GCONJUNCTS"

  let NORM_RE ← prove
   r"!x. &0 <= norm x + Re x /\ &0 <= norm x - Re x"
   (GEN_TAC THEN MP_TAC (← SPEC_ALL ABS_RE_NORM) THEN REAL_ARITH_TAC)

  let [NORM_RE_ADD, NORM_RE_SUB] ← GCONJUNCTS NORM_RE
    | throw "NORM_RE_ADD: GCONJUNCTS"

  let NORM2_ADD_REAL ← prove
   r"!x y.
    real x /\ real y ==> norm (x + ii * y) pow 2 = norm x pow 2 + norm y pow 2"
   (SIMP_TAC [real, complex_norm, RE_ADD, IM_ADD, RE_MUL_II, IM_MUL_II, REAL_NEG_0,
    REAL_ADD_LID, REAL_ADD_RID, REAL_POW_ZERO, ← ARITH_RULE (← q r"~(2=0)"), REAL_LE_POW_2,
    SQRT_POW_2, REAL_LE_ADD])

  let COMPLEX_EQ_RCANCEL_IMP ← GEN_ALL (← MATCH_MP (← MESON []
    (← q r"(p <=> r \/ q) ==> (p /\ ~r ==> q) ")) (← SPEC_ALL COMPLEX_EQ_MUL_RCANCEL))

  let COMPLEX_BALANCE_DIV_MUL ← prove
   r"!x y z t. ~(z=Cx(&0)) ==> (x = y/z * t <=> x*z = y * t)"
   (REPEAT STRIP_TAC THEN POP_ASSUM (fun x => tactic_of do
      pure (ASSUME_TAC (← REWRITE_RULE [x] (← SPEC_ALL COMPLEX_EQ_MUL_RCANCEL))
      THEN ASSUME_TAC (← REWRITE_RULE [x] (← SPECL [← q r"x:complex", ← q r"z:complex"]
      COMPLEX_DIV_RMUL))))
    THEN SUBGOAL_THEN (← q r"x=y/z*t <=> x*z=(y/z*t)*z:complex") (SINGLE REWRITE_TAC)
    THENL [ASM_REWRITE_TAC [],
      REWRITE_TAC [← SIMPLE_COMPLEX_ARITH (← q r"(y/z*t)*z=(y/z*z)*t:complex")]
    THEN ASM_REWRITE_TAC []])

  let CSQRT_MUL_LCX_LT ← prove
   r"!x y. &0 < x ==> csqrt(Cx x * y) = Cx(sqrt x) * csqrt y"
   (REWRITE_TAC [csqrt, complex_mul, IM, RE, IM_CX, REAL_MUL_LZERO, REAL_ADD_RID, RE_CX,
      REAL_SUB_RZERO]
    THEN REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC
    THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE)
    THEN ASM_SIMP_TAC [IM, RE, REAL_MUL_RZERO, SQRT_MUL]
    THENL [
      REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [REAL_ENTIRE, REAL_MUL_POS_LE]
      THEN REPEAT STRIP_TAC
      THEN ASM_REWRITE_TAC [SQRT_0, REAL_MUL_LZERO, REAL_MUL_RZERO],
      REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC [REAL_ENTIRE]
      THEN MESON_TAC [REAL_LT_IMP_NZ],
      ASM_MESON_TAC [REAL_LE_MUL_EQ, ← REAL_ARITH (← q r"~(&0 <= y) = &0 > y")],
      SIMP_TAC [REAL_NEG_RMUL] THEN REPEAT (POP_ASSUM MP_TAC)
      THEN SIMP_TAC [← REAL_ARITH (← q r"~(&0 <= y) = y < &0")]
      THEN SIMP_TAC [← GSYM REAL_NEG_GT0] THEN MESON_TAC [REAL_LT_IMP_LE, SQRT_MUL],
      REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC [REAL_ENTIRE]
      THEN MESON_TAC [REAL_LT_IMP_NZ],
      REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC [REAL_ENTIRE]
      THEN SIMP_TAC [DE_MORGAN_THM],
      REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC [REAL_ENTIRE]
      THEN SIMP_TAC [DE_MORGAN_THM], ALL_TAC] THENL [
        SIMP_TAC [REAL_NEG_0, SQRT_0, REAL_MUL_RZERO],
        ASM_MESON_TAC [← REAL_ARITH (← q r"~(x<y /\ ~(x <=y))")],
        ASM_MESON_TAC [← REAL_ARITH (← q r"~(x<y /\ y<x)")],
        ALL_TAC]
      THEN REWRITE_TAC [← GSYM (← REWRITE_RULE [CX_DEF, complex_mul, RE, IM,
        REAL_MUL_LZERO, REAL_ADD_RID, REAL_SUB_RZERO] COMPLEX_CMUL)]
      THEN SIMP_TAC [NORM_MUL] THEN POP_ASSUM MP_TAC
      THEN ASM_SIMP_TAC [← GSYM REAL_ABS_REFL] THEN DISCH_TAC
      THEN SIMP_TAC [REAL_ABS_MUL]
      THEN ASM_SIMP_TAC [← GSYM REAL_ABS_REFL]
      THEN SIMP_TAC [← GSYM REAL_ADD_LDISTRIB, ← GSYM REAL_SUB_LDISTRIB]
      THEN SUBGOAL_THEN (← q r"(x*Im y) / (x*abs(Im y)) = Im y / abs(Im y)") ASSUME_TAC
      THENL [
        SIMP_TAC [real_div] THEN SIMP_TAC [REAL_INV_MUL]
        THEN SIMP_TAC [← GSYM REAL_MUL_ASSOC] THEN ONCE_REWRITE_TAC [REAL_MUL_AC]
        THEN SUBGOAL_THEN (← q r"Im y * x * inv x * inv (abs(Im y)) =
          Im y * (x * inv x) * inv (abs (Im y)) ") ASSUME_TAC
          THENL [SIMP_TAC [REAL_MUL_AC], ALL_TAC]
        THEN ASM_SIMP_TAC [REAL_MUL_RINV, REAL_LT_IMP_NZ]
        THEN SIMP_TAC [REAL_MUL_LID] THEN SIMP_TAC [REAL_MUL_AC],
        ALL_TAC]
      THEN ASM_SIMP_TAC []
      THEN SUBGOAL_THEN (← q r"sqrt x * Im y / abs(Im y) * sqrt ((norm y-Re y) / &2) =
        Im y / abs (Im y) * sqrt x * sqrt ((norm y - Re y) / &2)") ASSUME_TAC
      THENL [SIMP_TAC [REAL_MUL_AC], ALL_TAC] THEN ASM_SIMP_TAC []
      THEN SUBGOAL_THEN (← q r"sqrt ((x * (norm y - Re y)) / &2) =
        sqrt (x * (norm y - Re y)) / sqrt (&2)") ASSUME_TAC
      THENL [
        SIMP_TAC [SQRT_DIV] THEN CONJ_TAC THENL [
          ASM_SIMP_TAC [REAL_LE_MUL_EQ, REAL_LT_IMP_LE] THEN SIMP_TAC [NORM_RE_SUB],
          REAL_ARITH_TAC],
        ALL_TAC]
      THEN ASM_SIMP_TAC [] THEN SUBGOAL_THEN (← q r"sqrt ((norm y - Re y) / &2) =
        sqrt (norm y - Re y) / sqrt (&2)") ASSUME_TAC
      THENL [
        SIMP_TAC [SQRT_DIV] THEN CONJ_TAC
        THENL [SIMP_TAC [NORM_RE_SUB], REAL_ARITH_TAC],
        ALL_TAC ]
      THEN ASM_SIMP_TAC []
      THEN SUBGOAL_THEN (← q r"sqrt ((x * (norm y + Re y)) / &2) =
        sqrt (x * (norm y + Re y)) / sqrt (&2)") ASSUME_TAC
      THENL [
        SIMP_TAC [SQRT_DIV] THEN CONJ_TAC
        THENL [
          ASM_SIMP_TAC [REAL_LE_MUL_EQ, REAL_LT_IMP_LE]
          THEN SIMP_TAC [NORM_RE_ADD],
          REAL_ARITH_TAC],
        ALL_TAC]
      THEN SUBGOAL_THEN (← q r"sqrt ((norm y + Re y) / &2) =
        sqrt (norm y + Re y) / sqrt (&2)") ASSUME_TAC
      THENL [
        SIMP_TAC [SQRT_DIV] THEN CONJ_TAC
        THENL [SIMP_TAC [NORM_RE_ADD], REAL_ARITH_TAC],
        ALL_TAC]
      THEN ASM_SIMP_TAC [] THEN SUBGOAL_THEN (← q r"&0 <= x") ASSUME_TAC
      THENL [ ASM_SIMP_TAC [REAL_LT_IMP_LE], ALL_TAC ]
      THEN SIMP_TAC [COMPLEX_EQ] THEN SIMP_TAC [RE, IM] THEN CONJ_TAC
      THENL [
        SUBGOAL_THEN (← q r"sqrt x * sqrt (norm y + Re y) / sqrt (&2) =
          (sqrt x * sqrt (norm y + Re y)) / sqrt (&2)") ASSUME_TAC
        THENL [REAL_ARITH_TAC, ALL_TAC]
        THEN ASM_MESON_TAC [SQRT_MUL, NORM_RE_ADD],
        SUBGOAL_THEN (← q r"Im y/abs(Im y) * sqrt x * sqrt (norm y-Re y) / sqrt(&2) =
          Im y/abs (Im y) * (sqrt x * sqrt (norm y - Re y))/sqrt(&2)") ASSUME_TAC
        THENL [REAL_ARITH_TAC, ALL_TAC]
        THEN ASM_MESON_TAC [SQRT_MUL, NORM_RE_SUB]])

  let CSQRT_MUL_LCX ← prove
   r"!x y. &0 <= x ==> csqrt(Cx x * y) = Cx(sqrt x) * csqrt y"
   (REWRITE_TAC [REAL_LE_LT] THEN REPEAT STRIP_TAC
    THEN ASM_SIMP_TAC [CSQRT_MUL_LCX_LT] THEN EXPAND_TAC "x"
    THEN REWRITE_TAC [COMPLEX_MUL_LZERO, SQRT_0, CSQRT_0])

  let REAL_ADD_POW_2 ← prove
   r"!x y:real. (x+y) pow 2 = x pow 2 + y pow 2 + &2 * x * y"
   REAL_ARITH_TAC

  let COMPLEX_ADD_POW_2 ← prove
   r"!x y:complex. (x+y) pow 2 = x pow 2 + y pow 2 + Cx(&2) * x * y"
   (REWRITE_TAC [COMPLEX_POW_2] THEN SIMPLE_COMPLEX_ARITH_TAC)

  -- Additions to the topology library

  D.prioritize_vector

  -- Lemmas
  let FINITE_INTER_ENUM ← prove
   r"!s n. FINITE(s INTER (0..n))"
   (MESON_TAC [FINITE_INTER, FINITE_NUMSEG])

  let NORM_PASTECART_GE1 ← prove
   r"!x y. norm x <= norm (pastecart x y)"
   (MESON_TAC [FSTCART_PASTECART, NORM_FSTCART])

  let NORM_PASTECART_GE2 ← prove
   r"!x y. norm y <= norm (pastecart x y)"
   (MESON_TAC [SNDCART_PASTECART, NORM_SNDCART])

  let SUMS_PASTECART ← prove
   r"!s f1:num->real^N f2:num->real^M l1 l2. (f1 sums l1) s /\ (f2 sums l2) s
    <=> ((\x. pastecart (f1 x) (f2 x)) sums (pastecart l1 l2)) s"
   (SIMP_TAC [sums, FINITE_INTER_ENUM, ← GSYM PASTECART_VSUM,
           ← GSYM LIM_PASTECART_EQ])

  let LINEAR_SUMS ← prove
   r"!s f l g. linear g ==> ((f sums l) s ==> ((g o f) sums (g l)) s)"
   (SIMP_TAC [sums, FINITE_INTER_ENUM, ← GSYM LINEAR_VSUM,
    ← REWRITE_RULE [o_DEF, CONTINUOUS_AT_SEQUENTIALLY] LINEAR_CONTINUOUS_AT])

  -- Embedding of reals in complex numbers

  let real_of_complex ← new_definition r"real_of_complex c = @r. c = Cx r"

  let REAL_OF_COMPLEX ← prove
   r"!c. real c ==> Cx(real_of_complex c) = c"
   (MESON_TAC [REAL, real_of_complex])

  let REAL_OF_COMPLEX_RE ← prove
   r"!c. real c ==> real_of_complex c = Re c"
   (MESON_TAC [RE_CX, REAL_OF_COMPLEX])

  let REAL_OF_COMPLEX_CX ← prove
   r"!r. real_of_complex (Cx r) = r"
   (SIMP_TAC [REAL_CX, REAL_OF_COMPLEX_RE, RE_CX])

  let REAL_OF_COMPLEX_NORM ← prove
   r"!c. real c ==> norm c = abs (real_of_complex c)"
   (MESON_TAC [REAL_NORM, REAL_OF_COMPLEX_RE])

  let REAL_OF_COMPLEX_ADD ← prove
   r"!x y. real x /\ real y
    ==> real_of_complex (x+y) = real_of_complex x + real_of_complex y"
   (MESON_TAC [REAL_ADD, REAL_OF_COMPLEX_RE, RE_ADD])

  let REAL_MUL ← prove
   r"!x y. real x /\ real y ==> real (x*y)"
   (REWRITE_TAC [real] THEN SIMPLE_COMPLEX_ARITH_TAC)

  let REAL_OF_COMPLEX_MUL ← prove
   r"!x y. real x /\ real y
    ==> real_of_complex (x*y) = real_of_complex x * real_of_complex y"
   (MESON_TAC [REAL_MUL, REAL_OF_COMPLEX, CX_MUL, REAL_OF_COMPLEX_CX])

  let REAL_OF_COMPLEX_0 ← prove
   r"!x. real x ==> (real_of_complex x = &0 <=> x = Cx(&0))"
   (REWRITE_TAC [REAL_EXISTS] THEN REPEAT STRIP_TAC
    THEN ASM_SIMP_TAC [REAL_OF_COMPLEX_CX, CX_INJ])

  let REAL_COMPLEX_ADD_CNJ ← prove
   r"!x. real(cnj x + x) /\ real(x + cnj x)"
   (REWRITE_TAC [COMPLEX_ADD_CNJ, REAL_CX])

  /- TODO
   *let RE_EQ_NORM = prove(`!x. Re x = norm x <=> real x /\ &0 <= real_of_complex x`,
   -/

  -- Additions to the vectors library

  let vector_const ← new_definition
   r"vector_const (k:A) :A^N = lambda i. k"
  let vector_map ← new_definition
   r"vector_map (f:A->B) (v:A^N) :B^N = lambda i. f(v$i)"
  let vector_map2 ← new_definition
   r"vector_map2 (f:A->B->C) (v1:A^N) (v2:B^N) :C^N =
    lambda i. f (v1$i) (v2$i)"
  let vector_map3 ← new_definition
   r"vector_map3 (f:A->B->C->D) (v1:A^N) (v2:B^N) (v3:C^N) :D^N =
    lambda i. f (v1$i) (v2$i) (v3$i)"

  let FINITE_INDEX_INRANGE_4 ← prove
   r"!i. ?k. 1 <= k /\ k <= dimindex(:N) /\ (!x:A^N. x$i = x$k)
  /\ (!x:B^N. x$i = x$k) /\ (!x:C^N. x$i = x$k) /\ (!x:D^N. x$i = x$k)"
   (REWRITE_TAC [finite_index] THEN MESON_TAC [FINITE_INDEX_WORKS])

  let COMPONENT_TAC (x : thm) : tactic := tactic_of do
    pure (REPEAT GEN_TAC THEN CHOOSE_TAC (← SPEC_ALL FINITE_INDEX_INRANGE_4)
      THEN ASM_SIMP_TAC [x, LAMBDA_BETA])

  let VECTOR_CONST_COMPONENT ← prove
   r"!i k. ((vector_const k):A^N)$i = k"
   (COMPONENT_TAC vector_const)
  let VECTOR_MAP_COMPONENT ← prove
   r"!i f:A->B v:A^N. (vector_map f v)$i = f (v$i)"
   (COMPONENT_TAC vector_map)
  let VECTOR_MAP2_COMPONENT ← prove
   r"!i f:A->B->C v1:A^N v2. (vector_map2 f v1 v2)$i = f (v1$i) (v2$i)"
   (COMPONENT_TAC vector_map2)
  let VECTOR_MAP3_COMPONENT ← prove
   r"!i f:A->B->C->D v1:A^N v2 v3. (vector_map3 f v1 v2 v3)$i =
    f (v1$i) (v2$i) (v3$i)"
   (COMPONENT_TAC vector_map3)

  let COMMON_TAC : tactic :=
    REWRITE_TAC [vector_const, vector_map, vector_map2, vector_map3]
    THEN ONCE_REWRITE_TAC [CART_EQ] THEN SIMP_TAC [LAMBDA_BETA, o_DEF]

  let VECTOR_MAP_VECTOR_CONST ← prove
   r"!f:A->B k. vector_map f ((vector_const k):A^N) = vector_const (f k)"
   COMMON_TAC

  let VECTOR_MAP_VECTOR_MAP ← prove
   r"!f:A->B g:C->A v:C^N.
    vector_map f (vector_map g v) = vector_map (f o g) v"
   COMMON_TAC

  let VECTOR_MAP_VECTOR_MAP2 ← prove
   r"!f:A->B g:C->D->A u v:D^N.
    vector_map f (vector_map2 g u v) = vector_map2 (\x y. f (g x y)) u v"
   COMMON_TAC

  let VECTOR_MAP2_LVECTOR_CONST ← prove
   r"!f:A->B->C k v:B^N.
    vector_map2 f (vector_const k) v = vector_map (f k) v"
   COMMON_TAC

  let VECTOR_MAP2_RVECTOR_CONST ← prove
   r"!f:A->B->C k v:A^N.
    vector_map2 f v (vector_const k) = vector_map (\x. f x k) v"
   COMMON_TAC

  let VECTOR_MAP2_LVECTOR_MAP ← prove
   r"!f:A->B->C g:D->A v1 v2:B^N.
    vector_map2 f (vector_map g v1) v2 = vector_map2 (f o g) v1 v2"
   COMMON_TAC

  let VECTOR_MAP2_RVECTOR_MAP ← prove
   r"!f:A->B->C g:D->B v1 v2:D^N.
    vector_map2 f v1 (vector_map g v2) = vector_map2 (\x y. f x (g y)) v1 v2"
   COMMON_TAC

  let VECTOR_MAP2_LVECTOR_MAP2 ← prove
   r"!f:A->B->C g:D->E->A v1 v2 v3:B^N.
    vector_map2 f (vector_map2 g v1 v2) v3 =
      vector_map3 (\x y. f (g x y)) v1 v2 v3"
   COMMON_TAC

  let VECTOR_MAP2_RVECTOR_MAP2 ← prove
   r"!f:A->B->C g:D->E->B v1 v2 v3:E^N.
    vector_map2 f v1 (vector_map2 g v2 v3) =
      vector_map3 (\x y z. f x (g y z)) v1 v2 v3"
   COMMON_TAC

  let VECTOR_MAP_SIMP_TAC : tactic := REWRITE_TAC [
      VECTOR_MAP_VECTOR_CONST, VECTOR_MAP2_LVECTOR_CONST,
      VECTOR_MAP2_RVECTOR_CONST, VECTOR_MAP_VECTOR_MAP, VECTOR_MAP2_RVECTOR_MAP,
      VECTOR_MAP2_LVECTOR_MAP, VECTOR_MAP2_RVECTOR_MAP2, VECTOR_MAP2_LVECTOR_MAP2,
      VECTOR_MAP_VECTOR_MAP2]

  let VECTOR_MAP_PROPERTY_TAC (fs : List thm) (prop : thm) : tactic :=
    REWRITE_TAC fs THEN VECTOR_MAP_SIMP_TAC THEN ONCE_REWRITE_TAC [CART_EQ]
    THEN REWRITE_TAC [VECTOR_MAP_COMPONENT, VECTOR_MAP2_COMPONENT,
      VECTOR_MAP3_COMPONENT, VECTOR_CONST_COMPONENT, o_DEF, prop]

  let VECTOR_MAP_PROPERTY (tm : term) (f : List thm) (prop : thm) :
      ExceptT String IO thm :=
    ExceptT.mk (HolCore.Tactics.prove HolBase.B tm (VECTOR_MAP_PROPERTY_TAC f prop))

  let COMPLEX_VECTOR_MAP ← prove
   r"!f:complex->complex g. f = vector_map g
    <=> !z. f z = complex (g (Re z), g (Im z))"
   (REWRITE_TAC [vector_map, FUN_EQ_THM, complex] THEN REPEAT (GEN_TAC ORELSE EQ_TAC)
    THEN ASM_SIMP_TAC [CART_EQ, DIMINDEX_2, FORALL_2, LAMBDA_BETA, VECTOR_2, RE_DEF, IM_DEF])

  let COMPLEX_NEG_IS_A_MAP ← prove
   r"(--):complex->complex = vector_map ((--):real->real)"
   (REWRITE_TAC [COMPLEX_VECTOR_MAP, complex_neg])

  let VECTOR_NEG_IS_A_MAP ← prove
   r"(--):real^N->real^N = vector_map ((--):real->real)"
   (REWRITE_TAC [FUN_EQ_THM, CART_EQ, VECTOR_NEG_COMPONENT, VECTOR_MAP_COMPONENT])

  let VECTOR_MAP_VECTOR_MAP_ALT ← prove
   r"!f:A^N->B^N g:C^N->A^N f' g'. f = vector_map f' /\ g = vector_map g' ==>
    f o g = vector_map (f' o g')"
   (SIMP_TAC [o_DEF, FUN_EQ_THM, VECTOR_MAP_VECTOR_MAP])

  let COMPLEX_VECTOR_MAP2 ← prove
   r"!f:complex->complex->complex g. f = vector_map2 g <=>
    !z1 z2. f z1 z2 = complex (g (Re z1) (Re z2), g (Im z1) (Im z2))"
   (REWRITE_TAC [vector_map2, FUN_EQ_THM, complex]
    THEN REPEAT (GEN_TAC ORELSE EQ_TAC)
    THEN ASM_SIMP_TAC [CART_EQ, DIMINDEX_2, FORALL_2, LAMBDA_BETA, VECTOR_2, RE_DEF,
      IM_DEF])

  let VECTOR_MAP2_RVECTOR_MAP_ALT ← prove
   r"!f:complex->complex->complex g:complex->complex f' g'.
    f = vector_map2 f' /\ g = vector_map g'
      ==> (\x y. f x (g y)) = vector_map2 (\x y. f' x (g' y))"
   (SIMP_TAC [FUN_EQ_THM, VECTOR_MAP2_RVECTOR_MAP])

  let COMPLEX_ADD_IS_A_MAP ← prove
   r"(+):complex->complex->complex = vector_map2 ((+):real->real->real)"
   (REWRITE_TAC [COMPLEX_VECTOR_MAP2, complex_add])

  let VECTOR_ADD_IS_A_MAP ← prove
   r"(+):real^N->real^N->real^N = vector_map2 ((+):real->real->real)"
   (REWRITE_TAC [FUN_EQ_THM, CART_EQ, VECTOR_ADD_COMPONENT, VECTOR_MAP2_COMPONENT])

  let COMPLEX_SUB_IS_A_MAP ← prove
   r"(-):complex->complex->complex = vector_map2 ((-):real->real->real)"
   (ONCE_REWRITE_TAC [← prove r"(-) = \x y:complex. x-y" (REWRITE_TAC [FUN_EQ_THM])]
    THEN ONCE_REWRITE_TAC [← prove r"(-) = \x y:real. x-y" (REWRITE_TAC [FUN_EQ_THM])]
    THEN REWRITE_TAC [complex_sub, real_sub]
    THEN MATCH_MP_TAC VECTOR_MAP2_RVECTOR_MAP_ALT
    THEN REWRITE_TAC [COMPLEX_NEG_IS_A_MAP, COMPLEX_ADD_IS_A_MAP])

  let VECTOR_SUB_IS_A_MAP ← prove
   r"(-):real^N->real^N->real^N = vector_map2 ((-):real->real->real)"
   (REWRITE_TAC [FUN_EQ_THM, CART_EQ, VECTOR_SUB_COMPONENT, VECTOR_MAP2_COMPONENT])

  let COMMON_TAC (x : thm) : tactic := tactic_of do
    pure (SIMP_TAC [CART_EQ, pastecart, x, LAMBDA_BETA] THEN REPEAT STRIP_TAC
    THEN REPEAT COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC []
    THEN SUBGOAL_THEN (← q r"1<= i-dimindex(:N) /\ i-dimindex(:N) <= dimindex(:M)")
      ASSUME_TAC
    THEN ASM_SIMP_TAC [LAMBDA_BETA]
    THEN REPEAT (POP_ASSUM (MP_TAC o REWRITE_RULE [DIMINDEX_FINITE_SUM]))
    THEN ARITH_TAC)

  let PASTECART_VECTOR_MAP ← prove
   r"!f:A->B x:A^N y:A^M.
    pastecart (vector_map f x) (vector_map f y) =
      vector_map f (pastecart x y)"
   (COMMON_TAC vector_map)

  let PASTECART_VECTOR_MAP2 ← prove
   r"!f:A->B->C x1:A^N x2 y1:A^M y2.
    pastecart (vector_map2 f x1 x2) (vector_map2 f y1 y2)
      = vector_map2 f (pastecart x1 y1) (pastecart x2 y2)"
   (COMMON_TAC vector_map2)

  let vector_zip ← new_definition
   r"vector_zip (v1:A^N) (v2:B^N) : (A#B)^N = lambda i. (v1$i,v2$i)"

  let VECTOR_ZIP_COMPONENT ← prove
   r"!i v1:A^N v2:B^N. (vector_zip v1 v2)$i = (v1$i,v2$i)"
   (REPEAT GEN_TAC THEN CHOOSE_TAC (← HolLight.INST_TYPE [(← qty "A#B", ← qty "C")] (← SPEC_ALL
      FINITE_INDEX_INRANGE_4)) THEN ASM_SIMP_TAC [vector_zip, LAMBDA_BETA])

  let vector_unzip ← new_definition
   r"vector_unzip (v:(A#B)^N):(A^N)#(B^N) = vector_map FST v,vector_map SND v"

  let VECTOR_UNZIP_COMPONENT ← prove
   r"!i v:(A#B)^N. (FST (vector_unzip v))$i = FST (v$i)
    /\ (SND (vector_unzip v))$i = SND (v$i)"
   (REWRITE_TAC [vector_unzip, VECTOR_MAP_COMPONENT])

  let VECTOR_MAP2_AS_VECTOR_MAP ← prove
   r"!f:A->B->C v1:A^N v2:B^N.
    vector_map2 f v1 v2 = vector_map (UNCURRY f) (vector_zip v1 v2)"
   (REWRITE_TAC [CART_EQ, VECTOR_MAP2_COMPONENT, VECTOR_MAP_COMPONENT,
      VECTOR_ZIP_COMPONENT, UNCURRY_DEF])

  return { SINGLE, distrib, DISTRIB, REWRITE_TACS, GCONJUNCTS, COMPONENT_LE_NORM_ALT,
           RE_IM_NORM, RE_NORM, IM_NORM, ABS_RE_NORM, ABS_IM_NORM, NORM_RE, NORM_RE_ADD,
           NORM_RE_SUB, NORM2_ADD_REAL, COMPLEX_EQ_RCANCEL_IMP, COMPLEX_BALANCE_DIV_MUL,
           CSQRT_MUL_LCX_LT, CSQRT_MUL_LCX, REAL_ADD_POW_2, COMPLEX_ADD_POW_2,
           FINITE_INTER_ENUM, NORM_PASTECART_GE1, NORM_PASTECART_GE2, SUMS_PASTECART,
           LINEAR_SUMS, real_of_complex, REAL_OF_COMPLEX, REAL_OF_COMPLEX_RE,
           REAL_OF_COMPLEX_CX, REAL_OF_COMPLEX_NORM, REAL_OF_COMPLEX_ADD, REAL_MUL,
           REAL_OF_COMPLEX_MUL, REAL_OF_COMPLEX_0, REAL_COMPLEX_ADD_CNJ, vector_const,
           vector_map, vector_map2, vector_map3, FINITE_INDEX_INRANGE_4, COMPONENT_TAC,
           VECTOR_CONST_COMPONENT, VECTOR_MAP_COMPONENT, VECTOR_MAP2_COMPONENT,
           VECTOR_MAP3_COMPONENT, VECTOR_MAP_VECTOR_CONST, VECTOR_MAP_VECTOR_MAP,
           VECTOR_MAP_VECTOR_MAP2, VECTOR_MAP2_LVECTOR_CONST, VECTOR_MAP2_RVECTOR_CONST,
           VECTOR_MAP2_LVECTOR_MAP, VECTOR_MAP2_RVECTOR_MAP, VECTOR_MAP2_LVECTOR_MAP2,
           VECTOR_MAP2_RVECTOR_MAP2, VECTOR_MAP_SIMP_TAC, VECTOR_MAP_PROPERTY_TAC,
           VECTOR_MAP_PROPERTY, COMPLEX_VECTOR_MAP, COMPLEX_NEG_IS_A_MAP, VECTOR_NEG_IS_A_MAP,
           VECTOR_MAP_VECTOR_MAP_ALT, COMPLEX_VECTOR_MAP2, VECTOR_MAP2_RVECTOR_MAP_ALT,
           COMPLEX_ADD_IS_A_MAP, VECTOR_ADD_IS_A_MAP, COMPLEX_SUB_IS_A_MAP,
           VECTOR_SUB_IS_A_MAP, PASTECART_VECTOR_MAP, PASTECART_VECTOR_MAP2, vector_zip,
           VECTOR_ZIP_COMPONENT, vector_unzip, VECTOR_UNZIP_COMPONENT,
           VECTOR_MAP2_AS_VECTOR_MAP }

/- ------------------------------------------------------------------------- -/
/- Basic arithmetic; vector space axioms and additional basic results;       -/
/- linearity.  (cvectors.ml 476-800)                                         -/
/- ------------------------------------------------------------------------- -/

structure CVB where
  prioritize_cvector : ExceptT String IO Unit
  cvector_zero : thm
  cvector_neg : thm
  cvector_add : thm
  cvector_sub : thm
  cvector_mul : thm
  CVECTOR_ZERO_COMPONENT : thm
  CVECTOR_NON_ZERO : thm
  CVECTOR_ADD_COMPONENT : thm
  CVECTOR_SUB_COMPONENT : thm
  CVECTOR_NEG_COMPONENT : thm
  CVECTOR_MUL_COMPONENT : thm
  CVECTOR_ARITH_TAC : tactic
  CVECTOR_ARITH : term → ExceptT String IO thm
  CVECTOR_ADD_SYM : thm
  CVECTOR_ADD_ASSOC : thm
  CVECTOR_ADD_ID : thm
  CVECTOR_ADD_RID : thm
  CVECTOR_ADD_LID : thm
  CVECTOR_ADD_INV : thm
  CVECTOR_MUL_ASSOC : thm
  CVECTOR_SUB_LDISTRIB : thm
  CVECTOR_SCALAR_RDIST : thm
  CVECTOR_MUL_ID : thm
  CVECTOR_SUB_REFL : thm
  CVECTOR_SUB_RADD : thm
  CVECTOR_NEG_SUB : thm
  CVECTOR_SUB_EQ : thm
  CVECTOR_SUB_ADD : thm
  CVECTOR_SUB_ADD2 : thm
  CVECTOR_ADD_LDISTRIB : thm
  CVECTOR_ADD_RDISTRIB : thm
  CVECTOR_SUB_RDISTRIB : thm
  CVECTOR_ADD_SUB : thm
  CVECTOR_EQ_ADDR : thm
  CVECTOR_SUB : thm
  CVECTOR_SUB_RZERO : thm
  CVECTOR_MUL_RZERO : thm
  CVECTOR_MUL_LZERO : thm
  CVECTOR_MUL_EQ_0 : thm
  CVECTOR_NEG_MINUS1 : thm
  CVECTOR_SUB_LZERO : thm
  CVECTOR_NEG_NEG : thm
  CVECTOR_MUL_LNEG : thm
  CVECTOR_MUL_RNEG : thm
  CVECTOR_NEG_0 : thm
  CVECTOR_NEG_EQ_0 : thm
  CVECTOR_ADD_AC : thm
  CVECTOR_MUL_LCANCEL : thm
  CVECTOR_MUL_RCANCEL : thm
  clinear : thm
  COMMON_TAC : List thm → tactic
  CLINEAR_COMPOSE_CMUL : thm
  CLINEAR_COMPOSE_NEG : thm
  CLINEAR_COMPOSE_ADD : thm
  CLINEAR_COMPOSE_SUB : thm
  CLINEAR_COMPOSE : thm
  CLINEAR_ID : thm
  CLINEAR_I : thm
  CLINEAR_ZERO : thm
  CLINEAR_NEGATION : thm
  CLINEAR_VMUL_COMPONENT : thm
  CLINEAR_0 : thm
  CLINEAR_CMUL : thm
  CLINEAR_NEG : thm
  CLINEAR_ADD : thm
  CLINEAR_SUB : thm
  CLINEAR_INJECTIVE_0 : thm
  deriving Inhabited

@[nospecialize]
def setupCVB [HolBase] (D : CvectorsDeps) (BA : CVA) : ExceptT String IO CVB := do
  -- @@SCOPE BEGIN
  let { new_definition, MESON_TAC, .. } := D.cx.cvx
  let { overload_interface, .. } := D.cx
  let { make_overloadable, .. } := D
  let { AND_FORALL_THM, CART_EQ, CONJ_ASSOC, .. } := D.cx.cvx.core1
  let { IMP_IMP, .. } := D.cx.cvx.core2
  let { LAMBDA_BETA, MONO_FORALL, .. } := D.cx.cvx.core3
  let { o_THM, .. } := D.cx.cvx.core6
  let { I_DEF, .. } := D.thms
  let { complex_sub, SIMPLE_COMPLEX_ARITH_TAC, .. } := D.cxa
  let { COMPLEX_ADD_SYM, COMPLEX_ADD_ASSOC, COMPLEX_ADD_LID, COMPLEX_ADD_LINV,
        COMPLEX_MUL_ASSOC, COMPLEX_MUL_LID, COMPLEX_ADD_LDISTRIB, COMPLEX_ADD_RID,
        COMPLEX_ADD_RINV, COMPLEX_ADD_RDISTRIB, COMPLEX_MUL_RZERO, COMPLEX_MUL_LZERO,
        COMPLEX_NEG_NEG, COMPLEX_MUL_RNEG, COMPLEX_MUL_LNEG, COMPLEX_NEG_0,
        COMPLEX_EQ_ADD_LCANCEL_0, COMPLEX_SUB_ADD, COMPLEX_SUB_ADD2, COMPLEX_SUB_REFL,
        COMPLEX_SUB_0, COMPLEX_NEG_EQ_0, COMPLEX_NEG_SUB, COMPLEX_ADD_SUB, COMPLEX_NEG_MINUS1,
        COMPLEX_SUB_LZERO, COMPLEX_SUB_RZERO, COMPLEX_ADD_SUB2, COMPLEX_SUB_LDISTRIB,
        COMPLEX_SUB_RDISTRIB, .. } := D.cxb
  let { COMPLEX_ENTIRE, .. } := D.cxc
  let { GCONJUNCTS, vector_const, vector_map, vector_map2, VECTOR_CONST_COMPONENT,
        VECTOR_MAP_COMPONENT, VECTOR_MAP2_COMPONENT, VECTOR_MAP_PROPERTY, .. } := BA
  -- @@SCOPE END

  /- ======================================================================= -/
  /- BASIC ARITHMETIC                                                        -/
  /- ======================================================================= -/

  make_overloadable "%" (← qty "A-> B-> B")

  let prioritize_cvector : ExceptT String IO Unit := do
    overload_interface "--" (← q r"(cvector_neg):complex^N->complex^N")
    overload_interface "+" (← q r"(cvector_add):complex^N->complex^N->complex^N")
    overload_interface "-" (← q r"(cvector_sub):complex^N->complex^N->complex^N")
    overload_interface "%" (← q r"(cvector_mul):complex->complex^N->complex^N")

  let cvector_zero ← new_definition
   r"cvector_zero:complex^N = vector_const (Cx(&0))"

  let cvector_neg ← new_definition
   r"cvector_neg :complex^N->complex^N = vector_map (--)"

  let cvector_add ← new_definition
   r"cvector_add :complex^N->complex^N->complex^N = vector_map2 (+)"

  let cvector_sub ← new_definition
   r"cvector_sub :complex^N->complex^N->complex^N = vector_map2 (-)"

  let cvector_mul ← new_definition
   r"(cvector_mul:complex->complex^N->complex^N) a = vector_map (( * ) a)"

  overload_interface "%" (← q r"(%):real->real^N->real^N")
  prioritize_cvector

  let CVECTOR_ZERO_COMPONENT ← prove
   r"!i. (cvector_zero:complex^N)$i = Cx(&0)"
   (REWRITE_TAC [cvector_zero, VECTOR_CONST_COMPONENT])

  let CVECTOR_NON_ZERO ← prove
   r"!x:complex^N. ~(x=cvector_zero)
    <=> ?i. 1 <= i /\ i <= dimindex(:N) /\ ~(x$i = Cx(&0))"
   (GEN_TAC THEN GEN_REWRITE_TAC (fun c => RATOR_CONV (ONCE_DEPTH_CONV c)) [CART_EQ]
    THEN REWRITE_TAC [CVECTOR_ZERO_COMPONENT] THEN MESON_TAC [])

  let CVECTOR_ADD_COMPONENT ← prove
   r"!X Y:complex^N i. ((X + Y)$i = X$i + Y$i)"
   (REWRITE_TAC [cvector_add, VECTOR_MAP2_COMPONENT])

  let CVECTOR_SUB_COMPONENT ← prove
   r"!X:complex^N Y i. ((X - Y)$i = X$i - Y$i)"
   (REWRITE_TAC [cvector_sub, VECTOR_MAP2_COMPONENT])

  let CVECTOR_NEG_COMPONENT ← prove
   r"!X:complex^N i. ((--X)$i = --(X$i))"
   (REWRITE_TAC [cvector_neg, VECTOR_MAP_COMPONENT])

  let CVECTOR_MUL_COMPONENT ← prove
   r"!c:complex X:complex^N i. ((c % X)$i = c * X$i)"
   (REWRITE_TAC [cvector_mul, VECTOR_MAP_COMPONENT])

  -- Simple generic tactic adapted from VECTOR_ARITH_TAC
  let CVECTOR_ARITH_TAC : tactic ← do
    let RENAMED_LAMBDA_BETA (th : thm) : ExceptT String IO thm := do
      let t ← liftExcept (funpowM 3 rand (concl th))
      let (d, _) ← liftExcept (HolCore.Basics.dest_fun_ty (type_of t))
      if d == aty then HolLight.INST_TYPE [(aty, bty), (bty, aty)] LAMBDA_BETA
      else pure LAMBDA_BETA
    pure (POP_ASSUM_LIST (K ALL_TAC) THEN
      REPEAT (GEN_TAC ORELSE CONJ_TAC ORELSE DISCH_TAC ORELSE EQ_TAC) THEN
      REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC] THEN
      GEN_REWRITE_TAC ONCE_DEPTH_CONV [CART_EQ] THEN
      REWRITE_TAC [AND_FORALL_THM] THEN TRY EQ_TAC THEN
      TRY (MATCH_MP_TAC MONO_FORALL) THEN GEN_TAC THEN
      REWRITE_TAC [← TAUT (← q r"(a ==> b) /\ (a ==> c) <=> a ==> b /\ c"),
                   ← TAUT (← q r"(a ==> b) \/ (a ==> c) <=> a ==> b \/ c")] THEN
      TRY (MATCH_MP_TAC (← TAUT (← q r"(a ==> b ==> c) ==> (a ==> b) ==> (a ==> c)"))) THEN
      REWRITE_TAC [cvector_zero, cvector_add, cvector_sub, cvector_neg, cvector_mul,
        vector_map, vector_map2, vector_const] THEN
      DISCH_THEN (fun th => tactic_of do
        pure (REWRITE_TAC [← MATCH_MP (← RENAMED_LAMBDA_BETA th) th])) THEN
      SIMPLE_COMPLEX_ARITH_TAC)

  let CVECTOR_ARITH (tm : term) : ExceptT String IO thm :=
    ExceptT.mk (HolCore.Tactics.prove HolBase.B tm CVECTOR_ARITH_TAC)

  /- ======================================================================= -/
  /-  VECTOR SPACE AXIOMS AND ADDITIONAL BASIC RESULTS                       -/
  /- ======================================================================= -/

  let CVECTOR_MAP_PROPERTY (tm : term) : thm → ExceptT String IO thm :=
    VECTOR_MAP_PROPERTY tm [cvector_zero, cvector_add, cvector_sub, cvector_neg,
      cvector_mul]

  let CVECTOR_ADD_SYM ← CVECTOR_MAP_PROPERTY
    (← q r"!x y:complex^N. x + y = y + x")
    COMPLEX_ADD_SYM

  let CVECTOR_ADD_ASSOC ← CVECTOR_MAP_PROPERTY
    (← q r"!x y z:complex^N. x + (y + z) = (x + y) + z")
    COMPLEX_ADD_ASSOC

  let CVECTOR_ADD_ID ← CVECTOR_MAP_PROPERTY
    (← q r"!x:complex^N. x + cvector_zero = x /\ cvector_zero + x = x")
    (← CONJ COMPLEX_ADD_RID COMPLEX_ADD_LID)

  let [CVECTOR_ADD_RID, CVECTOR_ADD_LID] ← GCONJUNCTS CVECTOR_ADD_ID
    | throw "CVECTOR_ADD_RID: GCONJUNCTS"

  let CVECTOR_ADD_INV ← CVECTOR_MAP_PROPERTY
    (← q r"!x:complex^N. x + -- x = cvector_zero /\ --x + x = cvector_zero")
    (← CONJ COMPLEX_ADD_RINV COMPLEX_ADD_LINV)

  let CVECTOR_MUL_ASSOC ← CVECTOR_MAP_PROPERTY
    (← q r"!a b x:complex^N. a % (b % x) = (a * b) % x")
    COMPLEX_MUL_ASSOC

  let CVECTOR_SUB_LDISTRIB ← CVECTOR_MAP_PROPERTY
    (← q r"!c x y:complex^N. c % (x - y) = c % x - c % y")
    COMPLEX_SUB_LDISTRIB

  let CVECTOR_SCALAR_RDIST ← CVECTOR_MAP_PROPERTY
    (← q r"!a b x:complex^N. (a + b) % x = a % x + b % x")
    COMPLEX_ADD_RDISTRIB

  let CVECTOR_MUL_ID ← CVECTOR_MAP_PROPERTY
    (← q r"!x:complex^N. Cx(&1) % x = x")
    COMPLEX_MUL_LID

  let CVECTOR_SUB_REFL ← CVECTOR_MAP_PROPERTY
    (← q r"!x:complex^N. x - x = cvector_zero")
    COMPLEX_SUB_REFL

  let CVECTOR_SUB_RADD ← CVECTOR_MAP_PROPERTY
    (← q r"!x y:complex^N. x - (x + y) = --y")
    COMPLEX_ADD_SUB2

  let CVECTOR_NEG_SUB ← CVECTOR_MAP_PROPERTY
    (← q r"!x y:complex^N. --(x - y) = y - x")
    COMPLEX_NEG_SUB

  let CVECTOR_SUB_EQ ← CVECTOR_MAP_PROPERTY
    (← q r"!x y:complex^N. (x - y = cvector_zero) <=> (x = y)")
    COMPLEX_SUB_0

  -- cvectors.ml 611 binds CVECTOR_MUL_LZERO here and rebinds it at 655
  -- before any use; this first binding is never referenced.
  let _CVECTOR_MUL_LZERO ← CVECTOR_MAP_PROPERTY
    (← q r"!x. Cx(&0) % x = cvector_zero")
    COMPLEX_MUL_LZERO

  let CVECTOR_SUB_ADD ← CVECTOR_MAP_PROPERTY
    (← q r"!x y:complex^N. (x - y) + y = x")
    COMPLEX_SUB_ADD

  let CVECTOR_SUB_ADD2 ← CVECTOR_MAP_PROPERTY
    (← q r"!x y:complex^N. y + (x - y) = x")
    COMPLEX_SUB_ADD2

  let CVECTOR_ADD_LDISTRIB ← CVECTOR_MAP_PROPERTY
    (← q r"!c x y:complex^N. c % (x + y) = c % x + c % y")
    COMPLEX_ADD_LDISTRIB

  let CVECTOR_ADD_RDISTRIB ← CVECTOR_MAP_PROPERTY
    (← q r"!a b x:complex^N. (a + b) % x = a % x + b % x")
    COMPLEX_ADD_RDISTRIB

  let CVECTOR_SUB_RDISTRIB ← CVECTOR_MAP_PROPERTY
    (← q r"!a b x:complex^N. (a - b) % x = a % x - b % x")
    COMPLEX_SUB_RDISTRIB

  let CVECTOR_ADD_SUB ← CVECTOR_MAP_PROPERTY
    (← q r"!x y:complex^N. (x + y:complex^N) - x = y")
    COMPLEX_ADD_SUB

  let CVECTOR_EQ_ADDR ← CVECTOR_MAP_PROPERTY
    (← q r"!x y:complex^N. (x + y = x) <=> (y = cvector_zero)")
    COMPLEX_EQ_ADD_LCANCEL_0

  let CVECTOR_SUB ← CVECTOR_MAP_PROPERTY
    (← q r"!x y:complex^N. x - y = x + --(y:complex^N)")
    complex_sub

  let CVECTOR_SUB_RZERO ← CVECTOR_MAP_PROPERTY
    (← q r"!x:complex^N. x - cvector_zero = x")
    COMPLEX_SUB_RZERO

  let CVECTOR_MUL_RZERO ← CVECTOR_MAP_PROPERTY
    (← q r"!c:complex. c % cvector_zero = cvector_zero")
    COMPLEX_MUL_RZERO

  let CVECTOR_MUL_LZERO ← CVECTOR_MAP_PROPERTY
    (← q r"!x:complex^N. Cx(&0) % x = cvector_zero")
    COMPLEX_MUL_LZERO

  let CVECTOR_MUL_EQ_0 ← prove
   r"!a:complex x:complex^N.
    (a % x = cvector_zero <=> a = Cx(&0) \/ x = cvector_zero)"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL [
      ASM_CASES_TAC (← q r"a=Cx(&0)") THENL [
        ASM_REWRITE_TAC [],
        GEN_REWRITE_TAC (fun c => RATOR_CONV (DEPTH_CONV c)) [CART_EQ]
        THEN ASM_REWRITE_TAC [CVECTOR_MUL_COMPONENT, CVECTOR_ZERO_COMPONENT,
          COMPLEX_ENTIRE]
        THEN GEN_REWRITE_TAC (fun c => RAND_CONV (DEPTH_CONV c)) [CART_EQ]
        THEN REWRITE_TAC [CVECTOR_ZERO_COMPONENT]
      ],
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [CVECTOR_MUL_RZERO, CVECTOR_MUL_LZERO]
    ])

  let CVECTOR_NEG_MINUS1 ← CVECTOR_MAP_PROPERTY
    (← q r"!x:complex^N. --x = (--(Cx(&1))) % x")
    (← GSYM COMPLEX_NEG_MINUS1)

  let CVECTOR_SUB_LZERO ← CVECTOR_MAP_PROPERTY
    (← q r"!x:complex^N. cvector_zero - x = --x")
    COMPLEX_SUB_LZERO

  let CVECTOR_NEG_NEG ← CVECTOR_MAP_PROPERTY
    (← q r"!x:complex^N. --(--(x:complex^N)) = x")
    COMPLEX_NEG_NEG

  let CVECTOR_MUL_LNEG ← CVECTOR_MAP_PROPERTY
    (← q r"!c x:complex^N. --c % x = --(c % x)")
    COMPLEX_MUL_LNEG

  let CVECTOR_MUL_RNEG ← CVECTOR_MAP_PROPERTY
    (← q r"!c x:complex^N. c % --x = --(c % x)")
    COMPLEX_MUL_RNEG

  let CVECTOR_NEG_0 ← CVECTOR_MAP_PROPERTY
    (← q r"--cvector_zero = cvector_zero")
    COMPLEX_NEG_0

  let CVECTOR_NEG_EQ_0 ← CVECTOR_MAP_PROPERTY
    (← q r"!x:complex^N. --x = cvector_zero <=> x = cvector_zero")
    COMPLEX_NEG_EQ_0

  let CVECTOR_ADD_AC ← prove
   r"!x y z:complex^N.
    (x + y = y + x) /\ ((x + y) + z = x + y + z) /\ (x + y + z = y + x + z)"
   (MESON_TAC [CVECTOR_ADD_SYM, CVECTOR_ADD_ASSOC])

  let CVECTOR_MUL_LCANCEL ← prove
   r"!a x y:complex^N. a % x = a % y <=> a = Cx(&0) \/ x = y"
   (MESON_TAC [CVECTOR_MUL_EQ_0, CVECTOR_SUB_LDISTRIB, CVECTOR_SUB_EQ])

  let CVECTOR_MUL_RCANCEL ← prove
   r"!a b x:complex^N. a % x = b % x <=> a = b \/ x = cvector_zero"
   (MESON_TAC [CVECTOR_MUL_EQ_0, CVECTOR_SUB_RDISTRIB, COMPLEX_SUB_0, CVECTOR_SUB_EQ])

  /- ======================================================================= -/
  /- LINEARITY                                                               -/
  /- ======================================================================= -/

  let clinear ← new_definition
   r"clinear (f:complex^M->complex^N)
    <=> (!x y. f(x + y) = f(x) + f(y)) /\ (!c x. f(c % x) = c % f(x))"

  let COMMON_TAC (additional_thms : List thm) : tactic :=
    SIMP_TAC [clinear] THEN REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [CART_EQ]
    THEN SIMP_TAC (CVECTOR_ADD_COMPONENT :: CVECTOR_MUL_COMPONENT :: additional_thms)
    THEN SIMPLE_COMPLEX_ARITH_TAC

  let CLINEAR_COMPOSE_CMUL ← prove
   r"!f:complex^M->complex^N c. clinear f ==> clinear (\x. c % f x)"
   (COMMON_TAC [])

  let CLINEAR_COMPOSE_NEG ← prove
   r"!f:complex^M->complex^N. clinear f ==> clinear (\x. --(f x))"
   (COMMON_TAC [CVECTOR_NEG_COMPONENT])

  let CLINEAR_COMPOSE_ADD ← prove
   r"!f:complex^M->complex^N g. clinear f /\ clinear g ==> clinear (\x. f x + g x)"
   (COMMON_TAC [])

  let CLINEAR_COMPOSE_SUB ← prove
   r"!f:complex^M->complex^N g. clinear f /\ clinear g ==> clinear (\x. f x - g x)"
   (COMMON_TAC [CVECTOR_SUB_COMPONENT])

  let CLINEAR_COMPOSE ← prove
   r"!f:complex^M->complex^N g. clinear f /\ clinear g ==> clinear (g o f)"
   (SIMP_TAC [clinear, o_THM])

  let CLINEAR_ID ← prove
   r"clinear (\x:complex^N. x)"
   (REWRITE_TAC [clinear])

  let CLINEAR_I ← prove
   r"clinear (I:complex^N->complex^N)"
   (REWRITE_TAC [I_DEF, CLINEAR_ID])

  let CLINEAR_ZERO ← prove
   r"clinear ((\x. cvector_zero):complex^M->complex^N)"
   (COMMON_TAC [CVECTOR_ZERO_COMPONENT])

  let CLINEAR_NEGATION ← prove
   r"clinear ((--):complex^N->complex^N)"
   (COMMON_TAC [CVECTOR_NEG_COMPONENT])

  let CLINEAR_VMUL_COMPONENT ← prove
   r"!f:complex^M->complex^N v:complex^P k.
     clinear f /\ 1 <= k /\ k <= dimindex(:N) ==> clinear (\x. (f x)$k % v)"
   (COMMON_TAC [])

  let CLINEAR_0 ← prove
   r"!f:complex^M->complex^N. clinear f ==> (f cvector_zero = cvector_zero)"
   (MESON_TAC [CVECTOR_MUL_LZERO, clinear])

  let CLINEAR_CMUL ← prove
   r"!f:complex^M->complex^N c x. clinear f ==> (f (c % x) = c % f x)"
   (SIMP_TAC [clinear])

  let CLINEAR_NEG ← prove
   r"!f:complex^M->complex^N x. clinear f ==> (f (--x) = --(f x))"
   (ONCE_REWRITE_TAC [CVECTOR_NEG_MINUS1] THEN SIMP_TAC [CLINEAR_CMUL])

  let CLINEAR_ADD ← prove
   r"!f:complex^M->complex^N x y. clinear f ==> (f (x + y) = f x + f y)"
   (SIMP_TAC [clinear])

  let CLINEAR_SUB ← prove
   r"!f:complex^M->complex^N x y. clinear f ==> (f(x - y) = f x - f y)"
   (SIMP_TAC [CVECTOR_SUB, CLINEAR_ADD, CLINEAR_NEG])

  let CLINEAR_INJECTIVE_0 ← prove
   r"!f:complex^M->complex^N.
  clinear f
   ==> ((!x y. f x = f y ==> x = y)
    <=> (!x. f x = cvector_zero ==> x = cvector_zero))"
   (ONCE_REWRITE_TAC [← GSYM CVECTOR_SUB_EQ]
    THEN SIMP_TAC [CVECTOR_SUB_RZERO, ← GSYM CLINEAR_SUB]
    THEN MESON_TAC [CVECTOR_SUB_RZERO])

  return { prioritize_cvector, cvector_zero, cvector_neg, cvector_add, cvector_sub,
           cvector_mul, CVECTOR_ZERO_COMPONENT, CVECTOR_NON_ZERO, CVECTOR_ADD_COMPONENT,
           CVECTOR_SUB_COMPONENT, CVECTOR_NEG_COMPONENT, CVECTOR_MUL_COMPONENT,
           CVECTOR_ARITH_TAC, CVECTOR_ARITH, CVECTOR_ADD_SYM, CVECTOR_ADD_ASSOC,
           CVECTOR_ADD_ID, CVECTOR_ADD_RID, CVECTOR_ADD_LID, CVECTOR_ADD_INV,
           CVECTOR_MUL_ASSOC, CVECTOR_SUB_LDISTRIB, CVECTOR_SCALAR_RDIST, CVECTOR_MUL_ID,
           CVECTOR_SUB_REFL, CVECTOR_SUB_RADD, CVECTOR_NEG_SUB, CVECTOR_SUB_EQ,
           CVECTOR_SUB_ADD, CVECTOR_SUB_ADD2, CVECTOR_ADD_LDISTRIB, CVECTOR_ADD_RDISTRIB,
           CVECTOR_SUB_RDISTRIB, CVECTOR_ADD_SUB, CVECTOR_EQ_ADDR, CVECTOR_SUB,
           CVECTOR_SUB_RZERO, CVECTOR_MUL_RZERO, CVECTOR_MUL_LZERO, CVECTOR_MUL_EQ_0,
           CVECTOR_NEG_MINUS1, CVECTOR_SUB_LZERO, CVECTOR_NEG_NEG, CVECTOR_MUL_LNEG,
           CVECTOR_MUL_RNEG, CVECTOR_NEG_0, CVECTOR_NEG_EQ_0, CVECTOR_ADD_AC,
           CVECTOR_MUL_LCANCEL, CVECTOR_MUL_RCANCEL, clinear, COMMON_TAC,
           CLINEAR_COMPOSE_CMUL, CLINEAR_COMPOSE_NEG, CLINEAR_COMPOSE_ADD,
           CLINEAR_COMPOSE_SUB, CLINEAR_COMPOSE, CLINEAR_ID, CLINEAR_I, CLINEAR_ZERO,
           CLINEAR_NEGATION, CLINEAR_VMUL_COMPONENT, CLINEAR_0, CLINEAR_CMUL, CLINEAR_NEG,
           CLINEAR_ADD, CLINEAR_SUB, CLINEAR_INJECTIVE_0 }

/- ------------------------------------------------------------------------- -/
/- Pasting complex vectors; real and imaginary vectors; flattening complex   -/
/- vectors into real vectors; conjugate vector.  (cvectors.ml 801-1162)      -/
/- ------------------------------------------------------------------------- -/

structure CVC where
  CLINEAR_FSTCART_SNDCART : thm
  FSTCART_CLINEAR : thm
  SNDCART_CLINEAR : thm
  FSTCART_SNDCART_CVECTOR_ZERO : thm
  FSTCART_CVECTOR_ZERO : thm
  SNDCART_CVECTOR_ZERO : thm
  FSTCART_SNDCART_CVECTOR_ADD : thm
  FSTCART_SNDCART_CVECTOR_MUL : thm
  PASTECART_TAC : List thm → tactic
  PASTECART_CVECTOR_ZERO : thm
  PASTECART_EQ_CVECTOR_ZERO : thm
  PASTECART_CVECTOR_ADD : thm
  PASTECART_CVECTOR_MUL : thm
  cvector_re : thm
  cvector_im : thm
  vector_to_cvector : thm
  CVECTOR_RE_COMPONENT : thm
  CVECTOR_IM_COMPONENT : thm
  VECTOR_TO_CVECTOR_COMPONENT : thm
  VECTOR_TO_CVECTOR_ZERO : thm
  VECTOR_TO_CVECTOR_ZERO_EQ : thm
  CVECTOR_ZERO_VEC0 : thm
  VECTOR_TO_CVECTOR_MUL : thm
  CVECTOR_EQ : thm
  CVECTOR_RE_VECTOR_TO_CVECTOR : thm
  CVECTOR_IM_VECTOR_TO_CVECTOR : thm
  CVECTOR_IM_VECTOR_TO_CVECTOR_IM : thm
  VECTOR_TO_CVECTOR_CVECTOR_RE_IM : thm
  CVECTOR_IM_VECTOR_TO_CVECTOR_RE_IM : thm
  CVECTOR_RE_VECTOR_TO_CVECTOR_RE_IM : thm
  CVECTOR_RE_ADD : thm
  CVECTOR_IM_ADD : thm
  CVECTOR_RE_MUL : thm
  CVECTOR_IM_MUL : thm
  CVECTOR_RE_VECTOR_MAP : thm
  CVECTOR_IM_VECTOR_MAP : thm
  VECTOR_MAP_CVECTOR_RE : thm
  VECTOR_MAP_CVECTOR_IM : thm
  CVECTOR_RE_VECTOR_MAP2 : thm
  CVECTOR_IM_VECTOR_MAP2 : thm
  cvector_flatten : thm
  FLATTEN_RE_IM_COMPONENT : thm
  complex_vector : thm
  COMPLEX_VECTOR_TRANSPOSE : thm
  cvector_unflatten : thm
  UNFLATTEN_FLATTEN : thm
  FLATTEN_UNFLATTEN : thm
  FLATTEN_CLINEAR : thm
  FLATTEN_MAP : thm
  FLATTEN_NEG : thm
  CVECTOR_NEG_ALT : thm
  FLATTEN_MAP2 : thm
  FLATTEN_ADD : thm
  CVECTOR_ADD_ALT : thm
  FLATTEN_SUB : thm
  CVECTOR_SUB_ALT : thm
  cvector_cnj : thm
  CVECTOR_MAP_PROPERTY : term → thm → ExceptT String IO thm
  CVECTOR_CNJ_ADD : thm
  CVECTOR_CNJ_SUB : thm
  CVECTOR_CNJ_NEG : thm
  CVECTOR_RE_CNJ : thm
  CVECTOR_IM_CNJ : thm
  CVECTOR_CNJ_CNJ : thm
  deriving Inhabited

@[nospecialize]
def setupCVC [HolBase] (D : CvectorsDeps) (BA : CVA) (BB : CVB) :
    ExceptT String IO CVC := do
  -- @@SCOPE BEGIN
  let { new_definition, ARITH_RULE, MESON_TAC, .. } := D.cx.cvx
  let { EQ_SYM, .. } := HolBase.T
  let { CART_EQ, DIMINDEX_FINITE_SUM, .. } := D.cx.cvx.core1
  let { FSTCART_PASTECART, FUN_EQ_THM, .. } := D.cx.cvx.core2
  let { LAMBDA_BETA, REAL_ADD_LID, REAL_ADD_RID, .. } := D.cx.cvx.core3
  let { REAL_MUL_LZERO, REAL_NEG_0, SNDCART_PASTECART, .. } := D.cx.cvx.core5
  let { o_DEF, .. } := D.cx.cvx.core6
  let { FSTCART_ADD, FSTCART_CMUL, .. } := D.cx.cvx.vec2
  let { PASTECART_ADD, PASTECART_CMUL, SNDCART_ADD, SNDCART_CMUL, .. } := D.cx.cvx.vec3
  let { VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, VEC_COMPONENT, linear, .. } :=
    D.cx.cvx.vec4
  let { I_DEF, MULT_2, PASTECART_EQ, PASTECART_FST_SND, fstcart, pastecart, sndcart, .. } :=
    D.thms
  let { RE_DEF, IM_DEF, COMPLEX_EQ, SIMPLE_COMPLEX_ARITH_TAC, .. } := D.cxa
  let { CX_INJ, CX_ADD, CX_MUL, RE_CX, RE_ADD, IM_CX, IM_ADD, RE_II, RE_MUL_II, IM_MUL_II,
        RE_MUL_CX, IM_MUL_CX, .. } := D.cxc
  let { CNJ_CNJ, CNJ_NEG, CNJ_ADD, CNJ_SUB, RE_CNJ, IM_CNJ, .. } := D.cxg
  let { VECTOR_MAP_COMPONENT, VECTOR_MAP2_COMPONENT, VECTOR_MAP_VECTOR_MAP,
        VECTOR_MAP_VECTOR_MAP2, VECTOR_MAP2_LVECTOR_MAP, VECTOR_MAP2_RVECTOR_MAP,
        VECTOR_MAP_PROPERTY_TAC, VECTOR_MAP_PROPERTY, COMPLEX_NEG_IS_A_MAP,
        VECTOR_NEG_IS_A_MAP, COMPLEX_ADD_IS_A_MAP, VECTOR_ADD_IS_A_MAP, COMPLEX_SUB_IS_A_MAP,
        VECTOR_SUB_IS_A_MAP, PASTECART_VECTOR_MAP, PASTECART_VECTOR_MAP2, .. } := BA
  let { cvector_zero, cvector_neg, cvector_add, cvector_sub, cvector_mul,
        CVECTOR_ZERO_COMPONENT, CVECTOR_ADD_COMPONENT, CVECTOR_MUL_COMPONENT, clinear,
        .. } := BB
  -- @@SCOPE END

  /- ======================================================================= -/
  /- PASTING COMPLEX VECTORS                                                 -/
  /- ======================================================================= -/

  let CLINEAR_FSTCART_SNDCART ← prove
   r"clinear fstcart /\ clinear sndcart"
   (SIMP_TAC [clinear, fstcart, sndcart, CART_EQ, LAMBDA_BETA, CVECTOR_ADD_COMPONENT,
      CVECTOR_MUL_COMPONENT, DIMINDEX_FINITE_SUM,
      ← ARITH_RULE (← q r"x <= a ==> x <= a + b:num"),
      ← ARITH_RULE (← q r"x <= b ==> x + a <= a + b:num")])

  let FSTCART_CLINEAR ← CONJUNCT1 CLINEAR_FSTCART_SNDCART
  let SNDCART_CLINEAR ← CONJUNCT2 CLINEAR_FSTCART_SNDCART

  let FSTCART_SNDCART_CVECTOR_ZERO ← prove
   r"fstcart cvector_zero = cvector_zero /\ sndcart cvector_zero = cvector_zero"
   (SIMP_TAC [CVECTOR_ZERO_COMPONENT, fstcart, sndcart, LAMBDA_BETA, CART_EQ,
      DIMINDEX_FINITE_SUM, ← ARITH_RULE (← q r"x <= a ==> x <= a + b:num"),
      ← ARITH_RULE (← q r"x <= b ==> x + a <= a + b:num")])

  let FSTCART_CVECTOR_ZERO ← CONJUNCT1 FSTCART_SNDCART_CVECTOR_ZERO
  let SNDCART_CVECTOR_ZERO ← CONJUNCT2 FSTCART_SNDCART_CVECTOR_ZERO

  let FSTCART_SNDCART_CVECTOR_ADD ← prove
   r"!x:complex^(M,N)finite_sum y.
  fstcart(x + y) = fstcart(x) + fstcart(y)
  /\ sndcart(x + y) = sndcart(x) + sndcart(y)"
   (REWRITE_TAC [← REWRITE_RULE [clinear] CLINEAR_FSTCART_SNDCART])

  let FSTCART_SNDCART_CVECTOR_MUL ← prove
   r"!x:complex^(M,N)finite_sum c.
  fstcart(c % x) = c % fstcart(x) /\ sndcart(c % x) = c % sndcart(x)"
   (REWRITE_TAC [← REWRITE_RULE [clinear] CLINEAR_FSTCART_SNDCART])

  let PASTECART_TAC (xs : List thm) : tactic :=
    REWRITE_TAC (PASTECART_EQ :: FSTCART_PASTECART :: SNDCART_PASTECART :: xs)

  let PASTECART_CVECTOR_ZERO ← prove
   r"pastecart (cvector_zero:complex^N) (cvector_zero:complex^M) = cvector_zero"
   (PASTECART_TAC [FSTCART_SNDCART_CVECTOR_ZERO])

  let PASTECART_EQ_CVECTOR_ZERO ← prove
   r"!x:complex^N y:complex^M.
    pastecart x y = cvector_zero <=> x = cvector_zero /\ y = cvector_zero"
   (PASTECART_TAC [FSTCART_SNDCART_CVECTOR_ZERO])

  let PASTECART_CVECTOR_ADD ← prove
   r"!x1 y2 x2:complex^N y2:complex^M.
  pastecart x1 y1 + pastecart x2 y2 = pastecart (x1 + x2) (y1 + y2)"
   (PASTECART_TAC [FSTCART_SNDCART_CVECTOR_ADD])

  let PASTECART_CVECTOR_MUL ← prove
   r"!x1 x2 c:complex.
  pastecart (c % x1) (c % y1) = c % pastecart x1 y1"
   (PASTECART_TAC [FSTCART_SNDCART_CVECTOR_MUL])

  /- ======================================================================= -/
  /- REAL AND IMAGINARY VECTORS                                              -/
  /- ======================================================================= -/

  let cvector_re ← new_definition
   r"cvector_re :complex^N -> real^N = vector_map Re"
  let cvector_im ← new_definition
   r"cvector_im :complex^N -> real^N = vector_map Im"
  let vector_to_cvector ← new_definition
   r"vector_to_cvector :real^N -> complex^N = vector_map Cx"

  let CVECTOR_RE_COMPONENT ← prove
   r"!x:complex^N i. (cvector_re x)$i = Re (x$i)"
   (REWRITE_TAC [cvector_re, VECTOR_MAP_COMPONENT])
  let CVECTOR_IM_COMPONENT ← prove
   r"!x:complex^N i. (cvector_im x)$i = Im (x$i)"
   (REWRITE_TAC [cvector_im, VECTOR_MAP_COMPONENT])
  let VECTOR_TO_CVECTOR_COMPONENT ← prove
   r"!x:real^N i. (vector_to_cvector x)$i = Cx(x$i)"
   (REWRITE_TAC [vector_to_cvector, VECTOR_MAP_COMPONENT])

  let VECTOR_TO_CVECTOR_ZERO ← prove
   r"vector_to_cvector (vec 0) = cvector_zero:complex^N"
   (ONCE_REWRITE_TAC [CART_EQ]
    THEN REWRITE_TAC [VECTOR_TO_CVECTOR_COMPONENT, CVECTOR_ZERO_COMPONENT,
      VEC_COMPONENT])

  let VECTOR_TO_CVECTOR_ZERO_EQ ← prove
   r"!x:real^N. vector_to_cvector x = cvector_zero <=> x = vec 0"
   (GEN_TAC THEN EQ_TAC THEN SIMP_TAC [VECTOR_TO_CVECTOR_ZERO]
    THEN ONCE_REWRITE_TAC [CART_EQ]
    THEN SIMP_TAC [VECTOR_TO_CVECTOR_COMPONENT, CVECTOR_ZERO_COMPONENT,
      VEC_COMPONENT, CX_INJ])

  let CVECTOR_ZERO_VEC0 ← prove
   r"!x:complex^N. x = cvector_zero <=> cvector_re x = vec 0 /\ cvector_im x = vec 0"
   (ONCE_REWRITE_TAC [CART_EQ]
    THEN REWRITE_TAC [CVECTOR_ZERO_COMPONENT, CVECTOR_RE_COMPONENT,
      CVECTOR_IM_COMPONENT, VEC_COMPONENT, COMPLEX_EQ, RE_CX, IM_CX]
    THEN MESON_TAC [])

  let VECTOR_TO_CVECTOR_MUL ← prove
   r"!a x:real^N. vector_to_cvector (a % x) = Cx a % vector_to_cvector x"
   (ONCE_REWRITE_TAC [CART_EQ] THEN REWRITE_TAC [VECTOR_TO_CVECTOR_COMPONENT,
      CVECTOR_MUL_COMPONENT, VECTOR_MUL_COMPONENT, CX_MUL])

  let CVECTOR_EQ ← prove
   r"!x:complex^N y z.
    x = vector_to_cvector y + ii % vector_to_cvector z
    <=> cvector_re x = y /\ cvector_im x = z"
   (ONCE_REWRITE_TAC [CART_EQ]
    THEN REWRITE_TAC [CVECTOR_ADD_COMPONENT, CVECTOR_MUL_COMPONENT,
      CVECTOR_RE_COMPONENT, CVECTOR_IM_COMPONENT, VECTOR_TO_CVECTOR_COMPONENT]
    THEN REWRITE_TAC [COMPLEX_EQ, RE_CX, IM_CX, RE_ADD, IM_ADD, RE_MUL_II, REAL_NEG_0,
      REAL_ADD_RID, REAL_ADD_LID, IM_MUL_II] THEN MESON_TAC [])

  let CVECTOR_RE_VECTOR_TO_CVECTOR ← prove
   r"!x:real^N. cvector_re (vector_to_cvector x) = x"
   (ONCE_REWRITE_TAC [CART_EQ]
    THEN REWRITE_TAC [CVECTOR_RE_COMPONENT, VECTOR_TO_CVECTOR_COMPONENT, RE_CX])

  let CVECTOR_IM_VECTOR_TO_CVECTOR ← prove
   r"!x:real^N. cvector_im (vector_to_cvector x) = vec 0"
   (ONCE_REWRITE_TAC [CART_EQ]
    THEN REWRITE_TAC [CVECTOR_IM_COMPONENT, VECTOR_TO_CVECTOR_COMPONENT, IM_CX,
      VEC_COMPONENT])

  let CVECTOR_IM_VECTOR_TO_CVECTOR_IM ← prove
   r"!x:real^N. cvector_im (ii % vector_to_cvector x) = x"
   (ONCE_REWRITE_TAC [CART_EQ]
    THEN REWRITE_TAC [CVECTOR_IM_COMPONENT, VECTOR_TO_CVECTOR_COMPONENT, IM_CX,
      VEC_COMPONENT, CVECTOR_MUL_COMPONENT, IM_MUL_II, RE_CX])

  let VECTOR_TO_CVECTOR_CVECTOR_RE_IM ← prove
   r"!x:complex^N.
    vector_to_cvector (cvector_re x) + ii % vector_to_cvector (cvector_im x)
      = x"
   (GEN_TAC THEN MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC [CVECTOR_EQ])

  let CVECTOR_IM_VECTOR_TO_CVECTOR_RE_IM ← prove
   r"!x y:real^N. cvector_im (vector_to_cvector x + ii % vector_to_cvector y) = y"
   (ONCE_REWRITE_TAC [CART_EQ]
    THEN REWRITE_TAC [CVECTOR_IM_COMPONENT, CVECTOR_ADD_COMPONENT,
      CVECTOR_MUL_COMPONENT, VECTOR_TO_CVECTOR_COMPONENT, IM_ADD, IM_CX, IM_MUL_II,
      RE_CX, REAL_ADD_LID])

  let CVECTOR_RE_VECTOR_TO_CVECTOR_RE_IM ← prove
   r"!x y:real^N. cvector_re (vector_to_cvector x + ii % vector_to_cvector y)= x"
   (ONCE_REWRITE_TAC [CART_EQ]
    THEN REWRITE_TAC [CVECTOR_RE_COMPONENT, CVECTOR_ADD_COMPONENT,
      CVECTOR_MUL_COMPONENT, RE_ADD, VECTOR_TO_CVECTOR_COMPONENT, RE_CX, RE_MUL_CX,
      RE_II, REAL_MUL_LZERO, REAL_ADD_RID])

  let CVECTOR_RE_ADD ← prove
   r"!x y:complex^N. cvector_re (x+y) = cvector_re x + cvector_re y"
   (ONCE_REWRITE_TAC [CART_EQ] THEN REWRITE_TAC [CVECTOR_RE_COMPONENT,
      VECTOR_ADD_COMPONENT, CVECTOR_ADD_COMPONENT, RE_ADD])

  let CVECTOR_IM_ADD ← prove
   r"!x y:complex^N. cvector_im (x+y) = cvector_im x + cvector_im y"
   (ONCE_REWRITE_TAC [CART_EQ]
    THEN REWRITE_TAC [CVECTOR_IM_COMPONENT, VECTOR_ADD_COMPONENT,
      CVECTOR_ADD_COMPONENT, IM_ADD])

  let CVECTOR_RE_MUL ← prove
   r"!a x:complex^N. cvector_re (Cx a % x) = a % cvector_re x"
   (ONCE_REWRITE_TAC [CART_EQ]
    THEN REWRITE_TAC [CVECTOR_RE_COMPONENT, VECTOR_MUL_COMPONENT,
      CVECTOR_MUL_COMPONENT, RE_MUL_CX])

  let CVECTOR_IM_MUL ← prove
   r"!a x:complex^N. cvector_im (Cx a % x) = a % cvector_im x"
   (ONCE_REWRITE_TAC [CART_EQ]
    THEN REWRITE_TAC [CVECTOR_IM_COMPONENT, VECTOR_MUL_COMPONENT,
      CVECTOR_MUL_COMPONENT, IM_MUL_CX])

  let CVECTOR_RE_VECTOR_MAP ← prove
   r"!f v:A^N. cvector_re (vector_map f v) = vector_map (Re o f) v"
   (REWRITE_TAC [cvector_re, VECTOR_MAP_VECTOR_MAP])

  let CVECTOR_IM_VECTOR_MAP ← prove
   r"!f v:A^N. cvector_im (vector_map f v) = vector_map (Im o f) v"
   (REWRITE_TAC [cvector_im, VECTOR_MAP_VECTOR_MAP])

  let VECTOR_MAP_CVECTOR_RE ← prove
   r"!f:real->A v:complex^N.
    vector_map f (cvector_re v) = vector_map (f o Re) v"
   (REWRITE_TAC [cvector_re, VECTOR_MAP_VECTOR_MAP])

  let VECTOR_MAP_CVECTOR_IM ← prove
   r"!f:real->A v:complex^N.
    vector_map f (cvector_im v) = vector_map (f o Im) v"
   (REWRITE_TAC [cvector_im, VECTOR_MAP_VECTOR_MAP])

  let CVECTOR_RE_VECTOR_MAP2 ← prove
   r"!f v1:A^N v2:B^N.
    cvector_re (vector_map2 f v1 v2) = vector_map2 (\x y. Re (f x y)) v1 v2"
   (REWRITE_TAC [cvector_re, VECTOR_MAP_VECTOR_MAP2])

  let CVECTOR_IM_VECTOR_MAP2 ← prove
   r"!f v1:A^N v2:B^N.
    cvector_im (vector_map2 f v1 v2) = vector_map2 (\x y. Im (f x y)) v1 v2"
   (REWRITE_TAC [cvector_im, VECTOR_MAP_VECTOR_MAP2])

  /- ======================================================================= -/
  /- FLATTENING COMPLEX VECTORS INTO REAL VECTORS                            -/
  /-                                                                         -/
  /- Note:                                                                   -/
  /- Theoretically, the following could be defined more generally for       -/
  /- matrices instead of complex vectors, but this would require a           -/
  /- "finite_prod" type constructor, which is not available right now, and   -/
  /- which, at first sight, would probably require dependent types.          -/
  /- ======================================================================= -/

  let cvector_flatten ← new_definition
   r"cvector_flatten (v:complex^N) :real^(N,N) finite_sum =
    pastecart (cvector_re v) (cvector_im v)"

  let FLATTEN_RE_IM_COMPONENT ← prove
   r"!v:complex^N i.
  1 <= i /\ i <= 2 * dimindex(:N)
    ==> (cvector_flatten v)$i =
      if i <= dimindex(:N)
      then (cvector_re v)$i
      else (cvector_im v)$(i-dimindex(:N))"
   (SIMP_TAC [MULT_2, ← GSYM DIMINDEX_FINITE_SUM, cvector_flatten, pastecart,
      LAMBDA_BETA])

  let complex_vector ← new_definition
   r"complex_vector (v1,v2) :complex^N
    = vector_map2 (\x y. Cx x + ii * Cx y) v1 v2"

  let COMPLEX_VECTOR_TRANSPOSE ← prove
   r"!v1 v2:real^N.
  complex_vector (v1,v2) = vector_to_cvector v1 + ii % vector_to_cvector v2"
   (ONCE_REWRITE_TAC [CART_EQ]
    THEN SIMP_TAC [complex_vector, CVECTOR_ADD_COMPONENT, CVECTOR_MUL_COMPONENT,
      VECTOR_TO_CVECTOR_COMPONENT, VECTOR_MAP2_COMPONENT])

  let cvector_unflatten ← new_definition
   r"cvector_unflatten (v:real^(N,N) finite_sum) :complex^N
    = complex_vector (fstcart v, sndcart v)"

  let UNFLATTEN_FLATTEN ← prove
   r"cvector_unflatten o cvector_flatten = I :complex^N -> complex^N"
   (REWRITE_TAC [FUN_EQ_THM, o_DEF, I_DEF, cvector_flatten, cvector_unflatten,
      FSTCART_PASTECART, SNDCART_PASTECART, COMPLEX_VECTOR_TRANSPOSE,
      VECTOR_TO_CVECTOR_CVECTOR_RE_IM])

  let FLATTEN_UNFLATTEN ← prove
   r"cvector_flatten o cvector_unflatten =
    I :real^(N,N) finite_sum -> real^(N,N) finite_sum"
   (REWRITE_TAC [FUN_EQ_THM, o_DEF, I_DEF, cvector_flatten, cvector_unflatten,
      PASTECART_FST_SND, COMPLEX_VECTOR_TRANSPOSE,
      CVECTOR_RE_VECTOR_TO_CVECTOR_RE_IM, CVECTOR_IM_VECTOR_TO_CVECTOR_RE_IM])

  let FLATTEN_CLINEAR ← prove
   r"!f:complex^N->complex^M.
    clinear f ==> linear (cvector_flatten o f o cvector_unflatten)"
   (REWRITE_TAC [clinear, linear, cvector_flatten, cvector_unflatten, o_DEF,
      FSTCART_ADD, SNDCART_ADD, PASTECART_ADD, complex_vector, ← GSYM PASTECART_CMUL]
    THEN REPEAT STRIP_TAC
    THEN REPEAT (AP_TERM_TAC ORELSE HolCore.Tactics.MK_COMB_TAC HolBase.B)
    THEN REWRITE_TAC (← [CVECTOR_RE_ADD, CVECTOR_IM_ADD, CVECTOR_RE_MUL,
      CVECTOR_IM_MUL].mapM GSYM)
    THEN AP_TERM_TAC THEN ASSUM_LIST (fun ths => tactic_of do
      pure (REWRITE_TAC (← ths.mapM GSYM)))
    THEN AP_TERM_TAC THEN ONCE_REWRITE_TAC [CART_EQ]
    THEN SIMP_TAC [VECTOR_MAP2_COMPONENT, VECTOR_ADD_COMPONENT,
      CVECTOR_ADD_COMPONENT, CX_ADD, VECTOR_MUL_COMPONENT, CVECTOR_MUL_COMPONENT,
      FSTCART_CMUL, SNDCART_CMUL, CX_MUL]
    THEN SIMPLE_COMPLEX_ARITH_TAC)

  let FLATTEN_MAP ← prove
   r"!f g.
    f = vector_map g
      ==> !x:complex^N.
        cvector_flatten (vector_map f x) = vector_map g (cvector_flatten x)"
   (SIMP_TAC [cvector_flatten, CVECTOR_RE_VECTOR_MAP, CVECTOR_IM_VECTOR_MAP,
      ← GSYM PASTECART_VECTOR_MAP, VECTOR_MAP_CVECTOR_RE, VECTOR_MAP_CVECTOR_IM,
      o_DEF, IM_DEF, RE_DEF, VECTOR_MAP_COMPONENT])

  let FLATTEN_NEG ← prove
   r"!x:complex^N. cvector_flatten (--x) = --(cvector_flatten x)"
   (REWRITE_TAC [cvector_neg, ← MATCH_MP FLATTEN_MAP COMPLEX_NEG_IS_A_MAP]
    THEN REWRITE_TAC [VECTOR_NEG_IS_A_MAP])

  let CVECTOR_NEG_ALT ← prove
   r"!x:complex^N. --x = cvector_unflatten (--(cvector_flatten x))"
   (REWRITE_TAC [← GSYM FLATTEN_NEG,
      ← REWRITE_RULE [o_DEF, FUN_EQ_THM, I_DEF] UNFLATTEN_FLATTEN])

  let FLATTEN_MAP2 ← prove
   r"!f g.
    f = vector_map2 g ==>
      !x y:complex^N.
        cvector_flatten (vector_map2 f x y) =
          vector_map2 g (cvector_flatten x) (cvector_flatten y)"
   (SIMP_TAC [cvector_flatten, CVECTOR_RE_VECTOR_MAP2, CVECTOR_IM_VECTOR_MAP2,
      CVECTOR_RE_VECTOR_MAP2, ← GSYM PASTECART_VECTOR_MAP2]
    THEN REWRITE_TAC [cvector_re, cvector_im, VECTOR_MAP2_LVECTOR_MAP,
      VECTOR_MAP2_RVECTOR_MAP]
    THEN REPEAT (HolCore.Tactics.MK_COMB_TAC HolBase.B)
    THEN REWRITE_TAC [FUN_EQ_THM, IM_DEF, RE_DEF, VECTOR_MAP2_COMPONENT, o_DEF])

  let FLATTEN_ADD ← prove
   r"!x y:complex^N.
    cvector_flatten (x+y) = cvector_flatten x + cvector_flatten y"
   (REWRITE_TAC [cvector_add, ← MATCH_MP FLATTEN_MAP2 COMPLEX_ADD_IS_A_MAP]
    THEN REWRITE_TAC [VECTOR_ADD_IS_A_MAP])

  let CVECTOR_ADD_ALT ← prove
   r"!x y:complex^N.
    x+y = cvector_unflatten (cvector_flatten x + cvector_flatten y)"
   (REWRITE_TAC [← GSYM FLATTEN_ADD,
      ← REWRITE_RULE [o_DEF, FUN_EQ_THM, I_DEF] UNFLATTEN_FLATTEN])

  let FLATTEN_SUB ← prove
   r"!x y:complex^N. cvector_flatten (x-y) = cvector_flatten x - cvector_flatten y"
   (REWRITE_TAC [cvector_sub, ← MATCH_MP FLATTEN_MAP2 COMPLEX_SUB_IS_A_MAP]
    THEN REWRITE_TAC [VECTOR_SUB_IS_A_MAP])

  let CVECTOR_SUB_ALT ← prove
   r"!x y:complex^N. x-y = cvector_unflatten (cvector_flatten x - cvector_flatten y)"
   (REWRITE_TAC [← GSYM FLATTEN_SUB,
      ← REWRITE_RULE [o_DEF, FUN_EQ_THM, I_DEF] UNFLATTEN_FLATTEN])

  /- ======================================================================= -/
  /- CONJUGATE VECTOR.                                                       -/
  /- ======================================================================= -/

  let cvector_cnj ← new_definition
   r"cvector_cnj : complex^N->complex^N = vector_map cnj"

  let CVECTOR_MAP_PROPERTY (tm : term) : thm → ExceptT String IO thm :=
    VECTOR_MAP_PROPERTY tm [cvector_zero, cvector_add, cvector_sub, cvector_neg,
    cvector_mul, cvector_cnj, cvector_re, cvector_im]

  let CVECTOR_CNJ_ADD ← CVECTOR_MAP_PROPERTY
    (← q r"!x y:complex^N. cvector_cnj (x+y) = cvector_cnj x + cvector_cnj y")
    CNJ_ADD

  let CVECTOR_CNJ_SUB ← CVECTOR_MAP_PROPERTY
    (← q r"!x y:complex^N. cvector_cnj (x-y) = cvector_cnj x - cvector_cnj y")
    CNJ_SUB

  let CVECTOR_CNJ_NEG ← CVECTOR_MAP_PROPERTY
    (← q r"!x:complex^N. cvector_cnj (--x) = --(cvector_cnj x)")
    CNJ_NEG

  let CVECTOR_RE_CNJ ← CVECTOR_MAP_PROPERTY
    (← q r"!x:complex^N. cvector_re (cvector_cnj x) = cvector_re x")
    RE_CNJ

  let CVECTOR_IM_CNJ ← prove
   r"!x:complex^N. cvector_im (cvector_cnj x) = --(cvector_im x)"
   (VECTOR_MAP_PROPERTY_TAC [cvector_im, cvector_cnj, VECTOR_NEG_IS_A_MAP] IM_CNJ)

  let CVECTOR_CNJ_CNJ ← CVECTOR_MAP_PROPERTY
    (← q r"!x:complex^N. cvector_cnj (cvector_cnj x) = x")
    CNJ_CNJ

  return { CLINEAR_FSTCART_SNDCART, FSTCART_CLINEAR, SNDCART_CLINEAR,
           FSTCART_SNDCART_CVECTOR_ZERO, FSTCART_CVECTOR_ZERO, SNDCART_CVECTOR_ZERO,
           FSTCART_SNDCART_CVECTOR_ADD, FSTCART_SNDCART_CVECTOR_MUL, PASTECART_TAC,
           PASTECART_CVECTOR_ZERO, PASTECART_EQ_CVECTOR_ZERO, PASTECART_CVECTOR_ADD,
           PASTECART_CVECTOR_MUL, cvector_re, cvector_im, vector_to_cvector,
           CVECTOR_RE_COMPONENT, CVECTOR_IM_COMPONENT, VECTOR_TO_CVECTOR_COMPONENT,
           VECTOR_TO_CVECTOR_ZERO, VECTOR_TO_CVECTOR_ZERO_EQ, CVECTOR_ZERO_VEC0,
           VECTOR_TO_CVECTOR_MUL, CVECTOR_EQ, CVECTOR_RE_VECTOR_TO_CVECTOR,
           CVECTOR_IM_VECTOR_TO_CVECTOR, CVECTOR_IM_VECTOR_TO_CVECTOR_IM,
           VECTOR_TO_CVECTOR_CVECTOR_RE_IM, CVECTOR_IM_VECTOR_TO_CVECTOR_RE_IM,
           CVECTOR_RE_VECTOR_TO_CVECTOR_RE_IM, CVECTOR_RE_ADD, CVECTOR_IM_ADD,
           CVECTOR_RE_MUL, CVECTOR_IM_MUL, CVECTOR_RE_VECTOR_MAP, CVECTOR_IM_VECTOR_MAP,
           VECTOR_MAP_CVECTOR_RE, VECTOR_MAP_CVECTOR_IM, CVECTOR_RE_VECTOR_MAP2,
           CVECTOR_IM_VECTOR_MAP2, cvector_flatten, FLATTEN_RE_IM_COMPONENT,
           complex_vector, COMPLEX_VECTOR_TRANSPOSE, cvector_unflatten, UNFLATTEN_FLATTEN,
           FLATTEN_UNFLATTEN, FLATTEN_CLINEAR, FLATTEN_MAP, FLATTEN_NEG, CVECTOR_NEG_ALT,
           FLATTEN_MAP2, FLATTEN_ADD, CVECTOR_ADD_ALT, FLATTEN_SUB, CVECTOR_SUB_ALT,
           cvector_cnj, CVECTOR_MAP_PROPERTY, CVECTOR_CNJ_ADD, CVECTOR_CNJ_SUB,
           CVECTOR_CNJ_NEG, CVECTOR_RE_CNJ, CVECTOR_IM_CNJ, CVECTOR_CNJ_CNJ }

/- ------------------------------------------------------------------------- -/
/- Cross products in complex^3; dot products in complex^N; relation with     -/
/- real dot and cross products; norm.  (cvectors.ml 1163-1533)              -/
/- ------------------------------------------------------------------------- -/

structure CVD where
  ccross : thm
  CCROSS_COMPONENT : thm
  CART_EQ3 : thm
  CCROSS_TAC : List thm → tactic
  CCROSS_LZERO : thm
  CCROSS_RZERO : thm
  CCROSS_SKEW : thm
  CCROSS_REFL : thm
  CCROSS_LADD : thm
  CCROSS_RADD : thm
  CCROSS_LMUL : thm
  CCROSS_RMUL : thm
  CCROSS_LNEG : thm
  CCROSS_RNEG : thm
  CCROSS_JACOBI : thm
  cdot : thm
  CDOT_SYM : thm
  REAL_CDOT_SELF : thm
  CDOT_LADD : thm
  CDOT_RADD : thm
  CDOT_LSUB : thm
  CDOT_RSUB : thm
  CDOT_LMUL : thm
  CDOT_RMUL : thm
  CDOT_LNEG : thm
  CDOT_RNEG : thm
  CDOT_LZERO : thm
  CNJ_ZERO : thm
  CDOT_RZERO : thm
  CDOT3 : thm
  ADD_CDOT_SYM : thm
  CCROSS_LREAL : thm
  CCROSS_RREAL : thm
  CDOT_LREAL : thm
  CDOT_RREAL : thm
  cnorm2 : thm
  CX_CNORM2 : thm
  CNORM2_CVECTOR_ZERO : thm
  CNORM2_MODULUS : thm
  CNORM2_EQ_0 : thm
  CDOT_EQ_0 : thm
  CNORM2_POS : thm
  CDOT_SELF_POS : thm
  CNORM2_MUL : thm
  CNORM2_NORM2_2 : thm
  CNORM2_NORM2 : thm
  CNORM2_ALT : thm
  CNORM2_SUB : thm
  CNORM2_VECTOR_TO_CVECTOR : thm
  cnorm : thm
  deriving Inhabited

@[nospecialize]
def setupCVD [HolBase] (D : CvectorsDeps) (BA : CVA) (BB : CVB) (BC : CVC) :
    ExceptT String IO CVD := do
  -- @@SCOPE BEGIN
  let { new_definition, parse_as_infix, ARITH_TAC, MESON, MESON_TAC, .. } := D.cx.cvx
  let { overload_interface, .. } := D.cx
  let { CARD_NUMSEG_1, CART_EQ, DIMINDEX_3, EQ_SYM_EQ, .. } := D.cx.cvx.core1
  let { FUN_EQ_THM, HAS_SIZE, .. } := D.cx.cvx.core2
  let { PAIR_EQ, REAL_ABS_REFL, .. } := D.cx.cvx.core3
  let { REAL_MUL_RNEG, REAL_NEG_0, REAL_POW2_ABS, REAL_POW_2, SQRT_POW_2, .. } :=
    D.cx.cvx.core5
  let { SUM_LMUL, .. } := D.cx.cvx.core6
  let { DOT_EQ_0, DOT_LZERO, DOT_POS_LE, .. } := D.cx.cvx.vec1
  let { FORALL_3, .. } := D.cx.cvx.vec2
  let { VECTOR_3, .. } := D.cx.cvx.vec3
  let { VEC_COMPONENT, VSUM_0, VSUM_ADD, VSUM_EQ, VSUM_SUB, dot, .. } := D.cx.cvx.vec4
  let { vector_norm, .. } := D.cx.cpx
  let { FINITE_HAS_SIZE, HAS_SIZE_NUMSEG_1, REAL_NEG_MINUS1, DOT_SQUARE_NORM, VSUM_3, .. } :=
    D.thms
  let { prioritize_complex, CX_DEF, complex_mul, RE, IM, complex_neg, complex_add,
        complex_sub, SIMPLE_COMPLEX_ARITH_TAC, SIMPLE_COMPLEX_ARITH, .. } := D.cxa
  let { COMPLEX_MUL_SYM, COMPLEX_MUL_ASSOC, COMPLEX_ADD_LDISTRIB, COMPLEX_MUL_AC,
        COMPLEX_ADD_RID, COMPLEX_ADD_RDISTRIB, COMPLEX_MUL_RZERO, COMPLEX_MUL_LZERO,
        COMPLEX_NEG_LMUL, COMPLEX_NEG_RMUL, COMPLEX_NEG_MINUS1, COMPLEX_SUB_LDISTRIB,
        COMPLEX_SUB_RDISTRIB, .. } := D.cxb
  let { COMPLEX_VEC_0, COMPLEX_POW_2, COMPLEX_POW_II_2, CX_INJ, CX_ADD, CX_MUL, CX_POW,
        COMPLEX_NORM_CX, RE_CX, IM_CX, COMPLEX_EXPAND, RE_II, IM_II, RE_MUL_CX, IM_MUL_CX,
        .. } := D.cxc
  let { COMPLEX_POLY_NEG_CLAUSES, .. } := D.cxd
  let { COMPLEX_NORM_ZERO, COMPLEX_NORM_POW, .. } := D.cxf
  let { cnj, CNJ_CNJ, CNJ_CX, CNJ_NEG, CNJ_ADD, CNJ_SUB, CNJ_MUL, RE_CNJ, IM_CNJ,
        COMPLEX_ADD_CNJ, CNJ_II, COMPLEX_MUL_CNJ, .. } := D.cxg
  let { RE_VSUM, IM_VSUM, VSUM_COMPLEX_LMUL, VSUM_CX, CNJ_VSUM, VSUM_CX_NUMSEG, REAL_CNJ,
        REAL_CX, .. } := D.cxi
  let { CROSS_COMPONENTS, .. } := D.crs
  let { REAL_OF_COMPLEX, REAL_OF_COMPLEX_CX, REAL_OF_COMPLEX_NORM, REAL_OF_COMPLEX_MUL,
        VECTOR_MAP_COMPONENT, .. } := BA
  let { CVECTOR_ZERO_COMPONENT, CVECTOR_ADD_COMPONENT, CVECTOR_SUB_COMPONENT,
        CVECTOR_NEG_COMPONENT, CVECTOR_MUL_COMPONENT, .. } := BB
  let { CVECTOR_RE_COMPONENT, CVECTOR_IM_COMPONENT, VECTOR_TO_CVECTOR_COMPONENT,
        CVECTOR_RE_VECTOR_TO_CVECTOR, CVECTOR_IM_VECTOR_TO_CVECTOR,
        VECTOR_TO_CVECTOR_CVECTOR_RE_IM, .. } := BC
  -- @@SCOPE END

  /- ======================================================================= -/
  /- CROSS PRODUCTS IN COMPLEX^3.                                            -/
  /- ======================================================================= -/

  D.prioritize_vector

  parse_as_infix ("ccross", (20, "right"))

  let ccross ← new_definition
   r"((ccross):complex^3 -> complex^3 -> complex^3) x y = vector [
    x$2 * y$3 - x$3 * y$2;
    x$3 * y$1 - x$1 * y$3;
    x$1 * y$2 - x$2 * y$1
  ]"

  let CCROSS_COMPONENT ← prove
   r"!x y:complex^3.
  (x ccross y)$1 = x$2 * y$3 - x$3 * y$2
  /\ (x ccross y)$2 = x$3 * y$1 - x$1 * y$3
  /\ (x ccross y)$3 = x$1 * y$2 - x$2 * y$1"
   (REWRITE_TAC [ccross, VECTOR_3])

  -- simple handy instantiation of CART_EQ for dimension 3
  let CART_EQ3 ← prove
   r"!x y:complex^3. x = y <=> x$1 = y$1 /\ x$2 = y$2 /\ x$3 = y$3"
   (GEN_REWRITE_TAC (fun c => Simp.pathConvIO "rbrblr" c) [CART_EQ]
    THEN REWRITE_TAC [DIMINDEX_3, FORALL_3])

  let CCROSS_TAC (lemmas : List thm) : tactic :=
    REWRITE_TAC (CART_EQ3 :: CCROSS_COMPONENT :: lemmas)
    THEN SIMPLE_COMPLEX_ARITH_TAC

  let CCROSS_LZERO ← prove
   r"!x:complex^3. cvector_zero ccross x = cvector_zero"
   (CCROSS_TAC [CVECTOR_ZERO_COMPONENT])

  let CCROSS_RZERO ← prove
   r"!x:complex^3. x ccross cvector_zero = cvector_zero"
   (CCROSS_TAC [CVECTOR_ZERO_COMPONENT])

  let CCROSS_SKEW ← prove
   r"!x y:complex^3. (x ccross y) = --(y ccross x)"
   (CCROSS_TAC [CVECTOR_NEG_COMPONENT])

  let CCROSS_REFL ← prove
   r"!x:complex^3. x ccross x = cvector_zero"
   (CCROSS_TAC [CVECTOR_ZERO_COMPONENT])

  let CCROSS_LADD ← prove
   r"!x y z:complex^3. (x + y) ccross z = (x ccross z) + (y ccross z)"
   (CCROSS_TAC [CVECTOR_ADD_COMPONENT])

  let CCROSS_RADD ← prove
   r"!x y z:complex^3. x ccross(y + z) = (x ccross y) + (x ccross z)"
   (CCROSS_TAC [CVECTOR_ADD_COMPONENT])

  let CCROSS_LMUL ← prove
   r"!c x y:complex^3. (c % x) ccross y = c % (x ccross y)"
   (CCROSS_TAC [CVECTOR_MUL_COMPONENT])

  let CCROSS_RMUL ← prove
   r"!c x y:complex^3. x ccross (c % y) = c % (x ccross y)"
   (CCROSS_TAC [CVECTOR_MUL_COMPONENT])

  let CCROSS_LNEG ← prove
   r"!x y:complex^3. (--x) ccross y = --(x ccross y)"
   (CCROSS_TAC [CVECTOR_NEG_COMPONENT])

  let CCROSS_RNEG ← prove
   r"!x y:complex^3. x ccross (--y) = --(x ccross y)"
   (CCROSS_TAC [CVECTOR_NEG_COMPONENT])

  let CCROSS_JACOBI ← prove
   r"!(x:complex^3) y z.
    x ccross (y ccross z) + y ccross (z ccross x) + z ccross (x ccross y) =
      cvector_zero"
   (REWRITE_TAC [CART_EQ3]
    THEN REWRITE_TAC [CVECTOR_ADD_COMPONENT, CCROSS_COMPONENT,
      CVECTOR_ZERO_COMPONENT] THEN SIMPLE_COMPLEX_ARITH_TAC)

  /- ======================================================================= -/
  /- DOT PRODUCTS IN COMPLEX^N                                               -/
  /-                                                                         -/
  /- Only difference with the real case:                                     -/
  /- we take the conjugate of the 2nd argument                               -/
  /- ======================================================================= -/

  prioritize_complex

  parse_as_infix ("cdot", (20, "right"))

  let cdot ← new_definition
   r"(cdot) (x:complex^N) (y:complex^N) =
    vsum (1..dimindex(:N)) (\i. x$i * cnj(y$i))"

  -- The dot product is symmetric MODULO the conjugate
  let CDOT_SYM ← prove
   r"!x:complex^N y. x cdot y = cnj (y cdot x)"
   (REWRITE_TAC [cdot]
    THEN REWRITE_TAC [← MATCH_MP (← SPEC_ALL CNJ_VSUM) (← SPEC (← q r"dimindex (:N)") (← GEN_ALL
      (← CONJUNCT1 (← SPEC_ALL (← REWRITE_RULE [HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
    THEN REWRITE_TAC [CNJ_MUL, CNJ_CNJ, COMPLEX_MUL_SYM])

  let REAL_CDOT_SELF ← prove
   r"!x:complex^N. real(x cdot x)"
   (REWRITE_TAC [REAL_CNJ, ← GSYM CDOT_SYM])

  /- The following theorems are usual axioms of the hermitian dot product,
     they are proved later on.
   * let CDOT_SELF_POS = prove(`!x:complex^N. &0 <= real_of_complex (x cdot x)`, ...
   * let CDOT_EQ_0 = prove(`!x:complex^N. x cdot x = Cx(&0) <=> x = cvector_zero`
   -/

  let CDOT_LADD ← prove
   r"!x:complex^N y z. (x + y) cdot z = (x cdot z) + (y cdot z)"
   (REWRITE_TAC [cdot]
    THEN REWRITE_TAC [← MATCH_MP (← GSYM VSUM_ADD) (← SPEC (← q r"dimindex (:N)") (← GEN_ALL
      (← CONJUNCT1 (← SPEC_ALL (← REWRITE_RULE [HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
    THEN REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_EQ THEN GEN_TAC THEN DISCH_TAC
    THEN REWRITE_TAC [FUN_EQ_THM]
    THEN REWRITE_TAC [← SPECL [← q r"(x:real^2^N)$(x':num)", ← q r"(y:real^2^N)$(x':num)",
      ← q r"cnj ((z:real^2^N)$(x':num))"] (← GSYM COMPLEX_ADD_RDISTRIB)]
    THEN REWRITE_TAC [CVECTOR_ADD_COMPONENT])

  let CDOT_RADD ← prove
   r"!x:complex^N y z. x cdot (y + z) = (x cdot y) + (x cdot z)"
   (REWRITE_TAC [cdot]
    THEN REWRITE_TAC [← MATCH_MP (← GSYM VSUM_ADD) (← SPEC (← q r"dimindex (:N)") (← GEN_ALL
      (← CONJUNCT1 (← SPEC_ALL (← REWRITE_RULE [HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
    THEN REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_EQ THEN GEN_TAC THEN DISCH_TAC
    THEN REWRITE_TAC [FUN_EQ_THM]
    THEN REWRITE_TAC [← SPECL [← q r"(x:real^2^N)$(x':num)", ← q r"cnj((y:real^2^N)$(x':num))",
    ← q r"cnj ((z:real^2^N)$(x':num))"] (← GSYM COMPLEX_ADD_LDISTRIB)]
    THEN REWRITE_TAC [CNJ_ADD, CVECTOR_ADD_COMPONENT])

  let CDOT_LSUB ← prove
   r"!x:complex^N y z. (x - y) cdot z = (x cdot z) - (y cdot z)"
   (REWRITE_TAC [cdot]
    THEN REWRITE_TAC [← MATCH_MP (← GSYM VSUM_SUB) (← SPEC (← q r"dimindex (:N)") (← GEN_ALL
      (← CONJUNCT1 (← SPEC_ALL (← REWRITE_RULE [HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
    THEN REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_EQ THEN GEN_TAC THEN DISCH_TAC
    THEN REWRITE_TAC [FUN_EQ_THM]
    THEN REWRITE_TAC [← SPECL [← q r"(x:real^2^N)$(x':num)", ← q r"(y:real^2^N)$(x':num)",
      ← q r"cnj ((z:real^2^N)$(x':num))"] (← GSYM COMPLEX_SUB_RDISTRIB)]
    THEN REWRITE_TAC [CVECTOR_SUB_COMPONENT])

  let CDOT_RSUB ← prove
   r"!x:complex^N y z. x cdot (y - z) = (x cdot y) - (x cdot z)"
   (REWRITE_TAC [cdot]
    THEN REWRITE_TAC [← MATCH_MP (← GSYM VSUM_SUB) (← SPEC (← q r"dimindex (:N)") (← GEN_ALL
      (← CONJUNCT1 (← SPEC_ALL (← REWRITE_RULE [HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
    THEN REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_EQ THEN GEN_TAC THEN DISCH_TAC
    THEN REWRITE_TAC [FUN_EQ_THM]
    THEN REWRITE_TAC [← SPECL [← q r"(x:real^2^N)$(x':num)", ← q r"cnj((y:real^2^N)$(x':num))",
      ← q r"cnj ((z:real^2^N)$(x':num))"] (← GSYM COMPLEX_SUB_LDISTRIB)]
    THEN REWRITE_TAC [CNJ_SUB, CVECTOR_SUB_COMPONENT])

  let CDOT_LMUL ← prove
   r"!c:complex x:complex^N y. (c % x) cdot y = c * (x cdot y)"
   (REWRITE_TAC [cdot]
    THEN REWRITE_TAC [← MATCH_MP (← GSYM VSUM_COMPLEX_LMUL) (← SPEC (← q r"dimindex (:N)") (← GEN_ALL
      (← CONJUNCT1 (← SPEC_ALL (← REWRITE_RULE [HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
    THEN REWRITE_TAC [CVECTOR_MUL_COMPONENT, ← GSYM COMPLEX_MUL_ASSOC])

  let CDOT_RMUL ← prove
   r"!c:complex x:complex^N x y. x cdot (c % y) = cnj c * (x cdot y)"
   (REWRITE_TAC [cdot]
    THEN REWRITE_TAC [← MATCH_MP (← GSYM VSUM_COMPLEX_LMUL) (← SPEC (← q r"dimindex (:N)") (← GEN_ALL
      (← CONJUNCT1 (← SPEC_ALL (← REWRITE_RULE [HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
    THEN REWRITE_TAC [CVECTOR_MUL_COMPONENT, CNJ_MUL, COMPLEX_MUL_AC])

  let CDOT_LNEG ← prove
   r"!x:complex^N y. (--x) cdot y = --(x cdot y)"
   (REWRITE_TAC [cdot] THEN ONCE_REWRITE_TAC [COMPLEX_NEG_MINUS1]
    THEN REWRITE_TAC [← MATCH_MP (← GSYM VSUM_COMPLEX_LMUL) (← SPEC (← q r"dimindex (:N)") (← GEN_ALL
      (← CONJUNCT1 (← SPEC_ALL (← REWRITE_RULE [HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
    THEN REWRITE_TAC [CVECTOR_NEG_COMPONENT] THEN ONCE_REWRITE_TAC [← GSYM
      COMPLEX_NEG_MINUS1] THEN REWRITE_TAC [COMPLEX_NEG_LMUL])

  let CDOT_RNEG ← prove
   r"!x:complex^N y. x cdot (--y) = --(x cdot y)"
   (REWRITE_TAC [cdot] THEN ONCE_REWRITE_TAC [COMPLEX_NEG_MINUS1]
    THEN REWRITE_TAC [← MATCH_MP (← GSYM VSUM_COMPLEX_LMUL) (← SPEC (← q r"dimindex (:N)") (← GEN_ALL
      (← CONJUNCT1 (← SPEC_ALL (← REWRITE_RULE [HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
    THEN ONCE_REWRITE_TAC [← GSYM COMPLEX_NEG_MINUS1]
    THEN REWRITE_TAC [CVECTOR_NEG_COMPONENT, CNJ_NEG, COMPLEX_NEG_RMUL])

  let CDOT_LZERO ← prove
   r"!x:complex^N. cvector_zero cdot x = Cx (&0)"
   (REWRITE_TAC [cdot] THEN REWRITE_TAC [CVECTOR_ZERO_COMPONENT]
    THEN REWRITE_TAC [COMPLEX_MUL_LZERO, ← GSYM COMPLEX_VEC_0, VSUM_0])

  let CNJ_ZERO ← prove
   r"cnj (Cx(&0)) = Cx(&0)"
   (REWRITE_TAC [cnj, RE_CX, IM_CX, CX_DEF, REAL_NEG_0])

  let CDOT_RZERO ← prove
   r"!x:complex^N. x cdot cvector_zero = Cx (&0)"
   (REWRITE_TAC [cdot] THEN REWRITE_TAC [CVECTOR_ZERO_COMPONENT]
    THEN REWRITE_TAC [CNJ_ZERO]
    THEN REWRITE_TAC [COMPLEX_MUL_RZERO, ← GSYM COMPLEX_VEC_0, VSUM_0])

  /- Cauchy Schwarz inequality: proved later on
   * let CDOT_CAUCHY_SCHWARZ = prove (`!x y:complex^N. norm (x cdot y) pow 2 <= cnorm2 x * cnorm2 y`,
   * let CDOT_CAUCHY_SCHWARZ_EQUAL = prove(`!x y:complex^N. norm (x cdot y) pow 2 = cnorm2 x * cnorm2 y <=> collinear_cvectors x y`,
   -/

  let CDOT3 ← prove
   r"!x y:complex^3.
    x cdot y = (x$1 * cnj (y$1) + x$2 * cnj (y$2) + x$3 * cnj (y$3))"
   (REWRITE_TAC [cdot] THEN SIMP_TAC [DIMINDEX_3] THEN REWRITE_TAC [VSUM_3])

  let ADD_CDOT_SYM ← prove
   r"!x y:complex^N. x cdot y + y cdot x = Cx(&2 * Re(x cdot y))"
   (MESON_TAC [CDOT_SYM, COMPLEX_ADD_CNJ])

  /- ======================================================================= -/
  /- RELATION WITH REAL DOT AND CROSS PRODUCTS                               -/
  /- ======================================================================= -/

  let CCROSS_LREAL ← prove
   r"!r c.
    (vector_to_cvector r) ccross c =
      vector_to_cvector (r cross (cvector_re c))
      + ii % (vector_to_cvector (r cross (cvector_im c)))"
   (REWRITE_TAC [CART_EQ3, CVECTOR_ADD_COMPONENT, CVECTOR_MUL_COMPONENT,
      VECTOR_TO_CVECTOR_COMPONENT, CCROSS_COMPONENT, CROSS_COMPONENTS,
      CVECTOR_RE_COMPONENT, CVECTOR_IM_COMPONENT, complex_mul, RE_CX, IM_CX, CX_DEF,
      complex_sub, complex_neg, complex_add, RE, IM, RE_II, IM_II]
    THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [PAIR_EQ]
    THEN ARITH_TAC)

  let CCROSS_RREAL ← prove
   r"!r c.
    c ccross (vector_to_cvector r) =
      vector_to_cvector ((cvector_re c) cross r)
      + ii % (vector_to_cvector ((cvector_im c) cross r))"
   (REWRITE_TAC [CART_EQ3, CVECTOR_ADD_COMPONENT, CVECTOR_MUL_COMPONENT,
      VECTOR_TO_CVECTOR_COMPONENT, CCROSS_COMPONENT, CROSS_COMPONENTS,
      CVECTOR_RE_COMPONENT, CVECTOR_IM_COMPONENT, complex_mul, RE_CX, IM_CX, CX_DEF,
      complex_sub, complex_neg, complex_add, RE, IM, RE_II, IM_II]
    THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [PAIR_EQ]
    THEN ARITH_TAC)

  let CDOT_LREAL ← prove
   r"!r c.
    (vector_to_cvector r) cdot c =
      Cx (r dot (cvector_re c)) - ii * Cx (r dot (cvector_im c))"
   (REWRITE_TAC [cdot, dot, VECTOR_TO_CVECTOR_COMPONENT, CVECTOR_RE_COMPONENT,
      CVECTOR_IM_COMPONENT] THEN REPEAT GEN_TAC
    THEN GEN_REWRITE_TAC (fun c => RATOR_CONV (ONCE_DEPTH_CONV c)) [COMPLEX_EXPAND]
    THEN REWRITE_TAC [← MATCH_MP RE_VSUM (← SPEC (← q r"dimindex (:N)") (← GEN_ALL
      (← CONJUNCT1 (← SPEC_ALL (← REWRITE_RULE [HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
    THEN REWRITE_TAC [← MATCH_MP (IM_VSUM) (← SPEC (← q r"dimindex (:N)") (← GEN_ALL
      (← CONJUNCT1 (← SPEC_ALL (← REWRITE_RULE [HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
    THEN REWRITE_TAC [RE_MUL_CX, RE_CNJ, IM_MUL_CX, IM_CNJ]
    THEN REWRITE_TAC [COMPLEX_POLY_NEG_CLAUSES] THEN REWRITE_TAC [COMPLEX_MUL_AC]
    THEN REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN REWRITE_TAC [← GSYM CX_MUL]
    THEN REWRITE_TAC [← GSYM SUM_LMUL]
    THEN REWRITE_TAC [← GSYM REAL_NEG_MINUS1, ← GSYM REAL_MUL_RNEG])

  let CDOT_RREAL ← prove
   r"!r c.
    c cdot (vector_to_cvector r) =
      Cx ((cvector_re c) dot r) + ii * Cx ((cvector_im c) dot r)"
   (REWRITE_TAC [cdot, dot, VECTOR_TO_CVECTOR_COMPONENT, CVECTOR_RE_COMPONENT,
      CVECTOR_IM_COMPONENT]
    THEN REPEAT GEN_TAC
    THEN GEN_REWRITE_TAC (fun c => RATOR_CONV (ONCE_DEPTH_CONV c)) [COMPLEX_EXPAND]
    THEN REWRITE_TAC [← MATCH_MP RE_VSUM (← SPEC (← q r"dimindex (:N)") (← GEN_ALL
      (← CONJUNCT1 (← SPEC_ALL (← REWRITE_RULE [HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
    THEN REWRITE_TAC [← MATCH_MP IM_VSUM (← SPEC (← q r"dimindex (:N)") (← GEN_ALL
      (← CONJUNCT1 (← SPEC_ALL (← REWRITE_RULE [HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
    THEN REWRITE_TAC [CNJ_CX]
    THEN REWRITE_TAC [RE_MUL_CX, RE_CNJ, IM_MUL_CX, IM_CNJ])

  /- ======================================================================= -/
  /- NORM, UNIT VECTORS.                                                     -/
  /- ======================================================================= -/

  let cnorm2 ← new_definition
   r"cnorm2 (v:complex^N) = real_of_complex (v cdot v)"

  let CX_CNORM2 ← prove
   r"!v:complex^N. Cx(cnorm2 v) = v cdot v"
   (SIMP_TAC [cnorm2, REAL_CDOT_SELF, REAL_OF_COMPLEX])

  let CNORM2_CVECTOR_ZERO ← prove
   r"cnorm2 (cvector_zero:complex^N) = &0"
   (REWRITE_TAC [cnorm2, CDOT_RZERO, REAL_OF_COMPLEX_CX])

  let CNORM2_MODULUS ← prove
   r"!x:complex^N. cnorm2 x = (vector_map norm x) dot (vector_map norm x)"
   (REWRITE_TAC [cnorm2, cdot, COMPLEX_MUL_CNJ, COMPLEX_POW_2, ← GSYM CX_MUL,
      VSUM_CX_NUMSEG, dot, VECTOR_MAP_COMPONENT, REAL_OF_COMPLEX_CX])

  let CNORM2_EQ_0 ← prove
   r"!x:complex^N. cnorm2 x = &0 <=> x = cvector_zero"
   (REWRITE_TAC [CNORM2_MODULUS, CX_INJ, DOT_EQ_0] THEN GEN_TAC
    THEN GEN_REWRITE_TAC (fun c => RATOR_CONV (DEPTH_CONV c)) [CART_EQ]
    THEN REWRITE_TAC [VEC_COMPONENT, VECTOR_MAP_COMPONENT, COMPLEX_NORM_ZERO]
    THEN GEN_REWRITE_TAC (fun c => RAND_CONV (DEPTH_CONV c)) [CART_EQ]
    THEN REWRITE_TAC [CVECTOR_ZERO_COMPONENT])

  let CDOT_EQ_0 ← prove
   r"!x:complex^N. x cdot x = Cx(&0) <=> x = cvector_zero"
   (SIMP_TAC [← TAUT (← q r"(p<=>q) <=> ((p==>q) /\ (q==>p))"), CDOT_LZERO]
    THEN GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP (← MESON [REAL_OF_COMPLEX_CX]
      (← q r"x = Cx y ==> real_of_complex x = y")))
    THEN REWRITE_TAC [← GSYM cnorm2, CNORM2_EQ_0])

  let CNORM2_POS ← prove
   r"!x:complex^N. &0 <= cnorm2 x"
   (REWRITE_TAC [CNORM2_MODULUS, DOT_POS_LE])

  let CDOT_SELF_POS ← prove
   r"!x:complex^N. &0 <= real_of_complex (x cdot x)"
   (REWRITE_TAC [← GSYM cnorm2, CNORM2_POS])

  let CNORM2_MUL ← prove
   r"!a x:complex^N. cnorm2 (a % x) = (norm a) pow 2 * cnorm2 x"
   (SIMP_TAC [cnorm2, CDOT_LMUL, CDOT_RMUL,
      ← SIMPLE_COMPLEX_ARITH (← q r"x * cnj x * y = (x * cnj x) * y"), COMPLEX_MUL_CNJ,
      REAL_OF_COMPLEX_CX, REAL_OF_COMPLEX_MUL, REAL_CX, REAL_CDOT_SELF,
      ← GSYM CX_POW])

  let CNORM2_NORM2_2 ← prove
   r"!x y:real^N.
    cnorm2 (vector_to_cvector x + ii % vector_to_cvector y) =
      norm x pow 2 + norm y pow 2"
   (REWRITE_TAC [cnorm2, vector_norm, cdot, CVECTOR_ADD_COMPONENT,
      CVECTOR_MUL_COMPONENT, VECTOR_TO_CVECTOR_COMPONENT, CNJ_ADD, CNJ_CX, CNJ_MUL,
      CNJ_II, COMPLEX_ADD_RDISTRIB, COMPLEX_ADD_LDISTRIB,
      ← SIMPLE_COMPLEX_ARITH
        (← q r"(x*x+x*(--ii)*y)+(ii*y)*x+(ii*y)*(--ii)*y = x*x-(ii*ii)*y*y")]
    THEN REWRITE_TAC [← GSYM COMPLEX_POW_2, COMPLEX_POW_II_2,
      ← SIMPLE_COMPLEX_ARITH (← q r"x-(--Cx(&1))*y = x+y")]
    THEN SIMP_TAC [← MESON [CARD_NUMSEG_1, HAS_SIZE_NUMSEG_1, FINITE_HAS_SIZE]
      (← q r"FINITE (1..dimindex(:N))"), VSUM_ADD, ← GSYM CX_POW, VSUM_CX, ← GSYM dot,
      REAL_POW_2, ← GSYM dot]
    THEN SIMP_TAC [← GSYM CX_ADD, REAL_OF_COMPLEX_CX, ← GSYM REAL_POW_2, DOT_POS_LE,
      SQRT_POW_2])

  let CNORM2_NORM2 ← prove
   r"!v:complex^N.
    cnorm2 v = norm (cvector_re v) pow 2 + norm (cvector_im v) pow 2"
   (GEN_TAC THEN GEN_REWRITE_TAC (fun c => RATOR_CONV (ONCE_DEPTH_CONV c)) [← GSYM
      VECTOR_TO_CVECTOR_CVECTOR_RE_IM] THEN REWRITE_TAC [CNORM2_NORM2_2])

  let CNORM2_ALT ← prove
   r"!x:complex^N. cnorm2 x = norm (x cdot x)"
   (SIMP_TAC [cnorm2, REAL_OF_COMPLEX_NORM, REAL_CDOT_SELF, EQ_SYM_EQ, REAL_ABS_REFL,
      ← REWRITE_RULE [cnorm2] CNORM2_POS])

  let CNORM2_SUB ← prove
   r"!x y:complex^N. cnorm2 (x-y) = cnorm2 (y-x)"
   (REWRITE_TAC [cnorm2, CDOT_LSUB, CDOT_RSUB] THEN REPEAT GEN_TAC THEN AP_TERM_TAC
    THEN SIMPLE_COMPLEX_ARITH_TAC)

  let CNORM2_VECTOR_TO_CVECTOR ← prove
   r"!x:real^N. cnorm2 (vector_to_cvector x) = norm x pow 2"
   (REWRITE_TAC [CNORM2_ALT, CDOT_RREAL, CVECTOR_RE_VECTOR_TO_CVECTOR,
      CVECTOR_IM_VECTOR_TO_CVECTOR, DOT_LZERO, COMPLEX_MUL_RZERO, COMPLEX_ADD_RID,
      DOT_SQUARE_NORM, CX_POW, COMPLEX_NORM_POW, COMPLEX_NORM_CX, REAL_POW2_ABS])

  let cnorm ← new_definition
   r"cnorm :complex^N->real = sqrt o cnorm2"

  overload_interface "norm" (← q r"cnorm:complex^N->real")

  return { ccross, CCROSS_COMPONENT, CART_EQ3, CCROSS_TAC, CCROSS_LZERO, CCROSS_RZERO,
           CCROSS_SKEW, CCROSS_REFL, CCROSS_LADD, CCROSS_RADD, CCROSS_LMUL, CCROSS_RMUL,
           CCROSS_LNEG, CCROSS_RNEG, CCROSS_JACOBI, cdot, CDOT_SYM, REAL_CDOT_SELF,
           CDOT_LADD, CDOT_RADD, CDOT_LSUB, CDOT_RSUB, CDOT_LMUL, CDOT_RMUL, CDOT_LNEG,
           CDOT_RNEG, CDOT_LZERO, CNJ_ZERO, CDOT_RZERO, CDOT3, ADD_CDOT_SYM, CCROSS_LREAL,
           CCROSS_RREAL, CDOT_LREAL, CDOT_RREAL, cnorm2, CX_CNORM2, CNORM2_CVECTOR_ZERO,
           CNORM2_MODULUS, CNORM2_EQ_0, CDOT_EQ_0, CNORM2_POS, CDOT_SELF_POS, CNORM2_MUL,
           CNORM2_NORM2_2, CNORM2_NORM2, CNORM2_ALT, CNORM2_SUB, CNORM2_VECTOR_TO_CVECTOR,
           cnorm }

/- ------------------------------------------------------------------------- -/
/- Norm (continued) and unit vectors; collinearity; orthogonality; vsum;     -/
/- infinite sum.  (cvectors.ml 1535-2025)                                    -/
/- ------------------------------------------------------------------------- -/

structure CVE where
  CNORM_CVECTOR_ZERO : thm
  CNORM_POW_2 : thm
  CNORM_NORM_2 : thm
  CNORM_NORM : thm
  CNORM_MUL : thm
  CNORM_EQ_0 : thm
  CNORM_POS : thm
  CNORM_SUB : thm
  CNORM_VECTOR_TO_CVECTOR : thm
  CNORM_BASIS : thm
  CNORM_BASIS_1 : thm
  CVECTOR_CHOOSE_SIZE : thm
  cunit : thm
  CUNIT_CVECTOR_ZERO : thm
  CDOT_CUNIT_MUL_CUNIT : thm
  collinear_cvectors : thm
  COLLINEAR_CVECTORS_SYM : thm
  COLLINEAR_CVECTORS_0 : thm
  NON_NULL_COLLINEARS : thm
  COLLINEAR_LNONNULL : thm
  COLLINEAR_RNONNULL : thm
  COLLINEAR_RUNITREAL : thm
  CCROSS_COLLINEAR_CVECTORS : thm
  CVECTOR_MUL_INV : thm
  CVECTOR_MUL_INV2 : thm
  COLLINEAR_CVECTORS_VECTOR_TO_CVECTOR : thm
  corthogonal : thm
  CORTHOGONAL_SYM : thm
  CORTHOGONAL_0 : thm
  CORTHOGONAL_LZERO : thm
  CORTHOGONAL_RZERO : thm
  CORTHOGONAL_COLLINEAR_CVECTORS : thm
  CORTHOGONAL_MUL_CLAUSES : thm
  CORTHOGONAL_RMUL : thm
  CORTHOGONAL_RMUL_EQ : thm
  CORTHOGONAL_LMUL : thm
  CORTHOGONAL_LMUL_EQ : thm
  CORTHOGONAL_LRMUL_CLAUSES : thm
  CORTHOGONAL_LRMUL : thm
  CORTHOGONAL_LRMUL_EQ : thm
  CORTHOGONAL_REAL_CLAUSES : thm
  CORTHOGONAL_RREAL : thm
  CORTHOGONAL_LREAL : thm
  CORTHOGONAL_UNIT : thm
  CORTHOGONAL_RUNIT : thm
  CORTHOGONAL_LUNIT : thm
  CORTHOGONAL_PROJECTION : thm
  CDOT_PYTHAGOREAN : thm
  CDOT_CAUCHY_SCHWARZ_POW_2 : thm
  CDOT_CAUCHY_SCHWARZ : thm
  CDOT_CAUCHY_SCHWARZ_POW_2_EQUAL : thm
  CDOT_CAUCHY_SCHWARZ_EQUAL : thm
  CNORM_TRIANGLE : thm
  REAL_ABS_SUB_CNORM : thm
  cvsum : thm
  csummable : thm
  cinfsum : thm
  CSUMMABLE_FLATTEN_CVECTOR : thm
  FLATTEN_CINFSUM : thm
  CSUMMABLE_LINEAR : thm
  CINFSUM_LINEAR : thm
  deriving Inhabited

@[nospecialize]
def setupCVE [HolBase] (D : CvectorsDeps) (BA : CVA) (BB : CVB) (BC : CVC) (BD : CVD) :
    ExceptT String IO CVE := do
  -- @@SCOPE BEGIN
  let { new_definition, ASM_MESON_TAC, MESON, MESON_TAC, REAL_ARITH, REAL_FIELD, .. } :=
    D.cx.cvx
  let { CART_EQ, ETA_AX, .. } := D.cx.cvx.core1
  let { FSTCART_PASTECART, FUN_EQ_THM, IMP_CONJ, .. } := D.cx.cvx.core2
  let { POW_2_SQRT, .. } := D.cx.cvx.core3
  let { REAL_ENTIRE, REAL_EQ_SQUARE_ABS, REAL_LE_ADD, REAL_LE_ADDL, REAL_LE_MUL,
        REAL_LE_POW_2, REAL_LE_REFL, REAL_LE_SQUARE_ABS, REAL_LE_TRANS, .. } := D.cx.cvx.core4
  let { REAL_MUL_RID, REAL_MUL_RINV, REAL_MUL_RZERO, REAL_NEG_SUB, REAL_POW_2, REAL_POW_INV,
        REAL_POW_MUL, REAL_POW_ONE, SNDCART_PASTECART, SQRT_0, SQRT_EQ_0, SQRT_MUL,
        SQRT_POS_LE, SQRT_POW_2, .. } := D.cx.cvx.core5
  let { o_DEF, .. } := D.cx.cvx.core6
  let { COLLINEAR_LEMMA_ALT, DOT_RZERO, .. } := D.cx.cvx.vec1
  let { LINEAR_FSTCART, LINEAR_SNDCART, NORM_BASIS, NORM_EQ_0, .. } := D.cx.cvx.vec2
  let { NORM_POS_LE, VECTOR_3, .. } := D.cx.cvx.vec3
  let { VECTOR_CHOOSE_SIZE, VECTOR_MUL_COMPONENT, orthogonal, .. } := D.cx.cvx.vec4
  let { VECTOR_2, .. } := D.cx.cpx
  let { I_DEF, PASTECART_FST_SND, REAL_ABS_BOUNDS, NORM_BASIS_1, NORM_EQ_1, INFSUM_LINEAR,
        SUMMABLE_LINEAR, summable, .. } := D.thms
  let { RE_DEF, IM_DEF, complex, CX_DEF, ii, complex_mul, COMPLEX_EQ,
        SIMPLE_COMPLEX_ARITH_TAC, SIMPLE_COMPLEX_ARITH, .. } := D.cxa
  let { COMPLEX_ADD_LID, COMPLEX_MUL_ASSOC, COMPLEX_MUL_LID, COMPLEX_ADD_LDISTRIB,
        COMPLEX_MUL_AC, COMPLEX_ADD_RID, COMPLEX_MUL_RID, COMPLEX_MUL_RZERO,
        COMPLEX_SUB_REFL, COMPLEX_SUB_0, COMPLEX_SUB_RZERO, .. } := D.cxb
  let { COMPLEX_MUL_LINV, COMPLEX_ENTIRE, COMPLEX_MUL_RINV, COMPLEX_POW_2, CX_INJ, CX_ADD,
        CX_INV, CX_MUL, CX_POW, RE_CX, RE_ADD, RE_SUB, IM_CX, IM_ADD, IM_SUB, RE_MUL_CX,
        .. } := D.cxc
  let { COMPLEX_POLY_CLAUSES, .. } := D.cxd
  let { COMPLEX_INV_0, COMPLEX_INV_MUL, .. } := D.cxe
  let { COMPLEX_INV_EQ_0, COMPLEX_NORM_0, COMPLEX_NORM_MUL, .. } := D.cxf
  let { COMPLEX_NORM_CNJ, CNJ_MUL, CNJ_EQ_0, COMPLEX_MUL_CNJ, .. } := D.cxg
  let { CSQRT, CX_SQRT, .. } := D.cxh
  let { REAL_CNJ, REAL_CX, REAL_ADD, REAL_INV, .. } := D.cxi
  let { SINGLE, DISTRIB, REWRITE_TACS, GCONJUNCTS, RE_NORM, COMPLEX_BALANCE_DIV_MUL,
        REAL_ADD_POW_2, SUMS_PASTECART, REAL_OF_COMPLEX, REAL_OF_COMPLEX_CX,
        REAL_OF_COMPLEX_ADD, REAL_OF_COMPLEX_MUL, .. } := BA
  let { CVECTOR_ZERO_COMPONENT, CVECTOR_MUL_COMPONENT, CVECTOR_MUL_ASSOC, CVECTOR_MUL_ID,
        CVECTOR_SUB_EQ, CVECTOR_SUB_ADD, CVECTOR_SUB_ADD2, CVECTOR_MUL_RZERO,
        CVECTOR_MUL_LZERO, .. } := BB
  let { VECTOR_TO_CVECTOR_COMPONENT, VECTOR_TO_CVECTOR_ZERO, VECTOR_TO_CVECTOR_ZERO_EQ,
        VECTOR_TO_CVECTOR_MUL, CVECTOR_RE_VECTOR_TO_CVECTOR, CVECTOR_IM_VECTOR_TO_CVECTOR,
        VECTOR_TO_CVECTOR_CVECTOR_RE_IM, cvector_flatten, COMPLEX_VECTOR_TRANSPOSE,
        cvector_unflatten, UNFLATTEN_FLATTEN, FLATTEN_CLINEAR, .. } := BC
  let { ccross, CART_EQ3, CDOT_SYM, REAL_CDOT_SELF, CDOT_LADD, CDOT_RADD, CDOT_LSUB,
        CDOT_LMUL, CDOT_RMUL, CDOT_LZERO, CNJ_ZERO, CDOT_RZERO, ADD_CDOT_SYM, CDOT_LREAL,
        CDOT_RREAL, cnorm2, CX_CNORM2, CNORM2_CVECTOR_ZERO, CNORM2_EQ_0, CDOT_EQ_0,
        CNORM2_POS, CNORM2_MUL, CNORM2_NORM2_2, CNORM2_ALT, CNORM2_SUB,
        CNORM2_VECTOR_TO_CVECTOR, cnorm, .. } := BD
  -- @@SCOPE END

  let CNORM_CVECTOR_ZERO ← prove
   r"norm (cvector_zero:complex^N) = &0"
   (REWRITE_TAC [cnorm, CNORM2_CVECTOR_ZERO, o_DEF, SQRT_0])

  let CNORM_POW_2 ← prove
   r"!x:complex^N. norm x pow 2 = cnorm2 x"
   (SIMP_TAC [cnorm, o_DEF, SQRT_POW_2, CNORM2_POS])

  let CNORM_NORM_2 ← prove
   r"!x y:real^N.
    norm (vector_to_cvector x + ii % vector_to_cvector y) =
      sqrt(norm x pow 2 + norm y pow 2)"
   (REWRITE_TAC [cnorm, o_DEF, CNORM2_NORM2_2])

  let CNORM_NORM ← prove
   r"!v:complex^N.
    norm v = sqrt(norm (cvector_re v) pow 2 + norm (cvector_im v) pow 2)"
   (GEN_TAC THEN GEN_REWRITE_TAC (fun c => RATOR_CONV (ONCE_DEPTH_CONV c)) [← GSYM
      VECTOR_TO_CVECTOR_CVECTOR_RE_IM] THEN REWRITE_TAC [CNORM_NORM_2])

  let CNORM_MUL ← prove
   r"!a x:complex^N. norm (a % x) = norm a * norm x"
   (SIMP_TAC [cnorm, o_DEF, CNORM2_MUL, REAL_LE_POW_2, SQRT_MUL, CNORM2_POS,
      NORM_POS_LE, POW_2_SQRT])

  let CNORM_EQ_0 ← prove
   r"!x:complex^N. norm x = &0 <=> x = cvector_zero"
   (SIMP_TAC [cnorm, o_DEF, SQRT_EQ_0, CNORM2_POS, CNORM2_EQ_0])

  let CNORM_POS ← prove
   r"!x:complex^N. &0 <= norm x"
   (SIMP_TAC [cnorm, o_DEF, SQRT_POS_LE, CNORM2_POS])

  let CNORM_SUB ← prove
   r"!x y:complex^N. norm (x-y) = norm (y-x)"
   (REWRITE_TAC [cnorm, o_DEF, CNORM2_SUB])

  let CNORM_VECTOR_TO_CVECTOR ← prove
   r"!x:real^N. norm (vector_to_cvector x) = norm x"
   (SIMP_TAC [cnorm, o_DEF, CNORM2_VECTOR_TO_CVECTOR, POW_2_SQRT, NORM_POS_LE])

  let CNORM_BASIS ← prove
   r"!k. 1 <= k /\ k <= dimindex(:N)
    ==> norm (vector_to_cvector (basis k :real^N)) = &1"
   (SIMP_TAC [NORM_BASIS, CNORM_VECTOR_TO_CVECTOR])

  let CNORM_BASIS_1 ← prove
   r"norm(basis 1:real^N) = &1"
   (SIMP_TAC [NORM_BASIS_1, CNORM_VECTOR_TO_CVECTOR])

  let CVECTOR_CHOOSE_SIZE ← prove
   r"!c. &0 <= c ==> ?x:complex^N. norm(x) = c"
   (MESON_TAC [VECTOR_CHOOSE_SIZE, CNORM_VECTOR_TO_CVECTOR])

  /- Triangle inequality. Proved later on using Cauchy Schwarz inequality.
   * let CNORM_TRIANGLE = prove(`!x y:complex^N. norm (x+y) <= norm x + norm y`, ...
   -/

  let cunit ← new_definition
   r"cunit (X:complex^N) = inv(Cx(norm X))% X"

  let CUNIT_CVECTOR_ZERO ← prove
   r"cunit cvector_zero = cvector_zero:complex^N"
   (REWRITE_TAC [cunit, CNORM_CVECTOR_ZERO, COMPLEX_INV_0, CVECTOR_MUL_LZERO])

  let CDOT_CUNIT_MUL_CUNIT ← prove
   r"!x:complex^N. (cunit x cdot x) % cunit x = x"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"x = cvector_zero:complex^N")
    THEN ASM_REWRITE_TAC [CUNIT_CVECTOR_ZERO, CDOT_LZERO, CVECTOR_MUL_LZERO]
    THEN SIMP_TAC [cunit, CVECTOR_MUL_ASSOC, CDOT_LMUL,
      ← SIMPLE_COMPLEX_ARITH (← q r"(x*y)*x=(x*x)*y"), ← GSYM COMPLEX_INV_MUL,
      ← GSYM CX_MUL, ← GSYM REAL_POW_2, cnorm, o_DEF, CNORM2_POS, SQRT_POW_2]
    THEN ASM_SIMP_TAC [cnorm2, REAL_OF_COMPLEX, REAL_CDOT_SELF, CDOT_EQ_0,
      CNORM2_CVECTOR_ZERO, CVECTOR_MUL_RZERO, CNORM2_EQ_0, COMPLEX_MUL_LINV,
      CVECTOR_MUL_ID])

  /- ======================================================================= -/
  /- COLLINEARITY                                                            -/
  /- ======================================================================= -/

  /- Definition of collinearity between complex vectors.
   * Note: This is different from collinearity between points (which is the
   * one defined in HOL-Light library)
   -/
  let collinear_cvectors ← new_definition
   r"collinear_cvectors x (y:complex^N) <=> ?a. y = a % x \/ x = a % y"

  let COLLINEAR_CVECTORS_SYM ← prove
   r"!x y:complex^N. collinear_cvectors x y <=> collinear_cvectors y x"
   (REWRITE_TAC [collinear_cvectors] THEN MESON_TAC [])

  let COLLINEAR_CVECTORS_0 ← prove
   r"!x:complex^N. collinear_cvectors x cvector_zero"
   (REWRITE_TAC [collinear_cvectors] THEN GEN_TAC THEN EXISTS_TAC (← q r"Cx(&0)")
    THEN REWRITE_TAC [CVECTOR_MUL_LZERO])

  let NON_NULL_COLLINEARS ← prove
   r"!x y:complex^N.
    collinear_cvectors x y /\ ~(x=cvector_zero) /\ ~(y=cvector_zero)
      ==> ?a. ~(a=Cx(&0)) /\ y = a % x"
   (REWRITE_TAC [collinear_cvectors] THEN REPEAT STRIP_TAC THENL [
      ASM_MESON_TAC [CVECTOR_MUL_LZERO],
      SUBGOAL_THEN (← q r"~(a=Cx(&0))") ASSUME_TAC THENL [
        ASM_MESON_TAC [CVECTOR_MUL_LZERO],
        EXISTS_TAC (← q r"inv a :complex")
        THEN ASM_REWRITE_TAC [COMPLEX_INV_EQ_0, CVECTOR_MUL_ASSOC]
        THEN ASM_SIMP_TAC [COMPLEX_MUL_LINV, CVECTOR_MUL_ID]]])

  let COLLINEAR_LNONNULL ← prove
   r"!x y:complex^N.
    collinear_cvectors x y /\ ~(x=cvector_zero) ==> ?a. y = a % x"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"y=cvector_zero:complex^N") THENL [
      ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"Cx(&0)")
      THEN ASM_MESON_TAC [CVECTOR_MUL_LZERO],
      ASM_MESON_TAC [NON_NULL_COLLINEARS] ])

  let COLLINEAR_RNONNULL ← prove
   r"!x y:complex^N.
    collinear_cvectors x y /\ ~(y=cvector_zero) ==> ?a. x = a % y"
   (MESON_TAC [COLLINEAR_LNONNULL, COLLINEAR_CVECTORS_SYM])

  let COLLINEAR_RUNITREAL ← prove
   r"!x y:real^N.
    collinear_cvectors x (vector_to_cvector y) /\ norm y = &1
      ==> x = (x cdot (vector_to_cvector y)) % vector_to_cvector y"
   (REPEAT STRIP_TAC
    THEN POP_ASSUM (DISTRIB [ASSUME_TAC, ASSUME_TAC o REWRITE_RULE [NORM_EQ_0,
      ← GSYM VECTOR_TO_CVECTOR_ZERO_EQ] o MATCH_MP
        (← REAL_ARITH (← q r"!x. x= &1 ==> ~(x= &0)"))])
    THEN FIRST_X_ASSUM (fun x => FIRST_X_ASSUM (fun y => tactic_of do
      pure (CHOOSE_THEN (SINGLE ONCE_REWRITE_TAC) (← MATCH_MP COLLINEAR_RNONNULL
        (← CONJ y x)))))
    THEN REWRITE_TAC [CDOT_LMUL, CDOT_LREAL, CVECTOR_RE_VECTOR_TO_CVECTOR,
      CVECTOR_IM_VECTOR_TO_CVECTOR, DOT_RZERO, COMPLEX_MUL_RZERO, COMPLEX_SUB_RZERO]
    THEN POP_ASSUM ((fun (x : thm) =>
      REWRITE_TAC [x, COMPLEX_MUL_RID]) o REWRITE_RULE [NORM_EQ_1]))

  let CCROSS_COLLINEAR_CVECTORS ← prove
   r"!x y:complex^3. x ccross y = cvector_zero <=> collinear_cvectors x y"
   (REWRITE_TAC [ccross, collinear_cvectors, CART_EQ3, VECTOR_3,
      CVECTOR_ZERO_COMPONENT, COMPLEX_SUB_0, CVECTOR_MUL_COMPONENT]
    THEN REPEAT GEN_TAC THEN EQ_TAC
    THENL [
      REPEAT (POP_ASSUM MP_TAC) THEN ASM_CASES_TAC (← q r"(x:complex^3)$1 = Cx(&0)")
      THENL [
        ASM_CASES_TAC (← q r"(x:complex^3)$2 = Cx(&0)") THENL [
          ASM_CASES_TAC (← q r"(x:complex^3)$3 = Cx(&0)") THENL [
            REPEAT DISCH_TAC THEN EXISTS_TAC (← q r"Cx(&0)")
            THEN ASM_REWRITE_TAC [COMPLEX_POLY_CLAUSES],
            REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"(y:complex^3)$3/(x:complex^3)$3")
            THEN ASM_SIMP_TAC [COMPLEX_BALANCE_DIV_MUL]
            THEN ASM_MESON_TAC [COMPLEX_MUL_AC]],
          REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"(y:complex^3)$2/(x:complex^3)$2")
          THEN ASM_SIMP_TAC [COMPLEX_BALANCE_DIV_MUL]
          THEN ASM_MESON_TAC [COMPLEX_MUL_AC] ],
        REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"(y:complex^3)$1/(x:complex^3)$1")
        THEN ASM_SIMP_TAC [COMPLEX_BALANCE_DIV_MUL]
        THEN ASM_MESON_TAC [COMPLEX_MUL_AC]],
        SIMPLE_COMPLEX_ARITH_TAC ])

  let CVECTOR_MUL_INV ← prove
   r"!a x y:complex^N. ~(a = Cx(&0)) /\ x = a % y ==> y = inv a % x"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [CVECTOR_MUL_ASSOC,
      ← MESON [] (← q r"(p\/q) <=> (~p ==> q)"), COMPLEX_MUL_LINV, CVECTOR_MUL_ID])

  let CVECTOR_MUL_INV2 ← prove
   r"!a x y:complex^N. ~(x = cvector_zero) /\ x = a % y ==> y = inv a % x"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"a=Cx(&0)")
    THEN ASM_MESON_TAC [CVECTOR_MUL_LZERO, CVECTOR_MUL_INV])

  let COLLINEAR_CVECTORS_VECTOR_TO_CVECTOR ← prove
   r"!x y:real^N.
    collinear_cvectors (vector_to_cvector x) (vector_to_cvector y)
      <=> collinear {vec 0,x,y}"
   (REWRITE_TAC [COLLINEAR_LEMMA_ALT, collinear_cvectors]
    THEN REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL [
      POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [CART_EQ]
      THEN REWRITE_TAC [CVECTOR_MUL_COMPONENT, VECTOR_TO_CVECTOR_COMPONENT,
        VECTOR_MUL_COMPONENT, COMPLEX_EQ, RE_CX, RE_MUL_CX]
      THEN REPEAT STRIP_TAC THEN DISJ2_TAC THEN EXISTS_TAC (← q r"Re a")
      THEN ASM_SIMP_TAC [],
      REWRITE_TAC [← MESON [] (← q r"(p\/q) <=> (~p ==> q)")]
      THEN REWRITE_TAC [← GSYM VECTOR_TO_CVECTOR_ZERO_EQ]
      THEN DISCH_TAC
      THEN HolCore.Tactics.SUBGOAL_TAC HolBase.B "" (← q r"vector_to_cvector (y:real^N) =
      inv a % vector_to_cvector x") [ASM_MESON_TAC [CVECTOR_MUL_INV2]]
      THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [CART_EQ]
      THEN REWRITE_TAC [CVECTOR_MUL_COMPONENT, VECTOR_TO_CVECTOR_COMPONENT,
        VECTOR_MUL_COMPONENT, COMPLEX_EQ, RE_CX, RE_MUL_CX]
      THEN REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"Re(inv a)") THEN ASM_SIMP_TAC [],
      EXISTS_TAC (← q r"Cx(&0)") THEN ASM_REWRITE_TAC [VECTOR_TO_CVECTOR_ZERO,
        CVECTOR_MUL_LZERO],
      ASM_REWRITE_TAC [VECTOR_TO_CVECTOR_MUL] THEN EXISTS_TAC (← q r"Cx c")
      THEN REWRITE_TAC []
    ])

  /- ======================================================================= -/
  /- ORTHOGONALITY                                                           -/
  /- ======================================================================= -/

  let corthogonal ← new_definition
   r"corthogonal (x:complex^N) y <=> x cdot y = Cx(&0)"

  let CORTHOGONAL_SYM ← prove
   r"!x y:complex^N. corthogonal x y <=> corthogonal y x"
   (MESON_TAC [corthogonal, CDOT_SYM, CNJ_ZERO])

  let CORTHOGONAL_0 ← prove
   r"!x:complex^N. corthogonal cvector_zero x /\ corthogonal x cvector_zero"
   (REWRITE_TAC [corthogonal, CDOT_LZERO, CDOT_RZERO])

  let [CORTHOGONAL_LZERO, CORTHOGONAL_RZERO] ← GCONJUNCTS CORTHOGONAL_0
    | throw "CORTHOGONAL_LZERO: GCONJUNCTS"

  let CORTHOGONAL_COLLINEAR_CVECTORS ← prove
   r"!x y:complex^N.
    collinear_cvectors x y /\ ~(x=cvector_zero) /\ ~(y=cvector_zero)
      ==> ~(corthogonal x y)"
   (REWRITE_TAC [collinear_cvectors, corthogonal] THEN REPEAT STRIP_TAC
    THEN POP_ASSUM MP_TAC
    THEN ASM_REWRITE_TAC [CDOT_RMUL, CDOT_LMUL, COMPLEX_ENTIRE, ← GSYM cnorm2,
      CDOT_EQ_0, CNJ_EQ_0]
    THEN ASM_MESON_TAC [CVECTOR_MUL_LZERO])

  let CORTHOGONAL_MUL_CLAUSES ← prove
   r"!x y a.
    (corthogonal x y ==> corthogonal x (a%y))
    /\ (corthogonal x y \/ a = Cx(&0) <=> corthogonal x (a%y))
    /\ (corthogonal x y ==> corthogonal (a%x) y)
    /\ (corthogonal x y \/ a = Cx(&0) <=> corthogonal (a%x) y)"
   (SIMP_TAC [corthogonal, CDOT_RMUL, CDOT_LMUL, COMPLEX_ENTIRE, CNJ_EQ_0]
    THEN MESON_TAC [])

  let [CORTHOGONAL_RMUL, CORTHOGONAL_RMUL_EQ, CORTHOGONAL_LMUL,
    CORTHOGONAL_LMUL_EQ] ← GCONJUNCTS CORTHOGONAL_MUL_CLAUSES
    | throw "CORTHOGONAL_RMUL: GCONJUNCTS"

  let CORTHOGONAL_LRMUL_CLAUSES ← prove
   r"!x y a b.
    (corthogonal x y ==> corthogonal (a%x) (b%y))
    /\ (corthogonal x y \/ a = Cx(&0) \/ b = Cx(&0)
      <=> corthogonal (a%x) (b%y))"
   (MESON_TAC [CORTHOGONAL_MUL_CLAUSES])

  let [CORTHOGONAL_LRMUL, CORTHOGONAL_LRMUL_EQ] ←
    GCONJUNCTS CORTHOGONAL_LRMUL_CLAUSES
    | throw "CORTHOGONAL_LRMUL: GCONJUNCTS"

  let CORTHOGONAL_REAL_CLAUSES ← prove
   r"!r c.
    (corthogonal c (vector_to_cvector r)
      <=> orthogonal (cvector_re c) r /\ orthogonal (cvector_im c) r)
    /\ (corthogonal (vector_to_cvector r) c
      <=> orthogonal r (cvector_re c) /\ orthogonal r (cvector_im c))"
   (REWRITE_TAC [corthogonal, orthogonal, CDOT_LREAL, CDOT_RREAL, COMPLEX_SUB_0,
      COMPLEX_EQ, RE_CX, IM_CX, RE_SUB, IM_SUB, RE_ADD, IM_ADD]
    THEN REWRITE_TAC [RE_DEF, CX_DEF, IM_DEF, complex, complex_mul, VECTOR_2, ii]
    THEN CONV_TAC (fun t => REAL_FIELD t))

  let [CORTHOGONAL_RREAL, CORTHOGONAL_LREAL] ←
    GCONJUNCTS CORTHOGONAL_REAL_CLAUSES
    | throw "CORTHOGONAL_RREAL: GCONJUNCTS"

  let CORTHOGONAL_UNIT ← prove
   r"!x y:complex^N.
    (corthogonal x (cunit y) <=> corthogonal x y)
    /\ (corthogonal (cunit x) y <=> corthogonal x y)"
   (REWRITE_TAC [cunit, ← GSYM CORTHOGONAL_MUL_CLAUSES, COMPLEX_INV_EQ_0, CX_INJ,
      CNORM_EQ_0]
    THEN MESON_TAC [CORTHOGONAL_0])

  let [CORTHOGONAL_RUNIT, CORTHOGONAL_LUNIT] ← GCONJUNCTS CORTHOGONAL_UNIT
    | throw "CORTHOGONAL_RUNIT: GCONJUNCTS"

  let CORTHOGONAL_PROJECTION ← prove
   r"!x y:complex^N. corthogonal (x - (x cdot cunit y) % cunit y) y"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"y=cvector_zero:complex^N")
    THEN ASM_REWRITE_TAC [corthogonal, CDOT_RZERO]
    THEN REWRITE_TAC [CDOT_LSUB, cunit, CVECTOR_MUL_ASSOC, ← GSYM cnorm2, CDOT_LMUL,
      CDOT_RMUL, ← REWRITE_RULE [REAL_CNJ] (← MATCH_MP REAL_INV (← SPEC_ALL REAL_CX))]
    THEN REWRITE_TAC [COMPLEX_MUL_AC, ← GSYM COMPLEX_INV_MUL, ← GSYM COMPLEX_POW_2,
      cnorm, o_DEF, CSQRT]
    THEN SIMP_TAC [CNORM2_POS, CX_SQRT, cnorm2, REAL_CDOT_SELF, REAL_OF_COMPLEX, CSQRT]
    THEN ASM_SIMP_TAC [CDOT_EQ_0, COMPLEX_MUL_RINV, COMPLEX_MUL_RID,
      COMPLEX_SUB_REFL])

  let CDOT_PYTHAGOREAN ← prove
   r"!x y:complex^N. corthogonal x y ==> cnorm2 (x+y) = cnorm2 x + cnorm2 y"
   (SIMP_TAC [corthogonal, cnorm2, CDOT_LADD, CDOT_RADD, COMPLEX_ADD_RID,
      COMPLEX_ADD_LID, REAL_OF_COMPLEX_ADD, REAL_CDOT_SELF,
      ← MESON [CDOT_SYM, CNJ_ZERO]
        (← q r"x cdot y = Cx (&0) ==> y cdot x = Cx(&0)")])

  let CDOT_CAUCHY_SCHWARZ_POW_2 ← prove
   r"!x y:complex^N. norm (x cdot y) pow 2 <= cnorm2 x * cnorm2 y"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"y = cvector_zero:complex^N")
    THEN ASM_REWRITE_TAC [CNORM2_CVECTOR_ZERO, CDOT_RZERO, COMPLEX_NORM_0,
      REAL_POW_2, REAL_MUL_RZERO, REAL_OF_COMPLEX_CX, REAL_LE_REFL]
    THEN ONCE_REWRITE_TAC [← MATCH_MP (← MESON [CVECTOR_SUB_ADD]
      (← q r"(!x:complex^N y. p (x - f x y) y)
        ==> cnorm2 x * z = cnorm2 (x - f x y + f x y) * z")) CORTHOGONAL_PROJECTION]
    THEN MATCH_MP_TAC (← GEN_ALL (← MATCH_MP (← MESON []
      (← q r"(!x y. P x y ==> f x y = (g x y:real))
      ==> P x y /\ a <= g x y * b ==> a <= f x y * b")) CDOT_PYTHAGOREAN))
    THEN REWRITE_TAC [← GSYM CORTHOGONAL_MUL_CLAUSES, CORTHOGONAL_RUNIT,
      CORTHOGONAL_PROJECTION]
    THEN SIMP_TAC [cnorm2, ← GSYM REAL_OF_COMPLEX_ADD, REAL_CDOT_SELF, REAL_ADD,
      ← GSYM REAL_OF_COMPLEX_MUL]
    THEN REWRITE_TACS [cunit, CDOT_RMUL, CVECTOR_MUL_ASSOC, ← REWRITE_RULE [REAL_CNJ]
      (← MATCH_MP REAL_INV (← SPEC_ALL REAL_CX)), COMPLEX_MUL_AC, ← GSYM COMPLEX_INV_MUL,
      ← GSYM COMPLEX_POW_2, cnorm, o_DEF, CSQRT, COMPLEX_ADD_LDISTRIB, cnorm2, CDOT_RMUL,
      CNJ_MUL, CDOT_LMUL, ← GSYM cnorm2,
      ← REWRITE_RULE [REAL_CNJ] (← MATCH_MP REAL_INV (← SPEC_ALL REAL_CX))]
    THEN SIMP_TAC [CX_SQRT, CNORM2_POS, CSQRT, CX_CNORM2]
    THEN REWRITE_TAC [← SIMPLE_COMPLEX_ARITH
      (← q r"x * ((y * inv x) * x) * (z * inv x') * inv x'
      = (y * z) * (x * inv x) * (x * inv x' * inv x'):complex")]
    THEN ASM_SIMP_TAC [CDOT_EQ_0, COMPLEX_MUL_RINV, COMPLEX_MUL_LID, COMPLEX_MUL_CNJ,
      ← GSYM COMPLEX_INV_MUL]
    THEN ONCE_REWRITE_TAC [
      ← GSYM (← MATCH_MP REAL_OF_COMPLEX (← SPEC_ALL REAL_CDOT_SELF))]
    THEN SIMP_TAC [← GSYM cnorm2, ← GSYM CX_SQRT, CNORM2_POS, ← GSYM CX_MUL,
      ← GSYM COMPLEX_POW_2, ← GSYM CX_POW, SQRT_POW_2, ← GSYM CX_INV]
    THEN ASM_SIMP_TAC [REAL_MUL_RINV, CNORM2_EQ_0, REAL_MUL_RID, ← GSYM CX_ADD,
      REAL_OF_COMPLEX_CX, ← GSYM REAL_POW_2, REAL_LE_ADDL, REAL_LE_MUL, CNORM2_POS])

  let CDOT_CAUCHY_SCHWARZ ← prove
   r"!x y:complex^N. norm (x cdot y) <= norm x * norm y"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [REAL_LE_SQUARE_ABS]
      (← REAL_ARITH (← q r"&0 <= x /\ &0 <= y /\ abs x <= abs y ==> x <= y")))
    THEN SIMP_TAC [NORM_POS_LE, CNORM_POS, REAL_LE_MUL, REAL_POW_MUL, CNORM_POW_2,
      CDOT_CAUCHY_SCHWARZ_POW_2])

  let CDOT_CAUCHY_SCHWARZ_POW_2_EQUAL ← prove
   r"!x y:complex^N.
    norm (x cdot y) pow 2 = cnorm2 x * cnorm2 y <=> collinear_cvectors x y"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"y = cvector_zero:complex^N")
    THEN ASM_REWRITE_TAC [CNORM2_CVECTOR_ZERO, CDOT_RZERO, COMPLEX_NORM_0,
      REAL_POW_2, REAL_MUL_RZERO, REAL_OF_COMPLEX_CX, COLLINEAR_CVECTORS_0]
    THEN EQ_TAC THENL [
      ONCE_REWRITE_TAC [← MATCH_MP (← MESON [CVECTOR_SUB_ADD]
        (← q r"(!x:complex^N y. p (x - f x y) y) ==>
        cnorm2 x * z = cnorm2 (x - f x y + f x y) * z")) CORTHOGONAL_PROJECTION]
      THEN MATCH_MP_TAC (← GEN_ALL (← MATCH_MP (← MESON []
        (← q r"(!x y. P x y ==> g x y = (f x y:real)) ==>
          P x y /\ (a = f x y * z ==> R) ==> (a = g x y * z ==> R)"))
        CDOT_PYTHAGOREAN))
      THEN REWRITE_TAC [← GSYM CORTHOGONAL_MUL_CLAUSES, CORTHOGONAL_RUNIT,
        CORTHOGONAL_PROJECTION]
      THEN SIMP_TAC [cnorm2, ← GSYM REAL_OF_COMPLEX_ADD, REAL_CDOT_SELF, REAL_ADD,
        ← GSYM REAL_OF_COMPLEX_MUL]
      THEN REWRITE_TACS [cunit, CDOT_RMUL, CVECTOR_MUL_ASSOC, ← REWRITE_RULE [REAL_CNJ]
        (← MATCH_MP REAL_INV (← SPEC_ALL REAL_CX)), COMPLEX_MUL_AC,
        ← GSYM COMPLEX_INV_MUL, ← GSYM COMPLEX_POW_2, cnorm, o_DEF, CSQRT,
        COMPLEX_ADD_LDISTRIB, cnorm2, CDOT_RMUL, CNJ_MUL, CDOT_LMUL, ← GSYM cnorm2,
        ← REWRITE_RULE [REAL_CNJ] (← MATCH_MP REAL_INV (← SPEC_ALL REAL_CX))]
      THEN SIMP_TAC [CX_SQRT, CNORM2_POS, CSQRT, CX_CNORM2]
      THEN REWRITE_TAC [← SIMPLE_COMPLEX_ARITH
        (← q r"x * ((y * inv x) * x) * (z * inv x') * inv x' =
          (y * z) * (x * inv x) * (x * inv x' * inv x'):complex")]
      THEN ONCE_REWRITE_TAC [← GSYM (← MATCH_MP REAL_OF_COMPLEX
        (← SPEC_ALL REAL_CDOT_SELF))]
      THEN SIMP_TAC [← GSYM cnorm2, ← GSYM CX_SQRT, CNORM2_POS, ← GSYM CX_MUL,
        ← GSYM COMPLEX_POW_2, ← GSYM CX_POW, SQRT_POW_2, ← GSYM CX_INV, REAL_POW_INV]
      THEN ASM_SIMP_TAC [REAL_MUL_RINV, CNORM2_EQ_0, REAL_MUL_RID, ← GSYM CX_ADD,
        REAL_OF_COMPLEX_CX, ← GSYM REAL_POW_2, REAL_LE_ADDL, REAL_LE_MUL, CNORM2_POS,
        ← GSYM CX_POW, REAL_POW_ONE, COMPLEX_MUL_RID, COMPLEX_MUL_CNJ,
        ← REAL_ARITH (← q r"x = y + x <=> y = &0"), REAL_ENTIRE, CNORM2_EQ_0,
        CVECTOR_SUB_EQ, collinear_cvectors]
      THEN MESON_TAC [],
      REWRITE_TAC [collinear_cvectors] THEN REPEAT STRIP_TAC
      THEN ASM_REWRITE_TAC [cnorm2, CDOT_LMUL, CDOT_RMUL, COMPLEX_NORM_MUL,
        COMPLEX_MUL_ASSOC]
      THEN SIMP_TAC [COMPLEX_MUL_CNJ, ← GSYM cnorm2, COMPLEX_NORM_CNJ, ← GSYM CX_POW,
        REAL_OF_COMPLEX_MUL, REAL_CX, REAL_CDOT_SELF, REAL_OF_COMPLEX_CX,
        ← GSYM CNORM2_ALT]
      THEN SIMPLE_COMPLEX_ARITH_TAC
    ])

  let CDOT_CAUCHY_SCHWARZ_EQUAL ← prove
   r"!x y:complex^N.
  norm (x cdot y) = norm x * norm y <=> collinear_cvectors x y"
   (ONCE_REWRITE_TAC [← REWRITE_RULE [REAL_EQ_SQUARE_ABS] (← REAL_ARITH
      (← q r"x=y <=> abs x = abs y /\ (&0 <= x /\ &0 <= y \/ x < &0 /\ y < &0)"))]
    THEN SIMP_TAC [NORM_POS_LE, CNORM_POS, REAL_LE_MUL, REAL_POW_MUL, CNORM_POW_2,
      CDOT_CAUCHY_SCHWARZ_POW_2_EQUAL])

  let CNORM_TRIANGLE ← prove
   r"!x y:complex^N. norm (x+y) <= norm x + norm y"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC (← REWRITE_RULE [REAL_LE_SQUARE_ABS]
      (← REAL_ARITH (← q r"abs x <= abs y /\ &0 <= x /\ &0 <= y ==> x <= y")))
    THEN SIMP_TAC [CNORM_POS, REAL_LE_ADD, REAL_ADD_POW_2, CNORM_POW_2, cnorm2,
      CDOT_LADD, CDOT_RADD,
      ← SIMPLE_COMPLEX_ARITH (← q r"(x+y)+z+t = x+(y+z)+t:complex"),
      ADD_CDOT_SYM, REAL_OF_COMPLEX_ADD, REAL_CDOT_SELF, REAL_CX, REAL_ADD,
      REAL_OF_COMPLEX_CX, ← REAL_ARITH (← q r"x+ &2*y+z<=x+z+ &2*t <=> y<=t:real")]
    THEN MESON_TAC [CDOT_CAUCHY_SCHWARZ, RE_NORM, REAL_LE_TRANS])

  let REAL_ABS_SUB_CNORM ← prove
   r"!x y:complex^N. abs (norm x - norm y) <= norm (x-y)"
   (← do
    let lemma ←
      REWRITE_RULE [CVECTOR_SUB_ADD2, ← REAL_ARITH (← q r"x<=y+z <=> x-y<=z:real")]
        (← SPECL [← q r"x:complex^N", ← q r"y-x:complex^N"] CNORM_TRIANGLE)
    pure (REPEAT GEN_TAC
    THEN MATCH_MP_TAC (← MATCH_MP (← MESON []
      (← q r"(!x y. P x y <=> Q x y) ==> Q x y ==> P x y")) REAL_ABS_BOUNDS)
    THEN ONCE_REWRITE_TAC [← REAL_ARITH (← q r"--x <= y <=>  --y <= x")]
    THEN REWRITE_TAC [REAL_NEG_SUB]
    THEN REWRITE_TAC [lemma, ← ONCE_REWRITE_RULE [CNORM_SUB] lemma]))

  /- ======================================================================= -/
  /- VSUM                                                                    -/
  /- ======================================================================= -/

  let cvsum ← new_definition
   r"(cvsum:(A->bool)->(A->complex^N)->complex^N) s f = lambda i. vsum s (\x. (f x)$i)"

  /- ======================================================================= -/
  /- INFINITE SUM                                                            -/
  /- ======================================================================= -/

  let csummable ← new_definition
   r"csummable (s:num->bool) (f:num->complex^N)
    <=> summable s (cvector_re o f) /\ summable s (cvector_im o f)"

  let cinfsum ← new_definition
   r"cinfsum (s:num->bool) (f:num->complex^N) :complex^N
    = vector_to_cvector (infsum s (\x. cvector_re (f x)))
      + ii % vector_to_cvector (infsum s (\x.cvector_im (f x)))"

  let CSUMMABLE_FLATTEN_CVECTOR ← prove
   r"!s (f:num->complex^N). csummable s f <=> summable s (cvector_flatten o f)"
   (REWRITE_TAC [csummable, summable, cvector_flatten, o_DEF]
    THEN REPEAT (STRIP_TAC ORELSE EQ_TAC)
    THENL [
      EXISTS_TAC (← q r"pastecart (l:real^N) (l':real^N)")
      THEN ASM_SIMP_TAC [← GSYM SUMS_PASTECART],
      EXISTS_TAC (← q r"fstcart (l:real^(N,N) finite_sum)")
      THEN MATCH_MP_TAC (← GEN_ALL (← MATCH_MP (← TAUT
          (← q r"(p /\ q <=> r) ==> (r ==> p)"))
        (← HolLight.INST_TYPE [(← qty "N", ← qty "M")] (← SPEC_ALL SUMS_PASTECART))))
      THEN EXISTS_TAC (← q r"(cvector_im o f) :num->real^N")
      THEN EXISTS_TAC (← q r"sndcart (l:real^(N,N) finite_sum)")
      THEN ASM_REWRITE_TAC [ETA_AX, o_DEF, PASTECART_FST_SND],
      EXISTS_TAC (← q r"sndcart (l:real^(N,N) finite_sum)")
      THEN MATCH_MP_TAC (← GEN_ALL (← MATCH_MP (← TAUT
          (← q r"(p /\ q <=> r) ==> (r ==> q)"))
        (← HolLight.INST_TYPE [(← qty "N", ← qty "M")] (← SPEC_ALL SUMS_PASTECART))))
      THEN EXISTS_TAC (← q r"(cvector_re o f) :num->real^N")
      THEN EXISTS_TAC (← q r"fstcart (l:real^(N,N) finite_sum)")
      THEN ASM_REWRITE_TAC [ETA_AX, o_DEF, PASTECART_FST_SND]
    ])

  let FLATTEN_CINFSUM ← prove
   r"!s f.
    csummable s f ==>
      ((cinfsum s f):complex^N) =
        cvector_unflatten (infsum s (cvector_flatten o f))"
   (SIMP_TAC [cinfsum, cvector_unflatten, COMPLEX_VECTOR_TRANSPOSE, LINEAR_FSTCART,
      LINEAR_SNDCART, CSUMMABLE_FLATTEN_CVECTOR, ← GSYM INFSUM_LINEAR, o_DEF,
      cvector_flatten, FSTCART_PASTECART, SNDCART_PASTECART])

  let CSUMMABLE_LINEAR ← prove
   r"!f h:complex^N->complex^M s.
    csummable s f /\ clinear h ==> csummable s (h o f)"
   (REWRITE_TAC [CSUMMABLE_FLATTEN_CVECTOR] THEN REPEAT STRIP_TAC
    THEN POP_ASSUM (ASSUME_TAC o MATCH_MP FLATTEN_CLINEAR)
    THEN SUBGOAL_THEN
      (← q r"cvector_flatten o (h:complex^N -> complex^M) o (f:num -> complex^N) =
      \n. (cvector_flatten o h o cvector_unflatten) (cvector_flatten (f n))")
      (SINGLE REWRITE_TAC)
    THENL [
      REWRITE_TAC [o_DEF, FUN_EQ_THM] THEN GEN_TAC THEN REPEAT AP_TERM_TAC
      THEN REWRITE_TAC [← REWRITE_RULE [o_DEF, I_DEF, FUN_EQ_THM] UNFLATTEN_FLATTEN],
      MATCH_MP_TAC SUMMABLE_LINEAR THEN ASM_SIMP_TAC [← GSYM o_DEF]
    ])

  let CINFSUM_LINEAR ← prove
   r"!f (h:complex^M->complex^N) s.
    csummable s f /\ clinear h ==> cinfsum s (h o f) = h (cinfsum s f)"
   (REPEAT GEN_TAC
    THEN DISCH_THEN (fun x => tactic_of do
      pure (MP_TAC (← CONJ (← MATCH_MP CSUMMABLE_LINEAR x) x)))
    THEN SIMP_TAC [FLATTEN_CINFSUM, CSUMMABLE_FLATTEN_CVECTOR]
    THEN REPEAT STRIP_TAC THEN POP_ASSUM (ASSUME_TAC o MATCH_MP FLATTEN_CLINEAR)
    THEN SUBGOAL_THEN
      (← q r"cvector_flatten o (h:complex^M->complex^N) o (f:num->complex^M) =
      \n. (cvector_flatten o h o cvector_unflatten) ((cvector_flatten o f) n)")
      (SINGLE REWRITE_TAC)
    THENL [
      REWRITE_TAC [o_DEF, FUN_EQ_THM] THEN GEN_TAC THEN REPEAT AP_TERM_TAC
      THEN REWRITE_TAC [← REWRITE_RULE [o_DEF, I_DEF, FUN_EQ_THM] UNFLATTEN_FLATTEN],
      FIRST_ASSUM (fun x => FIRST_ASSUM (fun y => tactic_of do
        pure (REWRITE_TAC [← MATCH_MP
          (← MATCH_MP (← REWRITE_RULE [IMP_CONJ] INFSUM_LINEAR) x) y])))
      THEN REWRITE_TAC [o_DEF, ← REWRITE_RULE [o_DEF, I_DEF, FUN_EQ_THM]
        UNFLATTEN_FLATTEN]
    ])

  return { CNORM_CVECTOR_ZERO, CNORM_POW_2, CNORM_NORM_2, CNORM_NORM, CNORM_MUL, CNORM_EQ_0,
           CNORM_POS, CNORM_SUB, CNORM_VECTOR_TO_CVECTOR, CNORM_BASIS, CNORM_BASIS_1,
           CVECTOR_CHOOSE_SIZE, cunit, CUNIT_CVECTOR_ZERO, CDOT_CUNIT_MUL_CUNIT,
           collinear_cvectors, COLLINEAR_CVECTORS_SYM, COLLINEAR_CVECTORS_0,
           NON_NULL_COLLINEARS, COLLINEAR_LNONNULL, COLLINEAR_RNONNULL, COLLINEAR_RUNITREAL,
           CCROSS_COLLINEAR_CVECTORS, CVECTOR_MUL_INV, CVECTOR_MUL_INV2,
           COLLINEAR_CVECTORS_VECTOR_TO_CVECTOR, corthogonal, CORTHOGONAL_SYM,
           CORTHOGONAL_0, CORTHOGONAL_LZERO, CORTHOGONAL_RZERO,
           CORTHOGONAL_COLLINEAR_CVECTORS, CORTHOGONAL_MUL_CLAUSES, CORTHOGONAL_RMUL,
           CORTHOGONAL_RMUL_EQ, CORTHOGONAL_LMUL, CORTHOGONAL_LMUL_EQ,
           CORTHOGONAL_LRMUL_CLAUSES, CORTHOGONAL_LRMUL, CORTHOGONAL_LRMUL_EQ,
           CORTHOGONAL_REAL_CLAUSES, CORTHOGONAL_RREAL, CORTHOGONAL_LREAL, CORTHOGONAL_UNIT,
           CORTHOGONAL_RUNIT, CORTHOGONAL_LUNIT, CORTHOGONAL_PROJECTION, CDOT_PYTHAGOREAN,
           CDOT_CAUCHY_SCHWARZ_POW_2, CDOT_CAUCHY_SCHWARZ, CDOT_CAUCHY_SCHWARZ_POW_2_EQUAL,
           CDOT_CAUCHY_SCHWARZ_EQUAL, CNORM_TRIANGLE, REAL_ABS_SUB_CNORM, cvsum, csummable,
           cinfsum, CSUMMABLE_FLATTEN_CVECTOR, FLATTEN_CINFSUM, CSUMMABLE_LINEAR,
           CINFSUM_LINEAR }

end HolMultiLib.CVectors
