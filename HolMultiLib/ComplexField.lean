/- ========================================================================= -/
/- The field of complex numbers is algebraically closed: the fundamental     -/
/- theorem of algebra (FTA of Multivariate/cauchy.ml) for complex_ring of    -/
/- Multivariate/complex_ring.ml.                                             -/
/- ========================================================================= -/
/- File: HolMultiLib/ComplexField.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Multivariate/complex_field.ml` (new in
  e7fbefd), in the style of HolMultiLib/ComplexRing.lean.  The deps are
  complex_ring.ml's (`ComplexRingDeps`) and bundle, and in `CfThms` the
  theorems used from the core library, Library/ringtheory.ml,
  Library/fieldtheory.ml and Multivariate/cauchy.ml.
  SessionMultiLib/ComplexField.lean supplies them.
-/

import HolMultiLib.ComplexRing

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs rhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax
open HolMultiLib.ComplexRing

namespace HolMultiLib.ComplexField

/-- The theorems complex_field.ml uses from the core library,
    Library/ringtheory.ml, Library/fieldtheory.ml and Multivariate/cauchy.ml. -/
structure CfThms where
  (IN_NUMSEG IN_UNIV LE_1 LE_REFL POLY_DEG_0 POLY_TOP_EQ_0 RING_POLYNOMIAL
   algebraically_closed_field FTA : thm)
  deriving Inhabited

structure ComplexFieldDeps where
  /-- What complex_ring.ml was given. -/
  crd : ComplexRingDeps
  cf : CfThms

/- ------------------------------------------------------------------------- -/
/- The complex field is algebraically closed.  (complex_field.ml 7-21)      -/
/- ------------------------------------------------------------------------- -/

structure CF where
  ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING : thm
  deriving Inhabited

@[nospecialize]
def setupCF [HolBase] (D : ComplexFieldDeps) (BCR : CR) : ExceptT String IO CF := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, .. } := D.crd.ca.cvx
  let { algebraically_closed_field, FTA, IN_NUMSEG, IN_UNIV, LE_1, LE_REFL, POLY_DEG_0,
        POLY_TOP_EQ_0, RING_POLYNOMIAL, .. } := D.cf
  let { COMPLEX_RING_CLAUSES, FIELD_COMPLEX_RING, POLY_EVAL_COMPLEX_RING, .. } := BCR
  -- @@SCOPE END

  let ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING ← prove
   r"algebraically_closed_field complex_ring"
   (REWRITE_TAC [algebraically_closed_field, FIELD_COMPLEX_RING] THEN
    X_GEN_TAC (← q r"p:(1->num)->complex") THEN STRIP_TAC THEN
    ASM_SIMP_TAC [POLY_EVAL_COMPLEX_RING, COMPLEX_RING_CLAUSES, IN_UNIV] THEN
    MATCH_MP_TAC FTA THEN DISJ2_TAC THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"poly_deg complex_ring (p:(1->num)->complex)")) THEN
    ASM_SIMP_TAC [IN_NUMSEG, LE_REFL, LE_1] THEN
    MP_TAC (← ISPECL [← q r"complex_ring", ← q r"p:(1->num)->complex"] POLY_TOP_EQ_0) THEN
    ASM_REWRITE_TAC [RING_POLYNOMIAL, COMPLEX_RING_CLAUSES] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC [POLY_DEG_0])

  return { ALGEBRAICALLY_CLOSED_FIELD_COMPLEX_RING }

end HolMultiLib.ComplexField
