/- ---------------------------------------------------------------------- -/
/- Session wiring for Multivariate/complex_ring.ml.                       -/
/- ---------------------------------------------------------------------- -/
/- File: SessionMultiLib/ComplexRing.lean

  The session half of the complex_ring.ml translation: it supplies
  HolMultiLib.ComplexRing's dependencies (complex_algebra.ml's deps and
  bundles, and the theorems of the core library, vectors.ml and
  Library/ringtheory.ml) and exports every theorem by name.  Importing this
  module is `needs "Multivariate/complex_ring.ml"`: its own `needs` are the
  imports of SessionLibrary.RingTheory and SessionMultiLib.ComplexAlgebra
  (in that order), and the bundle is built by `initialize` when the module
  is loaded.
-/

import SessionLibrary.RingTheory
import SessionMultiLib.ComplexAlgebra
import HolMultiLib.ComplexRing

open HolCore HolCore.Kernel

namespace SessionMultiLib.ComplexRing

open Session SessionLibrary.RingTheory in
/-- The theorems complex_ring.ml uses from the core library, vectors.ml and
    Library/ringtheory.ml. -/
def cr : HolMultiLib.ComplexRing.CrThms :=
  { BETA_THM, COND_SWAP, FINITE_INDUCT_STRONG, FINITE_NUMSEG, FORALL_INT_CASES,
    FUN_EQ_THM, IN_UNIV, PAIR, PAIR_EQ, REAL_OF_NUM_EQ, REAL_OF_NUM_SUC,
    RIGHT_FORALL_IMP_THM, SELECT_UNIQUE, SUBSET_UNIV, int_neg_th, int_of_num_th,
    VSUM_CLAUSES := SessionMultiLib.Vectors.VSUM_CLAUSES,
    FIELD_IMP_INTEGRAL_DOMAIN, FIELD_UNIT, POLY_EVAL_EXPAND, RING_CHAR_EQ_0,
    RING_OF_INT_CASES, RING_PRODUCT_CLAUSES, RING_SUM_CLAUSES, field, ring_0, ring_1,
    ring_add, ring_automorphism, ring_carrier, ring_div, ring_homomorphism, ring_inv,
    ring_isomorphism, ring_isomorphisms, ring_mul, ring_neg, ring_of_num, ring_pow,
    ring_sub, ring_tybij }

def deps : HolMultiLib.ComplexRing.ComplexRingDeps where
  ca := SessionMultiLib.ComplexAlgebra.deps
  cr := cr

private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

open SessionMultiLib.ComplexAlgebra in
initialize BCR : HolMultiLib.ComplexRing.CR ←
  ioB "setupCR" (HolMultiLib.ComplexRing.setupCR deps BCXA BCXC BCXD BCXE BCXG BCXK).run

-- CR (complex_ring.ml 9-109)
def complex_ring : thm := BCR.complex_ring
def COMPLEX_RING_CLAUSES : thm := BCR.COMPLEX_RING_CLAUSES
def FIELD_COMPLEX_RING : thm := BCR.FIELD_COMPLEX_RING
def INTEGRAL_DOMAIN_COMPLEX_RING : thm := BCR.INTEGRAL_DOMAIN_COMPLEX_RING
def COMPLEX_RING_OF_NUM : thm := BCR.COMPLEX_RING_OF_NUM
def COMPLEX_RING_OF_INT : thm := BCR.COMPLEX_RING_OF_INT
def RING_CHAR_COMPLEX_RING : thm := BCR.RING_CHAR_COMPLEX_RING
def COMPLEX_RING_SUB : thm := BCR.COMPLEX_RING_SUB
def COMPLEX_RING_INV : thm := BCR.COMPLEX_RING_INV
def COMPLEX_RING_DIV : thm := BCR.COMPLEX_RING_DIV
def COMPLEX_RING_POW : thm := BCR.COMPLEX_RING_POW
def COMPLEX_RING_SUM : thm := BCR.COMPLEX_RING_SUM
def COMPLEX_RING_PRODUCT : thm := BCR.COMPLEX_RING_PRODUCT
def POLY_EVAL_COMPLEX_RING : thm := BCR.POLY_EVAL_COMPLEX_RING
def RING_HOMOMORPHISM_CNJ : thm := BCR.RING_HOMOMORPHISM_CNJ
def RING_AUTOMORPHISM_CNJ : thm := BCR.RING_AUTOMORPHISM_CNJ

/-- `needs "Multivariate/complex_ring.ml"`: importing this module has built
    the bundle; a no-op kept for symmetry with the other wiring files. -/
def ensureComplexRing : IO Unit := pure ()

end SessionMultiLib.ComplexRing
