/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/binary.ml.                                  -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Binary.lean

  The session half of the binary.ml translation: it supplies
  HolLibrary.Binary's dependencies from Session and exports every name under
  its HOL Light name.  Importing this module is `needs "Library/binary.ml"`:
  the bundle is built by `initialize` when the module is loaded.
-/

import Session
import HolLibrary.Binary

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Binary

/-- The core theorems binary.ml uses. -/
def core1 : HolLibrary.Binary.CoreThms1 where
  ADD1 := Session.ADD1
  ADD_ASSOC := Session.ADD_ASSOC
  ADD_SYM := Session.ADD_SYM
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  BINARY_INDUCT := Session.BINARY_INDUCT
  COND_RAND := Session.COND_RAND
  CONJ_ACI := Session.CONJ_ACI
  DIV_0 := Session.DIV_0
  DIV_1 := Session.DIV_1
  DIV_DIV := Session.DIV_DIV
  DIV_LT := Session.DIV_LT
  DIV_UNIQ := Session.DIV_UNIQ
  EQ_ADD_RCANCEL := Session.EQ_ADD_RCANCEL
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EQ_TRANS := Session.EQ_TRANS
  EVEN_ADD := Session.EVEN_ADD
  EVEN_EXP := Session.EVEN_EXP
  EXP := Session.EXP
  EXP_ADD := Session.EXP_ADD
  EXP_EQ_0 := Session.EXP_EQ_0
  EXTENSION := Session.EXTENSION
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_SUBSET := Session.FINITE_SUBSET
  IMP_CONJ := Session.IMP_CONJ
  IN_DELETE := Session.IN_DELETE
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_INTER := Session.IN_INTER
  IN_NUMSEG := Session.IN_NUMSEG
  IN_UNION := Session.IN_UNION
  LEFT_ADD_DISTRIB := Session.LEFT_ADD_DISTRIB
  LET_TRANS := Session.LET_TRANS
  LE_0 := Session.LE_0
  LE_LT := Session.LE_LT
  LT := Session.LT
  LTE_TRANS := Session.LTE_TRANS
  LT_EXP := Session.LT_EXP
  LT_IMP_LE := Session.LT_IMP_LE
  LT_POW2_REFL := Session.LT_POW2_REFL
  LT_REFL := Session.LT_REFL
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_SYM := Session.MULT_SYM
  NEUTRAL_ADD := Session.NEUTRAL_ADD
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LE := Session.NOT_LE
  NOT_LT := Session.NOT_LT
  NOT_ODD := Session.NOT_ODD
  NOT_SUC := Session.NOT_SUC
  NSUM_CLAUSES := Session.NSUM_CLAUSES
  NSUM_EQ := Session.NSUM_EQ
  NSUM_IMAGE := Session.NSUM_IMAGE
  NSUM_LMUL := Session.NSUM_LMUL
  NSUM_SUBSET := Session.NSUM_SUBSET
  NSUM_SUPPORT := Session.NSUM_SUPPORT
  NSUM_UNION_EQ := Session.NSUM_UNION_EQ
  ODD := Session.ODD
  ODD_ADD := Session.ODD_ADD
  ODD_MULT := Session.ODD_MULT
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  SUBSET := Session.SUBSET
  SUB_EQ_0 := Session.SUB_EQ_0
  SUB_REFL := Session.SUB_REFL
  SUC_INJ := Session.SUC_INJ
  UNWIND_THM1 := Session.UNWIND_THM1
  num_INDUCTION := Session.num_INDUCTION
  o_DEF := Session.o_DEF
  support := Session.support

/-- What binary.ml uses from Session. -/
def deps : HolLibrary.Binary.BinaryDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  MESON_TAC := Session.MESON_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  core1 := core1

/-- binary.ml, run when this module is loaded. -/
initialize BBinary : HolLibrary.Binary.Binary ← do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly (HolLibrary.Binary.setupBinary deps).run with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"setupBinary failed: {e}")

-- Binary
def BOUNDED_FINITE : thm := BBinary.BOUNDED_FINITE
def EVEN_NSUM : thm := BBinary.EVEN_NSUM
def bitset : thm := BBinary.bitset
def binarysum : thm := BBinary.binarysum
def BITSET_BOUND_LEMMA : thm := BBinary.BITSET_BOUND_LEMMA
def BITSET_BOUND_WEAK : thm := BBinary.BITSET_BOUND_WEAK
def FINITE_BITSET : thm := BBinary.FINITE_BITSET
def BITSET_0 : thm := BBinary.BITSET_0
def BITSET_STEP : thm := BBinary.BITSET_STEP
def BINARYSUM_BITSET : thm := BBinary.BINARYSUM_BITSET
def BITSET_EQ : thm := BBinary.BITSET_EQ
def BITSET_EQ_EMPTY : thm := BBinary.BITSET_EQ_EMPTY
def BINARYSUM_BOUND_LEMMA : thm := BBinary.BINARYSUM_BOUND_LEMMA
def BINARYSUM_DIV_DIVISIBLE : thm := BBinary.BINARYSUM_DIV_DIVISIBLE
def BINARYSUM_DIV : thm := BBinary.BINARYSUM_DIV
def BITSET_BINARYSUM : thm := BBinary.BITSET_BINARYSUM
def BINARYSUM_BOUND : thm := BBinary.BINARYSUM_BOUND
def BITSET_BOUND : thm := BBinary.BITSET_BOUND
def BITSET_BOUND_EQ : thm := BBinary.BITSET_BOUND_EQ
def BINARYSUM_BOUND_EQ : thm := BBinary.BINARYSUM_BOUND_EQ

/-- `needs "Library/binary.ml"`: already done by importing this module. -/
def ensureBinary : IO Unit := pure ()

end SessionLibrary.Binary
