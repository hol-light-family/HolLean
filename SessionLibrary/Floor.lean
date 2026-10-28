/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/floor.ml.                                   -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Floor.lean

  The session half of the floor.ml translation: it supplies
  HolLibrary.Floor's dependencies from Session and exports every theorem by
  name.  Importing this module is `needs "Library/floor.ml"`: each bundle is
  built by `initialize` when the module is loaded, in file order.
-/

import Session
import HolLibrary.Floor

open HolCore HolCore.Kernel
open Session

namespace SessionLibrary.Floor

/-- The core theorems floor.ml uses, A-L. -/
def core1 : HolLibrary.Floor.CoreThms1 where
  ADD_SUB := Session.ADD_SUB
  ADD_SYM := Session.ADD_SYM
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DEPENDENT_CHOICE := Session.DEPENDENT_CHOICE
  DIVISION := Session.DIVISION
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EXTENSION := Session.EXTENSION
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_0 := Session.HAS_SIZE_0
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  HAS_SIZE_NUMSEG := Session.HAS_SIZE_NUMSEG
  HAS_SIZE_NUMSEG_LE := Session.HAS_SIZE_NUMSEG_LE
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  IMP_IMP := Session.IMP_IMP
  IN := Session.IN
  INFINITE := Session.INFINITE
  INFINITE_IMAGE := Session.INFINITE_IMAGE
  INFINITE_IMAGE_INJ := Session.INFINITE_IMAGE_INJ
  INFINITE_SUPERSET := Session.INFINITE_SUPERSET
  INTEGER_REAL_OF_INT := Session.INTEGER_REAL_OF_INT
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_NUMSEG := Session.IN_NUMSEG
  IN_UNION := Session.IN_UNION
  IN_UNIV := Session.IN_UNIV
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_1 := Session.LE_1
  LE_ADD := Session.LE_ADD
  LE_CASES := Session.LE_CASES
  LE_EXISTS := Session.LE_EXISTS
  LE_REFL := Session.LE_REFL
  LT := Session.LT
  LT_CASES := Session.LT_CASES
  LT_NZ := Session.LT_NZ
  LT_SUC_LE := Session.LT_SUC_LE

/-- The core theorems floor.ml uses, M-Z and lower case. -/
def core2 : HolLibrary.Floor.CoreThms2 where
  MONO_EXISTS := Session.MONO_EXISTS
  MONO_FORALL := Session.MONO_FORALL
  MULT_EQ_1 := Session.MULT_EQ_1
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
  OR_EXISTS_THM := Session.OR_EXISTS_THM
  REAL_ABS_ABS := Session.REAL_ABS_ABS
  REAL_ABS_DIV := Session.REAL_ABS_DIV
  REAL_ABS_MUL := Session.REAL_ABS_MUL
  REAL_ABS_NEG := Session.REAL_ABS_NEG
  REAL_ABS_NUM := Session.REAL_ABS_NUM
  REAL_ABS_POW := Session.REAL_ABS_POW
  REAL_ABS_ZERO := Session.REAL_ABS_ZERO
  REAL_ADD_LID := Session.REAL_ADD_LID
  REAL_ADD_SUB := Session.REAL_ADD_SUB
  REAL_ADD_SYM := Session.REAL_ADD_SYM
  REAL_ARCH_POW := Session.REAL_ARCH_POW
  REAL_ARCH_SIMPLE := Session.REAL_ARCH_SIMPLE
  REAL_EQ_ADD_LCANCEL := Session.REAL_EQ_ADD_LCANCEL
  REAL_EQ_NEG2 := Session.REAL_EQ_NEG2
  REAL_INV_0 := Session.REAL_INV_0
  REAL_INV_INV := Session.REAL_INV_INV
  REAL_LE_DIV := Session.REAL_LE_DIV
  REAL_LE_LDIV_EQ := Session.REAL_LE_LDIV_EQ
  REAL_LE_LT := Session.REAL_LE_LT
  REAL_LE_MUL := Session.REAL_LE_MUL
  REAL_LE_RDIV_EQ := Session.REAL_LE_RDIV_EQ
  REAL_LE_REFL := Session.REAL_LE_REFL
  REAL_LE_TOTAL := Session.REAL_LE_TOTAL
  REAL_LE_TRANS := Session.REAL_LE_TRANS
  REAL_LT_DIV := Session.REAL_LT_DIV
  REAL_LT_IMP_LE := Session.REAL_LT_IMP_LE
  REAL_LT_INV_EQ := Session.REAL_LT_INV_EQ
  REAL_LT_LDIV_EQ := Session.REAL_LT_LDIV_EQ
  REAL_LT_LE := Session.REAL_LT_LE
  REAL_LT_MIN := Session.REAL_LT_MIN
  REAL_LT_MUL := Session.REAL_LT_MUL
  REAL_LT_RDIV_EQ := Session.REAL_LT_RDIV_EQ
  REAL_LT_REFL := Session.REAL_LT_REFL
  REAL_LT_TRANS := Session.REAL_LT_TRANS
  REAL_MAX_LE := Session.REAL_MAX_LE
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_LNEG := Session.REAL_MUL_LNEG
  REAL_MUL_LZERO := Session.REAL_MUL_LZERO
  REAL_MUL_RZERO := Session.REAL_MUL_RZERO
  REAL_MUL_SYM := Session.REAL_MUL_SYM
  REAL_NEG_ADD := Session.REAL_NEG_ADD
  REAL_NEG_NEG := Session.REAL_NEG_NEG
  REAL_NEG_SUB := Session.REAL_NEG_SUB
  REAL_NOT_LE := Session.REAL_NOT_LE
  REAL_NOT_LT := Session.REAL_NOT_LT
  REAL_OF_NUM_ADD := Session.REAL_OF_NUM_ADD
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_LE := Session.REAL_OF_NUM_LE
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_OF_NUM_MUL := Session.REAL_OF_NUM_MUL
  REAL_OF_NUM_POW := Session.REAL_OF_NUM_POW
  REAL_OF_NUM_SUB := Session.REAL_OF_NUM_SUB
  REAL_OF_NUM_SUC := Session.REAL_OF_NUM_SUC
  REAL_POS := Session.REAL_POS
  REAL_POW_LE := Session.REAL_POW_LE
  REAL_POW_LT := Session.REAL_POW_LT
  REAL_SUB_0 := Session.REAL_SUB_0
  REAL_SUB_ADD := Session.REAL_SUB_ADD
  REAL_SUB_LE := Session.REAL_SUB_LE
  REAL_SUB_LT := Session.REAL_SUB_LT
  REAL_SUB_REFL := Session.REAL_SUB_REFL
  RIGHT_AND_EXISTS_THM := Session.RIGHT_AND_EXISTS_THM
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUM_CLOSED := Session.SUM_CLOSED
  SURJECTIVE_IMAGE_EQ := Session.SURJECTIVE_IMAGE_EQ
  SWAP_EXISTS_THM := Session.SWAP_EXISTS_THM
  TRANSITIVE_STEPWISE_LT := Session.TRANSITIVE_STEPWISE_LT
  UNWIND_THM1 := Session.UNWIND_THM1
  divides := Session.divides
  int_congruent := Session.int_congruent
  int_eq := Session.int_eq
  int_le := Session.int_le
  int_mul_th := Session.int_mul_th
  int_of_num := Session.int_of_num
  int_of_num_th := Session.int_of_num_th
  int_rep := Session.int_rep
  int_sub_th := Session.int_sub_th
  int_tybij := Session.int_tybij
  integer := Session.integer
  is_int := Session.is_int
  num_INFINITE := Session.num_INFINITE
  num_WOP := Session.num_WOP
  num_congruent := Session.num_congruent
  real_abs := Session.real_abs
  real_div := Session.real_div
  real_max := Session.real_max
  real_min := Session.real_min
  real_pow := Session.real_pow
  real_sub := Session.real_sub

/-- floor.ml's dependencies, from Session.  REAL_ARITH and REAL_ARITH_TAC
    are the ones HOL Light users have after hol.ml: calc_rat.ml's
    (`REAL_ARITH3`, `REAL_ARITH_TAC2`). -/
def deps : HolLibrary.Floor.FloorDeps where
  new_definition s := do
    let t ← ExceptT.mk (HolCore.Parser.parse_term s)
    ExceptT.mk (Session.new_definition t)
  new_specification ns th := ExceptT.mk (Session.new_specification ns th)
  ARITH_TAC := ARITH_TAC
  ASM_MESON_TAC := ASM_MESON_TAC
  ASM_REAL_ARITH_TAC := ASM_REAL_ARITH_TAC
  INDUCT_TAC := INDUCT_TAC
  INTEGER_RULE t := ExceptT.mk (INTEGER_RULE t)
  MESON ths t := ExceptT.mk (MESON ths t)
  MESON_TAC := MESON_TAC
  NUMBER_RULE t := ExceptT.mk (NUMBER_RULE t)
  REAL_ARITH t := ExceptT.mk (REAL_ARITH3 t)
  REAL_ARITH_TAC := REAL_ARITH_TAC2
  REAL_FIELD t := ExceptT.mk (REAL_FIELD t)
  REAL_POLY_CONV := REAL_POLY_CONV
  SET_TAC := SET_TAC
  core1 := core1
  core2 := core2

/-- floor.ml runs after the whole of hol.ml, then `prioritize_real()`
    (floor.ml 5).  Run when this module is loaded, before the first bundle. -/
initialize floorPrelude : Unit ← Session.prioritize_real

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} (name : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in floor.ml order (as `ensureFloor` forced them). -/
initialize BInteger : HolLibrary.Floor.Integer ←
  ioB "setupInteger" (HolLibrary.Floor.setupInteger deps).run
initialize BRational : HolLibrary.Floor.Rational ←
  ioB "setupRational" (HolLibrary.Floor.setupRational deps BInteger).run
initialize BFloorFrac : HolLibrary.Floor.FloorFrac ←
  ioB "setupFloorFrac" (HolLibrary.Floor.setupFloorFrac deps BInteger).run
initialize BFloorLemmas : HolLibrary.Floor.FloorLemmas ←
  ioB "setupFloorLemmas" (HolLibrary.Floor.setupFloorLemmas deps BInteger BFloorFrac).run
initialize BBetween : HolLibrary.Floor.Between ←
  ioB "setupBetween" (HolLibrary.Floor.setupBetween deps BInteger BFloorLemmas).run
initialize BRealOfInt : HolLibrary.Floor.RealOfInt ←
  ioB "setupRealOfInt" (HolLibrary.Floor.setupRealOfInt deps).run
initialize BFinite : HolLibrary.Floor.Finite ←
  ioB "setupFinite" (HolLibrary.Floor.setupFinite deps BInteger BRealOfInt).run
initialize BInfinite : HolLibrary.Floor.Infinite ←
  ioB "setupInfinite" (HolLibrary.Floor.setupInfinite deps BInteger BRational).run
initialize BApprox : HolLibrary.Floor.Approx ←
  ioB "setupApprox" (HolLibrary.Floor.setupApprox deps BInteger BRational BFloorLemmas).run
initialize BCongruence : HolLibrary.Floor.Congruence ←
  ioB "setupCongruence" (HolLibrary.Floor.setupCongruence deps BRealOfInt).run
initialize BIntegerTac : HolLibrary.Floor.IntegerTac ←
  ioB "setupIntegerTac" (HolLibrary.Floor.setupIntegerTac deps BInteger).run

/- The theorems, by name. -/
-- Integer
def INTEGER_CASES                : thm := BInteger.INTEGER_CASES
def REAL_ABS_INTEGER_LEMMA       : thm := BInteger.REAL_ABS_INTEGER_LEMMA
def INTEGER_CLOSED               : thm := BInteger.INTEGER_CLOSED
def INTEGER_ADD                  : thm := BInteger.INTEGER_ADD
def INTEGER_SUB                  : thm := BInteger.INTEGER_SUB
def INTEGER_MUL                  : thm := BInteger.INTEGER_MUL
def INTEGER_POW                  : thm := BInteger.INTEGER_POW
def REAL_LE_INTEGERS             : thm := BInteger.REAL_LE_INTEGERS
def REAL_LE_CASES_INTEGERS       : thm := BInteger.REAL_LE_CASES_INTEGERS
def REAL_LE_REVERSE_INTEGERS     : thm := BInteger.REAL_LE_REVERSE_INTEGERS
def REAL_LT_INTEGERS             : thm := BInteger.REAL_LT_INTEGERS
def REAL_EQ_INTEGERS             : thm := BInteger.REAL_EQ_INTEGERS
def REAL_EQ_INTEGERS_IMP         : thm := BInteger.REAL_EQ_INTEGERS_IMP
def INTEGER_NEG                  : thm := BInteger.INTEGER_NEG
def INTEGER_ABS                  : thm := BInteger.INTEGER_ABS
def INTEGER_POS                  : thm := BInteger.INTEGER_POS
def NONNEGATIVE_INTEGER          : thm := BInteger.NONNEGATIVE_INTEGER
def NONPOSITIVE_INTEGER          : thm := BInteger.NONPOSITIVE_INTEGER
def NONPOSITIVE_INTEGER_ALT      : thm := BInteger.NONPOSITIVE_INTEGER_ALT
def INTEGER_ADD_EQ               : thm := BInteger.INTEGER_ADD_EQ
def INTEGER_SUB_EQ               : thm := BInteger.INTEGER_SUB_EQ
def FORALL_INTEGER               : thm := BInteger.FORALL_INTEGER
def INTEGER_SUM                  : thm := BInteger.INTEGER_SUM
def INTEGER_ABS_MUL_EQ_1         : thm := BInteger.INTEGER_ABS_MUL_EQ_1
def INTEGER_DIV                  : thm := BInteger.INTEGER_DIV

-- Rational
def rational                     : thm := BRational.rational
def RATIONAL_INTEGER             : thm := BRational.RATIONAL_INTEGER
def RATIONAL_NUM                 : thm := BRational.RATIONAL_NUM
def RATIONAL_NEG                 : thm := BRational.RATIONAL_NEG
def RATIONAL_ABS                 : thm := BRational.RATIONAL_ABS
def RATIONAL_INV                 : thm := BRational.RATIONAL_INV
def RATIONAL_ADD                 : thm := BRational.RATIONAL_ADD
def RATIONAL_SUB                 : thm := BRational.RATIONAL_SUB
def RATIONAL_MUL                 : thm := BRational.RATIONAL_MUL
def RATIONAL_DIV                 : thm := BRational.RATIONAL_DIV
def RATIONAL_POW                 : thm := BRational.RATIONAL_POW
def RATIONAL_CLOSED              : thm := BRational.RATIONAL_CLOSED
def RATIONAL_NEG_EQ              : thm := BRational.RATIONAL_NEG_EQ
def RATIONAL_ABS_EQ              : thm := BRational.RATIONAL_ABS_EQ
def RATIONAL_INV_EQ              : thm := BRational.RATIONAL_INV_EQ
def RATIONAL_SUM                 : thm := BRational.RATIONAL_SUM
def RATIONAL_ALT                 : thm := BRational.RATIONAL_ALT

-- FloorFrac
def REAL_TRUNCATE_POS            : thm := BFloorFrac.REAL_TRUNCATE_POS
def REAL_TRUNCATE                : thm := BFloorFrac.REAL_TRUNCATE
def FLOOR_FRAC                   : thm := BFloorFrac.FLOOR_FRAC

-- FloorLemmas
def FLOOR_UNIQUE                 : thm := BFloorLemmas.FLOOR_UNIQUE
def FLOOR_EQ_0                   : thm := BFloorLemmas.FLOOR_EQ_0
def FLOOR                        : thm := BFloorLemmas.FLOOR
def FLOOR_DOUBLE                 : thm := BFloorLemmas.FLOOR_DOUBLE
def FRAC_FLOOR                   : thm := BFloorLemmas.FRAC_FLOOR
def FLOOR_NUM                    : thm := BFloorLemmas.FLOOR_NUM
def REAL_LE_FLOOR                : thm := BFloorLemmas.REAL_LE_FLOOR
def REAL_FLOOR_LE                : thm := BFloorLemmas.REAL_FLOOR_LE
def REAL_FLOOR_LT                : thm := BFloorLemmas.REAL_FLOOR_LT
def REAL_LT_FLOOR                : thm := BFloorLemmas.REAL_LT_FLOOR
def FLOOR_POS                    : thm := BFloorLemmas.FLOOR_POS
def FLOOR_DIV_DIV                : thm := BFloorLemmas.FLOOR_DIV_DIV
def FLOOR_MONO                   : thm := BFloorLemmas.FLOOR_MONO
def REAL_FLOOR_EQ                : thm := BFloorLemmas.REAL_FLOOR_EQ
def REAL_FLOOR_LT_REFL           : thm := BFloorLemmas.REAL_FLOOR_LT_REFL
def REAL_FRAC_EQ_0               : thm := BFloorLemmas.REAL_FRAC_EQ_0
def REAL_FRAC_POS_LT             : thm := BFloorLemmas.REAL_FRAC_POS_LT
def FRAC_NUM                     : thm := BFloorLemmas.FRAC_NUM
def REAL_FLOOR_REFL              : thm := BFloorLemmas.REAL_FLOOR_REFL
def REAL_FRAC_ZERO               : thm := BFloorLemmas.REAL_FRAC_ZERO
def REAL_FLOOR_ADD               : thm := BFloorLemmas.REAL_FLOOR_ADD
def REAL_FLOOR_TRIANGLE          : thm := BFloorLemmas.REAL_FLOOR_TRIANGLE
def REAL_FLOOR_NEG               : thm := BFloorLemmas.REAL_FLOOR_NEG
def REAL_FRAC_ADD                : thm := BFloorLemmas.REAL_FRAC_ADD
def FLOOR_POS_LE                 : thm := BFloorLemmas.FLOOR_POS_LE
def FRAC_UNIQUE                  : thm := BFloorLemmas.FRAC_UNIQUE
def REAL_FRAC_EQ                 : thm := BFloorLemmas.REAL_FRAC_EQ
def INTEGER_ROUND                : thm := BFloorLemmas.INTEGER_ROUND
def FRAC_DIV_MOD                 : thm := BFloorLemmas.FRAC_DIV_MOD
def FRAC_NEG                     : thm := BFloorLemmas.FRAC_NEG
def REAL_FLOOR_FLOOR_DIV         : thm := BFloorLemmas.REAL_FLOOR_FLOOR_DIV

-- Between
def INTEGER_EXISTS_BETWEEN_ALT   : thm := BBetween.INTEGER_EXISTS_BETWEEN_ALT
def INTEGER_EXISTS_BETWEEN_LT    : thm := BBetween.INTEGER_EXISTS_BETWEEN_LT
def INTEGER_EXISTS_BETWEEN       : thm := BBetween.INTEGER_EXISTS_BETWEEN
def INTEGER_EXISTS_BETWEEN_ABS   : thm := BBetween.INTEGER_EXISTS_BETWEEN_ABS
def INTEGER_EXISTS_BETWEEN_ABS_LT : thm := BBetween.INTEGER_EXISTS_BETWEEN_ABS_LT

-- RealOfInt
def REAL_OF_INT_OF_REAL          : thm := BRealOfInt.REAL_OF_INT_OF_REAL
def IMAGE_REAL_OF_INT_UNIV       : thm := BRealOfInt.IMAGE_REAL_OF_INT_UNIV

-- Finite
def HAS_SIZE_INTSEG_NUM          : thm := BFinite.HAS_SIZE_INTSEG_NUM
def FINITE_INTSEG                : thm := BFinite.FINITE_INTSEG
def HAS_SIZE_INTSEG_INT          : thm := BFinite.HAS_SIZE_INTSEG_INT
def CARD_INTSEG_INT              : thm := BFinite.CARD_INTSEG_INT
def REAL_CARD_INTSEG_INT         : thm := BFinite.REAL_CARD_INTSEG_INT

-- Infinite
def INFINITE_INTEGER             : thm := BInfinite.INFINITE_INTEGER
def INFINITE_RATIONAL            : thm := BInfinite.INFINITE_RATIONAL

-- Approx
def PADIC_RATIONAL_APPROXIMATION_STRADDLE : thm := BApprox.PADIC_RATIONAL_APPROXIMATION_STRADDLE
def PADIC_RATIONAL_APPROXIMATION_STRADDLE_POS : thm := BApprox.PADIC_RATIONAL_APPROXIMATION_STRADDLE_POS
def PADIC_RATIONAL_APPROXIMATION_STRADDLE_POS_LE : thm := BApprox.PADIC_RATIONAL_APPROXIMATION_STRADDLE_POS_LE
def RATIONAL_APPROXIMATION       : thm := BApprox.RATIONAL_APPROXIMATION
def RATIONAL_BETWEEN             : thm := BApprox.RATIONAL_BETWEEN
def RATIONAL_BETWEEN_EQ          : thm := BApprox.RATIONAL_BETWEEN_EQ
def RATIONAL_APPROXIMATION_STRADDLE : thm := BApprox.RATIONAL_APPROXIMATION_STRADDLE
def RATIONAL_APPROXIMATION_ABOVE : thm := BApprox.RATIONAL_APPROXIMATION_ABOVE
def RATIONAL_APPROXIMATION_BELOW : thm := BApprox.RATIONAL_APPROXIMATION_BELOW
def INFINITE_RATIONAL_IN_RANGE   : thm := BApprox.INFINITE_RATIONAL_IN_RANGE

-- Congruence
def REAL_CONGRUENCE              : thm := BCongruence.REAL_CONGRUENCE
def REAL_INT_CONGRUENCE          : thm := BCongruence.REAL_INT_CONGRUENCE

-- IntegerTac
def REAL_INTEGER_TAC             : HolCore.Tactics.tactic := BIntegerTac.REAL_INTEGER_TAC

/-- `needs "Library/floor.ml"`: already done by importing this module. -/
def ensureFloor : IO Unit := pure ()

end SessionLibrary.Floor
