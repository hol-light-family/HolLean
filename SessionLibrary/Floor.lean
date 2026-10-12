/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/floor.ml.                                   -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Floor.lean

  The `unsafe` half of the floor.ml translation (as SessionLibrary/Prime.lean
  is for prime.ml): it supplies HolLibrary.Floor's dependencies from Session,
  builds each bundle on first use (in file order), and exports every theorem
  by name.  `ensureFloor` is `needs "Library/floor.ml"`.
-/

import Session
import HolLibrary.Floor

open HolCore HolCore.Kernel
open Session

namespace SessionLibrary.Floor

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨sessionB, sessionC, sessionT⟩

/-- The core theorems floor.ml uses, A-L. -/
unsafe def core1 (_ : Unit) : HolLibrary.Floor.CoreThms1 where
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
unsafe def core2 (_ : Unit) : HolLibrary.Floor.CoreThms2 where
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

/-- floor.ml's dependencies, from Session.  A function, not a constant (see
    SessionLibrary/Prime.lean).  REAL_ARITH and REAL_ARITH_TAC are the ones
    HOL Light users have after hol.ml: calc_rat.ml's (`REAL_ARITH3`,
    `REAL_ARITH_TAC2`). -/
unsafe def deps (_ : Unit) : HolLibrary.Floor.FloorDeps where
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
  core1 := core1 ()
  core2 := core2 ()

/-- floor.ml runs after the whole of hol.ml, then `prioritize_real()`
    (floor.ml 5).  Run once, before the first bundle. -/
initialize theFloorPrelude : IO.Ref Bool ← IO.mkRef false

unsafe def ensureFloorPrelude : IO Unit := do
  unless (← theFloorPrelude.get) do
    theFloorPrelude.set true
    Session.ensureDefine
    Session.prioritize_real

/-- Build a bundle once, after the prelude. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      ensureFloorPrelude
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.Floor: {name}"

initialize theInteger : IO.Ref (Option HolLibrary.Floor.Integer) ← IO.mkRef none
private unsafe def BInteger : HolLibrary.Floor.Integer :=
  cached theInteger "setupInteger" fun _ => (HolLibrary.Floor.setupInteger (deps ())).run
initialize theRational : IO.Ref (Option HolLibrary.Floor.Rational) ← IO.mkRef none
private unsafe def BRational : HolLibrary.Floor.Rational :=
  cached theRational "setupRational" fun _ => (HolLibrary.Floor.setupRational (deps ()) BInteger).run
initialize theFloorFrac : IO.Ref (Option HolLibrary.Floor.FloorFrac) ← IO.mkRef none
private unsafe def BFloorFrac : HolLibrary.Floor.FloorFrac :=
  cached theFloorFrac "setupFloorFrac" fun _ => (HolLibrary.Floor.setupFloorFrac (deps ()) BInteger).run
initialize theFloorLemmas : IO.Ref (Option HolLibrary.Floor.FloorLemmas) ← IO.mkRef none
private unsafe def BFloorLemmas : HolLibrary.Floor.FloorLemmas :=
  cached theFloorLemmas "setupFloorLemmas" fun _ => (HolLibrary.Floor.setupFloorLemmas (deps ()) BInteger BFloorFrac).run
initialize theBetween : IO.Ref (Option HolLibrary.Floor.Between) ← IO.mkRef none
private unsafe def BBetween : HolLibrary.Floor.Between :=
  cached theBetween "setupBetween" fun _ => (HolLibrary.Floor.setupBetween (deps ()) BInteger BFloorLemmas).run
initialize theRealOfInt : IO.Ref (Option HolLibrary.Floor.RealOfInt) ← IO.mkRef none
private unsafe def BRealOfInt : HolLibrary.Floor.RealOfInt :=
  cached theRealOfInt "setupRealOfInt" fun _ => (HolLibrary.Floor.setupRealOfInt (deps ())).run
initialize theFinite : IO.Ref (Option HolLibrary.Floor.Finite) ← IO.mkRef none
private unsafe def BFinite : HolLibrary.Floor.Finite :=
  cached theFinite "setupFinite" fun _ => (HolLibrary.Floor.setupFinite (deps ()) BInteger BRealOfInt).run
initialize theInfinite : IO.Ref (Option HolLibrary.Floor.Infinite) ← IO.mkRef none
private unsafe def BInfinite : HolLibrary.Floor.Infinite :=
  cached theInfinite "setupInfinite" fun _ => (HolLibrary.Floor.setupInfinite (deps ()) BInteger BRational).run
initialize theApprox : IO.Ref (Option HolLibrary.Floor.Approx) ← IO.mkRef none
private unsafe def BApprox : HolLibrary.Floor.Approx :=
  cached theApprox "setupApprox" fun _ => (HolLibrary.Floor.setupApprox (deps ()) BInteger BRational BFloorLemmas).run
initialize theCongruence : IO.Ref (Option HolLibrary.Floor.Congruence) ← IO.mkRef none
private unsafe def BCongruence : HolLibrary.Floor.Congruence :=
  cached theCongruence "setupCongruence" fun _ => (HolLibrary.Floor.setupCongruence (deps ()) BRealOfInt).run
initialize theIntegerTac : IO.Ref (Option HolLibrary.Floor.IntegerTac) ← IO.mkRef none
private unsafe def BIntegerTac : HolLibrary.Floor.IntegerTac :=
  cached theIntegerTac "setupIntegerTac" fun _ => (HolLibrary.Floor.setupIntegerTac (deps ()) BInteger).run

/- The theorems, by name. -/
-- Integer
unsafe def INTEGER_CASES                : thm := BInteger.INTEGER_CASES
unsafe def REAL_ABS_INTEGER_LEMMA       : thm := BInteger.REAL_ABS_INTEGER_LEMMA
unsafe def INTEGER_CLOSED               : thm := BInteger.INTEGER_CLOSED
unsafe def INTEGER_ADD                  : thm := BInteger.INTEGER_ADD
unsafe def INTEGER_SUB                  : thm := BInteger.INTEGER_SUB
unsafe def INTEGER_MUL                  : thm := BInteger.INTEGER_MUL
unsafe def INTEGER_POW                  : thm := BInteger.INTEGER_POW
unsafe def REAL_LE_INTEGERS             : thm := BInteger.REAL_LE_INTEGERS
unsafe def REAL_LE_CASES_INTEGERS       : thm := BInteger.REAL_LE_CASES_INTEGERS
unsafe def REAL_LE_REVERSE_INTEGERS     : thm := BInteger.REAL_LE_REVERSE_INTEGERS
unsafe def REAL_LT_INTEGERS             : thm := BInteger.REAL_LT_INTEGERS
unsafe def REAL_EQ_INTEGERS             : thm := BInteger.REAL_EQ_INTEGERS
unsafe def REAL_EQ_INTEGERS_IMP         : thm := BInteger.REAL_EQ_INTEGERS_IMP
unsafe def INTEGER_NEG                  : thm := BInteger.INTEGER_NEG
unsafe def INTEGER_ABS                  : thm := BInteger.INTEGER_ABS
unsafe def INTEGER_POS                  : thm := BInteger.INTEGER_POS
unsafe def NONNEGATIVE_INTEGER          : thm := BInteger.NONNEGATIVE_INTEGER
unsafe def NONPOSITIVE_INTEGER          : thm := BInteger.NONPOSITIVE_INTEGER
unsafe def NONPOSITIVE_INTEGER_ALT      : thm := BInteger.NONPOSITIVE_INTEGER_ALT
unsafe def INTEGER_ADD_EQ               : thm := BInteger.INTEGER_ADD_EQ
unsafe def INTEGER_SUB_EQ               : thm := BInteger.INTEGER_SUB_EQ
unsafe def FORALL_INTEGER               : thm := BInteger.FORALL_INTEGER
unsafe def INTEGER_SUM                  : thm := BInteger.INTEGER_SUM
unsafe def INTEGER_ABS_MUL_EQ_1         : thm := BInteger.INTEGER_ABS_MUL_EQ_1
unsafe def INTEGER_DIV                  : thm := BInteger.INTEGER_DIV

-- Rational
unsafe def rational                     : thm := BRational.rational
unsafe def RATIONAL_INTEGER             : thm := BRational.RATIONAL_INTEGER
unsafe def RATIONAL_NUM                 : thm := BRational.RATIONAL_NUM
unsafe def RATIONAL_NEG                 : thm := BRational.RATIONAL_NEG
unsafe def RATIONAL_ABS                 : thm := BRational.RATIONAL_ABS
unsafe def RATIONAL_INV                 : thm := BRational.RATIONAL_INV
unsafe def RATIONAL_ADD                 : thm := BRational.RATIONAL_ADD
unsafe def RATIONAL_SUB                 : thm := BRational.RATIONAL_SUB
unsafe def RATIONAL_MUL                 : thm := BRational.RATIONAL_MUL
unsafe def RATIONAL_DIV                 : thm := BRational.RATIONAL_DIV
unsafe def RATIONAL_POW                 : thm := BRational.RATIONAL_POW
unsafe def RATIONAL_CLOSED              : thm := BRational.RATIONAL_CLOSED
unsafe def RATIONAL_NEG_EQ              : thm := BRational.RATIONAL_NEG_EQ
unsafe def RATIONAL_ABS_EQ              : thm := BRational.RATIONAL_ABS_EQ
unsafe def RATIONAL_INV_EQ              : thm := BRational.RATIONAL_INV_EQ
unsafe def RATIONAL_SUM                 : thm := BRational.RATIONAL_SUM
unsafe def RATIONAL_ALT                 : thm := BRational.RATIONAL_ALT

-- FloorFrac
unsafe def REAL_TRUNCATE_POS            : thm := BFloorFrac.REAL_TRUNCATE_POS
unsafe def REAL_TRUNCATE                : thm := BFloorFrac.REAL_TRUNCATE
unsafe def FLOOR_FRAC                   : thm := BFloorFrac.FLOOR_FRAC

-- FloorLemmas
unsafe def FLOOR_UNIQUE                 : thm := BFloorLemmas.FLOOR_UNIQUE
unsafe def FLOOR_EQ_0                   : thm := BFloorLemmas.FLOOR_EQ_0
unsafe def FLOOR                        : thm := BFloorLemmas.FLOOR
unsafe def FLOOR_DOUBLE                 : thm := BFloorLemmas.FLOOR_DOUBLE
unsafe def FRAC_FLOOR                   : thm := BFloorLemmas.FRAC_FLOOR
unsafe def FLOOR_NUM                    : thm := BFloorLemmas.FLOOR_NUM
unsafe def REAL_LE_FLOOR                : thm := BFloorLemmas.REAL_LE_FLOOR
unsafe def REAL_FLOOR_LE                : thm := BFloorLemmas.REAL_FLOOR_LE
unsafe def REAL_FLOOR_LT                : thm := BFloorLemmas.REAL_FLOOR_LT
unsafe def REAL_LT_FLOOR                : thm := BFloorLemmas.REAL_LT_FLOOR
unsafe def FLOOR_POS                    : thm := BFloorLemmas.FLOOR_POS
unsafe def FLOOR_DIV_DIV                : thm := BFloorLemmas.FLOOR_DIV_DIV
unsafe def FLOOR_MONO                   : thm := BFloorLemmas.FLOOR_MONO
unsafe def REAL_FLOOR_EQ                : thm := BFloorLemmas.REAL_FLOOR_EQ
unsafe def REAL_FLOOR_LT_REFL           : thm := BFloorLemmas.REAL_FLOOR_LT_REFL
unsafe def REAL_FRAC_EQ_0               : thm := BFloorLemmas.REAL_FRAC_EQ_0
unsafe def REAL_FRAC_POS_LT             : thm := BFloorLemmas.REAL_FRAC_POS_LT
unsafe def FRAC_NUM                     : thm := BFloorLemmas.FRAC_NUM
unsafe def REAL_FLOOR_REFL              : thm := BFloorLemmas.REAL_FLOOR_REFL
unsafe def REAL_FRAC_ZERO               : thm := BFloorLemmas.REAL_FRAC_ZERO
unsafe def REAL_FLOOR_ADD               : thm := BFloorLemmas.REAL_FLOOR_ADD
unsafe def REAL_FLOOR_TRIANGLE          : thm := BFloorLemmas.REAL_FLOOR_TRIANGLE
unsafe def REAL_FLOOR_NEG               : thm := BFloorLemmas.REAL_FLOOR_NEG
unsafe def REAL_FRAC_ADD                : thm := BFloorLemmas.REAL_FRAC_ADD
unsafe def FLOOR_POS_LE                 : thm := BFloorLemmas.FLOOR_POS_LE
unsafe def FRAC_UNIQUE                  : thm := BFloorLemmas.FRAC_UNIQUE
unsafe def REAL_FRAC_EQ                 : thm := BFloorLemmas.REAL_FRAC_EQ
unsafe def INTEGER_ROUND                : thm := BFloorLemmas.INTEGER_ROUND
unsafe def FRAC_DIV_MOD                 : thm := BFloorLemmas.FRAC_DIV_MOD
unsafe def FRAC_NEG                     : thm := BFloorLemmas.FRAC_NEG
unsafe def REAL_FLOOR_FLOOR_DIV         : thm := BFloorLemmas.REAL_FLOOR_FLOOR_DIV

-- Between
unsafe def INTEGER_EXISTS_BETWEEN_ALT   : thm := BBetween.INTEGER_EXISTS_BETWEEN_ALT
unsafe def INTEGER_EXISTS_BETWEEN_LT    : thm := BBetween.INTEGER_EXISTS_BETWEEN_LT
unsafe def INTEGER_EXISTS_BETWEEN       : thm := BBetween.INTEGER_EXISTS_BETWEEN
unsafe def INTEGER_EXISTS_BETWEEN_ABS   : thm := BBetween.INTEGER_EXISTS_BETWEEN_ABS
unsafe def INTEGER_EXISTS_BETWEEN_ABS_LT : thm := BBetween.INTEGER_EXISTS_BETWEEN_ABS_LT

-- RealOfInt
unsafe def REAL_OF_INT_OF_REAL          : thm := BRealOfInt.REAL_OF_INT_OF_REAL
unsafe def IMAGE_REAL_OF_INT_UNIV       : thm := BRealOfInt.IMAGE_REAL_OF_INT_UNIV

-- Finite
unsafe def HAS_SIZE_INTSEG_NUM          : thm := BFinite.HAS_SIZE_INTSEG_NUM
unsafe def FINITE_INTSEG                : thm := BFinite.FINITE_INTSEG
unsafe def HAS_SIZE_INTSEG_INT          : thm := BFinite.HAS_SIZE_INTSEG_INT
unsafe def CARD_INTSEG_INT              : thm := BFinite.CARD_INTSEG_INT
unsafe def REAL_CARD_INTSEG_INT         : thm := BFinite.REAL_CARD_INTSEG_INT

-- Infinite
unsafe def INFINITE_INTEGER             : thm := BInfinite.INFINITE_INTEGER
unsafe def INFINITE_RATIONAL            : thm := BInfinite.INFINITE_RATIONAL

-- Approx
unsafe def PADIC_RATIONAL_APPROXIMATION_STRADDLE : thm := BApprox.PADIC_RATIONAL_APPROXIMATION_STRADDLE
unsafe def PADIC_RATIONAL_APPROXIMATION_STRADDLE_POS : thm := BApprox.PADIC_RATIONAL_APPROXIMATION_STRADDLE_POS
unsafe def PADIC_RATIONAL_APPROXIMATION_STRADDLE_POS_LE : thm := BApprox.PADIC_RATIONAL_APPROXIMATION_STRADDLE_POS_LE
unsafe def RATIONAL_APPROXIMATION       : thm := BApprox.RATIONAL_APPROXIMATION
unsafe def RATIONAL_BETWEEN             : thm := BApprox.RATIONAL_BETWEEN
unsafe def RATIONAL_BETWEEN_EQ          : thm := BApprox.RATIONAL_BETWEEN_EQ
unsafe def RATIONAL_APPROXIMATION_STRADDLE : thm := BApprox.RATIONAL_APPROXIMATION_STRADDLE
unsafe def RATIONAL_APPROXIMATION_ABOVE : thm := BApprox.RATIONAL_APPROXIMATION_ABOVE
unsafe def RATIONAL_APPROXIMATION_BELOW : thm := BApprox.RATIONAL_APPROXIMATION_BELOW
unsafe def INFINITE_RATIONAL_IN_RANGE   : thm := BApprox.INFINITE_RATIONAL_IN_RANGE

-- Congruence
unsafe def REAL_CONGRUENCE              : thm := BCongruence.REAL_CONGRUENCE
unsafe def REAL_INT_CONGRUENCE          : thm := BCongruence.REAL_INT_CONGRUENCE

-- IntegerTac
unsafe def REAL_INTEGER_TAC             : HolCore.Tactics.tactic := BIntegerTac.REAL_INTEGER_TAC

/-- `needs "Library/floor.ml"`: build every bundle, in file order. -/
unsafe def ensureFloor : IO Unit := do
  let _ ← IO.mkRef (concl BInteger.INTEGER_CASES)
  let _ ← IO.mkRef (concl BRational.rational)
  let _ ← IO.mkRef (concl BFloorFrac.REAL_TRUNCATE_POS)
  let _ ← IO.mkRef (concl BFloorLemmas.FLOOR_UNIQUE)
  let _ ← IO.mkRef (concl BBetween.INTEGER_EXISTS_BETWEEN_ALT)
  let _ ← IO.mkRef (concl BRealOfInt.REAL_OF_INT_OF_REAL)
  let _ ← IO.mkRef (concl BFinite.HAS_SIZE_INTSEG_NUM)
  let _ ← IO.mkRef (concl BInfinite.INFINITE_INTEGER)
  let _ ← IO.mkRef (concl BApprox.PADIC_RATIONAL_APPROXIMATION_STRADDLE)
  let _ ← IO.mkRef (concl BCongruence.REAL_CONGRUENCE)
  let _ ← IO.mkRef BIntegerTac.REAL_INTEGER_TAC
  pure ()

end SessionLibrary.Floor
