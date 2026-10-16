/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/integer.ml.                           -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Integer.lean

  The `unsafe` half of the integer.ml translation: it supplies HolLibrary.Integer's
  dependencies from Session, builds the bundles once, in order,
  and exports every name under its HOL Light name.  `ensureInteger` is
  `needs "Library/integer.ml"` (which first does nothing (no `needs`)).

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Integer.lean by tools/integerdiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.Integer

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Integer

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems integer.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.Integer.CoreThms1 where
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DISJ_ACI := Session.DISJ_ACI
  EQ_ADD_RCANCEL_0 := Session.EQ_ADD_RCANCEL_0
  EXISTS_OR_THM := Session.EXISTS_OR_THM
  FACT := Session.FACT
  FACT_NZ := Session.FACT_NZ
  FINITE_IMAGE_INJ := Session.FINITE_IMAGE_INJ
  INFINITE := Session.INFINITE
  INT_ABS := Session.INT_ABS
  INT_ABS_ABS := Session.INT_ABS_ABS
  INT_ABS_MUL := Session.INT_ABS_MUL
  INT_ABS_MUL_1 := Session.INT_ABS_MUL_1
  INT_ABS_NEG := Session.INT_ABS_NEG
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ABS_POS := Session.INT_ABS_POS
  INT_ABS_POW := Session.INT_ABS_POW
  INT_ABS_ZERO := Session.INT_ABS_ZERO
  INT_CONG_DIV2 := Session.INT_CONG_DIV2
  INT_CONG_RREM := Session.INT_CONG_RREM
  INT_DIVIDES_ABS := Session.INT_DIVIDES_ABS
  INT_DIVIDES_LABS := Session.INT_DIVIDES_LABS
  INT_DIVIDES_LCM_GCD := Session.INT_DIVIDES_LCM_GCD
  INT_DIVIDES_RABS := Session.INT_DIVIDES_RABS
  INT_DIV_1 := Session.INT_DIV_1
  INT_DIV_MUL := Session.INT_DIV_MUL
  INT_ENTIRE := Session.INT_ENTIRE
  INT_EQ_MUL_LCANCEL := Session.INT_EQ_MUL_LCANCEL
  INT_EXISTS_POS := Session.INT_EXISTS_POS
  INT_GT := Session.INT_GT
  INT_IMAGE := Session.INT_IMAGE
  INT_LCM_DIVIDES := Session.INT_LCM_DIVIDES
  INT_LCM_POS := Session.INT_LCM_POS
  INT_LE_LMUL := Session.INT_LE_LMUL
  INT_LE_MUL := Session.INT_LE_MUL
  INT_LT_LE := Session.INT_LT_LE
  INT_LT_MUL := Session.INT_LT_MUL
  INT_MUL_AC := Session.INT_MUL_AC
  INT_MUL_LCM_GCD := Session.INT_MUL_LCM_GCD
  INT_MUL_LID := Session.INT_MUL_LID
  INT_MUL_LNEG := Session.INT_MUL_LNEG
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_MUL_RID := Session.INT_MUL_RID
  INT_MUL_RNEG := Session.INT_MUL_RNEG
  INT_MUL_RZERO := Session.INT_MUL_RZERO
  INT_MUL_SYM := Session.INT_MUL_SYM
  INT_NEG_EQ_0 := Session.INT_NEG_EQ_0
  INT_NEG_NEG := Session.INT_NEG_NEG
  INT_NOT_LE := Session.INT_NOT_LE
  INT_OF_NUM_ADD := Session.INT_OF_NUM_ADD
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_SUC := Session.INT_OF_NUM_SUC
  INT_POS := Session.INT_POS
  INT_POW := Session.INT_POW
  INT_POW_ADD := Session.INT_POW_ADD
  INT_POW_EQ_0 := Session.INT_POW_EQ_0
  INT_POW_MONO_LT := Session.INT_POW_MONO_LT
  INT_POW_MUL := Session.INT_POW_MUL
  INT_POW_NEG := Session.INT_POW_NEG
  INT_POW_ONE := Session.INT_POW_ONE
  INT_POW_ZERO := Session.INT_POW_ZERO
  INT_SUB_0 := Session.INT_SUB_0
  IN_ELIM_THM := Session.IN_ELIM_THM
  LEFT_EXISTS_AND_THM := Session.LEFT_EXISTS_AND_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_EXISTS := Session.LE_EXISTS
  MONO_AND := Session.MONO_AND
/-- The core theorems integer.ml uses. -/
unsafe def core2 (_ : Unit) : HolLibrary.Integer.CoreThms2 where
  MONO_EXISTS := Session.MONO_EXISTS
  MONO_FORALL := Session.MONO_FORALL
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_LE := Session.NOT_LE
  NOT_ODD := Session.NOT_ODD
  NOT_SUC := Session.NOT_SUC
  OR_EXISTS_THM := Session.OR_EXISTS_THM
  RIGHT_EXISTS_AND_THM := Session.RIGHT_EXISTS_AND_THM
  RIGHT_OR_DISTRIB := Session.RIGHT_OR_DISTRIB
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  UNWIND_THM2 := Session.UNWIND_THM2
  WF_INT_MEASURE := Session.WF_INT_MEASURE
  int_congruent := Session.int_congruent
  int_divides := Session.int_divides
  int_gcd := Session.int_gcd
  int_lcm := Session.int_lcm
  num_FINITE := Session.num_FINITE
/-- The core theorems integer.ml uses. -/
unsafe def core3 (_ : Unit) : HolLibrary.Integer.CoreThms3 where
/-- The core theorems integer.ml uses. -/
unsafe def core4 (_ : Unit) : HolLibrary.Integer.CoreThms4 where
-- @@CORE END

/-- What integer.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Integer.IntegerDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  prioritize_int := do
    match ← HolCore.Kernel.mk_type "int" [] with
    | .ok ty => Session.prioritize_overload ty
    | .error e => throw (IO.userError e)
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)
  INT_ARITH_TAC := Session.INT_ARITH_TAC
  ASM_INT_ARITH_TAC := Session.ASM_INT_ARITH_TAC
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  INTEGER_TAC := Session.INTEGER_TAC
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  INT_RING t := ExceptT.mk (Session.INT_RING t)
  INT_REDUCE_CONV := Session.INT_REDUCE_CONV
  METIS_TAC := Session.METIS_TAC
  core1 := core1 ()
  core2 := core2 ()
  core3 := core3 ()
  core4 := core4 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`, and MATCH_CONV's basic conversions, which HOL
    Light adds loading ind_types.ml). -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.Integer: {name}"

/- The bundles, in file order; each forces the one before it. -/

-- @@BUNDLES BEGIN
initialize theDivides : IO.Ref (Option HolLibrary.Integer.Divides) ← IO.mkRef none
unsafe def BDivides : HolLibrary.Integer.Divides :=
  cached theDivides "setupDivides" fun _ => do
    (HolLibrary.Integer.setupDivides (deps ())).run

initialize theGcd : IO.Ref (Option HolLibrary.Integer.Gcd) ← IO.mkRef none
unsafe def BGcd : HolLibrary.Integer.Gcd :=
  cached theGcd "setupGcd" fun _ => do
    let _ ← IO.mkRef BDivides.INT_DIVIDES_REFL
    (HolLibrary.Integer.setupGcd (deps ()) BDivides).run

initialize theLcm : IO.Ref (Option HolLibrary.Integer.Lcm) ← IO.mkRef none
unsafe def BLcm : HolLibrary.Integer.Lcm :=
  cached theLcm "setupLcm" fun _ => do
    let _ ← IO.mkRef BGcd.INT_GCD_POS
    (HolLibrary.Integer.setupLcm (deps ()) BDivides BGcd).run

initialize theCoprime : IO.Ref (Option HolLibrary.Integer.Coprime) ← IO.mkRef none
unsafe def BCoprime : HolLibrary.Integer.Coprime :=
  cached theCoprime "setupCoprime" fun _ => do
    let _ ← IO.mkRef BLcm.INT_ABS_LCM
    (HolLibrary.Integer.setupCoprime (deps ()) BDivides BGcd BLcm).run

initialize theCong : IO.Ref (Option HolLibrary.Integer.Cong) ← IO.mkRef none
unsafe def BCong : HolLibrary.Integer.Cong :=
  cached theCong "setupCong" fun _ => do
    let _ ← IO.mkRef BCoprime.INT_COPRIME
    (HolLibrary.Integer.setupCong (deps ()) BDivides BGcd BCoprime).run

initialize theCrt : IO.Ref (Option HolLibrary.Integer.Crt) ← IO.mkRef none
unsafe def BCrt : HolLibrary.Integer.Crt :=
  cached theCrt "setupCrt" fun _ => do
    let _ ← IO.mkRef BCong.INT_CONG_MOD_0
    (HolLibrary.Integer.setupCrt (deps ())).run

initialize theIntPrime : IO.Ref (Option HolLibrary.Integer.IntPrime) ← IO.mkRef none
unsafe def BIntPrime : HolLibrary.Integer.IntPrime :=
  cached theIntPrime "setupIntPrime" fun _ => do
    let _ ← IO.mkRef BCrt.INT_CRT_STRONG
    (HolLibrary.Integer.setupIntPrime (deps ()) BDivides BCrt).run

initialize theIntPrime2 : IO.Ref (Option HolLibrary.Integer.IntPrime2) ← IO.mkRef none
unsafe def BIntPrime2 : HolLibrary.Integer.IntPrime2 :=
  cached theIntPrime2 "setupIntPrime2" fun _ => do
    let _ ← IO.mkRef BIntPrime.int_prime
    (HolLibrary.Integer.setupIntPrime2 (deps ()) BDivides BGcd BCoprime BCrt BIntPrime).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Divides
unsafe def INT_DIVIDES_REFL : thm := BDivides.INT_DIVIDES_REFL
unsafe def INT_DIVIDES_TRANS : thm := BDivides.INT_DIVIDES_TRANS
unsafe def INT_DIVIDES_ADD : thm := BDivides.INT_DIVIDES_ADD
unsafe def INT_DIVIDES_SUB : thm := BDivides.INT_DIVIDES_SUB
unsafe def INT_DIVIDES_0 : thm := BDivides.INT_DIVIDES_0
unsafe def INT_DIVIDES_ZERO : thm := BDivides.INT_DIVIDES_ZERO
unsafe def INT_DIVIDES_LNEG : thm := BDivides.INT_DIVIDES_LNEG
unsafe def INT_DIVIDES_RNEG : thm := BDivides.INT_DIVIDES_RNEG
unsafe def INT_DIVIDES_RMUL : thm := BDivides.INT_DIVIDES_RMUL
unsafe def INT_DIVIDES_LMUL : thm := BDivides.INT_DIVIDES_LMUL
unsafe def INT_DIVIDES_1 : thm := BDivides.INT_DIVIDES_1
unsafe def INT_DIVIDES_ADD_REVR : thm := BDivides.INT_DIVIDES_ADD_REVR
unsafe def INT_DIVIDES_ADD_REVL : thm := BDivides.INT_DIVIDES_ADD_REVL
unsafe def INT_DIVIDES_MUL_L : thm := BDivides.INT_DIVIDES_MUL_L
unsafe def INT_DIVIDES_MUL_R : thm := BDivides.INT_DIVIDES_MUL_R
unsafe def INT_DIVIDES_LMUL2 : thm := BDivides.INT_DIVIDES_LMUL2
unsafe def INT_DIVIDES_RMUL2 : thm := BDivides.INT_DIVIDES_RMUL2
unsafe def INT_DIVIDES_CMUL2 : thm := BDivides.INT_DIVIDES_CMUL2
unsafe def INT_DIVIDES_LMUL2_EQ : thm := BDivides.INT_DIVIDES_LMUL2_EQ
unsafe def INT_DIVIDES_RMUL2_EQ : thm := BDivides.INT_DIVIDES_RMUL2_EQ
unsafe def INT_DIVIDES_MUL2 : thm := BDivides.INT_DIVIDES_MUL2
unsafe def INT_DIVIDES_POW : thm := BDivides.INT_DIVIDES_POW
unsafe def INT_DIVIDES_POW2 : thm := BDivides.INT_DIVIDES_POW2
unsafe def INT_DIVIDES_RPOW : thm := BDivides.INT_DIVIDES_RPOW
unsafe def INT_DIVIDES_RPOW_SUC : thm := BDivides.INT_DIVIDES_RPOW_SUC
unsafe def INT_DIVIDES_POW_LE_IMP : thm := BDivides.INT_DIVIDES_POW_LE_IMP
unsafe def INT_DIVIDES_ANTISYM_DIVISORS : thm := BDivides.INT_DIVIDES_ANTISYM_DIVISORS
unsafe def INT_DIVIDES_ANTISYM_MULTIPLES : thm := BDivides.INT_DIVIDES_ANTISYM_MULTIPLES
unsafe def INT_DIVIDES_ONE_POS : thm := BDivides.INT_DIVIDES_ONE_POS
unsafe def INT_DIVIDES_ONE_ABS : thm := BDivides.INT_DIVIDES_ONE_ABS
unsafe def INT_DIVIDES_ONE : thm := BDivides.INT_DIVIDES_ONE
unsafe def INT_DIVIDES_ANTISYM_ASSOCIATED : thm := BDivides.INT_DIVIDES_ANTISYM_ASSOCIATED
unsafe def INT_DIVIDES_ANTISYM : thm := BDivides.INT_DIVIDES_ANTISYM
unsafe def INT_DIVIDES_ANTISYM_ABS : thm := BDivides.INT_DIVIDES_ANTISYM_ABS
unsafe def INT_DIVIDES_ANTISYM_POS : thm := BDivides.INT_DIVIDES_ANTISYM_POS

-- Gcd
unsafe def INT_GCD_POS : thm := BGcd.INT_GCD_POS
unsafe def INT_ABS_GCD : thm := BGcd.INT_ABS_GCD
unsafe def INT_GCD_DIVIDES : thm := BGcd.INT_GCD_DIVIDES
unsafe def INT_COPRIME_GCD : thm := BGcd.INT_COPRIME_GCD
unsafe def INT_GCD_BEZOUT : thm := BGcd.INT_GCD_BEZOUT
unsafe def INT_DIVIDES_GCD : thm := BGcd.INT_DIVIDES_GCD
unsafe def INT_GCD : thm := BGcd.INT_GCD
unsafe def INT_GCD_UNIQUE : thm := BGcd.INT_GCD_UNIQUE
unsafe def INT_GCD_UNIQUE_ABS : thm := BGcd.INT_GCD_UNIQUE_ABS
unsafe def INT_GCD_REFL : thm := BGcd.INT_GCD_REFL
unsafe def INT_GCD_SYM : thm := BGcd.INT_GCD_SYM
unsafe def INT_GCD_ASSOC : thm := BGcd.INT_GCD_ASSOC
unsafe def INT_GCD_1 : thm := BGcd.INT_GCD_1
unsafe def INT_GCD_0 : thm := BGcd.INT_GCD_0
unsafe def INT_GCD_EQ_0 : thm := BGcd.INT_GCD_EQ_0
unsafe def INT_GCD_ABS : thm := BGcd.INT_GCD_ABS
unsafe def INT_GCD_ADD : thm := BGcd.INT_GCD_ADD
unsafe def INT_GCD_SUB : thm := BGcd.INT_GCD_SUB
unsafe def INT_DIVIDES_GCD_LEFT : thm := BGcd.INT_DIVIDES_GCD_LEFT
unsafe def INT_DIVIDES_GCD_RIGHT : thm := BGcd.INT_DIVIDES_GCD_RIGHT
unsafe def INT_GCD_EQ : thm := BGcd.INT_GCD_EQ
unsafe def INT_GCD_LNEG : thm := BGcd.INT_GCD_LNEG
unsafe def INT_GCD_RNEG : thm := BGcd.INT_GCD_RNEG
unsafe def INT_GCD_NEG : thm := BGcd.INT_GCD_NEG
unsafe def INT_GCD_LABS : thm := BGcd.INT_GCD_LABS
unsafe def INT_GCD_RABS : thm := BGcd.INT_GCD_RABS
unsafe def INT_GCD_LMUL : thm := BGcd.INT_GCD_LMUL
unsafe def INT_GCD_RMUL : thm := BGcd.INT_GCD_RMUL
unsafe def INT_GCD_COPRIME_LMUL : thm := BGcd.INT_GCD_COPRIME_LMUL
unsafe def INT_GCD_COPRIME_RMUL : thm := BGcd.INT_GCD_COPRIME_RMUL
unsafe def INT_GCD_COPRIME_DIVIDES_LMUL : thm := BGcd.INT_GCD_COPRIME_DIVIDES_LMUL
unsafe def INT_GCD_COPRIME_DIVIDES_RMUL : thm := BGcd.INT_GCD_COPRIME_DIVIDES_RMUL
unsafe def INT_GCD_COPRIME_EXISTS : thm := BGcd.INT_GCD_COPRIME_EXISTS

-- Lcm
unsafe def INT_ABS_LCM : thm := BLcm.INT_ABS_LCM
unsafe def INT_LCM_EQ_0 : thm := BLcm.INT_LCM_EQ_0
unsafe def INT_DIVIDES_LCM : thm := BLcm.INT_DIVIDES_LCM
unsafe def INT_LCM_0 : thm := BLcm.INT_LCM_0
unsafe def INT_LCM_1 : thm := BLcm.INT_LCM_1
unsafe def INT_LCM_UNIQUE_ABS : thm := BLcm.INT_LCM_UNIQUE_ABS
unsafe def INT_LCM_UNIQUE : thm := BLcm.INT_LCM_UNIQUE
unsafe def INT_LCM_EQ : thm := BLcm.INT_LCM_EQ
unsafe def INT_LCM_REFL : thm := BLcm.INT_LCM_REFL
unsafe def INT_LCM_SYM : thm := BLcm.INT_LCM_SYM
unsafe def INT_LCM_ASSOC : thm := BLcm.INT_LCM_ASSOC
unsafe def INT_LCM_LNEG : thm := BLcm.INT_LCM_LNEG
unsafe def INT_LCM_RNEG : thm := BLcm.INT_LCM_RNEG
unsafe def INT_LCM_NEG : thm := BLcm.INT_LCM_NEG
unsafe def INT_LCM_LABS : thm := BLcm.INT_LCM_LABS
unsafe def INT_LCM_RABS : thm := BLcm.INT_LCM_RABS
unsafe def INT_LCM_ABS : thm := BLcm.INT_LCM_ABS
unsafe def INT_LCM_LMUL : thm := BLcm.INT_LCM_LMUL
unsafe def INT_LCM_RMUL : thm := BLcm.INT_LCM_RMUL

-- Coprime
unsafe def INT_COPRIME : thm := BCoprime.INT_COPRIME
unsafe def INT_COPRIME_ALT : thm := BCoprime.INT_COPRIME_ALT
unsafe def INT_COPRIME_SYM : thm := BCoprime.INT_COPRIME_SYM
unsafe def INT_COPRIME_DIVPROD : thm := BCoprime.INT_COPRIME_DIVPROD
unsafe def INT_COPRIME_1 : thm := BCoprime.INT_COPRIME_1
unsafe def INT_GCD_COPRIME : thm := BCoprime.INT_GCD_COPRIME
unsafe def INT_COPRIME_0 : thm := BCoprime.INT_COPRIME_0
unsafe def INT_COPRIME_MUL : thm := BCoprime.INT_COPRIME_MUL
unsafe def INT_COPRIME_LMUL2 : thm := BCoprime.INT_COPRIME_LMUL2
unsafe def INT_COPRIME_RMUL2 : thm := BCoprime.INT_COPRIME_RMUL2
unsafe def INT_COPRIME_LMUL : thm := BCoprime.INT_COPRIME_LMUL
unsafe def INT_COPRIME_RMUL : thm := BCoprime.INT_COPRIME_RMUL
unsafe def INT_COPRIME_REFL : thm := BCoprime.INT_COPRIME_REFL
unsafe def INT_COPRIME_PLUS1 : thm := BCoprime.INT_COPRIME_PLUS1
unsafe def INT_COPRIME_MINUS1 : thm := BCoprime.INT_COPRIME_MINUS1
unsafe def INT_COPRIME_RPOW : thm := BCoprime.INT_COPRIME_RPOW
unsafe def INT_COPRIME_LPOW : thm := BCoprime.INT_COPRIME_LPOW
unsafe def INT_COPRIME_POW2 : thm := BCoprime.INT_COPRIME_POW2
unsafe def INT_COPRIME_POW : thm := BCoprime.INT_COPRIME_POW
unsafe def INT_COPRIME_POW_IMP : thm := BCoprime.INT_COPRIME_POW_IMP
unsafe def INT_GCD_POW : thm := BCoprime.INT_GCD_POW
unsafe def INT_LCM_POW : thm := BCoprime.INT_LCM_POW
unsafe def INT_DIVISION_DECOMP : thm := BCoprime.INT_DIVISION_DECOMP
unsafe def INT_DIVIDES_MUL : thm := BCoprime.INT_DIVIDES_MUL
unsafe def INT_CHINESE_REMAINDER : thm := BCoprime.INT_CHINESE_REMAINDER
unsafe def INT_CHINESE_REMAINDER_USUAL : thm := BCoprime.INT_CHINESE_REMAINDER_USUAL
unsafe def INT_COPRIME_DIVISORS : thm := BCoprime.INT_COPRIME_DIVISORS
unsafe def INT_COPRIME_LNEG : thm := BCoprime.INT_COPRIME_LNEG
unsafe def INT_COPRIME_RNEG : thm := BCoprime.INT_COPRIME_RNEG
unsafe def INT_COPRIME_NEG : thm := BCoprime.INT_COPRIME_NEG
unsafe def INT_COPRIME_LABS : thm := BCoprime.INT_COPRIME_LABS
unsafe def INT_COPRIME_RABS : thm := BCoprime.INT_COPRIME_RABS
unsafe def INT_COPRIME_ABS : thm := BCoprime.INT_COPRIME_ABS

-- Cong
unsafe def INT_CONG_MOD_0 : thm := BCong.INT_CONG_MOD_0
unsafe def INT_CONG_MOD_1 : thm := BCong.INT_CONG_MOD_1
unsafe def INT_CONG : thm := BCong.INT_CONG
unsafe def INT_CONG_MOD_ABS : thm := BCong.INT_CONG_MOD_ABS
unsafe def INT_CONG_MUL_LCANCEL : thm := BCong.INT_CONG_MUL_LCANCEL
unsafe def INT_CONG_MUL_RCANCEL : thm := BCong.INT_CONG_MUL_RCANCEL
unsafe def INT_CONG_MULT_LCANCEL_ALL : thm := BCong.INT_CONG_MULT_LCANCEL_ALL
unsafe def INT_CONG_LMUL : thm := BCong.INT_CONG_LMUL
unsafe def INT_CONG_RMUL : thm := BCong.INT_CONG_RMUL
unsafe def INT_CONG_REFL : thm := BCong.INT_CONG_REFL
unsafe def INT_EQ_IMP_CONG : thm := BCong.INT_EQ_IMP_CONG
unsafe def INT_CONG_SYM : thm := BCong.INT_CONG_SYM
unsafe def INT_CONG_TRANS : thm := BCong.INT_CONG_TRANS
unsafe def INT_CONG_ADD : thm := BCong.INT_CONG_ADD
unsafe def INT_CONG_SUB : thm := BCong.INT_CONG_SUB
unsafe def INT_CONG_MUL : thm := BCong.INT_CONG_MUL
unsafe def INT_CONG_POW : thm := BCong.INT_CONG_POW
unsafe def INT_CONG_MUL_1 : thm := BCong.INT_CONG_MUL_1
unsafe def INT_CONG_POW_1 : thm := BCong.INT_CONG_POW_1
unsafe def INT_CONG_MUL_LCANCEL_EQ : thm := BCong.INT_CONG_MUL_LCANCEL_EQ
unsafe def INT_CONG_MUL_RCANCEL_EQ : thm := BCong.INT_CONG_MUL_RCANCEL_EQ
unsafe def INT_CONG_ADD_LCANCEL_EQ : thm := BCong.INT_CONG_ADD_LCANCEL_EQ
unsafe def INT_CONG_ADD_RCANCEL_EQ : thm := BCong.INT_CONG_ADD_RCANCEL_EQ
unsafe def INT_CONG_ADD_RCANCEL : thm := BCong.INT_CONG_ADD_RCANCEL
unsafe def INT_CONG_ADD_LCANCEL : thm := BCong.INT_CONG_ADD_LCANCEL
unsafe def INT_CONG_ADD_LCANCEL_EQ_0 : thm := BCong.INT_CONG_ADD_LCANCEL_EQ_0
unsafe def INT_CONG_ADD_RCANCEL_EQ_0 : thm := BCong.INT_CONG_ADD_RCANCEL_EQ_0
unsafe def INT_CONG_INT_DIVIDES_MODULUS : thm := BCong.INT_CONG_INT_DIVIDES_MODULUS
unsafe def INT_CONG_0_DIVIDES : thm := BCong.INT_CONG_0_DIVIDES
unsafe def INT_CONG_1_DIVIDES : thm := BCong.INT_CONG_1_DIVIDES
unsafe def INT_CONG_DIVIDES : thm := BCong.INT_CONG_DIVIDES
unsafe def INT_CONG_COPRIME : thm := BCong.INT_CONG_COPRIME
unsafe def INT_COPRIME_RREM : thm := BCong.INT_COPRIME_RREM
unsafe def INT_COPRIME_LREM : thm := BCong.INT_COPRIME_LREM
unsafe def INT_CONG_GCD_RIGHT : thm := BCong.INT_CONG_GCD_RIGHT
unsafe def INT_CONG_GCD_LEFT : thm := BCong.INT_CONG_GCD_LEFT
unsafe def INT_CONG_TO_1 : thm := BCong.INT_CONG_TO_1
unsafe def INT_CONG_SOLVE : thm := BCong.INT_CONG_SOLVE
unsafe def INT_CONG_SOLVE_EQ : thm := BCong.INT_CONG_SOLVE_EQ
unsafe def INT_CONG_SOLVE_UNIQUE : thm := BCong.INT_CONG_SOLVE_UNIQUE
unsafe def INT_CONG_CHINESE : thm := BCong.INT_CONG_CHINESE
unsafe def INT_CHINESE_REMAINDER_COPRIME : thm := BCong.INT_CHINESE_REMAINDER_COPRIME
unsafe def INT_CHINESE_REMAINDER_COPRIME_UNIQUE : thm := BCong.INT_CHINESE_REMAINDER_COPRIME_UNIQUE
unsafe def SOLVABLE_GCD : thm := BCong.SOLVABLE_GCD
unsafe def INT_LINEAR_CONG_POS : thm := BCong.INT_LINEAR_CONG_POS
unsafe def INT_CONG_SOLVE_POS : thm := BCong.INT_CONG_SOLVE_POS
unsafe def INT_CONG_IMP_EQ : thm := BCong.INT_CONG_IMP_EQ
unsafe def INT_CONG_DIV : thm := BCong.INT_CONG_DIV
unsafe def INT_CONG_DIV_COPRIME : thm := BCong.INT_CONG_DIV_COPRIME

-- Crt
unsafe def INT_CRT_STRONG : thm := BCrt.INT_CRT_STRONG
unsafe def INT_CRT_STRONG_IFF : thm := BCrt.INT_CRT_STRONG_IFF
unsafe def EVEN_SQUARE_MOD4 : thm := BCrt.EVEN_SQUARE_MOD4
unsafe def ODD_SQUARE_MOD4 : thm := BCrt.ODD_SQUARE_MOD4
unsafe def INT_DIVIDES_LE : thm := BCrt.INT_DIVIDES_LE
unsafe def INT_DIVIDES_POW_LE : thm := BCrt.INT_DIVIDES_POW_LE

-- IntPrime
unsafe def int_prime : thm := BIntPrime.int_prime
unsafe def INT_PRIME_NEG : thm := BIntPrime.INT_PRIME_NEG
unsafe def INT_PRIME_ABS : thm := BIntPrime.INT_PRIME_ABS
unsafe def INT_PRIME_GE_2 : thm := BIntPrime.INT_PRIME_GE_2
unsafe def INT_PRIME_0 : thm := BIntPrime.INT_PRIME_0
unsafe def INT_PRIME_1 : thm := BIntPrime.INT_PRIME_1
unsafe def INT_PRIME_2 : thm := BIntPrime.INT_PRIME_2
unsafe def INT_PRIME_FACTOR : thm := BIntPrime.INT_PRIME_FACTOR
unsafe def INT_PRIME_FACTOR_LT : thm := BIntPrime.INT_PRIME_FACTOR_LT
unsafe def INT_PRIME_FACTOR_INDUCT : thm := BIntPrime.INT_PRIME_FACTOR_INDUCT

-- IntPrime2
unsafe def INT_DIVIDES_FACT : thm := BIntPrime2.INT_DIVIDES_FACT
unsafe def INT_EUCLID_BOUND : thm := BIntPrime2.INT_EUCLID_BOUND
unsafe def INT_EUCLID : thm := BIntPrime2.INT_EUCLID
unsafe def INT_PRIMES_INFINITE : thm := BIntPrime2.INT_PRIMES_INFINITE
unsafe def INT_COPRIME_PRIME : thm := BIntPrime2.INT_COPRIME_PRIME
unsafe def INT_COPRIME_PRIME_EQ : thm := BIntPrime2.INT_COPRIME_PRIME_EQ
unsafe def INT_PRIME_COPRIME : thm := BIntPrime2.INT_PRIME_COPRIME
unsafe def INT_PRIME_COPRIME_EQ : thm := BIntPrime2.INT_PRIME_COPRIME_EQ
unsafe def INT_COPRIME_PRIMEPOW : thm := BIntPrime2.INT_COPRIME_PRIMEPOW
unsafe def INT_COPRIME_BEZOUT : thm := BIntPrime2.INT_COPRIME_BEZOUT
unsafe def INT_COPRIME_BEZOUT_ALT : thm := BIntPrime2.INT_COPRIME_BEZOUT_ALT
unsafe def INT_BEZOUT_PRIME : thm := BIntPrime2.INT_BEZOUT_PRIME
unsafe def INT_PRIME_DIVPROD : thm := BIntPrime2.INT_PRIME_DIVPROD
unsafe def INT_PRIME_DIVPROD_EQ : thm := BIntPrime2.INT_PRIME_DIVPROD_EQ
unsafe def INT_PRIME_DIVPOW : thm := BIntPrime2.INT_PRIME_DIVPOW
unsafe def INT_PRIME_DIVPOW_N : thm := BIntPrime2.INT_PRIME_DIVPOW_N
unsafe def INT_COPRIME_SOS : thm := BIntPrime2.INT_COPRIME_SOS
unsafe def INT_PRIME_IMP_NZ : thm := BIntPrime2.INT_PRIME_IMP_NZ
unsafe def INT_DISTINCT_PRIME_COPRIME : thm := BIntPrime2.INT_DISTINCT_PRIME_COPRIME
unsafe def INT_PRIME_COPRIME_LT : thm := BIntPrime2.INT_PRIME_COPRIME_LT
unsafe def INT_DIVIDES_PRIME_PRIME : thm := BIntPrime2.INT_DIVIDES_PRIME_PRIME
unsafe def INT_COPRIME_POW_DIVPROD : thm := BIntPrime2.INT_COPRIME_POW_DIVPROD
unsafe def INT_PRIME_COPRIME_CASES : thm := BIntPrime2.INT_PRIME_COPRIME_CASES
unsafe def INT_PRIME_DIVPROD_POW : thm := BIntPrime2.INT_PRIME_DIVPROD_POW
unsafe def INT_DIVIDES_POW2_REV : thm := BIntPrime2.INT_DIVIDES_POW2_REV
unsafe def INT_DIVIDES_POW2_EQ : thm := BIntPrime2.INT_DIVIDES_POW2_EQ
unsafe def INT_POW_MUL_EXISTS : thm := BIntPrime2.INT_POW_MUL_EXISTS
unsafe def INT_COPRIME_POW_ABS : thm := BIntPrime2.INT_COPRIME_POW_ABS
unsafe def INT_COPRIME_POW_ODD : thm := BIntPrime2.INT_COPRIME_POW_ODD
unsafe def INT_DIVIDES_PRIME_POW_LE : thm := BIntPrime2.INT_DIVIDES_PRIME_POW_LE
unsafe def INT_EQ_PRIME_POW_ABS : thm := BIntPrime2.INT_EQ_PRIME_POW_ABS
unsafe def INT_EQ_PRIME_POW_POS : thm := BIntPrime2.INT_EQ_PRIME_POW_POS
unsafe def INT_DIVIDES_FACT_PRIME : thm := BIntPrime2.INT_DIVIDES_FACT_PRIME
-- @@EXPORTS END

/-- `needs "Library/integer.ml"`: build the bundles, in order. -/
unsafe def ensureInteger : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BDivides.INT_DIVIDES_REFL
  let _ ← IO.mkRef BGcd.INT_GCD_POS
  let _ ← IO.mkRef BLcm.INT_ABS_LCM
  let _ ← IO.mkRef BCoprime.INT_COPRIME
  let _ ← IO.mkRef BCong.INT_CONG_MOD_0
  let _ ← IO.mkRef BCrt.INT_CRT_STRONG
  let _ ← IO.mkRef BIntPrime.int_prime
  let _ ← IO.mkRef BIntPrime2.INT_DIVIDES_FACT  -- @@ENSURE END
  pure ()

end SessionLibrary.Integer
