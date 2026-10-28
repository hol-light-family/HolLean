/- File: SessionMath/CalcNum.lean
calc_num.ml: calculation with natural numbers.  The rewrite collection,
numeral constants, proformas and nets are built by `initialize` when this
module is imported.  NUM_REL_CONV, NUM_RED_CONV and NUM_COMPUTE_CONV are
closures, kept in `IO.Ref`s; they are built by `ensureCalcNumProcs` at the
end of SessionMath/Grobner.lean, as the old Session forced them.
-/
import SessionMath.Wf
import HolMath.CalcNum

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic

namespace Session

private def ioOk' {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")


/- calc_num.ml : the `ARITH_*` trivial-arithmetic rewrite collection.     -/
/- ---------------------------------------------------------------------- -/

initialize CnA : HolMath.CalcNum.ArithRewrites ←
  ioOk' "setupArithRewrites" (HolMath.CalcNum.setupArithRewrites Nm arith1 arith2 arith3 arith4 arith5).run

def ARITH_ZERO : thm := CnA.ARITH_ZERO
def BIT0_0     : thm := CnA.BIT0_0
def BIT1_0     : thm := CnA.BIT1_0
def ARITH_SUC  : thm := CnA.ARITH_SUC
def ARITH_PRE  : thm := CnA.ARITH_PRE
def ARITH_ADD  : thm := CnA.ARITH_ADD
def ARITH_MULT : thm := CnA.ARITH_MULT
def ARITH_EXP  : thm := CnA.ARITH_EXP
def ARITH_EVEN : thm := CnA.ARITH_EVEN
def ARITH_ODD  : thm := CnA.ARITH_ODD
def ARITH_LE   : thm := CnA.ARITH_LE
def ARITH_LT   : thm := CnA.ARITH_LT
def ARITH_GE   : thm := CnA.ARITH_GE
def ARITH_GT   : thm := CnA.ARITH_GT
def ARITH_EQ   : thm := CnA.ARITH_EQ
def ARITH_SUB  : thm := CnA.ARITH_SUB
def ARITH      : thm := CnA.ARITH
def EXP_2_NE_0 : thm := CnA.EXP_2_NE_0

/- ---------------------------------------------------------------------- -/
/- calc_num.ml : the delicate numeral conversions (lines 208-603).        -/
/- ---------------------------------------------------------------------- -/

/-- The shared `calc_num.ml` numeral-conversion term constants. -/
initialize CnK : HolMath.CalcNum.CalcNumConsts ←
  ioOk' "setupCalcNumConsts" (HolMath.CalcNum.setupCalcNumConsts Nm.ZERO_DEF TWO ADD_0 EXP_2
    DIVISION SUB_0 LE_0 (HolMath.Nums.mk_small_numeral Nm.numK)).run

/-- The `calc_num.ml` delicate-conversion proformas. -/
initialize CnP : HolMath.CalcNum.CalcNumProformas ←
  -- `setupCalcNumProformas` PARSES terms mentioning `DIV` and `MOD`, so those
  -- constants must already be DECLARED.  DIVISION (arith.ml, forced by the
  -- eager Arith layer) declares them, so by now they are.
  ioOk' "setupCalcNumProformas" (HolMath.CalcNum.setupCalcNumProformas CnK CnA
    Nm.NUMERAL BIT0 BIT1 ADD_CLAUSES MULT_CLAUSES Nm.SUC_INJ
    EQ_MULT_LCANCEL MULT_2 MULT_ASSOC LEFT_ADD_DISTRIB
    ADD_EQ_0 MULT_EQ_0
    RIGHT_ADD_DISTRIB EXP_2 MULT_AC ADD_AC EQ_ADD_LCANCEL
    EQ_ADD_RCANCEL ADD_SYM ADD1 ADD_ASSOC Nm.NOT_SUC MULT_SYM
    EXP EXP_ADD LT_EXISTS LE_ADD NOT_LT NOT_LE
    LE_ANTISYM LT_REFL LE_REFL
    PRE SUB_EQ_0 ADD_SUB DIVMOD_UNIQ DIV_ZERO MOD_ZERO FACT LT
    MESON_TAC MOD_DOWN_CONV NUM_CANCEL_CONV (HolMath.Nums.mk_small_numeral Nm.numK)).run

/-- What calc_num.ml's later conversions build before their `fun tm ->`.
    Forced at calc_num.ml's position, because `REWRITE_CONV[GSYM CONJ_ASSOC]`
    captures the basic rewrites current then. -/
initialize CnN : HolMath.CalcNum.CalcNumNets ←
  ioOk' "setupCalcNumNets" (HolMath.CalcNum.setupCalcNumNets CnA CnK CnP GT GE C.COND_CLAUSES
    T.CONJ_ASSOC MOD_ZERO).run

/-- The shared `calc_num.ml` numeral-conversion constants. -/
def calcNumConsts : HolMath.CalcNum.CalcNumConsts := CnK

/-- `NUM_EVEN_CONV` (calc_num.ml 211). -/
def NUM_EVEN_CONV : ioconv := fun tm => CnN.even_conv tm

/-- `NUM_ODD_CONV` (calc_num.ml 215). -/
def NUM_ODD_CONV : ioconv := fun tm => CnN.odd_conv tm

/-- The `calc_num.ml` delicate-conversion proformas. -/
def calcNumProformas : HolMath.CalcNum.CalcNumProformas := CnP

/-- `NUM_ADD_RULE mtm ntm` (calc_num.ml): add two raw numerals. -/
def NUM_ADD_RULE (mtm ntm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_ADD_RULE CnK CnP mtm ntm

/-- `NUM_ADC_RULE mtm ntm` (calc_num.ml): add two raw numerals with carry. -/
def NUM_ADC_RULE (mtm ntm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_ADC_RULE CnK CnP mtm ntm

/-- `NUM_SHIFT_CONV k tm` (calc_num.ml). -/
def NUM_SHIFT_CONV (k : Int) (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_SHIFT_CONV CnK CnP k tm

/-- `NUM_UNSHIFT_CONV tm` (calc_num.ml). -/
def NUM_UNSHIFT_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_UNSHIFT_CONV CnK CnP tm

/-- `TOOM3_CONV` (calc_num.ml). -/
def TOOM3_CONV : ioconv := HolMath.CalcNum.TOOM3_CONV CnK CnP

/-- `NUM_SQUARE_RULE tm` (calc_num.ml). -/
def NUM_SQUARE_RULE (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_SQUARE_RULE CnK CnP (HolMath.Nums.mk_numeral Nm.numK) tm

/-- `NUM_MUL_RULE k l tm tm'` (calc_num.ml). -/
def NUM_MUL_RULE (k l : Int) (tm tm' : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_MUL_RULE CnK CnP (HolMath.Nums.mk_numeral Nm.numK) k l tm tm'

/-- `NUM_SUC_CONV tm` (calc_num.ml): `|- SUC (NUMERAL m) = NUMERAL n`. -/
def NUM_SUC_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_SUC_CONV CnK CnP tm

/-- `NUM_ADD_CONV tm` (calc_num.ml): `|- NUMERAL m + NUMERAL n = NUMERAL p`. -/
def NUM_ADD_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_ADD_CONV CnK CnP tm

/-- `NUM_MULT_CONV tm` (calc_num.ml): `|- NUMERAL m * NUMERAL n = NUMERAL p`. -/
def NUM_MULT_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_MULT_CONV CnK CnP (HolMath.Nums.mk_numeral Nm.numK) tm

/-- `NUM_EXP_CONV tm` (calc_num.ml): `|- NUMERAL m EXP NUMERAL n = NUMERAL p`. -/
def NUM_EXP_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_EXP_CONV CnK CnP (HolMath.Nums.mk_numeral Nm.numK) CnN.exp_tconv tm

/-- `NUM_LT_CONV tm` (calc_num.ml): `|- (NUMERAL m < NUMERAL n) <=> T/F`. -/
def NUM_LT_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_LT_CONV CnK CnP tm

/-- `NUM_LE_CONV tm` (calc_num.ml): `|- (NUMERAL m <= NUMERAL n) <=> T/F`. -/
def NUM_LE_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_LE_CONV CnK CnP tm

/-- `NUM_EQ_CONV tm` (calc_num.ml): `|- (NUMERAL m = NUMERAL n) <=> T/F`. -/
def NUM_EQ_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_EQ_CONV CnK CnP tm

/- ---------------------------------------------------------------------- -/
/- calc_num.ml : the remaining conversions (lines 1314-1560).             -/
/- ---------------------------------------------------------------------- -/

/-- `NUM_GT_CONV` (calc_num.ml). -/
def NUM_GT_CONV : ioconv := HolMath.CalcNum.NUM_GT_CONV CnN CnK CnP

/-- `NUM_GE_CONV` (calc_num.ml). -/
def NUM_GE_CONV : ioconv := HolMath.CalcNum.NUM_GE_CONV CnN CnK CnP

/-- `NUM_PRE_CONV tm` (calc_num.ml): `|- PRE (NUMERAL n) = NUMERAL m`. -/
def NUM_PRE_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_PRE_CONV CnN CnK CnP (HolMath.Nums.mk_numeral Nm.numK) tm

/-- `NUM_SUB_CONV tm` (calc_num.ml): `|- NUMERAL m - NUMERAL n = NUMERAL p`. -/
def NUM_SUB_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_SUB_CONV CnK CnP (HolMath.Nums.mk_numeral Nm.numK) tm

/-- `NUM_DIV_CONV tm` (calc_num.ml): `|- NUMERAL m DIV NUMERAL n = NUMERAL q`. -/
def NUM_DIV_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_DIV_CONV CnN CnK CnP (HolMath.Nums.mk_numeral Nm.numK) tm

/-- `NUM_MOD_CONV tm` (calc_num.ml): `|- NUMERAL m MOD NUMERAL n = NUMERAL r`. -/
def NUM_MOD_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_MOD_CONV CnN CnK CnP (HolMath.Nums.mk_numeral Nm.numK) tm

/-- `NUM_FACT_CONV tm` (calc_num.ml): `|- FACT (NUMERAL n) = NUMERAL z`. -/
def NUM_FACT_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.NUM_FACT_CONV CnN CnK CnP (HolMath.Nums.mk_numeral Nm.numK) tm

/-- `NUM_MAX_CONV` (calc_num.ml). -/
def NUM_MAX_CONV : ioconv :=
  HolMath.CalcNum.NUM_MAX_CONV CnN MAX CnK CnP

/-- `NUM_MIN_CONV` (calc_num.ml). -/
def NUM_MIN_CONV : ioconv :=
  HolMath.CalcNum.NUM_MIN_CONV CnN MIN CnK CnP

/-- `num_CONV tm` (calc_num.ml): `|- NUMERAL n = SUC (NUMERAL (n-1))`. -/
def num_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.num_CONV CnK CnP (HolMath.Nums.mk_numeral Nm.numK) tm

/-- `EXPAND_CASES_CONV` (calc_num.ml): expand `!n. n < k ==> P n` into cases. -/
def EXPAND_CASES_CONV : ioconv :=
  HolMath.CalcNum.EXPAND_CASES_CONV CnN CnK CnP (HolMath.Nums.mk_numeral Nm.numK)

/-- `NUM_EVEN_CONV` as a plain `ioconv` (forcing the cached ARITH_EVEN conv). -/
def numEvenConvIO : ioconv := NUM_EVEN_CONV

/-- `NUM_ODD_CONV` as a plain `ioconv` (forcing the cached ARITH_ODD conv). -/
def numOddConvIO : ioconv := NUM_ODD_CONV


/- ---------------------------------------------------------------------- -/
/- calc_num.ml : NUM_RED_CONV / NUM_REL_CONV / NUM_REDUCE_* / NUM_COMPUTE.  -/
/- These build nets/compsets from UNANNOTATED patterns when the file loads,
   so Session caches each in an `Option` ref and forces it at this point.
   Here the refs are plain and seeded, in file order, by the forcing block
   `ensureCalcNumProcs` below (they hold closures, so they cannot be
   function-typed `initialize` constants; same reason as Arith procs). -/
/- ---------------------------------------------------------------------- -/

initialize theNumRedConvList : IO.Ref (Option (List (term × ioconv))) ← IO.mkRef none
initialize theNumRedConv : IO.Ref (Option ioconv) ← IO.mkRef none
initialize theNumRelConv : IO.Ref (Option ioconv) ← IO.mkRef none
initialize theNumComputeConv : IO.Ref (Option ioconv) ← IO.mkRef none

private def numRedConvListIO : IO (Except String (List (term × ioconv))) := do
  match ← theNumRedConvList.get with
  | some l => return .ok l
  | none =>
    match ← HolMath.CalcNum.num_red_conv_list
        NUM_SUC_CONV NUM_PRE_CONV NUM_FACT_CONV NUM_LT_CONV NUM_LE_CONV
        NUM_GT_CONV NUM_GE_CONV NUM_EQ_CONV numEvenConvIO numOddConvIO
        NUM_ADD_CONV NUM_SUB_CONV NUM_MULT_CONV NUM_EXP_CONV NUM_DIV_CONV
        NUM_MOD_CONV NUM_MAX_CONV NUM_MIN_CONV with
    | .error e => return .error e
    | .ok l => do theNumRedConvList.set (some l); return .ok l

private def numRedConvIO : IO (Except String ioconv) := do
  match ← theNumRedConv.get with
  | some c => return .ok c
  | none =>
    match ← numRedConvListIO with
    | .error e => return .error e
    | .ok l =>
      match ← HolMath.CalcNum.NUM_RED_CONV l with
      | .error e => return .error e
      | .ok c => do theNumRedConv.set (some c); return .ok c

private def numRelConvIO : IO (Except String ioconv) := do
  match ← theNumRelConv.get with
  | some c => return .ok c
  | none =>
    match ← HolMath.CalcNum.NUM_REL_CONV NUM_LT_CONV NUM_LE_CONV NUM_GT_CONV
        NUM_GE_CONV NUM_EQ_CONV with
    | .error e => return .error e
    | .ok c => do theNumRelConv.set (some c); return .ok c

/-- `NUM_REL_CONV` (calc_num.ml 1443-1451): the five relational reductions. -/
def NUM_REL_CONV (tm : term) : IO (Except String thm) := do
  match ← numRelConvIO with
  | .error e => return .error e
  | .ok c => c tm

/-- `NUM_RED_CONV tm` (calc_num.ml): a single numeral reduction step. -/
def NUM_RED_CONV (tm : term) : IO (Except String thm) := do
  match ← numRedConvIO with
  | .error e => return .error e
  | .ok c => c tm

/-- `NUM_REDUCE_CONV tm` (calc_num.ml): `DEPTH_CONV NUM_RED_CONV`. -/
def NUM_REDUCE_CONV (tm : term) : IO (Except String thm) := do
  match ← numRedConvIO with
  | .error e => return .error e
  | .ok c => HolMath.CalcNum.NUM_REDUCE_CONV c tm

/-- `NUM_REDUCE_TAC` (calc_num.ml): `CONV_TAC NUM_REDUCE_CONV`. -/
def NUM_REDUCE_TAC : tactic :=
  HolMath.CalcNum.NUM_REDUCE_TAC NUM_REDUCE_CONV

private def numComputeConvIO : IO (Except String ioconv) := do
  match ← theNumComputeConv.get with
  | some c => return .ok c
  | none =>
    match ← numRedConvListIO with
    | .error e => return .error e
    | .ok l =>
      match ← HolMath.CalcNum.NUM_COMPUTE_CONV l bool_compset
          set_skip add_conv WEAK_CBV_CONV [[ COND: bool -> A -> A -> A ]] with
      | .error e => return .error e
      | .ok c => do theNumComputeConv.set (some c); return .ok c

/-- `NUM_COMPUTE_CONV tm` (calc_num.ml): call-by-value numeral evaluation via a
    `bool_compset ()` extended with the reduction conversions. -/
def NUM_COMPUTE_CONV (tm : term) : IO (Except String thm) := do
  match ← numComputeConvIO with
  | .error e => return .error e
  | .ok c => c tm

/-- `EXP_MOD_CONV tm` (calc_num.ml): compute `(a EXP k) MOD n` with reduced
    intermediates. -/
def EXP_MOD_CONV (tm : term) : IO (Except String thm) :=
  HolMath.CalcNum.EXP_MOD_CONV CnN NUM_EXP_CONV NUM_MULT_CONV NUM_MOD_CONV tm

/- ---------------------------------------------------------------------- -/
/- calc_num.ml 1443-1487: NUM_REL_CONV, NUM_RED_CONV and NUM_COMPUTE_CONV, -/
/- built here, at the end of calc_num.ml as in HOL Light.  They build nets  -/
/- and a compset from unannotated patterns, so under `num`'s overloads.    -/
/- ---------------------------------------------------------------------- -/
initialize calcNumConvsLayer : Unit ← do
  match ← numRelConvIO with                                 -- calc_num.ml 1443
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"NUM_REL_CONV setup: {e}")
  match ← numRedConvIO with                                 -- calc_num.ml 1473
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"NUM_RED_CONV setup: {e}")
  match ← numComputeConvIO with                             -- calc_num.ml 1487
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"NUM_COMPUTE_CONV setup: {e}")

/- ---------------------------------------------------------------------- -/

end Session
