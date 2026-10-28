/- File: SessionMath/CalcInt.lean
calc_int.ml: calculation with integer-valued reals, built by `initialize`
when this module is imported.  REAL_INT_RED_CONV and REAL_INT_COMPUTE_CONV
are closures, kept in `IO.Ref`s; `calcIntConvsLayer` builds them at the end
of the module (calc_int.ml 376-403), as HOL Light does at the end of the file.
-/
import SessionMath.RealAx
import HolMath.CalcInt

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic

namespace Session

private def ioOk' {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")


/- ---------------------------------------------------------------------- -/
/- calc_int.ml: calculation with integer-valued reals.                     -/
/-                                                                        -/
/- Seven stages, in calc_int.ml's own order.  As with realax.ml the order  -/
/- is enforced STRUCTURALLY — each stage takes the previous stage's record  -/
/- as a parameter — and reproduced by `initialize` declaration order.      -/
/- ---------------------------------------------------------------------- -/

/-- `RatSyntax` (calc_int.ml 32-60): the terms `mk_realintconst` and
    `term_of_rat` close over.  It PARSES `real_of_num`, `(--)` and `(/)`, so
    the real layer must already exist (it does — `Rl` is forced above). -/
initialize ratSyntaxLayer : HolMath.CalcInt.RatSyntax ←
  ioOk' "setupRatSyntax" (HolMath.CalcInt.setupRatSyntax mk_numeral).run

def RSyn : HolMath.CalcInt.RatSyntax := ratSyntaxLayer

/-- `CalcIntThms` (calc_int.ml 66-171): the nineteen elementary real theorems
    derived from the realax.ml axioms. -/
initialize calcIntLayer : HolMath.CalcInt.CalcIntThms ←
  ioOk' "setupCalcInt" (HolMath.CalcInt.setupCalcInt arith2 arith5 Nm Rl MESON_TAC).run

def CiT : HolMath.CalcInt.CalcIntThms := calcIntLayer

/-- The five comparison conversions (calc_int.ml 177-246). -/
initialize realIntCompareLayer : HolMath.CalcInt.RealIntCompareConvs ←
  ioOk' "setupRealIntCompareConvs" (HolMath.CalcInt.setupRealIntCompareConvs NUM_EQ_CONV
    NUM_LE_CONV NUM_LT_CONV CiT Rl arith1 arith2 arith3).run

def CiV : HolMath.CalcInt.RealIntCompareConvs := realIntCompareLayer

/-- The six arithmetic conversions (calc_int.ml 248-374). -/
initialize realIntArithLayer : HolMath.CalcInt.RealIntArithConvs ←
  ioOk' "setupRealIntArithConvs" (HolMath.CalcInt.setupRealIntArithConvs NUM_MULT_CONV NUM_ADD_CONV
    NUM_EXP_CONV NUM_EVEN_CONV mk_numeral CiT Rl).run

def CiW : HolMath.CalcInt.RealIntArithConvs := realIntArithLayer

/- Public accessors for the calc_int.ml bundles. -/

/-- The `calc_int.ml` rational-syntax record (32-60). -/
def ratSyntax : HolMath.CalcInt.RatSyntax := RSyn
/-- The `calc_int.ml` elementary-real-theorem record (66-171). -/
def calcIntThms : HolMath.CalcInt.CalcIntThms := CiT
/-- The `calc_int.ml` comparison conversions (177-246). -/
def realIntCompareConvs : HolMath.CalcInt.RealIntCompareConvs := CiV
/-- The `calc_int.ml` arithmetic conversions (248-374). -/
def realIntArithConvs : HolMath.CalcInt.RealIntArithConvs := CiW

/- The six syntax operations, with the `RatSyntax` record already supplied. -/

/-- `is_realintconst` (calc_int.ml 16). -/
def is_realintconst : term → Bool := HolMath.CalcInt.is_realintconst
/-- `dest_realintconst` (calc_int.ml 23). -/
def dest_realintconst : term → Except String Rat :=
  HolMath.CalcInt.dest_realintconst
/-- `mk_realintconst` (calc_int.ml 32). -/
def mk_realintconst (x : Rat) : Except String term :=
  HolMath.CalcInt.mk_realintconst RSyn x
/-- `is_ratconst` (calc_int.ml 38). -/
def is_ratconst : term → Bool := HolMath.CalcInt.is_ratconst
/-- `rat_of_term` (calc_int.ml 46). -/
def rat_of_term : term → Except String Rat := HolMath.CalcInt.rat_of_term
/-- `term_of_rat` (calc_int.ml 54). -/
def term_of_rat (x : Rat) : Except String term :=
  HolMath.CalcInt.term_of_rat RSyn x

/- The five comparison and six arithmetic conversions, as plain `ioconv`s. -/

/-- `REAL_INT_LE_CONV` (calc_int.ml 177). -/
def REAL_INT_LE_CONV  : ioconv := CiV.REAL_INT_LE_CONV
/-- `REAL_INT_LT_CONV` (calc_int.ml 177). -/
def REAL_INT_LT_CONV  : ioconv := CiV.REAL_INT_LT_CONV
/-- `REAL_INT_GE_CONV` (calc_int.ml 177). -/
def REAL_INT_GE_CONV  : ioconv := CiV.REAL_INT_GE_CONV
/-- `REAL_INT_GT_CONV` (calc_int.ml 177). -/
def REAL_INT_GT_CONV  : ioconv := CiV.REAL_INT_GT_CONV
/-- `REAL_INT_EQ_CONV` (calc_int.ml 177). -/
def REAL_INT_EQ_CONV  : ioconv := CiV.REAL_INT_EQ_CONV
/-- `REAL_INT_NEG_CONV` (calc_int.ml 248). -/
def REAL_INT_NEG_CONV : ioconv := CiW.REAL_INT_NEG_CONV
/-- `REAL_INT_MUL_CONV` (calc_int.ml 255). -/
def REAL_INT_MUL_CONV : ioconv := CiW.REAL_INT_MUL_CONV
/-- `REAL_INT_ADD_CONV` (calc_int.ml 274). -/
def REAL_INT_ADD_CONV : ioconv := CiW.REAL_INT_ADD_CONV
/-- `REAL_INT_SUB_CONV` (calc_int.ml 348). -/
def REAL_INT_SUB_CONV : ioconv := CiW.REAL_INT_SUB_CONV
/-- `REAL_INT_POW_CONV` (calc_int.ml 353). -/
def REAL_INT_POW_CONV : ioconv := CiW.REAL_INT_POW_CONV
/-- `REAL_INT_ABS_CONV` (calc_int.ml 369). -/
def REAL_INT_ABS_CONV : ioconv := CiW.REAL_INT_ABS_CONV

/-- `real_int_red_conv_list` (calc_int.ml 376-387).  Built once; holds
    `ioconv` closures, so it lives in a plain `Option` ref seeded by the
    forcing block `ensureRealAxProcs` below. -/
initialize theRealIntRedConvList : IO.Ref (Option (List (term × ioconv))) ← IO.mkRef none

private def realIntRedConvListIO : IO (Except String (List (term × ioconv))) := do
  match ← theRealIntRedConvList.get with
  | some l => return .ok l
  | none =>
    match ← (HolMath.CalcInt.real_int_red_conv_list CiV CiW).run with
    | .ok l => do theRealIntRedConvList.set (some l); return .ok l
    | .error e => return .error e

/-- `real_int_red_conv_list` (calc_int.ml 376-387), built once. -/
def real_int_red_conv_list : IO (Except String (List (term × ioconv))) :=
  realIntRedConvListIO

/-- Cache for `REAL_INT_RED_CONV` (calc_int.ml 389).  Memoised because the
    OCaml SNAPSHOTS `basic_net()` once when the conversion is defined; building
    the net afresh on every call would not reproduce that. -/
initialize theRealIntRed : IO.Ref (Option ioconv) ← IO.mkRef none

private def realIntRedIO : IO (Except String ioconv) := do
  match ← theRealIntRed.get with
  | some c => return .ok c
  | none =>
    match ← (do HolMath.CalcInt.REAL_INT_RED_CONV (← ExceptT.mk realIntRedConvListIO)).run with
    | .ok c => do theRealIntRed.set (some c); return .ok c
    | .error e => return .error s!"REAL_INT_RED_CONV: {e}"

/-- `REAL_INT_RED_CONV` (calc_int.ml 389): one reduction step on an
    integer-constant term, via the eleven-entry net over `basic_net()`. -/
def REAL_INT_RED_CONV : ioconv := fun tm => do
  match ← realIntRedIO with
  | .ok c => c tm
  | .error e => return .error e

/-- `REAL_INT_REDUCE_CONV` (calc_int.ml 394): `DEPTH_CONV REAL_INT_RED_CONV`. -/
def REAL_INT_REDUCE_CONV : ioconv := Simp.depthConvIO REAL_INT_RED_CONV

/-- `real_int_compute_add_convs` (calc_int.ml 396): register the eleven
    conversions with a `compset`. -/
def real_int_compute_add_convs (cs : HolMath.Compute.compset) :
    IO (Except String Unit) :=
  (do HolMath.CalcInt.real_int_compute_add_convs (← ExceptT.mk realIntRedConvListIO) cs).run

/-- Cache for `REAL_INT_COMPUTE_CONV` (calc_int.ml 403): call-by-value
    reduction over the boolean compset extended with those conversions.  The
    OCaml builds its compset once, so memoise. -/
initialize theRealIntCompute : IO.Ref (Option ioconv) ← IO.mkRef none

private def realIntComputeIO : IO (Except String ioconv) := do
  match ← theRealIntCompute.get with
  | some c => return .ok c
  | none =>
    match ← realIntRedConvListIO with
    | .error e => return .error e
    | .ok cl =>
      match ← (HolMath.CalcInt.REAL_INT_COMPUTE_CONV cl bool_compset WEAK_CBV_CONV).run with
      | .ok c => do theRealIntCompute.set (some c); return .ok c
      | .error e => return .error s!"REAL_INT_COMPUTE_CONV: {e}"

/-- `REAL_INT_COMPUTE_CONV` (calc_int.ml 403). -/
def REAL_INT_COMPUTE_CONV : ioconv := fun tm => do
  match ← realIntComputeIO with
  | .ok c => c tm
  | .error e => return .error e

/-- calc_int.ml 376-403: `real_int_red_conv_list`, REAL_INT_RED_CONV and
    REAL_INT_COMPUTE_CONV, built here, at the end of calc_int.ml as in HOL
    Light.  Each snapshots `basic_net()` while realax.ml's `real` overloads
    are current. -/
initialize calcIntConvsLayer : Unit ← do
  match ← realIntRedConvListIO with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"real_int_red_conv_list setup: {e}")
  match ← realIntRedIO with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"REAL_INT_RED_CONV setup: {e}")
  match ← realIntComputeIO with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"REAL_INT_COMPUTE_CONV setup: {e}")


/- The calc_int.ml theorems as bare names, as HOL Light has them. -/
def REAL_ADD_AC         : thm := CiT.REAL_ADD_AC
def REAL_ADD_RINV       : thm := CiT.REAL_ADD_RINV
def REAL_EQ_ADD_LCANCEL : thm := CiT.REAL_EQ_ADD_LCANCEL
def REAL_EQ_ADD_RCANCEL : thm := CiT.REAL_EQ_ADD_RCANCEL
def REAL_MUL_RZERO      : thm := CiT.REAL_MUL_RZERO
def REAL_MUL_LZERO      : thm := CiT.REAL_MUL_LZERO
def REAL_NEG_NEG        : thm := CiT.REAL_NEG_NEG
def REAL_MUL_RNEG       : thm := CiT.REAL_MUL_RNEG
def REAL_MUL_LNEG       : thm := CiT.REAL_MUL_LNEG
def REAL_NEG_ADD        : thm := CiT.REAL_NEG_ADD
def REAL_ADD_RID        : thm := CiT.REAL_ADD_RID
def REAL_NEG_0          : thm := CiT.REAL_NEG_0
def REAL_LE_LNEG        : thm := CiT.REAL_LE_LNEG
def REAL_LE_NEG2        : thm := CiT.REAL_LE_NEG2
def REAL_LE_RNEG        : thm := CiT.REAL_LE_RNEG
def REAL_OF_NUM_POW     : thm := CiT.REAL_OF_NUM_POW
def REAL_POW_NEG        : thm := CiT.REAL_POW_NEG
def REAL_ABS_NUM        : thm := CiT.REAL_ABS_NUM
def REAL_ABS_NEG        : thm := CiT.REAL_ABS_NEG


end Session
