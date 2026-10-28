/- File: SessionMath/Int.lean
int.ml (hol_lib.ml 98), the integers embedded in the reals, each layer built
by `initialize` when this module is imported, in int.ml order.  As in HOL
Light, `int` is the default type for overloaded symbols from int.ml 61's
`overload_interface` (which puts the int operations first; int.ml defines
`prioritize_int` at 70 but does not call it) until the file's last
statement, `prioritize_num` (int.ml 2765), which restores `num`.  The two
reduction nets INT_RED_CONV (int.ml 1821) and INT_COMPUTE_CONV (int.ml 1835)
are built from untyped patterns, so they are built while int priority is
current.

The bundles of theorems are `initialize` constants.  The conversions
(`INT_OF_REAL_THM`, `INT_RED_CONV`, `INT_COMPUTE_CONV`, ...) are closures, so
they are kept in `IO.Ref`s filled in file order (an `initialize` must not have a
function type; see `WfQqconvBox`, SessionMath/Wf.lean).
`IntRingConvs` and `IntDivisibility` get `deriving instance Inhabited` here,
which an `initialize` constant needs.
-/
import SessionMath.CalcRat
import HolMath.Int

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic

namespace Session

private def ioOk' {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")

private def pt (s : String) : IO term := ioOk' s!"parse {s}" (HolCore.Parser.parse_term s)


/- `IntRingConvs`/`IntDivisibility` carry function-typed fields and are NOT
   declared `Inhabited` in the pure library, but an `initialize` constant needs
   it.  Every field is a `thm` or a function into `IO`, so Lean derives these
   (exactly the two Session adds). -/
deriving instance Inhabited for HolMath.Int.IntRingConvs
deriving instance Inhabited for HolMath.Int.IntDivisibility

/- ---------------------------------------------------------------------- -/
/- int.ml (hol_lib.ml 98): the integers, embedded in the reals.           -/
/-                                                                        -/
/- Wired in int.ml's own order, with `int` the default for overloaded     -/
/- symbols from int.ml 61 to 2765.  Each                                   -/
/- structural stage is an `initialize` constant.  `REAL_ARITH` throughout   -/
/- means calc_rat.ml's FINAL `REAL_ARITH3` (int.ml sits at hol_lib.ml 98,   -/
/- above calc_rat.ml 97): `REAL_ARITH_TAC` here is `CONV_TAC REAL_ARITH3`.  -/
/- ---------------------------------------------------------------------- -/

/-- `integer` (int.ml 20): `integer(x) <=> ?n. abs x = &n`.  `new_definition`
    CREATES the `integer` constant.  int.ml sits above calc_rat.ml, so the
    real/calc_rat layers (forced already, this module imports Real) make
    `abs x = &n` parse at `:real`. -/
initialize integerLayer : thm ←
  ioOk' "setupInteger" (HolMath.Int.setupInteger new_definition).run

def integerDef : thm := integerLayer

/-- `IntExistence` (int.ml 23-34): `is_int` and the `?x. integer x` existence
    theorem fed to `new_type_definition`.  Uses the FINAL `REAL_ARITH3`. -/
initialize intExistenceLayer : HolMath.Int.IntExistence ←
  ioOk' "setupIntExistence" (HolMath.Int.setupIntExistence Rl integerDef REAL_ARITH3).run

def IntEx : HolMath.Int.IntExistence := intExistenceLayer

/-- The `int` type (int.ml 31): `new_type_definition "int" "int_of_real"
    "real_of_int"` from the `?x. integer x` theorem CREATES the type `int` and
    the maps `int_of_real`/`real_of_int`, then `setupIntTybij` derives the
    bijection family. -/
initialize intTybijLayer : HolMath.Int.IntTybij ← do
  let int_tybij ← ioOk' "int_tybij"
    (new_type_definition "int" "int_of_real" "real_of_int" IntEx.int_exists)
  ioOk' "setupIntTybij" (HolMath.Int.setupIntTybij IntEx.is_int int_tybij MESON_TAC).run

def IntTb : HolMath.Int.IntTybij := intTybijLayer

/-- The int interface map (int.ml 61-68): thirteen `overload_interface` calls
    putting `+ - * < <= > >= -- pow abs max min &` onto `int`, first in the
    interface, so every int stage below parses `+`/`*`/`<`/... at `:int`.
    Global parser side effects only.  The `int` type must exist first;
    `intTybijLayer` above created it. -/
initialize intInterfaceLayer : Unit ←
  ioOk' "setupIntInterface"
    (HolMath.Int.setupIntInterface overload_interface).run

/-- `IntOps` (int.ml 76-257): the fourteen operation definitions, their ten
    `_th` bridge theorems, `REAL_OF_INT_CLAUSES` and the six convenient
    theorems.  Forced after the interface so `x + y`/`x < y`/... parse at
    `:int`. -/
initialize intOpsLayer : HolMath.Int.IntOps ← do
  let _ := intInterfaceLayer
  ioOk' "setupIntOps" (HolMath.Int.setupIntOps Nm Rl CiT RT1 RT2 RT3 RT10
    arith1 arith2 arith3 arith4 CnA
    IntTb.int_rep IntTb.int_abstr IntEx.is_int IntTb.dest_int_rep
    IntTb.int_eq MESON_TAC REWRITE_CONV REAL_ARITH3 new_definition).run

def IntO : HolMath.Int.IntOps := intOpsLayer

/-- `IntConstSyntax` (int.ml 279-281): the `int_of_num`/`int_neg` term
    constants `mk_intconst` builds `&n`/`--(&n)` from.  `IntO` above made them
    exist. -/
initialize intConstSyntaxLayer : HolMath.Int.IntConstSyntax ← do
  let _ := intOpsLayer
  ioOk' "setupIntConstSyntax" (HolMath.Int.setupIntConstSyntax mk_numeral).run

def IntKs : HolMath.Int.IntConstSyntax := intConstSyntaxLayer

/-- `INT_OF_REAL_THM` (int.ml 290): the lifting rule the int bundles build on,
    a `thm -> IO (Except String thm)` CLOSURE.  Session caches it (building it
    proves the inline `cond_th` lemma once); the closure lives in a plain
    `Option` ref seeded by the forcing block, as it does not survive `dlopen`
    as a function-typed `initialize` constant. -/
initialize theIntOfRealThm : IO.Ref (Option (thm → IO (Except String thm))) ← IO.mkRef none

initialize intOfRealThmLayer : Unit ← do
  match ← (HolMath.Int.setupIntOfRealThm IntTb.int_eq IntO).run with
  | .ok f => theIntOfRealThm.set (some f)
  | .error e => throw (IO.userError s!"setupIntOfRealThm: {e}")

def INT_OF_REAL_THM : thm → IO (Except String thm) := fun th => do
  match ← theIntOfRealThm.get with
  | some f => f th
  | none => return .error "INT_OF_REAL_THM not initialized"

/- The 276 lifts, in ten bundles (int.ml 322-598).  Each `setupIntThmsN` maps
   `INT_OF_REAL_THM` over a slice of the `REAL_` theorems. -/

initialize intThms1Layer : HolMath.Int.IntThms1 ←
  ioOk' "setupIntThms1" (HolMath.Int.setupIntThms1 INT_OF_REAL_THM
    REAL_ABS_0 REAL_ABS_1 REAL_ABS_ABS REAL_ABS_BETWEEN
    REAL_ABS_BETWEEN1 REAL_ABS_BETWEEN2 REAL_ABS_BOUND
    REAL_ABS_BOUNDS REAL_ABS_CASES REAL_ABS_CIRCLE REAL_ABS_LE
    REAL_ABS_MUL REAL_ABS_NEG REAL_ABS_NUM REAL_ABS_NZ REAL_ABS_POS
    REAL_ABS_POW REAL_ABS_REFL REAL_ABS_SGN REAL_ABS_SIGN
    REAL_ABS_SIGN2 REAL_ABS_STILLNZ REAL_ABS_SUB REAL_ABS_SUB_ABS
    REAL_ABS_TRIANGLE REAL_ABS_ZERO REAL_ADD2_SUB2 REAL_ADD_AC).run
def IT1 : HolMath.Int.IntThms1 := intThms1Layer

initialize intThms2Layer : HolMath.Int.IntThms2 ←
  ioOk' "setupIntThms2" (HolMath.Int.setupIntThms2 INT_OF_REAL_THM
    REAL_ADD_ASSOC REAL_ADD_LDISTRIB REAL_ADD_LID REAL_ADD_LINV
    REAL_ADD_RDISTRIB REAL_ADD_RID REAL_ADD_RINV REAL_ADD_SUB
    REAL_ADD_SUB2 REAL_ADD_SYM REAL_BOUNDS_LE REAL_BOUNDS_LT
    REAL_DIFFSQ REAL_ENTIRE REAL_EQ_ADD_LCANCEL
    REAL_EQ_ADD_LCANCEL_0 REAL_EQ_ADD_RCANCEL REAL_EQ_ADD_RCANCEL_0
    REAL_EQ_IMP_LE REAL_EQ_LCANCEL_IMP REAL_EQ_MUL_LCANCEL
    REAL_EQ_MUL_RCANCEL REAL_EQ_NEG2 REAL_EQ_RCANCEL_IMP
    REAL_EQ_SGN_ABS REAL_EQ_SQUARE_ABS REAL_EQ_SUB_LADD
    REAL_EQ_SUB_RADD).run
def IT2 : HolMath.Int.IntThms2 := intThms2Layer

initialize intThms3Layer : HolMath.Int.IntThms3 ←
  ioOk' "setupIntThms3" (HolMath.Int.setupIntThms3 INT_OF_REAL_THM
    REAL_EVENPOW_ABS REAL_LET_ADD REAL_LET_ADD2 REAL_LET_ANTISYM
    REAL_LET_TOTAL REAL_LET_TRANS REAL_LE_01 REAL_LE_ADD
    REAL_LE_ADD2 REAL_LE_ADDL REAL_LE_ADDR REAL_LE_ANTISYM
    REAL_LE_DOUBLE REAL_LE_LADD REAL_LE_LADD_IMP REAL_LE_LCANCEL_IMP
    REAL_LE_LMUL REAL_LE_LMUL_EQ REAL_LE_LNEG REAL_LE_LT REAL_LE_MAX
    REAL_LE_MIN REAL_LE_MUL REAL_LE_MUL2 REAL_LE_MUL_EQ REAL_LE_NEG2
    REAL_LE_NEGL REAL_LE_NEGR).run
def IT3 : HolMath.Int.IntThms3 := intThms3Layer

initialize intThms4Layer : HolMath.Int.IntThms4 ←
  ioOk' "setupIntThms4" (HolMath.Int.setupIntThms4 INT_OF_REAL_THM
    REAL_LE_NEGTOTAL REAL_LE_POW2 REAL_LE_POW_2 REAL_LE_RADD
    REAL_LE_RCANCEL_IMP REAL_LE_REFL REAL_LE_RMUL REAL_LE_RMUL_EQ
    REAL_LE_RNEG REAL_LE_SQUARE REAL_LE_SQUARE_ABS REAL_LE_SUB_LADD
    REAL_LE_SUB_RADD REAL_LE_TOTAL REAL_LE_TRANS REAL_LNEG_UNIQ
    REAL_LTE_ADD REAL_LTE_ADD2 REAL_LTE_ANTISYM REAL_LTE_TOTAL
    REAL_LTE_TRANS REAL_LT_01 REAL_LT_ADD REAL_LT_ADD1 REAL_LT_ADD2
    REAL_LT_ADDL REAL_LT_ADDNEG REAL_LT_ADDNEG2).run
def IT4 : HolMath.Int.IntThms4 := intThms4Layer

initialize intThms5Layer : HolMath.Int.IntThms5 ←
  ioOk' "setupIntThms5" (HolMath.Int.setupIntThms5 INT_OF_REAL_THM
    REAL_LT_ADDR REAL_LT_ADD_SUB REAL_LT_ANTISYM REAL_LT_GT
    REAL_LT_IMP_LE REAL_LT_IMP_NE REAL_LT_LADD REAL_LT_LADD_IMP
    REAL_LT_LCANCEL_IMP REAL_LT_LE REAL_LT_LMUL REAL_LT_LMUL_EQ
    REAL_LT_LNEG REAL_LT_MAX REAL_LT_MIN REAL_LT_MUL REAL_LT_MUL2
    REAL_LT_MUL_EQ REAL_LT_NEG2 REAL_LT_NEGTOTAL REAL_LT_POW2
    REAL_LT_POW_2 REAL_LT_RADD REAL_LT_RCANCEL_IMP REAL_LT_REFL
    REAL_LT_RMUL REAL_LT_RMUL_EQ REAL_LT_RNEG).run
def IT5 : HolMath.Int.IntThms5 := intThms5Layer

initialize intThms6Layer : HolMath.Int.IntThms6 ←
  ioOk' "setupIntThms6" (HolMath.Int.setupIntThms6 INT_OF_REAL_THM
    REAL_LT_SQUARE REAL_LT_SQUARE_ABS REAL_LT_SUB_LADD
    REAL_LT_SUB_RADD REAL_LT_TOTAL REAL_LT_TRANS REAL_MAX_ACI
    REAL_MAX_ASSOC REAL_MAX_LE REAL_MAX_LT REAL_MAX_MAX REAL_MAX_MIN
    REAL_MAX_SYM REAL_MIN_ACI REAL_MIN_ASSOC REAL_MIN_LE REAL_MIN_LT
    REAL_MIN_MAX REAL_MIN_MIN REAL_MIN_SYM REAL_MUL_2 REAL_MUL_AC
    REAL_MUL_ASSOC REAL_MUL_LID REAL_MUL_LNEG REAL_MUL_LZERO
    REAL_MUL_POS_LE REAL_MUL_POS_LT).run
def IT6 : HolMath.Int.IntThms6 := intThms6Layer

initialize intThms7Layer : HolMath.Int.IntThms7 ←
  ioOk' "setupIntThms7" (HolMath.Int.setupIntThms7 INT_OF_REAL_THM
    REAL_MUL_RID REAL_MUL_RNEG REAL_MUL_RZERO REAL_MUL_SYM
    REAL_NEG_0 REAL_NEG_ADD REAL_NEG_EQ REAL_NEG_EQ_0 REAL_NEG_GE0
    REAL_NEG_GT0 REAL_NEG_LE0 REAL_NEG_LMUL REAL_NEG_LT0
    REAL_NEG_MINUS1 REAL_NEG_MUL2 REAL_NEG_NEG REAL_NEG_RMUL
    REAL_NEG_SUB REAL_NOT_EQ REAL_NOT_LE REAL_NOT_LT REAL_OF_NUM_ADD
    REAL_OF_NUM_CLAUSES REAL_OF_NUM_EQ REAL_OF_NUM_GE REAL_OF_NUM_GT
    REAL_OF_NUM_LE REAL_OF_NUM_LT).run
def IT7 : HolMath.Int.IntThms7 := intThms7Layer

initialize intThms8Layer : HolMath.Int.IntThms8 ←
  ioOk' "setupIntThms8" (HolMath.Int.setupIntThms8 INT_OF_REAL_THM
    REAL_OF_NUM_MAX REAL_OF_NUM_MIN REAL_OF_NUM_MOD REAL_OF_NUM_MUL
    REAL_OF_NUM_POW REAL_OF_NUM_SUB REAL_OF_NUM_SUB_CASES
    REAL_OF_NUM_SUC REAL_POS REAL_POS_EQ_SQUARE REAL_LT_IMP_NZ
    REAL_POW2_ABS REAL_POW_1 REAL_POW_1_LE REAL_POW_1_LT REAL_POW_2
    REAL_POW_ADD REAL_POW_EQ REAL_POW_EQ_0 REAL_POW_EQ_1
    REAL_POW_EQ_1_IMP REAL_POW_EQ_ABS REAL_POW_EQ_EQ REAL_POW_EQ_ODD
    REAL_POW_EQ_ODD_EQ REAL_POW_LBOUND REAL_POW_LE REAL_POW_LE2).run
def IT8 : HolMath.Int.IntThms8 := intThms8Layer

initialize intThms9Layer : HolMath.Int.IntThms9 ←
  ioOk' "setupIntThms9" (HolMath.Int.setupIntThms9 INT_OF_REAL_THM
    REAL_POW_LE2_ODD REAL_POW_LE2_ODD_EQ REAL_POW_LE2_REV
    REAL_POW_LE_1 REAL_POW_LT REAL_POW_LT2 REAL_POW_LT2_ODD
    REAL_POW_LT2_ODD_EQ REAL_POW_LT2_REV REAL_POW_LT_1 REAL_POW_MONO
    REAL_POW_MONO_LT REAL_POW_MUL REAL_POW_NEG REAL_POW_NZ
    REAL_POW_ONE REAL_POW_POW REAL_POW_ZERO REAL_RNEG_UNIQ real_sgn
    REAL_SGNS_EQ REAL_SGNS_EQ_ALT REAL_SGN_0 REAL_SGN_ABS
    REAL_SGN_ABS_ALT REAL_SGN_CASES).run
def IT9 : HolMath.Int.IntThms9 := intThms9Layer

initialize intThms10Layer : HolMath.Int.IntThms10 ←
  ioOk' "setupIntThms10" (HolMath.Int.setupIntThms10 INT_OF_REAL_THM
    REAL_SGN_EQ REAL_SGN_EQ_INEQ REAL_SGN_INEQS REAL_SGN_REAL_SGN
    REAL_SGN_MUL REAL_SGN_NEG REAL_SGN_POW REAL_SGN_POW_2
    REAL_SOS_EQ_0 REAL_SUB_0 REAL_SUB_ABS REAL_SUB_ADD REAL_SUB_ADD2
    REAL_SUB_LDISTRIB REAL_SUB_LE REAL_SUB_LNEG REAL_SUB_LT
    REAL_SUB_LZERO REAL_SUB_NEG2 REAL_SUB_RDISTRIB REAL_SUB_REFL
    REAL_SUB_RNEG REAL_SUB_RZERO REAL_SUB_SUB REAL_SUB_SUB2
    REAL_SUB_TRIANGLE).run
def IT10 : HolMath.Int.IntThms10 := intThms10Layer

/-- `IntWlog` (int.ml 603-616): the three integer WLOG theorems. -/
initialize intWlogLayer : HolMath.Int.IntWlog ←
  ioOk' "setupIntWlog" (HolMath.Int.setupIntWlog IT4.INT_LE_TOTAL IT6.INT_LT_TOTAL MESON_TAC).run
def IWl : HolMath.Int.IntWlog := intWlogLayer

/-- `IntArith1` (int.ml 619-709): image theorems, pseudo-definitions and the
    BOOTSTRAPPING integer decision procedure `INT_ARITH1`/`INT_ARITH_TAC1`/
    `ASM_INT_ARITH_TAC1` (the FIRST of two `INT_ARITH`s). -/
initialize intArith1Layer : HolMath.Int.IntArith1 ←
  ioOk' "setupIntArith1" (HolMath.Int.setupIntArith1 nnfPths IntO IntTb.int_eq
    INT_OF_REAL_THM Rl arith2
    IT2.INT_ADD_LID IT4.INT_LE_RNEG
    IT7.INT_OF_NUM_LE IT7.INT_NEG_0 IT7.INT_NOT_LE IT7.INT_NOT_LT
    IT7.INT_NOT_EQ IT1.INT_ABS_POS IT1.INT_ABS_REFL
    PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV REAL_ARITH3
    MESON_TAC).run
def IA1 : HolMath.Int.IntArith1 := intArith1Layer

/-- The `div`/`rem` infixes (int.ml 712): `parse_as_infix` for both.  Global
    parser side effects; forced here so `setupIntDivMod`'s `div`/`rem` terms
    parse as infixes. -/
initialize intDivRemInfixesLayer : Unit ← HolMath.Int.setupIntDivRemInfixes

/-- `IntDivMod` (int.ml 714-866): `INT_SUB`/`INT_MAX`/`INT_MIN`, the Euclidean
    division/remainder specification `INT_DIVISION` and its family.  Uses
    `new_specification`, which CREATES the `div`/`rem` constants (the infixes
    above come first). -/
initialize intDivModLayer : HolMath.Int.IntDivMod ← do
  let _ := intDivRemInfixesLayer
  ioOk' "setupIntDivMod" (HolMath.Int.setupIntDivMod IA1 IntO
    IT8.INT_POS IT8.INT_OF_NUM_MUL
    IT4.INT_LE_TRANS IT4.INT_LE_REFL IT4.INT_LE_TOTAL
    IT6.INT_MUL_LNEG
    IT7.INT_MUL_RNEG IT7.INT_NEG_NEG IT7.INT_OF_NUM_EQ IT7.INT_NEG_EQ
    IT7.INT_OF_NUM_LE
    IT1.INT_ABS_POS IT1.INT_ABS_MUL
    IT2.INT_ADD_LID
    IT3.INT_LE_LMUL IT3.INT_LET_TRANS
    IT5.INT_LT_REFL
    MULT_EQ_1 LE_REFL NOT_LE num_WOP
    new_specification MESON MESON_TAC ASM_MESON_TAC).run
def IDm : HolMath.Int.IntDivMod := intDivModLayer

/-- `IntCompareConvs` (int.ml 871-940): the five relational numeral conversions
    `INT_LE_CONV`/`INT_LT_CONV`/`INT_GE_CONV`/`INT_GT_CONV`/`INT_EQ_CONV`. -/
initialize intCompareConvsLayer : HolMath.Int.IntCompareConvs ←
  ioOk' "setupIntCompareConvs" (HolMath.Int.setupIntCompareConvs
    NUM_EQ_CONV NUM_LE_CONV NUM_LT_CONV IA1
    IT3.INT_LE_NEG2 IT3.INT_LE_LNEG IT4.INT_LE_RNEG
    IT7.INT_OF_NUM_ADD IT7.INT_OF_NUM_LE IT3.INT_LE_ANTISYM
    LE LE_0 ADD_EQ_0 NOT_LE LE_ANTISYM).run
def ICv : HolMath.Int.IntCompareConvs := intCompareConvsLayer

/-- `IntArithConvs` (int.ml 941-1084): the nine arithmetic numeral conversions.
    `NUM_EVEN_CONV` is already a plain `ioconv` here. -/
initialize intArithConvsLayer : HolMath.Int.IntArithConvs ← do
  let evenC : ioconv := NUM_EVEN_CONV
  ioOk' "setupIntArithConvs" (HolMath.Int.setupIntArithConvs ICv
    NUM_MULT_CONV NUM_ADD_CONV NUM_EXP_CONV evenC mk_numeral
    IT7.INT_NEG_NEG IT7.INT_NEG_0
    IT6.INT_MUL_LZERO IT7.INT_MUL_RZERO IT6.INT_MUL_LNEG
    IT7.INT_MUL_RNEG
    IT2.INT_ADD_LINV IT2.INT_ADD_RINV IT7.INT_NEG_ADD IT2.INT_ADD_LID
    IT2.INT_ADD_ASSOC IT2.INT_ADD_SYM
    IT8.INT_OF_NUM_MUL IT7.INT_OF_NUM_ADD IT8.INT_OF_NUM_POW
    IT9.INT_POW_NEG
    IT1.INT_ABS_NEG IT1.INT_ABS_NUM
    IDm.INT_SUB IDm.INT_MAX IDm.INT_MIN IT9.INT_SGN).run
def IAv : HolMath.Int.IntArithConvs := intArithConvsLayer

/-- `IntPolyConvs` (int.ml 1091-1120): `INT_POLY_CONV`, the canonical
    polynomial normalizer for the integers. -/
initialize intPolyConvsLayer : HolMath.Int.IntPolyConvs ←
  ioOk' "setupIntPolyConvs" (HolMath.Int.setupIntPolyConvs IA1 IAv
    TRUTH NmzP.2 num_CONV
    NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV).run
def IPc : HolMath.Int.IntPolyConvs := intPolyConvsLayer

/-- `IntRingConvs` (int.ml 1122-1147): `INT_RING`, `int_ideal_cofactors` and
    `INT_INTEGRAL`. -/
initialize intRingConvsLayer : HolMath.Int.IntRingConvs ←
  ioOk' "setupIntRing" (HolMath.Int.setupIntRing IntKs ICv IA1 IPc Nm.numK
    MULT_CLAUSES EQ_ADD_LCANCEL
    IT7.INT_OF_NUM_EQ IT7.INT_OF_NUM_ADD IT8.INT_OF_NUM_MUL
    IT10.INT_SUB_0 IT2.INT_ENTIRE
    PRESIMP_CONV CONDS_ELIM_CONV NNF_CONV WEAK_DNF_CONV
    T.AND_FORALL_THM T.LEFT_AND_FORALL_THM T.RIGHT_AND_FORALL_THM
    C.LEFT_OR_FORALL_THM C.RIGHT_OR_FORALL_THM T.OR_EXISTS_THM
    T.LEFT_OR_EXISTS_THM T.RIGHT_OR_EXISTS_THM T.LEFT_AND_EXISTS_THM
    T.RIGHT_AND_EXISTS_THM
    GrG TRUTH).run
def IRg : HolMath.Int.IntRingConvs := intRingConvsLayer

/-- The divisibility/congruence/coprimality block (int.ml 1148-1223).  Threads
    `make_overloadable`/`parse_as_infix`/`parse_as_prefix`/`overload_interface`/
    `new_definition` and runs them in int.ml's EXACT order (the three
    `overload_interface` calls PRECEDE the `new_definition` they refer to so
    `divides`/`mod`/`coprime` parse as CONSTANTS).  CREATES constants.
    `int_coprime`'s LHS `coprime(a,b)` is a PAIRED varstruct, which pair.ml's
    `new_definition` handles. -/
initialize intDivisibilityLayer : HolMath.Int.IntDivisibility ←
  ioOk' "setupIntDivisibility" (HolMath.Int.setupIntDivisibility IA1
    IT1.INT_ABS_MUL IT2.INT_ENTIRE IT3.INT_LE_MUL
    make_overloadable overload_interface parse_as_infix
    parse_as_prefix new_definition_pair).run
def IDv : HolMath.Int.IntDivisibility := intDivisibilityLayer

/-- `INTEGER_TAC1`/`INTEGER_RULE1` (int.ml 1224-1327), the FIRST of the two
    integer decision procedures.  Pure. -/
initialize intTac1Layer : HolMath.Int.IntTac1 ←
  ioOk' "setupIntTac1" (HolMath.Int.setupIntTac1 IA1 IPc IRg IDv
    IT10.INT_SUB_0 IT2.INT_ENTIRE MESON).run
def ITc1 : HolMath.Int.IntTac1 := intTac1Layer

/-- `IntDivRem1` (int.ml 1329-1763): the 47 further div/rem/congruence proofs. -/
initialize intDivRem1Layer : HolMath.Int.IntDivRem1 ←
  ioOk' "setupIntDivRem1" (HolMath.Int.setupIntDivRem1 Nm IntO IA1 IDm IRg IDv ITc1
    IT1 IT2 IT3 IT4 IT5 IT6 IT7 IT8 IT9 IT10
    arith7.DIVISION arith7.DIV_ZERO arith7.MOD_ZERO arith8.MOD_LE arith3.LE_1
    arith7.RDIV_LT_EQ MESON_TAC ASM_MESON_TAC).run
def IDr1 : HolMath.Int.IntDivRem1 := intDivRem1Layer

/-- `IntDivRemConvs` (int.ml 1772-1801): `INT_DIV_CONV`/`INT_REM_CONV`, the
    numeral div/rem evaluators cut from the shared `INT_DIVMOD_CONV`. -/
initialize intDivRemConvsLayer : HolMath.Int.IntDivRemConvs ←
  ioOk' "setupIntDivRemConvs" (HolMath.Int.setupIntDivRemConvs IntKs ICv IAv IDr1 MESON_TAC).run
def IDrc : HolMath.Int.IntDivRemConvs := intDivRemConvsLayer

/- ---------------------------------------------------------------------- -/
/- The two reduction nets, built WHILE `int` priority is in force (int.ml  -/
/- 1803/1821/1835).  They are built here, before `prioritize_num` (int.ml   -/
/- 2765); `int_red_conv_list`'s sixteen                                     -/
/- patterns are all UNANNOTATED (`x + y`, `x <= y`, `x pow n`, ...) except  -/
/- `x:int = y`, so their types come from the ambient `int` priority.  They  -/
/- hold closures, so they live in plain `Option` refs seeded here, and the  -/
/- public `INT_RED_CONV`/`INT_COMPUTE_CONV` read them back.                 -/
/- ---------------------------------------------------------------------- -/

initialize theIntRedConvList : IO.Ref (Option (List (term × ioconv))) ← IO.mkRef none
initialize theIntRed : IO.Ref (Option ioconv) ← IO.mkRef none
initialize theIntCompute : IO.Ref (Option ioconv) ← IO.mkRef none

/-- `int_red_conv_list` (int.ml 1803): a top-level value in OCaml, its sixteen
    patterns parsed once while `int` is the default for overloaded symbols. -/
initialize intRedConvListLayer : Unit ← do
  match ← (HolMath.Int.int_red_conv_list ICv IAv IDrc).run with
  | .ok l => theIntRedConvList.set (some l)
  | .error e => throw (IO.userError s!"int_red_conv_list: {e}")

def int_red_conv_list : IO (Except String (List (term × ioconv))) := do
  match ← theIntRedConvList.get with
  | some l => return .ok l
  | none => return .error "int_red_conv_list not initialized"

/-- `INT_RED_CONV` (int.ml 1821): one reduction step on an integer-constant
    term, via the sixteen-entry net over `basic_net()` (snapshotted here, under
    int priority). -/
initialize intRedLayer : Unit ← do
  match ← (do HolMath.Int.INT_RED_CONV (← ExceptT.mk int_red_conv_list)).run with
  | .ok c => theIntRed.set (some c)
  | .error e => throw (IO.userError s!"INT_RED_CONV net (int.ml 1821): {e}")

def INT_RED_CONV : ioconv := fun tm => do
  match ← theIntRed.get with
  | some c => c tm
  | none => return .error "INT_RED_CONV not initialized"

/-- `INT_REDUCE_CONV` (int.ml 1826): `DEPTH_CONV INT_RED_CONV`. -/
def INT_REDUCE_CONV : ioconv := Simp.depthConvIO INT_RED_CONV

/-- `int_compute_add_convs` (int.ml 1828): register the sixteen conversions with
    a `compset`. -/
def int_compute_add_convs (cs : HolMath.Compute.compset) : IO (Except String Unit) :=
  (do HolMath.Int.int_compute_add_convs (← ExceptT.mk int_red_conv_list) cs).run

private def intComputeConvIO : ExceptT String IO ioconv := do
  let l ← ExceptT.mk int_red_conv_list
  HolMath.Int.INT_COMPUTE_CONV l bool_compset WEAK_CBV_CONV

/-- `INT_COMPUTE_CONV` (int.ml 1835): call-by-value reduction over the boolean
    compset extended with those conversions (built here, under int priority). -/
initialize intComputeLayer : Unit ← do
  match ← intComputeConvIO.run with
  | .ok c => theIntCompute.set (some c)
  | .error e => throw (IO.userError s!"INT_COMPUTE_CONV net (int.ml 1835): {e}")

def INT_COMPUTE_CONV : ioconv := fun tm => do
  match ← theIntCompute.get with
  | some c => c tm
  | none => return .error "INT_COMPUTE_CONV not initialized"

/-- `IntEvenOdd` (int.ml 1844-1877): the four `&2 divides` combining theorems.
    Uses `INT_REDUCE_CONV` (the net above). -/
initialize intEvenOddLayer : HolMath.Int.IntEvenOdd ←
  ioOk' "setupIntEvenOdd" (HolMath.Int.setupIntEvenOdd Nm INT_REDUCE_CONV
    IDr1 IA1.INT_POW Nm.NOT_SUC).run
def IEo : HolMath.Int.IntEvenOdd := intEvenOddLayer

/-- `IntRemConvs` (int.ml 1880-1928): `INT_REM_DOWN_CONV` and `INT_POW_REM_CONV`. -/
initialize intRemConvsLayer : HolMath.Int.IntRemConvs ←
  ioOk' "setupIntRemConvs" (HolMath.Int.setupIntRemConvs IDr1 IDrc IAv
    IT9.INT_POW_NEG IT7.INT_OF_NUM_CLAUSES C.COND_CLAUSES
    numEvenConvIO EXP_MOD_CONV).run
def IRc : HolMath.Int.IntRemConvs := intRemConvsLayer

/-- `IntGcdLcm` (int.ml 1929-2067): the two well-founded integer measures, the
    Bezout existence theorems, the `int_gcd`/`int_lcm` constants and the SECOND
    `INTEGER_TAC`/`INTEGER_RULE`.  CREATES `int_gcd`/`int_lcm`, two
    `overload_interface` calls.  Registers the `int` `gcd`/`lcm` overloads, so
    it MUST precede `INoN`. -/
initialize intGcdLcmLayer : HolMath.Int.IntGcdLcm ←
  ioOk' "setupIntGcdLcm" (HolMath.Int.setupIntGcdLcm
    Pr.FORALL_PAIR_THM Pr.FORALL_UNCURRY IA1 ITc1 IDr1
    num_WF IT7.INT_OF_NUM_LT IA1.INT_FORALL_POS
    IT6.INT_MUL_LZERO IT2.INT_ADD_LID IT2.INT_ADD_RID IT7.INT_MUL_RID
    IT4.INT_LE_NEGTOTAL
    IA1.INT_ABS IT8.INT_POS IT1.INT_ABS_POS IT1.INT_ABS_NUM
    IT1.INT_ABS_ZERO
    IT7.INT_MUL_RZERO IT7.INT_MUL_SYM
    Pr.EXISTS_UNCURRY C.SKOLEM_THM
    MESON_TAC ASM_MESON_TAC
    overload_interface new_specification new_definition_pair).run
def IGl : HolMath.Int.IntGcdLcm := intGcdLcmLayer

/-- `IntNumOfInt` (int.ml 2070-2104): the map from a nonnegative integer to the
    natural it names.  `new_definition` CREATES `num_of_int`. -/
initialize intNumOfIntLayer : HolMath.Int.IntNumOfInt ←
  ioOk' "setupIntNumOfInt" (HolMath.Int.setupIntNumOfInt
    IT7.INT_OF_NUM_EQ IT7.INT_OF_NUM_ADD IT8.INT_OF_NUM_MUL
    IT8.INT_OF_NUM_POW IA1.INT_FORALL_POS IT8.INT_POS
    T.RIGHT_FORALL_IMP_THM T.IMP_CONJ T.SWAP_FORALL_THM
    SELECT_CONV MESON_TAC new_definition).run
def INoI : HolMath.Int.IntNumOfInt := intNumOfIntLayer

/-- `IntNumNotions` (int.ml 2107-2149): the natural-number divisibility notions
    and `NUM_TO_INT_CONV`.  FIVE `overload_interface` calls (for `num`) precede
    six definitions.  `num_of_int` (from `INoI`, forced above) must exist when
    `num_gcd`/`num_lcm` are parsed.  `num_coprime`/`num_gcd`/`num_lcm` have
    PAIRED left-hand sides, handled by pair.ml's `new_definition`. -/
initialize intNumNotionsLayer : HolMath.Int.IntNumNotions ←
  ioOk' "setupIntNumNotions" (HolMath.Int.setupIntNumNotions IDv.cong
    IA1.INT_EXISTS_POS IA1.INT_FORALL_POS
    IT7.INT_OF_NUM_EQ IT7.INT_OF_NUM_LE IT7.INT_OF_NUM_LT
    IT7.INT_OF_NUM_GE IT7.INT_OF_NUM_GT IT8.INT_OF_NUM_SUC
    IT7.INT_OF_NUM_ADD IT8.INT_OF_NUM_MUL IT8.INT_OF_NUM_POW
    NUM_SIMPLIFY_CONV MESON_TAC
    overload_interface new_definition_pair).run
def INoN : HolMath.Int.IntNumNotions := intNumNotionsLayer

/-- `IntArithRule` (int.ml 2153-2189): `ARITH_RULE`/`ARITH_TAC`/`ASM_ARITH_TAC`,
    the linear decision procedure for the naturals, delegating to
    `IA1.INT_ARITH1`.  Built, as in HOL Light, while `int` is still the
    default for overloaded symbols (int.ml 61; `prioritize_num` is at 2765). -/
initialize intArithRuleLayer : HolMath.Int.IntArithRule ← do
  ioOk' "setupIntArithRule" (HolMath.Int.setupIntArithRule IA1.INT_ARITH1 IT8.INT_POS
    IT7.INT_OF_NUM_EQ IT7.INT_OF_NUM_LE IT7.INT_OF_NUM_LT
    IT7.INT_OF_NUM_GE IT7.INT_OF_NUM_GT IT7.INT_OF_NUM_ADD
    IT8.INT_OF_NUM_MUL IT8.INT_OF_NUM_MAX IT8.INT_OF_NUM_MIN
    arith1.ADD1 NUM_SIMPLIFY_CONV NUM_NORMALIZE_CONV PRENEX_CONV).run
def IAr : HolMath.Int.IntArithRule := intArithRuleLayer

/-- `IntArith2` (int.ml 2192-2323): the ENHANCED integer decision procedure
    `INT_ARITH2`/`INT_ARITH_TAC2`/`ASM_INT_ARITH_TAC2`, which additionally
    eliminates `div`/`rem` and SUPERSEDES `INT_ARITH1`.  Built afresh (`IA1`'s
    `INT_ARITH1` is not called). -/
initialize intArith2Layer : HolMath.Int.IntArith2 ← do
  ioOk' "setupIntArith2" (HolMath.Int.setupIntArith2 nnfPths IA1 IntO IntTb.int_eq
    IT7.INT_NOT_LE IT7.INT_NOT_LT IT7.INT_NOT_EQ
    IT8.INT_POS IT3.INT_LE_ADD IT3.INT_LE_MUL IT8.INT_POW_LE
    IT1.INT_ABS_NUM IT3.INT_LET_ANTISYM IDm.INT_DIV_0 IDm.INT_REM_0
    IDm.INT_DIVISION IDr1.INT_LE_DIV IDr1.INT_DIVMOD_UNIQ
    PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV INT_REDUCE_CONV
    REAL_ARITH3 ASM_METIS_TAC).run
def IA2 : HolMath.Int.IntArith2 := intArith2Layer

/-- `IntMiscNat` (int.ml 2326-2375): four miscellaneous `num` lemmas;
    `INT_REM_REM_POW_MIN`'s `ASM_INT_ARITH_TAC` is the ENHANCED
    `ASM_INT_ARITH_TAC2`, so this forces `IA2` first. -/
initialize intMiscNatLayer : HolMath.Int.IntMiscNat ←
  ioOk' "setupIntMiscNat" (HolMath.Int.setupIntMiscNat IAr IA2
    arith4.num_WF arith2.LE_0 arith4.LE_EXISTS arith3.NOT_LE arith3.LT_IMP_LE
    IDr1.INT_REM_ZERO IT9.INT_POW_ZERO IDm.INT_REM_0 IDr1.INT_REM_1
    IT8.INT_POW_ADD IDr1.INT_REM_REM_MUL IDr1.INT_REM_REM_LE
    IT8.INT_POW_EQ_0 IT1.INT_ABS_POW IT9.INT_POW_MONO
    MESON_TAC ASM_MESON_TAC).run
def IMn : HolMath.Int.IntMiscNat := intMiscNatLayer

/-- `IntNumber` (int.ml 2378-2566): the `num` divisibility layer and
    `NUMBER_TAC` (int.ml 2503), the natural-number decision procedure that
    reduces a `num` goal to an integer one and hands off to the ENHANCED
    `INTEGER_TAC2` (`IGl.INTEGER_TAC2`). -/
initialize intNumberLayer : HolMath.Int.IntNumber ←
  ioOk' "setupIntNumber" (HolMath.Int.setupIntNumber IA1 IA2 IGl IAr INoN INoI
    IDv.int_divides
    IT7.INT_OF_NUM_EQ IT7.INT_OF_NUM_LE IT7.INT_OF_NUM_LT
    IT7.INT_OF_NUM_GE IT7.INT_OF_NUM_GT
    IT8.INT_OF_NUM_SUC IT7.INT_OF_NUM_ADD IT8.INT_OF_NUM_MUL
    IT8.INT_OF_NUM_POW IDr1.INT_OF_NUM_DIV
    IDr1.INT_REM_EQ IDr1.INT_OF_NUM_REM
    IT1.INT_ABS_POS IT1.INT_ABS_ABS IT1.INT_ABS_MUL IA1.INT_ABS
    IT3.INT_LE_LMUL IDr1.INT_MUL_DIV_EQ IDr1.INT_DIV_BY_DIV
    IDr1.INT_DIVIDES_DIV_DIVIDES IDr1.INT_DIVIDES_DIV_SELF
    IDr1.INT_DIVIDES_DIVIDES_DIV IDr1.INT_DIVIDES_DIVIDES_DIV_EQ
    arith8.DIV_MOD arith7.MOD_MOD_REFL arith7.MOD_EQ_0 arith7.DIV_ZERO
    arith8.DIV_MULT_ADD arith7.DIV_MULT arith7.DIV_0
    arith1.ADD_CLAUSES arith2.MULT_CLAUSES arith2.MULT_EQ_1 arith2.MULT_EQ_0
    arith4.LE_MULT_LCANCEL arith2.MULT_SYM arith2.MULT_ASSOC arith3.LE_1
    arith2.LE_0 arith3.LE_REFL
    NUM_RING MESON_TAC).run
def INum : HolMath.Int.IntNumber := intNumberLayer

/-- `IntPrime` (int.ml 2571-2630): the definition of `prime` and its five
    theorems.  `new_definition` CREATES the `prime` constant.  Runs over the
    `IntNumber` layer. -/
initialize intPrimeLayer : HolMath.Int.IntPrime ←
  ioOk' "setupIntPrime" (HolMath.Int.setupIntPrime INum
    arith2.MULT_EQ_0 arith2.MULT_EQ_1 arith2.MULT_CLAUSES
    arith4.LE_MULT_LCANCEL arith4.LE_MULT_RCANCEL
    new_definition IAr.ARITH_RULE ASM_MESON_TAC).run
def IPr : HolMath.Int.IntPrime := intPrimeLayer

/-- `RealZpow` (int.ml 2633-2761): `real_zpow` and its 22 theorems.  THREE
    parser side effects precede the definition (int.ml 2634-2636:
    `make_overloadable "zpow"`, `parse_as_infix("zpow",(24,"left"))`,
    `overload_interface "zpow" real_zpow`), threaded in with `new_definition`;
    `zpow` is a fresh symbol that does not disturb num/int priority.  Uses the
    ENHANCED `INT_ARITH2`. -/
initialize realZpowLayer : HolMath.Int.RealZpow ←
  ioOk' "setupRealZpow" (HolMath.Int.setupRealZpow
    IT8.INT_POS INoI.NUM_OF_INT_OF_NUM IntO.FORALL_INT_CASES
    arith4.WLOG_LE
    real_pow REAL_POW_1 REAL_POW_2 REAL_POW_ONE
    REAL_INV_1 REAL_INV_INV REAL_INV_0 REAL_INV_MUL REAL_INV_POW
    REAL_POW_ZERO REAL_POW_POW REAL_POW_MUL REAL_POW_ADD
    REAL_POW_EQ_0 REAL_POW_LE REAL_POW_LT
    REAL_LE_INV_EQ REAL_LT_INV_EQ REAL_INV_EQ_0
    REAL_EQ_INV2 REAL_MUL_LINV REAL_MUL_LID REAL_MUL_ASSOC
    REAL_MUL_SYM REAL_MUL_AC real_div
    REAL_ABS_INV REAL_ABS_POW REAL_SGN_POW REAL_SGN_INV REAL_INV_SGN
    C.COND_ID C.COND_SWAP
    IT7.INT_NEG_0 IT7.INT_NEG_NEG IT7.INT_NEG_EQ_0 IT7.INT_NEG_ADD
    IT7.INT_OF_NUM_EQ IT7.INT_OF_NUM_ADD IT8.INT_OF_NUM_MUL
    IT6.INT_MUL_LNEG IT7.INT_MUL_RNEG IT2.INT_ADD_SYM IDm.INT_SUB
    T.SWAP_FORALL_THM T.RIGHT_FORALL_IMP_THM T.LEFT_IMP_EXISTS_THM
    arith4.LE_EXISTS
    make_overloadable overload_interface parse_as_infix
    new_definition IA2.INT_ARITH2 IAr.ARITH_RULE MESON_TAC).run
def RZp : HolMath.Int.RealZpow := realZpowLayer

/- ---------------------------------------------------------------------- -/
/- `prioritize_num ()` (int.ml 2765), the last statement of int.ml.  Until -/
/- here `int` is the default for overloaded symbols, because int.ml 61's   -/
/- `overload_interface` put the int operations at the front of the        -/
/- interface (int.ml defines `prioritize_int` at 70 but never calls it).   -/
/- This restores `num`, as in HOL Light.                                    -/
/- ---------------------------------------------------------------------- -/
initialize prioritizeNumLayer : Unit ←
  ioOk' "prioritize_num" (HolMath.Int.prioritize_num prioritize_overload).run

/-- `ensurePrioritizeNum` (Session 7051): all of int.ml's load-bearing parser
    state is now set up by the `initialize`s above, which ran in
    `ensurePrioritizeNum`'s exact forcing order.  Kept as a no-op `Unit`
    accessor for callers that referenced the Session name. -/
def ensurePrioritizeNum : IO Unit := pure ()

/-- `ensureHolPrefixThroughInt` (Session 7870): forced the hol_lib.ml prefix
    through int.ml, in load order.  Importing this module has done that (every
    layer below is an `initialize`), so it is a no-op kept for callers. -/
def ensureHolPrefixThroughInt : IO Unit := pure ()

/- ---------------------------------------------------------------------- -/
/- int.ml bare theorem re-exports.  In HOL Light every theorem is a       -/
/- global name; the bundle records are a translation artefact, so each    -/
/- field is re-exported bare here as a plain `def`.                       -/
/- ---------------------------------------------------------------------- -/
-- integer definition + existence
def integer : thm := integerDef
def is_int  : thm := IntEx.is_int
-- IntTybij
def int_tybij              : thm := IntTb.int_tybij
def int_abstr              : thm := IntTb.int_abstr
def int_rep                : thm := IntTb.int_rep
def dest_int_rep           : thm := IntTb.dest_int_rep
def INTEGER_REAL_OF_INT    : thm := IntTb.INTEGER_REAL_OF_INT
def int_eq                 : thm := IntTb.int_eq
-- IntOps
def int_le                 : thm := IntO.int_le
def int_lt                 : thm := IntO.int_lt
def int_ge                 : thm := IntO.int_ge
def int_gt                 : thm := IntO.int_gt
def int_of_num             : thm := IntO.int_of_num
def int_of_num_th          : thm := IntO.int_of_num_th
def int_neg                : thm := IntO.int_neg
def int_neg_th             : thm := IntO.int_neg_th
def int_add                : thm := IntO.int_add
def int_add_th             : thm := IntO.int_add_th
def int_sub                : thm := IntO.int_sub
def int_sub_th             : thm := IntO.int_sub_th
def int_mul                : thm := IntO.int_mul
def int_mul_th             : thm := IntO.int_mul_th
def int_abs                : thm := IntO.int_abs
def int_abs_th             : thm := IntO.int_abs_th
def int_sgn                : thm := IntO.int_sgn
def int_sgn_th             : thm := IntO.int_sgn_th
def int_max                : thm := IntO.int_max
def int_max_th             : thm := IntO.int_max_th
def int_min                : thm := IntO.int_min
def int_min_th             : thm := IntO.int_min_th
def int_pow                : thm := IntO.int_pow
def int_pow_th             : thm := IntO.int_pow_th
def REAL_OF_INT_CLAUSES    : thm := IntO.REAL_OF_INT_CLAUSES
def INT_IMAGE              : thm := IntO.INT_IMAGE
def FORALL_INT_CASES       : thm := IntO.FORALL_INT_CASES
def EXISTS_INT_CASES       : thm := IntO.EXISTS_INT_CASES
def INT_LT_DISCRETE        : thm := IntO.INT_LT_DISCRETE
def INT_GT_DISCRETE        : thm := IntO.INT_GT_DISCRETE
-- IntThms1..10
def INT_ABS_0              : thm := IT1.INT_ABS_0
def INT_ABS_1              : thm := IT1.INT_ABS_1
def INT_ABS_ABS            : thm := IT1.INT_ABS_ABS
def INT_ABS_BETWEEN        : thm := IT1.INT_ABS_BETWEEN
def INT_ABS_BETWEEN1       : thm := IT1.INT_ABS_BETWEEN1
def INT_ABS_BETWEEN2       : thm := IT1.INT_ABS_BETWEEN2
def INT_ABS_BOUND          : thm := IT1.INT_ABS_BOUND
def INT_ABS_BOUNDS         : thm := IT1.INT_ABS_BOUNDS
def INT_ABS_CASES          : thm := IT1.INT_ABS_CASES
def INT_ABS_CIRCLE         : thm := IT1.INT_ABS_CIRCLE
def INT_ABS_LE             : thm := IT1.INT_ABS_LE
def INT_ABS_MUL            : thm := IT1.INT_ABS_MUL
def INT_ABS_NEG            : thm := IT1.INT_ABS_NEG
def INT_ABS_NUM            : thm := IT1.INT_ABS_NUM
def INT_ABS_NZ             : thm := IT1.INT_ABS_NZ
def INT_ABS_POS            : thm := IT1.INT_ABS_POS
def INT_ABS_POW            : thm := IT1.INT_ABS_POW
def INT_ABS_REFL           : thm := IT1.INT_ABS_REFL
def INT_ABS_SGN            : thm := IT1.INT_ABS_SGN
def INT_ABS_SIGN           : thm := IT1.INT_ABS_SIGN
def INT_ABS_SIGN2          : thm := IT1.INT_ABS_SIGN2
def INT_ABS_STILLNZ        : thm := IT1.INT_ABS_STILLNZ
def INT_ABS_SUB            : thm := IT1.INT_ABS_SUB
def INT_ABS_SUB_ABS        : thm := IT1.INT_ABS_SUB_ABS
def INT_ABS_TRIANGLE       : thm := IT1.INT_ABS_TRIANGLE
def INT_ABS_ZERO           : thm := IT1.INT_ABS_ZERO
def INT_ADD2_SUB2          : thm := IT1.INT_ADD2_SUB2
def INT_ADD_AC             : thm := IT1.INT_ADD_AC
def INT_ADD_ASSOC          : thm := IT2.INT_ADD_ASSOC
def INT_ADD_LDISTRIB       : thm := IT2.INT_ADD_LDISTRIB
def INT_ADD_LID            : thm := IT2.INT_ADD_LID
def INT_ADD_LINV           : thm := IT2.INT_ADD_LINV
def INT_ADD_RDISTRIB       : thm := IT2.INT_ADD_RDISTRIB
def INT_ADD_RID            : thm := IT2.INT_ADD_RID
def INT_ADD_RINV           : thm := IT2.INT_ADD_RINV
def INT_ADD_SUB            : thm := IT2.INT_ADD_SUB
def INT_ADD_SUB2           : thm := IT2.INT_ADD_SUB2
def INT_ADD_SYM            : thm := IT2.INT_ADD_SYM
def INT_BOUNDS_LE          : thm := IT2.INT_BOUNDS_LE
def INT_BOUNDS_LT          : thm := IT2.INT_BOUNDS_LT
def INT_DIFFSQ             : thm := IT2.INT_DIFFSQ
def INT_ENTIRE             : thm := IT2.INT_ENTIRE
def INT_EQ_ADD_LCANCEL     : thm := IT2.INT_EQ_ADD_LCANCEL
def INT_EQ_ADD_LCANCEL_0   : thm := IT2.INT_EQ_ADD_LCANCEL_0
def INT_EQ_ADD_RCANCEL     : thm := IT2.INT_EQ_ADD_RCANCEL
def INT_EQ_ADD_RCANCEL_0   : thm := IT2.INT_EQ_ADD_RCANCEL_0
def INT_EQ_IMP_LE          : thm := IT2.INT_EQ_IMP_LE
def INT_EQ_LCANCEL_IMP     : thm := IT2.INT_EQ_LCANCEL_IMP
def INT_EQ_MUL_LCANCEL     : thm := IT2.INT_EQ_MUL_LCANCEL
def INT_EQ_MUL_RCANCEL     : thm := IT2.INT_EQ_MUL_RCANCEL
def INT_EQ_NEG2            : thm := IT2.INT_EQ_NEG2
def INT_EQ_RCANCEL_IMP     : thm := IT2.INT_EQ_RCANCEL_IMP
def INT_EQ_SGN_ABS         : thm := IT2.INT_EQ_SGN_ABS
def INT_EQ_SQUARE_ABS      : thm := IT2.INT_EQ_SQUARE_ABS
def INT_EQ_SUB_LADD        : thm := IT2.INT_EQ_SUB_LADD
def INT_EQ_SUB_RADD        : thm := IT2.INT_EQ_SUB_RADD
def INT_EVENPOW_ABS        : thm := IT3.INT_EVENPOW_ABS
def INT_LET_ADD            : thm := IT3.INT_LET_ADD
def INT_LET_ADD2           : thm := IT3.INT_LET_ADD2
def INT_LET_ANTISYM        : thm := IT3.INT_LET_ANTISYM
def INT_LET_TOTAL          : thm := IT3.INT_LET_TOTAL
def INT_LET_TRANS          : thm := IT3.INT_LET_TRANS
def INT_LE_01              : thm := IT3.INT_LE_01
def INT_LE_ADD             : thm := IT3.INT_LE_ADD
def INT_LE_ADD2            : thm := IT3.INT_LE_ADD2
def INT_LE_ADDL            : thm := IT3.INT_LE_ADDL
def INT_LE_ADDR            : thm := IT3.INT_LE_ADDR
def INT_LE_ANTISYM         : thm := IT3.INT_LE_ANTISYM
def INT_LE_DOUBLE          : thm := IT3.INT_LE_DOUBLE
def INT_LE_LADD            : thm := IT3.INT_LE_LADD
def INT_LE_LADD_IMP        : thm := IT3.INT_LE_LADD_IMP
def INT_LE_LCANCEL_IMP     : thm := IT3.INT_LE_LCANCEL_IMP
def INT_LE_LMUL            : thm := IT3.INT_LE_LMUL
def INT_LE_LMUL_EQ         : thm := IT3.INT_LE_LMUL_EQ
def INT_LE_LNEG            : thm := IT3.INT_LE_LNEG
def INT_LE_LT              : thm := IT3.INT_LE_LT
def INT_LE_MAX             : thm := IT3.INT_LE_MAX
def INT_LE_MIN             : thm := IT3.INT_LE_MIN
def INT_LE_MUL             : thm := IT3.INT_LE_MUL
def INT_LE_MUL2            : thm := IT3.INT_LE_MUL2
def INT_LE_MUL_EQ          : thm := IT3.INT_LE_MUL_EQ
def INT_LE_NEG2            : thm := IT3.INT_LE_NEG2
def INT_LE_NEGL            : thm := IT3.INT_LE_NEGL
def INT_LE_NEGR            : thm := IT3.INT_LE_NEGR
def INT_LE_NEGTOTAL        : thm := IT4.INT_LE_NEGTOTAL
def INT_LE_POW2            : thm := IT4.INT_LE_POW2
def INT_LE_POW_2           : thm := IT4.INT_LE_POW_2
def INT_LE_RADD            : thm := IT4.INT_LE_RADD
def INT_LE_RCANCEL_IMP     : thm := IT4.INT_LE_RCANCEL_IMP
def INT_LE_REFL            : thm := IT4.INT_LE_REFL
def INT_LE_RMUL            : thm := IT4.INT_LE_RMUL
def INT_LE_RMUL_EQ         : thm := IT4.INT_LE_RMUL_EQ
def INT_LE_RNEG            : thm := IT4.INT_LE_RNEG
def INT_LE_SQUARE          : thm := IT4.INT_LE_SQUARE
def INT_LE_SQUARE_ABS      : thm := IT4.INT_LE_SQUARE_ABS
def INT_LE_SUB_LADD        : thm := IT4.INT_LE_SUB_LADD
def INT_LE_SUB_RADD        : thm := IT4.INT_LE_SUB_RADD
def INT_LE_TOTAL           : thm := IT4.INT_LE_TOTAL
def INT_LE_TRANS           : thm := IT4.INT_LE_TRANS
def INT_LNEG_UNIQ          : thm := IT4.INT_LNEG_UNIQ
def INT_LTE_ADD            : thm := IT4.INT_LTE_ADD
def INT_LTE_ADD2           : thm := IT4.INT_LTE_ADD2
def INT_LTE_ANTISYM        : thm := IT4.INT_LTE_ANTISYM
def INT_LTE_TOTAL          : thm := IT4.INT_LTE_TOTAL
def INT_LTE_TRANS          : thm := IT4.INT_LTE_TRANS
def INT_LT_01              : thm := IT4.INT_LT_01
def INT_LT_ADD             : thm := IT4.INT_LT_ADD
def INT_LT_ADD1            : thm := IT4.INT_LT_ADD1
def INT_LT_ADD2            : thm := IT4.INT_LT_ADD2
def INT_LT_ADDL            : thm := IT4.INT_LT_ADDL
def INT_LT_ADDNEG          : thm := IT4.INT_LT_ADDNEG
def INT_LT_ADDNEG2         : thm := IT4.INT_LT_ADDNEG2
def INT_LT_ADDR            : thm := IT5.INT_LT_ADDR
def INT_LT_ADD_SUB         : thm := IT5.INT_LT_ADD_SUB
def INT_LT_ANTISYM         : thm := IT5.INT_LT_ANTISYM
def INT_LT_GT              : thm := IT5.INT_LT_GT
def INT_LT_IMP_LE          : thm := IT5.INT_LT_IMP_LE
def INT_LT_IMP_NE          : thm := IT5.INT_LT_IMP_NE
def INT_LT_LADD            : thm := IT5.INT_LT_LADD
def INT_LT_LADD_IMP        : thm := IT5.INT_LT_LADD_IMP
def INT_LT_LCANCEL_IMP     : thm := IT5.INT_LT_LCANCEL_IMP
def INT_LT_LE              : thm := IT5.INT_LT_LE
def INT_LT_LMUL            : thm := IT5.INT_LT_LMUL
def INT_LT_LMUL_EQ         : thm := IT5.INT_LT_LMUL_EQ
def INT_LT_LNEG            : thm := IT5.INT_LT_LNEG
def INT_LT_MAX             : thm := IT5.INT_LT_MAX
def INT_LT_MIN             : thm := IT5.INT_LT_MIN
def INT_LT_MUL             : thm := IT5.INT_LT_MUL
def INT_LT_MUL2            : thm := IT5.INT_LT_MUL2
def INT_LT_MUL_EQ          : thm := IT5.INT_LT_MUL_EQ
def INT_LT_NEG2            : thm := IT5.INT_LT_NEG2
def INT_LT_NEGTOTAL        : thm := IT5.INT_LT_NEGTOTAL
def INT_LT_POW2            : thm := IT5.INT_LT_POW2
def INT_LT_POW_2           : thm := IT5.INT_LT_POW_2
def INT_LT_RADD            : thm := IT5.INT_LT_RADD
def INT_LT_RCANCEL_IMP     : thm := IT5.INT_LT_RCANCEL_IMP
def INT_LT_REFL            : thm := IT5.INT_LT_REFL
def INT_LT_RMUL            : thm := IT5.INT_LT_RMUL
def INT_LT_RMUL_EQ         : thm := IT5.INT_LT_RMUL_EQ
def INT_LT_RNEG            : thm := IT5.INT_LT_RNEG
def INT_LT_SQUARE          : thm := IT6.INT_LT_SQUARE
def INT_LT_SQUARE_ABS      : thm := IT6.INT_LT_SQUARE_ABS
def INT_LT_SUB_LADD        : thm := IT6.INT_LT_SUB_LADD
def INT_LT_SUB_RADD        : thm := IT6.INT_LT_SUB_RADD
def INT_LT_TOTAL           : thm := IT6.INT_LT_TOTAL
def INT_LT_TRANS           : thm := IT6.INT_LT_TRANS
def INT_MAX_ACI            : thm := IT6.INT_MAX_ACI
def INT_MAX_ASSOC          : thm := IT6.INT_MAX_ASSOC
def INT_MAX_LE             : thm := IT6.INT_MAX_LE
def INT_MAX_LT             : thm := IT6.INT_MAX_LT
def INT_MAX_MAX            : thm := IT6.INT_MAX_MAX
def INT_MAX_MIN            : thm := IT6.INT_MAX_MIN
def INT_MAX_SYM            : thm := IT6.INT_MAX_SYM
def INT_MIN_ACI            : thm := IT6.INT_MIN_ACI
def INT_MIN_ASSOC          : thm := IT6.INT_MIN_ASSOC
def INT_MIN_LE             : thm := IT6.INT_MIN_LE
def INT_MIN_LT             : thm := IT6.INT_MIN_LT
def INT_MIN_MAX            : thm := IT6.INT_MIN_MAX
def INT_MIN_MIN            : thm := IT6.INT_MIN_MIN
def INT_MIN_SYM            : thm := IT6.INT_MIN_SYM
def INT_MUL_2              : thm := IT6.INT_MUL_2
def INT_MUL_AC             : thm := IT6.INT_MUL_AC
def INT_MUL_ASSOC          : thm := IT6.INT_MUL_ASSOC
def INT_MUL_LID            : thm := IT6.INT_MUL_LID
def INT_MUL_LNEG           : thm := IT6.INT_MUL_LNEG
def INT_MUL_LZERO          : thm := IT6.INT_MUL_LZERO
def INT_MUL_POS_LE         : thm := IT6.INT_MUL_POS_LE
def INT_MUL_POS_LT         : thm := IT6.INT_MUL_POS_LT
def INT_MUL_RID            : thm := IT7.INT_MUL_RID
def INT_MUL_RNEG           : thm := IT7.INT_MUL_RNEG
def INT_MUL_RZERO          : thm := IT7.INT_MUL_RZERO
def INT_MUL_SYM            : thm := IT7.INT_MUL_SYM
def INT_NEG_0              : thm := IT7.INT_NEG_0
def INT_NEG_ADD            : thm := IT7.INT_NEG_ADD
def INT_NEG_EQ             : thm := IT7.INT_NEG_EQ
def INT_NEG_EQ_0           : thm := IT7.INT_NEG_EQ_0
def INT_NEG_GE0            : thm := IT7.INT_NEG_GE0
def INT_NEG_GT0            : thm := IT7.INT_NEG_GT0
def INT_NEG_LE0            : thm := IT7.INT_NEG_LE0
def INT_NEG_LMUL           : thm := IT7.INT_NEG_LMUL
def INT_NEG_LT0            : thm := IT7.INT_NEG_LT0
def INT_NEG_MINUS1         : thm := IT7.INT_NEG_MINUS1
def INT_NEG_MUL2           : thm := IT7.INT_NEG_MUL2
def INT_NEG_NEG            : thm := IT7.INT_NEG_NEG
def INT_NEG_RMUL           : thm := IT7.INT_NEG_RMUL
def INT_NEG_SUB            : thm := IT7.INT_NEG_SUB
def INT_NOT_EQ             : thm := IT7.INT_NOT_EQ
def INT_NOT_LE             : thm := IT7.INT_NOT_LE
def INT_NOT_LT             : thm := IT7.INT_NOT_LT
def INT_OF_NUM_ADD         : thm := IT7.INT_OF_NUM_ADD
def INT_OF_NUM_CLAUSES     : thm := IT7.INT_OF_NUM_CLAUSES
def INT_OF_NUM_EQ          : thm := IT7.INT_OF_NUM_EQ
def INT_OF_NUM_GE          : thm := IT7.INT_OF_NUM_GE
def INT_OF_NUM_GT          : thm := IT7.INT_OF_NUM_GT
def INT_OF_NUM_LE          : thm := IT7.INT_OF_NUM_LE
def INT_OF_NUM_LT          : thm := IT7.INT_OF_NUM_LT
def INT_OF_NUM_MAX         : thm := IT8.INT_OF_NUM_MAX
def INT_OF_NUM_MIN         : thm := IT8.INT_OF_NUM_MIN
def INT_OF_NUM_MOD         : thm := IT8.INT_OF_NUM_MOD
def INT_OF_NUM_MUL         : thm := IT8.INT_OF_NUM_MUL
def INT_OF_NUM_POW         : thm := IT8.INT_OF_NUM_POW
def INT_OF_NUM_SUB         : thm := IT8.INT_OF_NUM_SUB
def INT_OF_NUM_SUB_CASES   : thm := IT8.INT_OF_NUM_SUB_CASES
def INT_OF_NUM_SUC         : thm := IT8.INT_OF_NUM_SUC
def INT_POS                : thm := IT8.INT_POS
def INT_POS_EQ_SQUARE      : thm := IT8.INT_POS_EQ_SQUARE
def INT_POS_NZ             : thm := IT8.INT_POS_NZ
def INT_POW2_ABS           : thm := IT8.INT_POW2_ABS
def INT_POW_1              : thm := IT8.INT_POW_1
def INT_POW_1_LE           : thm := IT8.INT_POW_1_LE
def INT_POW_1_LT           : thm := IT8.INT_POW_1_LT
def INT_POW_2              : thm := IT8.INT_POW_2
def INT_POW_ADD            : thm := IT8.INT_POW_ADD
def INT_POW_EQ             : thm := IT8.INT_POW_EQ
def INT_POW_EQ_0           : thm := IT8.INT_POW_EQ_0
def INT_POW_EQ_1           : thm := IT8.INT_POW_EQ_1
def INT_POW_EQ_1_IMP       : thm := IT8.INT_POW_EQ_1_IMP
def INT_POW_EQ_ABS         : thm := IT8.INT_POW_EQ_ABS
def INT_POW_EQ_EQ          : thm := IT8.INT_POW_EQ_EQ
def INT_POW_EQ_ODD         : thm := IT8.INT_POW_EQ_ODD
def INT_POW_EQ_ODD_EQ      : thm := IT8.INT_POW_EQ_ODD_EQ
def INT_POW_LBOUND         : thm := IT8.INT_POW_LBOUND
def INT_POW_LE             : thm := IT8.INT_POW_LE
def INT_POW_LE2            : thm := IT8.INT_POW_LE2
def INT_POW_LE2_ODD        : thm := IT9.INT_POW_LE2_ODD
def INT_POW_LE2_ODD_EQ     : thm := IT9.INT_POW_LE2_ODD_EQ
def INT_POW_LE2_REV        : thm := IT9.INT_POW_LE2_REV
def INT_POW_LE_1           : thm := IT9.INT_POW_LE_1
def INT_POW_LT             : thm := IT9.INT_POW_LT
def INT_POW_LT2            : thm := IT9.INT_POW_LT2
def INT_POW_LT2_ODD        : thm := IT9.INT_POW_LT2_ODD
def INT_POW_LT2_ODD_EQ     : thm := IT9.INT_POW_LT2_ODD_EQ
def INT_POW_LT2_REV        : thm := IT9.INT_POW_LT2_REV
def INT_POW_LT_1           : thm := IT9.INT_POW_LT_1
def INT_POW_MONO           : thm := IT9.INT_POW_MONO
def INT_POW_MONO_LT        : thm := IT9.INT_POW_MONO_LT
def INT_POW_MUL            : thm := IT9.INT_POW_MUL
def INT_POW_NEG            : thm := IT9.INT_POW_NEG
def INT_POW_NZ             : thm := IT9.INT_POW_NZ
def INT_POW_ONE            : thm := IT9.INT_POW_ONE
def INT_POW_POW            : thm := IT9.INT_POW_POW
def INT_POW_ZERO           : thm := IT9.INT_POW_ZERO
def INT_RNEG_UNIQ          : thm := IT9.INT_RNEG_UNIQ
def INT_SGN                : thm := IT9.INT_SGN
def INT_SGNS_EQ            : thm := IT9.INT_SGNS_EQ
def INT_SGNS_EQ_ALT        : thm := IT9.INT_SGNS_EQ_ALT
def INT_SGN_0              : thm := IT9.INT_SGN_0
def INT_SGN_ABS            : thm := IT9.INT_SGN_ABS
def INT_SGN_ABS_ALT        : thm := IT9.INT_SGN_ABS_ALT
def INT_SGN_CASES          : thm := IT9.INT_SGN_CASES
def INT_SGN_EQ             : thm := IT10.INT_SGN_EQ
def INT_SGN_EQ_INEQ        : thm := IT10.INT_SGN_EQ_INEQ
def INT_SGN_INEQS          : thm := IT10.INT_SGN_INEQS
def INT_SGN_INT_SGN        : thm := IT10.INT_SGN_INT_SGN
def INT_SGN_MUL            : thm := IT10.INT_SGN_MUL
def INT_SGN_NEG            : thm := IT10.INT_SGN_NEG
def INT_SGN_POW            : thm := IT10.INT_SGN_POW
def INT_SGN_POW_2          : thm := IT10.INT_SGN_POW_2
def INT_SOS_EQ_0           : thm := IT10.INT_SOS_EQ_0
def INT_SUB_0              : thm := IT10.INT_SUB_0
def INT_SUB_ABS            : thm := IT10.INT_SUB_ABS
def INT_SUB_ADD            : thm := IT10.INT_SUB_ADD
def INT_SUB_ADD2           : thm := IT10.INT_SUB_ADD2
def INT_SUB_LDISTRIB       : thm := IT10.INT_SUB_LDISTRIB
def INT_SUB_LE             : thm := IT10.INT_SUB_LE
def INT_SUB_LNEG           : thm := IT10.INT_SUB_LNEG
def INT_SUB_LT             : thm := IT10.INT_SUB_LT
def INT_SUB_LZERO          : thm := IT10.INT_SUB_LZERO
def INT_SUB_NEG2           : thm := IT10.INT_SUB_NEG2
def INT_SUB_RDISTRIB       : thm := IT10.INT_SUB_RDISTRIB
def INT_SUB_REFL           : thm := IT10.INT_SUB_REFL
def INT_SUB_RNEG           : thm := IT10.INT_SUB_RNEG
def INT_SUB_RZERO          : thm := IT10.INT_SUB_RZERO
def INT_SUB_SUB            : thm := IT10.INT_SUB_SUB
def INT_SUB_SUB2           : thm := IT10.INT_SUB_SUB2
def INT_SUB_TRIANGLE       : thm := IT10.INT_SUB_TRIANGLE
-- IntWlog
def INT_WLOG_LE            : thm := IWl.INT_WLOG_LE
def INT_WLOG_LT            : thm := IWl.INT_WLOG_LT
def INT_WLOG_LE_3          : thm := IWl.INT_WLOG_LE_3
-- IntArith1 (thm fields only)
def INT_FORALL_POS         : thm := IA1.INT_FORALL_POS
def INT_EXISTS_POS         : thm := IA1.INT_EXISTS_POS
def INT_FORALL_ABS         : thm := IA1.INT_FORALL_ABS
def INT_EXISTS_ABS         : thm := IA1.INT_EXISTS_ABS
def INT_POW                : thm := IA1.INT_POW
def INT_ABS                : thm := IA1.INT_ABS
def INT_GE                 : thm := IA1.INT_GE
def INT_GT                 : thm := IA1.INT_GT
def INT_LT                 : thm := IA1.INT_LT
-- IntDivMod
def INT_SUB                : thm := IDm.INT_SUB
def INT_MAX                : thm := IDm.INT_MAX
def INT_MIN                : thm := IDm.INT_MIN
def INT_OF_NUM_EXISTS      : thm := IDm.INT_OF_NUM_EXISTS
def INT_LE_DISCRETE        : thm := IDm.INT_LE_DISCRETE
def INT_LE_TRANS_LE        : thm := IDm.INT_LE_TRANS_LE
def INT_LE_TRANS_LT        : thm := IDm.INT_LE_TRANS_LT
def INT_MUL_EQ_1           : thm := IDm.INT_MUL_EQ_1
def INT_ABS_MUL_1          : thm := IDm.INT_ABS_MUL_1
def INT_WOP                : thm := IDm.INT_WOP
def INT_ARCH               : thm := IDm.INT_ARCH
def INT_DIVMOD_EXIST_0     : thm := IDm.INT_DIVMOD_EXIST_0
def INT_DIVISION_0         : thm := IDm.INT_DIVISION_0
def INT_DIVISION           : thm := IDm.INT_DIVISION
def INT_DIVISION_SIMP      : thm := IDm.INT_DIVISION_SIMP
def INT_REM_POS            : thm := IDm.INT_REM_POS
def INT_DIV_0              : thm := IDm.INT_DIV_0
def INT_REM_0              : thm := IDm.INT_REM_0
def INT_REM_POS_EQ         : thm := IDm.INT_REM_POS_EQ
def INT_REM_DIV            : thm := IDm.INT_REM_DIV
def INT_LT_REM             : thm := IDm.INT_LT_REM
def INT_LT_REM_EQ          : thm := IDm.INT_LT_REM_EQ
-- IntDivisibility
def cong                   : thm := IDv.cong
def real_mod               : thm := IDv.real_mod
def int_divides            : thm := IDv.int_divides
def INT_DIVIDES_LE         : thm := IDv.INT_DIVIDES_LE
def int_mod                : thm := IDv.int_mod
def int_congruent          : thm := IDv.int_congruent
def INT_CONG_IMP_EQ        : thm := IDv.INT_CONG_IMP_EQ
def int_coprime            : thm := IDv.int_coprime
-- IntArith1 procedures (int.ml 674-707): the bootstrapping decision procedure.
def INT_ARITH1 : term → IO (Except String thm) := IA1.INT_ARITH1
def INT_ARITH_TAC1 : tactic := IA1.INT_ARITH_TAC1
def ASM_INT_ARITH_TAC1 : tactic := IA1.ASM_INT_ARITH_TAC1
def INTEGER_TAC1 : tactic := ITc1.INTEGER_TAC1
def INTEGER_RULE1 : term → IO (Except String thm) := ITc1.INTEGER_RULE1
-- IntDivRem1 (int.ml 1329-1763): the 47 further div/rem/congruence proofs.
def INT_DIVMOD_UNIQ        : thm := IDr1.INT_DIVMOD_UNIQ
def INT_DIV_UNIQ           : thm := IDr1.INT_DIV_UNIQ
def INT_REM_UNIQ           : thm := IDr1.INT_REM_UNIQ
def INT_DIV_LT             : thm := IDr1.INT_DIV_LT
def INT_REM_LT             : thm := IDr1.INT_REM_LT
def INT_DIV_RNEG           : thm := IDr1.INT_DIV_RNEG
def INT_REM_RNEG           : thm := IDr1.INT_REM_RNEG
def INT_REM_RABS           : thm := IDr1.INT_REM_RABS
def INT_REM_REM            : thm := IDr1.INT_REM_REM
def INT_REM_EQ             : thm := IDr1.INT_REM_EQ
def INT_DIV_ZERO           : thm := IDr1.INT_DIV_ZERO
def INT_REM_ZERO           : thm := IDr1.INT_REM_ZERO
def INT_REM_EQ_0           : thm := IDr1.INT_REM_EQ_0
def INT_MUL_DIV_EQ         : thm := IDr1.INT_MUL_DIV_EQ
def INT_CONG_LREM          : thm := IDr1.INT_CONG_LREM
def INT_CONG_RREM          : thm := IDr1.INT_CONG_RREM
def INT_REM_MOD_SELF       : thm := IDr1.INT_REM_MOD_SELF
def INT_REM_REM_MUL        : thm := IDr1.INT_REM_REM_MUL
def INT_CONG_SOLVE_BOUNDS  : thm := IDr1.INT_CONG_SOLVE_BOUNDS
def INT_NEG_REM            : thm := IDr1.INT_NEG_REM
def INT_ADD_REM            : thm := IDr1.INT_ADD_REM
def INT_SUB_REM            : thm := IDr1.INT_SUB_REM
def INT_MUL_REM            : thm := IDr1.INT_MUL_REM
def INT_POW_REM            : thm := IDr1.INT_POW_REM
def INT_OF_NUM_DIV         : thm := IDr1.INT_OF_NUM_DIV
def INT_OF_NUM_REM         : thm := IDr1.INT_OF_NUM_REM
def INT_DIV_REFL           : thm := IDr1.INT_DIV_REFL
def INT_REM_REFL           : thm := IDr1.INT_REM_REFL
def INT_DIV_LNEG           : thm := IDr1.INT_DIV_LNEG
def INT_REM_LNEG           : thm := IDr1.INT_REM_LNEG
def INT_DIV_NEG2           : thm := IDr1.INT_DIV_NEG2
def INT_REM_NEG2           : thm := IDr1.INT_REM_NEG2
def INT_DIV_1              : thm := IDr1.INT_DIV_1
def INT_REM_1              : thm := IDr1.INT_REM_1
def INT_DIV_MUL            : thm := IDr1.INT_DIV_MUL
def INT_REM_MUL            : thm := IDr1.INT_REM_MUL
def INT_DIV_LT_EQ          : thm := IDr1.INT_DIV_LT_EQ
def INT_LE_DIV_EQ          : thm := IDr1.INT_LE_DIV_EQ
def INT_DIV_LE_EQ          : thm := IDr1.INT_DIV_LE_EQ
def INT_LT_DIV_EQ          : thm := IDr1.INT_LT_DIV_EQ
def INT_DIV_LE             : thm := IDr1.INT_DIV_LE
def INT_DIV_DIV            : thm := IDr1.INT_DIV_DIV
def INT_REM_MUL_REM        : thm := IDr1.INT_REM_MUL_REM
def INT_DIV_EQ_0           : thm := IDr1.INT_DIV_EQ_0
def INT_REM_EQ_SELF        : thm := IDr1.INT_REM_EQ_SELF
def INT_REM_UNIQUE         : thm := IDr1.INT_REM_UNIQUE
def INT_DIV_REM            : thm := IDr1.INT_DIV_REM
def INT_REM_REM_LE         : thm := IDr1.INT_REM_REM_LE
def INT_LE_DIV             : thm := IDr1.INT_LE_DIV
def INT_LT_DIV             : thm := IDr1.INT_LT_DIV
def INT_REM_LE_EQ          : thm := IDr1.INT_REM_LE_EQ
def INT_REM_LE             : thm := IDr1.INT_REM_LE
def INT_REM_MUL_ADD        : thm := IDr1.INT_REM_MUL_ADD
def INT_DIV_MUL_ADD        : thm := IDr1.INT_DIV_MUL_ADD
def INT_CONG_DIV2          : thm := IDr1.INT_CONG_DIV2
def INT_REM_2_CASES        : thm := IDr1.INT_REM_2_CASES
def NOT_INT_REM_2          : thm := IDr1.NOT_INT_REM_2
def INT_REM_2_DIVIDES      : thm := IDr1.INT_REM_2_DIVIDES
def INT_REM_2_EXPAND       : thm := IDr1.INT_REM_2_EXPAND
def INT_REM_2_NEG          : thm := IDr1.INT_REM_2_NEG
def INT_DIVIDES_DIV_SELF   : thm := IDr1.INT_DIVIDES_DIV_SELF
def INT_DIV_BY_DIV         : thm := IDr1.INT_DIV_BY_DIV
def INT_DIVIDES_DIV_DIVIDES : thm := IDr1.INT_DIVIDES_DIV_DIVIDES
def INT_DIVIDES_DIVIDES_DIV : thm := IDr1.INT_DIVIDES_DIVIDES_DIV
def INT_DIVIDES_DIVIDES_DIV_EQ : thm := IDr1.INT_DIVIDES_DIVIDES_DIV_EQ
-- Reduction net, even/odd analogues and rem conversions (int.ml 1772-1928).
def INT_DIV_CONV           : ioconv := IDrc.INT_DIV_CONV
def INT_REM_CONV           : ioconv := IDrc.INT_REM_CONV
def INT_2_DIVIDES_ADD      : thm := IEo.INT_2_DIVIDES_ADD
def INT_2_DIVIDES_SUB      : thm := IEo.INT_2_DIVIDES_SUB
def INT_2_DIVIDES_MUL      : thm := IEo.INT_2_DIVIDES_MUL
def INT_2_DIVIDES_POW      : thm := IEo.INT_2_DIVIDES_POW
def INT_REM_DOWN_CONV      : ioconv := IRc.INT_REM_DOWN_CONV
def INT_POW_REM_CONV       : ioconv := IRc.INT_POW_REM_CONV
-- IntGcdLcm (int.ml 1929-2067): gcd/lcm, Bezout, and the SECOND INTEGER_TAC.
def WF_INT_MEASURE         : thm := IGl.WF_INT_MEASURE
def WF_INT_MEASURE_2       : thm := IGl.WF_INT_MEASURE_2
def INT_GCD_EXISTS         : thm := IGl.INT_GCD_EXISTS
def INT_GCD_EXISTS_POS     : thm := IGl.INT_GCD_EXISTS_POS
def int_gcd                : thm := IGl.int_gcd
def int_lcm                : thm := IGl.int_lcm
def INT_DIVIDES_LABS       : thm := IGl.INT_DIVIDES_LABS
def INT_DIVIDES_RABS       : thm := IGl.INT_DIVIDES_RABS
def INT_DIVIDES_ABS        : thm := IGl.INT_DIVIDES_ABS
def INT_LCM_POS            : thm := IGl.INT_LCM_POS
def INT_MUL_GCD_LCM        : thm := IGl.INT_MUL_GCD_LCM
def INT_MUL_LCM_GCD        : thm := IGl.INT_MUL_LCM_GCD
def INT_DIVIDES_LCM_GCD    : thm := IGl.INT_DIVIDES_LCM_GCD
def INT_LCM_DIVIDES        : thm := IGl.INT_LCM_DIVIDES
def INT_LCM                : thm := IGl.INT_LCM
-- The SECOND INTEGER_TAC/INTEGER_RULE (int.ml 2045/2064), which REPLACE v1:
-- they additionally eliminate gcd/lcm.  The unnumbered names alias v2 (as
-- int.ml's later text refers to the NAME INTEGER_TAC = v2); v1 remains as
-- INTEGER_TAC1/INTEGER_RULE1 for the div/rem layer and INTEGER_TAC2's fallback.
def INTEGER_TAC2 : tactic := IGl.INTEGER_TAC2
def INTEGER_RULE2 : term → IO (Except String thm) := IGl.INTEGER_RULE2
def INTEGER_TAC : tactic := IGl.INTEGER_TAC2
def INTEGER_RULE : term → IO (Except String thm) := IGl.INTEGER_RULE2
-- IntConstSyntax operations (int.ml 268-281).
def is_intconst : term → Bool := HolMath.Int.is_intconst
def dest_intconst : term → Except String Rat := HolMath.Int.dest_intconst
def mk_intconst (x : Rat) : Except String term := HolMath.Int.mk_intconst IntKs x
-- IntCompareConvs (int.ml 887-936): the five relational numeral conversions.
def INT_LE_CONV : ioconv := ICv.INT_LE_CONV
def INT_LT_CONV : ioconv := ICv.INT_LT_CONV
def INT_GE_CONV : ioconv := ICv.INT_GE_CONV
def INT_GT_CONV : ioconv := ICv.INT_GT_CONV
def INT_EQ_CONV : ioconv := ICv.INT_EQ_CONV
-- IntArithConvs (int.ml 941-1079): the nine arithmetic numeral conversions.
def INT_NEG_CONV : ioconv := IAv.INT_NEG_CONV
def INT_MUL_CONV : ioconv := IAv.INT_MUL_CONV
def INT_ADD_CONV : ioconv := IAv.INT_ADD_CONV
def INT_SUB_CONV : ioconv := IAv.INT_SUB_CONV
def INT_POW_CONV : ioconv := IAv.INT_POW_CONV
def INT_ABS_CONV : ioconv := IAv.INT_ABS_CONV
def INT_MAX_CONV : ioconv := IAv.INT_MAX_CONV
def INT_MIN_CONV : ioconv := IAv.INT_MIN_CONV
def INT_SGN_CONV : ioconv := IAv.INT_SGN_CONV
-- IntPolyConvs (int.ml 1090) and IntRingConvs (int.ml 1122-1147).
def INT_POLY_CONV : ioconv := IPc.INT_POLY_CONV
def INT_RING : term → IO (Except String thm) := IRg.INT_RING
def int_ideal_cofactors : List term → term → IO (Except String (List term)) :=
  IRg.int_ideal_cofactors
def INT_INTEGRAL : thm := IRg.INT_INTEGRAL
-- IntNumOfInt (int.ml 2070-2104): the nonnegative-integer -> natural map.
def num_of_int         : thm := INoI.num_of_int
def NUM_OF_INT_OF_NUM  : thm := INoI.NUM_OF_INT_OF_NUM
def INT_OF_NUM_OF_INT  : thm := INoI.INT_OF_NUM_OF_INT
def NUM_OF_INT         : thm := INoI.NUM_OF_INT
def NUM_OF_INT_ADD     : thm := INoI.NUM_OF_INT_ADD
def NUM_OF_INT_MUL     : thm := INoI.NUM_OF_INT_MUL
def NUM_OF_INT_POW     : thm := INoI.NUM_OF_INT_POW
-- IntNumNotions (int.ml 2107-2149): natural-number divisibility notions.
def num_divides        : thm := INoN.num_divides
def num_mod            : thm := INoN.num_mod
def num_congruent      : thm := INoN.num_congruent
def num_coprime        : thm := INoN.num_coprime
def num_gcd            : thm := INoN.num_gcd
def num_lcm            : thm := INoN.num_lcm
def NUM_TO_INT_CONV    : ioconv := INoN.NUM_TO_INT_CONV
-- IntArithRule (int.ml 2153-2189): the linear decision procedure for N.
def ARITH_RULE : term → IO (Except String thm) := IAr.ARITH_RULE
def ARITH_TAC : tactic := IAr.ARITH_TAC
def ASM_ARITH_TAC : tactic := IAr.ASM_ARITH_TAC
-- IntArith2 (int.ml 2192-2323): the ENHANCED int decision procedure.  These
-- SUPERSEDE the IntArith1 versions; the unnumbered INT_ARITH/INT_ARITH_TAC/
-- ASM_INT_ARITH_TAC names alias the v2 forms; v1 stays as INT_ARITH1/etc.
def INT_ARITH2 : term → IO (Except String thm) := IA2.INT_ARITH2
def INT_ARITH_TAC2 : tactic := IA2.INT_ARITH_TAC2
def ASM_INT_ARITH_TAC2 : tactic := IA2.ASM_INT_ARITH_TAC2
def INT_ARITH : term → IO (Except String thm) := IA2.INT_ARITH2
def INT_ARITH_TAC : tactic := IA2.INT_ARITH_TAC2
def ASM_INT_ARITH_TAC : tactic := IA2.ASM_INT_ARITH_TAC2
-- IntMiscNat (int.ml 2326-2375): four miscellaneous natural-number lemmas.
def BINARY_INDUCT       : thm := IMn.BINARY_INDUCT
def NUM_CASES_BINARY    : thm := IMn.NUM_CASES_BINARY
def num_WF_DOWN         : thm := IMn.num_WF_DOWN
def INT_REM_REM_POW_MIN : thm := IMn.INT_REM_REM_POW_MIN
-- IntNumber (int.ml 2378-2566): the natural-number divisibility layer and
-- NUMBER_TAC (int.ml 2503)/NUMBER_RULE (int.ml 2520).
def NUM_GCD                 : thm := INum.NUM_GCD
def NUM_LCM                 : thm := INum.NUM_LCM
def CONG                    : thm := INum.CONG
def CONG_LMOD               : thm := INum.CONG_LMOD
def CONG_RMOD               : thm := INum.CONG_RMOD
def CONG_DIV2               : thm := INum.CONG_DIV2
def divides                 : thm := INum.divides
def DIVIDES_LE              : thm := INum.DIVIDES_LE
def DIVIDES_LE_STRONG       : thm := INum.DIVIDES_LE_STRONG
def DIVIDES_LE_IMP          : thm := INum.DIVIDES_LE_IMP
def PROPERLY_DIVIDES_LE_IMP : thm := INum.PROPERLY_DIVIDES_LE_IMP
def DIVIDES_ANTISYM         : thm := INum.DIVIDES_ANTISYM
def DIVIDES_ONE             : thm := INum.DIVIDES_ONE
def DIV_ADD                 : thm := INum.DIV_ADD
def DIVIDES_MOD             : thm := INum.DIVIDES_MOD
def DIVIDES_DIV_MULT        : thm := INum.DIVIDES_DIV_MULT
def DIV_BY_DIV              : thm := INum.DIV_BY_DIV
def DIVIDES_DIV_DIVIDES     : thm := INum.DIVIDES_DIV_DIVIDES
def DIVIDES_DIV_SELF        : thm := INum.DIVIDES_DIV_SELF
def DIVIDES_DIVIDES_DIV     : thm := INum.DIVIDES_DIVIDES_DIV
def DIVIDES_DIVIDES_DIV_EQ  : thm := INum.DIVIDES_DIVIDES_DIV_EQ
def DIVIDES_DIVIDES_DIV_IMP : thm := INum.DIVIDES_DIVIDES_DIV_IMP
def MULT_DIV                : thm := INum.MULT_DIV
def NUMBER_TAC : tactic := INum.NUMBER_TAC
def NUMBER_RULE : term → IO (Except String thm) := INum.NUMBER_RULE
def COPRIME_LMOD            : thm := INum.COPRIME_LMOD
def COPRIME_RMOD            : thm := INum.COPRIME_RMOD
def INT_CONG_NUM_EXISTS     : thm := INum.INT_CONG_NUM_EXISTS
def GCD                     : thm := INum.GCD
def coprime                 : thm := INum.coprime
-- IntPrime (int.ml 2571-2630): the definition of `prime` and five theorems.
def prime                            : thm := IPr.prime
def ONE_OR_PRIME                     : thm := IPr.ONE_OR_PRIME
def ONE_OR_PRIME_DIVIDES_OR_COPRIME  : thm := IPr.ONE_OR_PRIME_DIVIDES_OR_COPRIME
def PRIME_COPRIME_EQ_NONDIVISIBLE    : thm := IPr.PRIME_COPRIME_EQ_NONDIVISIBLE
def ZERO_ONE_OR_PRIME_DIVPROD        : thm := IPr.ZERO_ONE_OR_PRIME_DIVPROD
def ZERO_ONE_OR_PRIME                : thm := IPr.ZERO_ONE_OR_PRIME
-- RealZpow (int.ml 2633-2761): `real_zpow` and its 22 theorems.
def real_zpow        : thm := RZp.real_zpow
def REAL_POW_ZPOW    : thm := RZp.REAL_POW_ZPOW
def REAL_ZPOW_NUM    : thm := RZp.REAL_ZPOW_NUM
def REAL_ZPOW_0      : thm := RZp.REAL_ZPOW_0
def REAL_ZPOW_1      : thm := RZp.REAL_ZPOW_1
def REAL_ZPOW_2      : thm := RZp.REAL_ZPOW_2
def REAL_ZPOW_ONE    : thm := RZp.REAL_ZPOW_ONE
def REAL_ZPOW_NEG    : thm := RZp.REAL_ZPOW_NEG
def REAL_ZPOW_MINUS1 : thm := RZp.REAL_ZPOW_MINUS1
def REAL_ZPOW_ZERO   : thm := RZp.REAL_ZPOW_ZERO
def REAL_ZPOW_POW    : thm := RZp.REAL_ZPOW_POW
def REAL_INV_ZPOW    : thm := RZp.REAL_INV_ZPOW
def REAL_ZPOW_INV    : thm := RZp.REAL_ZPOW_INV
def REAL_ZPOW_ZPOW   : thm := RZp.REAL_ZPOW_ZPOW
def REAL_ZPOW_MUL    : thm := RZp.REAL_ZPOW_MUL
def REAL_ZPOW_DIV    : thm := RZp.REAL_ZPOW_DIV
def REAL_ZPOW_ADD    : thm := RZp.REAL_ZPOW_ADD
def REAL_ZPOW_SUB    : thm := RZp.REAL_ZPOW_SUB
def REAL_ZPOW_LE     : thm := RZp.REAL_ZPOW_LE
def REAL_ZPOW_LT     : thm := RZp.REAL_ZPOW_LT
def REAL_ZPOW_EQ_0   : thm := RZp.REAL_ZPOW_EQ_0
def REAL_ABS_ZPOW    : thm := RZp.REAL_ABS_ZPOW
def REAL_SGN_ZPOW    : thm := RZp.REAL_SGN_ZPOW

end Session
