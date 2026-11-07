/- File: SessionMath/CalcRat.lean
calc_rat.ml: calculation with rational-valued reals, and the final
REAL_ARITH (`REAL_ARITH3`), REAL_RING and REAL_FIELD, built by `initialize`
when this module is imported.  The conversions and decision procedures are
closures, kept in `IO.Ref`s that `initialize` blocks fill at their calc_rat.ml
positions (REAL_FIELD at 581; REAL_RAT_RED_CONV and REAL_RAT_COMPUTE_CONV
last, by `ensureRealProcs`).
-/
import SessionMath.Real
import HolMath.CalcRat

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic

namespace Session

private def ioOk' {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")


/- calc_rat.ml (hol_lib.ml 97): calculation with rational-valued reals.    -/
/-                                                                        -/
/- Fifteen setups wired in dependency order.  This is the THIRD and final  -/
/- redefinition of GEN_REAL_ARITH / REAL_ARITH / REAL_ARITH_TAC: the final -/
/- tools here (`REAL_ARITH3`, `REAL_ARITH_TAC2`, `ASM_REAL_ARITH_TAC`)      -/
/- SUPERSEDE realarith.ml's `REAL_ARITH2` / real.ml's `REAL_ARITH_TAC`.     -/
/- Each structural stage is an `initialize`; the closure-holding            -/
/- conversions (`REAL_RAT_RED/COMPUTE_CONV`, `REAL_POLY_CONV`,              -/
/- `REAL_RING`/`REAL_ARITH3` and `REAL_FIELD`) live in `Option` refs,       -/
/- seeded in file order by the forcing blocks below. -/
/- ---------------------------------------------------------------------- -/

/- `RealRingConvs`/`FinalRealArith`/`RealPolyConvs1` carry only function-typed
   fields (`term → IO ...` etc.) and are NOT declared `Inhabited` in the pure
   library, but an `initialize` constant of that type needs an
   `Inhabited`/`Nonempty` fallback.  Functions into `IO` are inhabited, so Lean
   derives these (same device as RealAx's `RealArith1Ctx`/`RealArith2Ctx`). -/
deriving instance Inhabited for HolMath.CalcRat.RealRingConvs
deriving instance Inhabited for HolMath.CalcRat.FinalRealArith
deriving instance Inhabited for HolMath.CalcRat.RealPolyConvs1

/-- `DECIMAL` (calc_rat.ml 16-17): `|- DECIMAL x y = &x / &y`.  CREATES a new
    constant, so NOT idempotent — this `initialize` runs `setupDecimal`
    exactly once.  Reading `Dec` declares the constant, so every downstream
    setup that parses a `DECIMAL`-mentioning term takes `Dec` as its `DECIMAL`
    parameter to force this first. -/
initialize decimalLayer : thm ←
  ioOk' "setupDecimal" (HolMath.CalcRat.setupDecimal new_definition).run

def Dec : thm := decimalLayer

/-- `RatLemmas` (calc_rat.ml 20-80): `RAT_LEMMA1..5`. -/
initialize ratLemmasLayer : HolMath.CalcRat.RatLemmas ←
  ioOk' "setupRatLemmas" (HolMath.CalcRat.setupRatLemmas Rl CiT RaL RT1 RT6 REAL_ARITH2).run

def RatLm : HolMath.CalcRat.RatLemmas := ratLemmasLayer

/-- `RealRatRelConvs` (calc_rat.ml 81-171): `REAL_INT_RAT_CONV` and the six
    relational conversions (LE, LT, GE, GT, EQ, SGN). -/
initialize realRatRelLayer : HolMath.CalcRat.RealRatRelConvs ←
  ioOk' "setupRealRatRelConvs" (HolMath.CalcRat.setupRealRatRelConvs RatLm Dec CiV CiW
    Rl CiT RT2 RT6 RT10).run

def RRel : HolMath.CalcRat.RealRatRelConvs := realRatRelLayer

/-- `REAL_INT_RAT_CONV` (calc_rat.ml 84). -/
def REAL_INT_RAT_CONV : ioconv := fun tm => RRel.REAL_INT_RAT_CONV tm

/-- `RealRatUnaryConvs` (calc_rat.ml 172-229): NEG, ABS, INV. -/
initialize realRatUnaryLayer : HolMath.CalcRat.RealRatUnaryConvs ←
  ioOk' "setupRealRatUnaryConvs" (HolMath.CalcRat.setupRealRatUnaryConvs Dec Rl CiT RaL RT1 RT6).run

def RUn : HolMath.CalcRat.RealRatUnaryConvs := realRatUnaryLayer

/-- `RealRatArithConvs` (calc_rat.ml 230-358): ADD, SUB, MUL, DIV. -/
initialize realRatArithLayer : HolMath.CalcRat.RealRatArithConvs ←
  ioOk' "setupRealRatArithConvs" (HolMath.CalcRat.setupRealRatArithConvs RatLm RRel RUn CiV CiW
    RSyn Rl RaL RT1 RT6 REAL_INT_REDUCE_CONV).run

def RAr : HolMath.CalcRat.RealRatArithConvs := realRatArithLayer

/-- `RealRatPowMaxMinConvs` (calc_rat.ml 359-385): POW, MAX, MIN. -/
initialize realRatPowMaxMinLayer : HolMath.CalcRat.RealRatPowMaxMinConvs ←
  ioOk' "setupRealRatPowMaxMinConvs" (HolMath.CalcRat.setupRealRatPowMaxMinConvs RRel CiW Rl RT6).run

def RPmm : HolMath.CalcRat.RealRatPowMaxMinConvs := realRatPowMaxMinLayer

/- Public accessors for the calc_rat.ml conversion bundles. -/

/-- The `calc_rat.ml` relational conversions (81-171). -/
def realRatRelConvs : HolMath.CalcRat.RealRatRelConvs := RRel
/-- The `calc_rat.ml` unary conversions (172-229). -/
def realRatUnaryConvs : HolMath.CalcRat.RealRatUnaryConvs := RUn
/-- The `calc_rat.ml` arithmetic conversions (230-358). -/
def realRatArithConvs : HolMath.CalcRat.RealRatArithConvs := RAr
/-- The `calc_rat.ml` powers/max/min conversions (359-385). -/
def realRatPowMaxMinConvs : HolMath.CalcRat.RealRatPowMaxMinConvs := RPmm

/- The rational-constant conversions as plain `ioconv`s. -/

/-- `REAL_RAT_LE_CONV` (calc_rat.ml 98). -/
def REAL_RAT_LE_CONV  : ioconv := RRel.REAL_RAT_LE_CONV
/-- `REAL_RAT_LT_CONV` (calc_rat.ml 117). -/
def REAL_RAT_LT_CONV  : ioconv := RRel.REAL_RAT_LT_CONV
/-- `REAL_RAT_GE_CONV` (calc_rat.ml 138). -/
def REAL_RAT_GE_CONV  : ioconv := RRel.REAL_RAT_GE_CONV
/-- `REAL_RAT_GT_CONV` (calc_rat.ml 141). -/
def REAL_RAT_GT_CONV  : ioconv := RRel.REAL_RAT_GT_CONV
/-- `REAL_RAT_EQ_CONV` (calc_rat.ml 144); also `RING_EQ_CONV` for `REAL_RING`. -/
def REAL_RAT_EQ_CONV  : ioconv := RRel.REAL_RAT_EQ_CONV
/-- `REAL_RAT_SGN_CONV` (calc_rat.ml 163). -/
def REAL_RAT_SGN_CONV : ioconv := RRel.REAL_RAT_SGN_CONV
/-- `REAL_RAT_NEG_CONV` (calc_rat.ml 175). -/
def REAL_RAT_NEG_CONV : ioconv := RUn.REAL_RAT_NEG_CONV
/-- `REAL_RAT_ABS_CONV` (calc_rat.ml 194). -/
def REAL_RAT_ABS_CONV : ioconv := RUn.REAL_RAT_ABS_CONV
/-- `REAL_RAT_INV_CONV` (calc_rat.ml 205). -/
def REAL_RAT_INV_CONV : ioconv := RUn.REAL_RAT_INV_CONV
/-- `REAL_RAT_ADD_CONV` (calc_rat.ml 233). -/
def REAL_RAT_ADD_CONV : ioconv := RAr.REAL_RAT_ADD_CONV
/-- `REAL_RAT_SUB_CONV` (calc_rat.ml 279). -/
def REAL_RAT_SUB_CONV : ioconv := RAr.REAL_RAT_SUB_CONV
/-- `REAL_RAT_MUL_CONV` (calc_rat.ml 290). -/
def REAL_RAT_MUL_CONV : ioconv := RAr.REAL_RAT_MUL_CONV
/-- `REAL_RAT_DIV_CONV` (calc_rat.ml 351). -/
def REAL_RAT_DIV_CONV : ioconv := RAr.REAL_RAT_DIV_CONV
/-- `REAL_RAT_POW_CONV` (calc_rat.ml 362). -/
def REAL_RAT_POW_CONV : ioconv := RPmm.REAL_RAT_POW_CONV
/-- `REAL_RAT_MAX_CONV` (calc_rat.ml 375). -/
def REAL_RAT_MAX_CONV : ioconv := RPmm.REAL_RAT_MAX_CONV
/-- `REAL_RAT_MIN_CONV` (calc_rat.ml 380). -/
def REAL_RAT_MIN_CONV : ioconv := RPmm.REAL_RAT_MIN_CONV

/- compute.ml helpers (as CalcNum/RealAx keep them, re-derived here because
   they are `private` there).  `monitoring`/`stoppers` are the Arith-layer
   refs. -/

private def pt (s : String) : IO term := ioOk' s!"parse {s}" (HolCore.Parser.parse_term s)


/-- `real_rat_red_conv_list` (calc_rat.ml 389-405).  Built once; holds `ioconv`
    closures, so it lives in a plain `Option` ref seeded by the forcing block
    `ensureRealRatRedProcs` below. -/
initialize theRealRatRedConvList : IO.Ref (Option (List (term × ioconv))) ← IO.mkRef none

private def realRatRedConvListIO : IO (Except String (List (term × ioconv))) := do
  match ← theRealRatRedConvList.get with
  | some l => return .ok l
  | none =>
    match ← (HolMath.CalcRat.real_rat_red_conv_list RRel RUn RAr RPmm).run with
    | .ok l => do theRealRatRedConvList.set (some l); return .ok l
    | .error e => return .error e

/-- `real_rat_red_conv_list` (calc_rat.ml 389-405), built once. -/
def real_rat_red_conv_list : IO (Except String (List (term × ioconv))) :=
  realRatRedConvListIO

/-- Cache for `REAL_RAT_RED_CONV` (calc_rat.ml 407): one reduction step over a
    SNAPSHOT of `basic_net()` extended with the sixteen conversions.  The OCaml
    snapshots `basic_net()` once when the conversion is defined; this `IO.Ref`
    reproduces that evaluate-once semantics. -/
initialize theRealRatRed : IO.Ref (Option ioconv) ← IO.mkRef none

private def realRatRedIO : IO (Except String ioconv) := do
  match ← theRealRatRed.get with
  | some c => return .ok c
  | none =>
    match ← (do HolMath.CalcRat.REAL_RAT_RED_CONV (← ExceptT.mk realRatRedConvListIO)).run with
    | .ok c => do theRealRatRed.set (some c); return .ok c
    | .error e => return .error s!"REAL_RAT_RED_CONV: {e}"

/-- `REAL_RAT_RED_CONV` (calc_rat.ml 407). -/
def REAL_RAT_RED_CONV : ioconv := fun tm => do
  match ← realRatRedIO with
  | .ok c => c tm
  | .error e => return .error e

/-- `REAL_RAT_REDUCE_CONV` (calc_rat.ml 412): `DEPTH_CONV REAL_RAT_RED_CONV`.
    The entry point `REAL_FIELD` relies on, so it must work standalone. -/
def REAL_RAT_REDUCE_CONV : ioconv := Simp.depthConvIO REAL_RAT_RED_CONV

/-- `REAL_RAT_REDUCE_TAC`: `CONV_TAC REAL_RAT_REDUCE_CONV`. -/
def REAL_RAT_REDUCE_TAC : tactic := Tactics.CONV_TAC B REAL_RAT_REDUCE_CONV

/-- `real_rat_compute_add_convs` (calc_rat.ml 414): register the sixteen
    conversions with a `compset`. -/
def real_rat_compute_add_convs (cs : HolMath.Compute.compset) :
    IO (Except String Unit) :=
  (do HolMath.CalcRat.real_rat_compute_add_convs (← ExceptT.mk realRatRedConvListIO) cs).run

/-- Cache for `REAL_RAT_COMPUTE_CONV` (calc_rat.ml 421): call-by-value
    reduction over the boolean compset extended with the sixteen conversions.
    The OCaml builds its compset once, so memoise. -/
initialize theRealRatCompute : IO.Ref (Option ioconv) ← IO.mkRef none

private def realRatComputeIO : IO (Except String ioconv) := do
  match ← theRealRatCompute.get with
  | some c => return .ok c
  | none =>
    match ← realRatRedConvListIO with
    | .error e => return .error e
    | .ok cl =>
      match ← (HolMath.CalcRat.REAL_RAT_COMPUTE_CONV cl bool_compset WEAK_CBV_CONV).run with
      | .ok c => do theRealRatCompute.set (some c); return .ok c
      | .error e => return .error s!"REAL_RAT_COMPUTE_CONV: {e}"

/-- `REAL_RAT_COMPUTE_CONV` (calc_rat.ml 421). -/
def REAL_RAT_COMPUTE_CONV : ioconv := fun tm => do
  match ← realRatComputeIO with
  | .ok c => c tm
  | .error e => return .error e

/-- `RealPolyConvs1` (calc_rat.ml 428-438): the six rational normalizer
    conversions.  Instantiated with `is_ratconst`, so rational constants
    become foldable coefficients (this is why the final `REAL_ARITH` beats
    realarith.ml's on `/ &2`-style goals). -/
initialize realPolyConvs1Layer : HolMath.CalcRat.RealPolyConvs1 ←
  ioOk' "setupRealPolyConvs1" (HolMath.CalcRat.setupRealPolyConvs1 RaL RAr RPmm
    TRUTH NmzP.2 num_CONV
    NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV).run

def Q1 : HolMath.CalcRat.RealPolyConvs1 := realPolyConvs1Layer

/-- Cache for `REAL_POLY_CONV` (calc_rat.ml 443-485): the SECOND normalizer,
    extending the first to `inv`, division by rational constants, and the
    abs/max/min wrappers.  Holds an `ioconv` closure, so a plain `Option` ref. -/
initialize theRealPolyConv2 : IO.Ref (Option ioconv) ← IO.mkRef none

private def realPolyConv2IO : IO (Except String ioconv) := do
  match ← theRealPolyConv2.get with
  | some c => return .ok c
  | none =>
    match ← (HolMath.CalcRat.setupRealPolyConv2 Rl RUn Q1).run with
    | .ok c => do theRealPolyConv2.set (some c); return .ok c
    | .error e => return .error s!"REAL_POLY_CONV: {e}"

/-- `REAL_POLY_CONV` (the calc_rat.ml 443 redefinition, the
    `RING_NORMALIZE_CONV` for `REAL_RING`/`GEN_REAL_ARITH3`). -/
def REAL_POLY_CONV : ioconv := fun tm => do
  match ← realPolyConv2IO with
  | .ok c => c tm
  | .error e => return .error e

/- The six first-normalizer polynomial conversions (calc_rat.ml 431). -/

/-- `REAL_POLY_NEG_CONV` (calc_rat.ml 431). -/
def REAL_POLY_NEG_CONV : ioconv := Q1.polys.POLYNOMIAL_NEG_CONV
/-- `REAL_POLY_ADD_CONV` (calc_rat.ml 431). -/
def REAL_POLY_ADD_CONV : ioconv := Q1.polys.POLYNOMIAL_ADD_CONV
/-- `REAL_POLY_SUB_CONV` (calc_rat.ml 431). -/
def REAL_POLY_SUB_CONV : ioconv := Q1.polys.POLYNOMIAL_SUB_CONV
/-- `REAL_POLY_MUL_CONV` (calc_rat.ml 431). -/
def REAL_POLY_MUL_CONV : ioconv := Q1.polys.POLYNOMIAL_MUL_CONV
/-- `REAL_POLY_POW_CONV` (calc_rat.ml 431). -/
def REAL_POLY_POW_CONV : ioconv := Q1.polys.POLYNOMIAL_POW_CONV

/-- `RealRingConvs` (calc_rat.ml 487-533): `REAL_RING`, `real_ideal_cofactors`,
    `REAL_IDEAL_CONV`.  The two nested `prove`s (`REAL_INTEGRAL`,
    `REAL_RABINOWITSCH`) use the EARLIER `REAL_ARITH` (`REAL_ARITH2`), the
    non-circular choice.  This setup must be built while `:real` is still the
    schematic default (its `REAL_INTEGRAL` proof ends in REAL_ARITH_TAC). -/
initialize realRingLayer : HolMath.CalcRat.RealRingConvs ←
  ioOk' "setupRealRing" (HolMath.CalcRat.setupRealRing RSyn RRel REAL_POLY_CONV Dec Nm.numK
    MULT_CLAUSES EQ_ADD_LCANCEL
    REAL_OF_NUM_EQ REAL_OF_NUM_ADD REAL_OF_NUM_MUL
    REAL_SUB_0 REAL_ENTIRE REAL_MUL_RINV REAL_MUL_LZERO
    REAL_ARITH2 MESON_TAC
    PRESIMP_CONV CONDS_ELIM_CONV NNF_CONV WEAK_DNF_CONV
    T.AND_FORALL_THM T.LEFT_AND_FORALL_THM T.RIGHT_AND_FORALL_THM
    C.LEFT_OR_FORALL_THM C.RIGHT_OR_FORALL_THM T.OR_EXISTS_THM
    T.LEFT_OR_EXISTS_THM T.RIGHT_OR_EXISTS_THM T.LEFT_AND_EXISTS_THM
    T.RIGHT_AND_EXISTS_THM
    GrG TRUTH).run

def RRing : HolMath.CalcRat.RealRingConvs := realRingLayer

/-- `REAL_RING tm` (calc_rat.ml 490/514): the ring decision procedure. -/
def REAL_RING : term → IO (Except String thm) := RRing.REAL_RING
/-- `real_ideal_cofactors tms tm` (calc_rat.ml 490/515). -/
def real_ideal_cofactors : List term → term → IO (Except String (List term)) :=
  RRing.real_ideal_cofactors
/-- `REAL_IDEAL_CONV tms tm` (calc_rat.ml 524). -/
def REAL_IDEAL_CONV : List term → term → IO (Except String thm) :=
  RRing.REAL_IDEAL_CONV

/-- `FinalRealArith` (calc_rat.ml 534-559): `GEN_REAL_ARITH3`, `REAL_ARITH3`,
    `REAL_ARITH_TAC2`, `ASM_REAL_ARITH_TAC`.  These are the FINAL versions and
    SUPERSEDE realarith.ml's `REAL_ARITH2` / real.ml's `REAL_ARITH_TAC`.  Needs
    `GrA2` (`genRealArith2Ctx`, built at load by RealAx's
    `ensureRealAxProcs`); built while `:real` is the schematic default. -/
initialize finalRealArithLayer : HolMath.CalcRat.FinalRealArith ←
  ioOk' "setupFinalRealArith" (do
    let GrA2 := genRealArith2Ctx
    HolMath.CalcRat.setupFinalRealArith nnfPths GrA1 GrA2
      PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV
      WEAK_DNF_CONV RSyn RRel Q1 REAL_POLY_CONV Dec
      REAL_LINEAR_PROVER).run

def FRA : HolMath.CalcRat.FinalRealArith := finalRealArithLayer

/-- The `calc_rat.ml` final real-arithmetic bundle (534-559). -/
def finalRealArith : HolMath.CalcRat.FinalRealArith := FRA

/-- `GEN_REAL_ARITH3 PROVER tm` (calc_rat.ml 537): the FINAL, one-parameter
    `GEN_REAL_ARITH`.  SUPERSEDES `GEN_REAL_ARITH1`/`GEN_REAL_ARITH2`. -/
def GEN_REAL_ARITH3 :
    (((List thm × List thm × List thm) →
      HolMath.RealArith.positivstellensatz → IO (Except String thm)) →
     (List thm × List thm × List thm) → IO (Except String thm)) →
    term → IO (Except String thm) := FRA.GEN_REAL_ARITH3

/-- `REAL_ARITH3 tm` (calc_rat.ml 544): the FINAL real decision procedure.
    SUPERSEDES realarith.ml's `REAL_ARITH2`; this is the `REAL_ARITH` general
    code should now use. -/
def REAL_ARITH3 : term → IO (Except String thm) := FRA.REAL_ARITH3

/-- `REAL_ARITH_TAC2` (calc_rat.ml 553): `CONV_TAC REAL_ARITH3`.  SUPERSEDES
    real.ml 106's `REAL_ARITH_TAC`. -/
def REAL_ARITH_TAC2 : tactic := FRA.REAL_ARITH_TAC2

/-- `ASM_REAL_ARITH_TAC` (calc_rat.ml 555): move the non-universal assumptions
    into the goal, then `REAL_ARITH_TAC2`.  First appears here. -/
def ASM_REAL_ARITH_TAC : tactic := FRA.ASM_REAL_ARITH_TAC

/- HOL Light's names for the final versions.  HOL Light's later definitions
   replace the earlier ones; here the plain names are the final versions and
   the numbered ones stay available: GEN_REAL_ARITH1/2 and REAL_ARITH1/2
   (realarith.ml), REAL_ARITH_TAC1 (real.ml), and GEN_REAL_ARITH3,
   REAL_ARITH3 and REAL_ARITH_TAC2 (the same functions as below). -/
/-- `GEN_REAL_ARITH` (calc_rat.ml 537), the final version: `GEN_REAL_ARITH3`. -/
def GEN_REAL_ARITH :
    (((List thm × List thm × List thm) →
      HolMath.RealArith.positivstellensatz → IO (Except String thm)) →
     (List thm × List thm × List thm) → IO (Except String thm)) →
    term → IO (Except String thm) := GEN_REAL_ARITH3
/-- `REAL_ARITH` (calc_rat.ml 544), the final version: `REAL_ARITH3`. -/
def REAL_ARITH : term → IO (Except String thm) := REAL_ARITH3
/-- `REAL_ARITH_TAC` (calc_rat.ml 553), the final version: `REAL_ARITH_TAC2`. -/
def REAL_ARITH_TAC : tactic := REAL_ARITH_TAC2

/-- `RealFieldTrans` (calc_rat.ml 560-577): the three equivalential
    transitivity forms.  Uses this file's FINAL `REAL_ARITH` (`REAL_ARITH3`). -/
initialize realFieldTransLayer : HolMath.CalcRat.RealFieldTrans ←
  ioOk' "setupRealFieldTrans" (HolMath.CalcRat.setupRealFieldTrans Rl MESON_TAC REAL_ARITH3).run

def RFT : HolMath.CalcRat.RealFieldTrans := realFieldTransLayer

/-- Cache for `REAL_FIELD` (calc_rat.ml 581-630): the field decision procedure,
    for goals genuinely needing division and nonzero-denominator side
    conditions that `REAL_RING` alone cannot prove.  `core_rule` falls back to
    `REAL_ARITH3` when `REAL_RING` fails.  Holds an `ioconv` closure, so a plain
    `Option` ref seeded by the forcing block below. -/
initialize theRealField : IO.Ref (Option (term → IO (Except String thm))) ← IO.mkRef none

private def realFieldIO : IO (Except String (term → IO (Except String thm))) := do
  match ← theRealField.get with
  | some f => return .ok f
  | none =>
    match ← (HolMath.CalcRat.setupRealField Rl RT6 RT7
               NNF_CONV NNFC_CONV WEAK_CNF_CONV CONJ_CANON_CONV PRENEX_CONV
               CONDS_CELIM_CONV NUM_REDUCE_CONV REAL_RAT_REDUCE_CONV
               REAL_RING REAL_ARITH3 MESON).run with
    | .ok f => do theRealField.set (some f); return .ok f
    | .error e => return .error s!"REAL_FIELD: {e}"

/-- `REAL_FIELD tm` (calc_rat.ml 581-630). -/
def REAL_FIELD : term → IO (Except String thm) := fun tm => do
  match ← realFieldIO with
  | .ok f => f tm
  | .error e => return .error e

/-- calc_rat.ml 581: build `REAL_FIELD` here, before the RealShrink theorems
    (631-688).  Its setup's MESON calls then print where HOL Light's do. -/
initialize realFieldLayer : Unit ← do
  match ← realFieldIO with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"REAL_FIELD setup: {e}")

/-- `RealShrink` (calc_rat.ml 631-688): the eight monotone-mapping theorems
    between R and (-1,1). -/
initialize realShrinkLayer : HolMath.CalcRat.RealShrink ←
  ioOk' "setupRealShrink" (HolMath.CalcRat.setupRealShrink Rl CiT RaL RT6 RT7
    REAL_ARITH3 REAL_FIELD MESON MESON_TAC).run

def RShr : HolMath.CalcRat.RealShrink := realShrinkLayer

/-- The `calc_rat.ml` transitivity forms (560-577). -/
def realFieldTrans : HolMath.CalcRat.RealFieldTrans := RFT
/-- The `calc_rat.ml` monotone-mapping theorems (631-688). -/
def realShrink : HolMath.CalcRat.RealShrink := RShr

/- The calc_rat.ml theorems as bare names, as HOL Light has them. -/
def RAT_LEMMA1          : thm := RatLm.RAT_LEMMA1
def RAT_LEMMA2          : thm := RatLm.RAT_LEMMA2
def RAT_LEMMA3          : thm := RatLm.RAT_LEMMA3
def RAT_LEMMA4          : thm := RatLm.RAT_LEMMA4
def RAT_LEMMA5          : thm := RatLm.RAT_LEMMA5
def DECIMAL             : thm := Dec
def REAL_LE_TRANS_LE    : thm := RFT.REAL_LE_TRANS_LE
def REAL_LE_TRANS_LTE   : thm := RFT.REAL_LE_TRANS_LTE
def REAL_LE_TRANS_LT    : thm := RFT.REAL_LE_TRANS_LT
def REAL_SHRINK_RANGE   : thm := RShr.REAL_SHRINK_RANGE
def REAL_SHRINK_LT      : thm := RShr.REAL_SHRINK_LT
def REAL_SHRINK_LE      : thm := RShr.REAL_SHRINK_LE
def REAL_SHRINK_EQ      : thm := RShr.REAL_SHRINK_EQ
def REAL_SHRINK_GALOIS  : thm := RShr.REAL_SHRINK_GALOIS
def REAL_GROW_SHRINK    : thm := RShr.REAL_GROW_SHRINK
def REAL_SHRINK_GROW_EQ : thm := RShr.REAL_SHRINK_GROW_EQ
def REAL_SHRINK_GROW    : thm := RShr.REAL_SHRINK_GROW

/-- `REAL_INTEGRAL` (calc_rat.ml 491), proved by the REAL_RING setup. -/
def REAL_INTEGRAL : thm := RRing.REAL_INTEGRAL
/-- `REAL_RABINOWITSCH` (calc_rat.ml 500), proved by the REAL_RING setup. -/
def REAL_RABINOWITSCH : thm := RRing.REAL_RABINOWITSCH

/- ---------------------------------------------------------------------- -/
/- calc_rat.ml 407/414: REAL_RAT_RED_CONV and REAL_RAT_COMPUTE_CONV, built
   last, after the `real` overloads of this region are current, so their
   `basic_net()` snapshot is taken here.  (REAL_FIELD was built above, by
   `realFieldLayer`; the check below only confirms it.) -/
/- ---------------------------------------------------------------------- -/
initialize ensureRealProcs : Unit ← do
  match ← realFieldIO with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"REAL_FIELD setup: {e}")
  match ← realRatRedIO with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"REAL_RAT_RED_CONV setup: {e}")
  match ← realRatComputeIO with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"REAL_RAT_COMPUTE_CONV setup: {e}")


end Session
