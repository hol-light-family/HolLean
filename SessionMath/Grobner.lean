/- File: SessionMath/Grobner.lean
grobner.ml: the Grobner-basis ring and ideal procedure for the naturals,
built by `initialize` when this module is imported.  NUM_SIMPLIFY_CONV and
NUM_RING are closures, kept in `IO.Ref`s.  At the end, `ensureCalcNumProcs`
builds them (NUM_SIMPLIFY_CONV, then NUM_RING), before realax.ml registers
the `real` overloads, as in HOL Light.
-/
import SessionMath.Normalizer
import HolMath.Grobner

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic

namespace Session

private def ioOk' {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")

private def pt (s : String) : IO term := ioOk' s!"parse {s}" (HolCore.Parser.parse_term s)

/- grobner.ml : the Grobner-basis ring/ideal decision procedure.          -/
/- ---------------------------------------------------------------------- -/

/-- The `NUM_SIMPLIFY_CONV`-local constants (grobner.ml 628-650):
    `pre_tm`/`div_tm`/`mod_tm`/`sub_tm` recovered from the elimination
    theorems, the three primed'' theorems (`CONV_RULE(RAND_CONV NNF_CONV)`) and
    `pth_evenodd`. -/
initialize NsC : HolMath.Grobner.NumSimplifyConsts ←
  ioOk' "setupNumSimplifyConsts" (HolMath.Grobner.setupNumSimplifyConsts NNF_CONV
    PRE_ELIM_THM SUB_ELIM_THM DIVMOD_ELIM_THM
    PRE_ELIM_THM' SUB_ELIM_THM' DIVMOD_ELIM_THM'
    NOT_EXISTS_THM EVEN_EXISTS ODD_EXISTS NOT_EVEN NOT_ODD).run

/-- `NUM_MULTIPLY_CONV pos tm` (grobner.ml 651-687). -/
def NUM_MULTIPLY_CONV (pos : Bool) (tm : term) : IO (Except String thm) :=
  HolMath.Grobner.numMultiplyConv NsC pos tm

/-- Cache for the assembled `NUM_SIMPLIFY_CONV` ioconv (grobner.ml 651-703). -/
initialize theNumSimplifyConv : IO.Ref (Option ioconv) ← IO.mkRef none

private def numSimplifyConvIO : IO (Except String ioconv) := do
  match ← theNumSimplifyConv.get with
  | some c => return .ok c
  | none =>
    match ← (HolMath.Grobner.NUM_SIMPLIFY_CONV NsC
               NUM_REDUCE_CONV CONDS_CELIM_CONV NNF_CONV).run with
    | .error e => return .error e
    | .ok c => do theNumSimplifyConv.set (some c); return .ok c

/-- `NUM_SIMPLIFY_CONV tm` (grobner.ml 651-703): the six-link `THENC` chain
    `NUM_REDUCE_CONV THENC CONDS_CELIM_CONV THENC NNF_CONV THENC
     NUM_MULTIPLY_CONV true THENC NUM_REDUCE_CONV THENC
     GEN_REWRITE_CONV ONCE_DEPTH_CONV [pth_evenodd]`. -/
def NUM_SIMPLIFY_CONV : ioconv := fun tm => do
  match ← numSimplifyConvIO with
  | .ok c => c tm
  | .error e => return .error e

/-- `NUM_INTEGRAL_LEMMA` (grobner.ml 708-715). -/
initialize NUM_INTEGRAL_LEMMA : thm ←
  ioOk' "NUM_INTEGRAL_LEMMA" (HolMath.Grobner.NUM_INTEGRAL_LEMMA ADD_AC
    LEFT_ADD_DISTRIB RIGHT_ADD_DISTRIB ADD_ASSOC
    EQ_ADD_LCANCEL EQ_ADD_LCANCEL_0 MULT_EQ_0).run

/-- `NUM_INTEGRAL` (grobner.ml 716-726). -/
initialize NUM_INTEGRAL : thm ←
  ioOk' "NUM_INTEGRAL" (HolMath.Grobner.NUM_INTEGRAL ASM_MESON_TAC
    NUM_INTEGRAL_LEMMA MULT_CLAUSES EQ_ADD_LCANCEL LE_CASES
    LE_EXISTS ADD_SYM MULT_SYM).run

/-- The natural-number `RingParms` bundle (grobner.ml 727-732).
    `ring_dest_const = dest_numeral`, `ring_mk_const = mk_numeral`,
    `RING_EQ_CONV = NUM_EQ_CONV`, `add/mul/pow_tm` are the genuine `num`
    constants, the neg/sub/inv/div slots are fresh `genvar bool_ty` dummies,
    `RING_INTEGRAL = NUM_INTEGRAL`, `RABINOWITSCH_THM = TRUTH` (selects the
    SCALED runner), and `RING_NORMALIZE_CONV = NUM_NORMALIZE_CONV`. -/
initialize NRP : HolMath.Grobner.RingParms ← do
  -- grobner.ml 727-732 parses the three operators; OCaml builds the
  -- argument tuple right to left.
  let exp_tm ← pt "(EXP):num->num->num"
  let mul_tm ← pt "(*):num->num->num"
  let add_tm ← pt "(+):num->num->num"
  HolMath.Grobner.numRingParms Nm.numK NUM_EQ_CONV NUM_NORMALIZE_CONV
    add_tm mul_tm exp_tm NUM_INTEGRAL TRUTH

/-- The natural-number `RingParms` bundle (grobner.ml 727-732). -/
def numRingParms : HolMath.Grobner.RingParms := NRP

/-- The parameter-independent part of `RING_AND_IDEAL_CONV` (grobner.ml
    336-354): `pth_step`, `FINAL_RULE`, `false_tm`. -/
initialize GrG : HolMath.Grobner.GrobnerGlobals ←
  ioOk' "setupGrobnerGlobals" (HolMath.Grobner.setupGrobnerGlobals DE_MORGAN_THM CONTRAPOS_THM).run

/-- What `RING_AND_IDEAL_CONV` builds from the natural-number parameters
    (grobner.ml 364-465). -/
initialize NRC : HolMath.Grobner.RingCtx ←
  ioOk' "setupRingCtx (num)" (HolMath.Grobner.setupRingCtx GrG Nm.numK (concl TRUTH)
    PRESIMP_CONV CONDS_ELIM_CONV NNF_CONV WEAK_DNF_CONV
    T.AND_FORALL_THM T.LEFT_AND_FORALL_THM T.RIGHT_AND_FORALL_THM
    C.LEFT_OR_FORALL_THM C.RIGHT_OR_FORALL_THM T.OR_EXISTS_THM
    T.LEFT_OR_EXISTS_THM T.RIGHT_OR_EXISTS_THM T.LEFT_AND_EXISTS_THM
    T.RIGHT_AND_EXISTS_THM NRP).run

/-- `RING` at the natural-number parameters (grobner.ml 582-601); the
    `rawring` of `NUM_RING`. -/
def RING (tm : term) : IO (Except String thm) :=
  HolMath.Grobner.RING NRC tm

/-- `ideal_cofactors` at the natural-number parameters (grobner.ml 618). -/
def ideal_cofactors (tms : List term) (tm : term) :
    IO (Except String (List term)) :=
  HolMath.Grobner.ideal_cofactors NRC tms tm

/-- `grobner_ideal vars pols pol` (grobner.ml 304-308), exposed for direct
    testing. -/
def grobner_ideal (vars : List term) (pols : List HolMath.Grobner.poly)
    (pol : HolMath.Grobner.poly) :
    IO (Except String (List (Int × HolMath.Grobner.poly))) :=
  (HolMath.Grobner.grobner_ideal vars pols pol).run

/-- Cache for `NUM_RING` (grobner.ml 707-737). -/
initialize theNumRing : IO.Ref (Option ioconv) ← IO.mkRef none

private def numRingIO : IO (Except String ioconv) := do
  match ← theNumRing.get with
  | some c => return .ok c
  | none =>
    match ← (HolMath.Grobner.NUM_RING NUM_SIMPLIFY_CONV ADD1 RING).run with
    | .error e => return .error e
    | .ok c => do theNumRing.set (some c); return .ok c

/-- `NUM_RING tm` (grobner.ml 707-737). -/
def NUM_RING : ioconv := fun tm => do
  match ← numRingIO with
  | .ok c => c tm
  | .error e => return .error e

/- ---------------------------------------------------------------------- -/
/- The conversions of grobner.ml, built at its end.  The bundle
   `initialize`s above already ran (NsC, NUM_INTEGRAL, NRP, GrG, NRC) in
   declaration order; this fills the closure-holding refs: NUM_SIMPLIFY_CONV,
   NUM_RING.  NUM_RING is built here, before realax.ml registers the `real`
   overloads, as in HOL Light. -/
/- ---------------------------------------------------------------------- -/
initialize ensureCalcNumProcs : Unit ← do
  -- (calc_num.ml's NUM_REL_CONV, NUM_RED_CONV and NUM_COMPUTE_CONV were built
  -- at the end of SessionMath/CalcNum.lean.)
  -- grobner.ml: NUM_RING's setup proofs search over the registered overloads,
  -- so it must be built before realax.ml adds the `real` ones.
  match ← numSimplifyConvIO with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"NUM_SIMPLIFY_CONV setup: {e}")
  match ← numRingIO with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"NUM_RING setup: {e}")

end Session
