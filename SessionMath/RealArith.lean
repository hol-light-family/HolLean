/- File: SessionMath/RealArith.lean
realarith.ml: the universal linear real decision procedure, built by
`initialize` when this module is imported.  At the end, `ensureRealAxProcs`
builds realarith.ml's conversions (the second framework and REAL_ARITH2).
-/
import SessionMath.CalcInt
import HolMath.RealArith

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic

namespace Session

private def ioOk' {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")

private def pt (s : String) : IO term := ioOk' s!"parse {s}" (HolCore.Parser.parse_term s)

/- ---------------------------------------------------------------------- -/
/- realarith.ml: universal linear real decision procedure.                 -/
/-                                                                        -/
/- Six layers, in realarith.ml's own order.  Each `setupX` takes the       -/
/- previous layers' records as parameters, reproduced by `initialize`       -/
/- declaration order.  The ONE non-structural dependency is that            -/
/- `setupGenRealArith2Ctx` proves its 42-clause ABSMAXMIN proforma by       -/
/- running the fully-applied bootstrapping `realArith1Closure` — which is   -/
/- the whole reason HOL Light defines REAL_ARITH twice.  The order is       -/
/- therefore  L -> G -> A -> RA1 -> (realArith1Closure) -> G2 -> RA2.       -/
/- ---------------------------------------------------------------------- -/

/- `RealArith1Ctx`/`RealArith2Ctx`/`PolynomialConvs` carry only
   `ioconv`/polynomial-conversion fields and are NOT declared `Inhabited` in
   the pure library, but an `initialize` constant of that type needs an
   `Inhabited`/`Nonempty` fallback.  Every field is ultimately an `ioconv` (a
   function into `IO`, hence inhabited), so Lean can derive these. -/
deriving instance Inhabited for HolMath.Normalizer.PolynomialConvs
deriving instance Inhabited for HolMath.RealArith.RealArith1Ctx
deriving instance Inhabited for HolMath.RealArith.RealArith2Ctx
deriving instance Inhabited for HolMath.RealArith.GenRealArith2Ctx

/-- REAL_LINEAR_PROVER's constants: linear_ineqs' `&1` (realarith.ml 388),
    then lin_of_hol's `&1`, `&0`, `(+):real->real->real`,
    `(*):real->real->real` (realarith.ml 446-449).  Parsed once, at
    realarith.ml's position, where `&` means `real_of_num`. -/
initialize realArithConstsLayer : term × term × term × term × term ← do
  -- realarith.ml 446-447 parse them untyped.
  let lpOne ← pt "&1"
  let one  ← pt "&1"
  let zero ← pt "&0"
  let add  ← pt "(+):real->real->real"
  let mul  ← pt "(*):real->real->real"
  pure (lpOne, one, zero, add, mul)

def RaC : term × term × term × term × term := realArithConstsLayer

/-- The twenty-nine driving lemmas (realarith.ml 16-160). -/
initialize realArithLemmasLayer : HolMath.RealArith.RealArithLemmas ←
  ioOk' "setupRealArithLemmas" (HolMath.RealArith.setupRealArithLemmas arith2 arith3 CiT Rl
    MESON_TAC num_CONV).run

def RaL : HolMath.RealArith.RealArithLemmas := realArithLemmasLayer

/-- `GenRealArith1Ctx` (realarith.ml 185-256): the six proformas and the term
    constants of the bootstrapping framework. -/
initialize genRealArith1Layer : HolMath.RealArith.GenRealArith1Ctx ←
  ioOk' "setupGenRealArith1Ctx" (HolMath.RealArith.setupGenRealArith1Ctx CiT Rl RaL MESON_TAC).run

def GrA1 : HolMath.RealArith.GenRealArith1Ctx := genRealArith1Layer

/-- `LinearProverAliens` (realarith.ml 477-479): the two alien lemmas. -/
initialize linearProverAliensLayer : HolMath.RealArith.LinearProverAliens ←
  ioOk' "setupLinearProverAliens" (HolMath.RealArith.setupLinearProverAliens Rl RaL).run

def LpA : HolMath.RealArith.LinearProverAliens := linearProverAliensLayer

/-- `RealArith1Ctx` (realarith.ml 495-509): the six polynomial conversions and
    `deabs_conv` of the bootstrapping instance. -/
initialize realArith1CtxLayer : HolMath.RealArith.RealArith1Ctx ←
  ioOk' "setupRealArith1Ctx" (HolMath.RealArith.setupRealArith1Ctx Rl RaL
    TRUTH NmzP.2 num_CONV
    is_realintconst
    REAL_INT_ADD_CONV REAL_INT_MUL_CONV REAL_INT_POW_CONV
    NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV).run

def RA1c : HolMath.RealArith.RealArith1Ctx := realArith1CtxLayer

/-- `REAL_LINEAR_PROVER` (realarith.ml 385-489), with its `RatSyntax`, alien
    lemmas and `lin_of_hol` constants supplied. -/
def REAL_LINEAR_PROVER : HolMath.RealArith.PsProver :=
  let (lp_one_tm, one_tm, zero_tm, add_tm, mul_tm) := RaC
  HolMath.RealArith.REAL_LINEAR_PROVER RSyn LpA lp_one_tm one_tm zero_tm add_tm mul_tm

/-- Cache for the first `REAL_ARITH` (realarith.ml 494-511): the BOOTSTRAPPING
    decision procedure.  Holds an `ioconv` closure, so it lives in a plain
    `Option` ref seeded (together with the two abs/max/min contexts it forces)
    by `ensureRealAxProcs` below. -/
initialize theRealArith1 : IO.Ref (Option ioconv) ← IO.mkRef none

/-- The first `REAL_ARITH` (realarith.ml 494-511).  It proves
    `setupGenRealArith2Ctx`'s ABSMAXMIN proforma. -/
private def realArith1Closure : ioconv := fun tm => do
  match ← theRealArith1.get with
  | some c => c tm
  | none =>
    match ← (HolMath.RealArith.REAL_ARITH1 Cn.nnf GrA1 RA1c
               PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV WEAK_DNF_CONV
               mk_realintconst REAL_INT_EQ_CONV REAL_INT_GE_CONV REAL_INT_GT_CONV
               REAL_LINEAR_PROVER).run with
    | .error e => return .error e
    | .ok c => do theRealArith1.set (some c); c tm

/-- Cache for `GenRealArith2Ctx` (realarith.ml 518-641): the two hardwired
    abs/max/min elimination conversions and the three `pth`s.

    THIS LAYER IS EXPENSIVE — about 8.8 seconds — because its 42-clause
    ABSMAXMIN proforma is proved by the full linear decision procedure
    (`realArith1Closure`).  HOL Light itself wraps that proof in `time` for the
    same reason.  Forced by `ensureRealAxProcs` (it is NOT forced by any
    cheaper accessor). -/
initialize theGenRealArith2Ctx : IO.Ref (Option HolMath.RealArith.GenRealArith2Ctx) ←
  IO.mkRef none

private def genRealArith2IO : IO (Except String HolMath.RealArith.GenRealArith2Ctx) := do
  match ← theGenRealArith2Ctx.get with
  | some d => return .ok d
  | none =>
    match ← (HolMath.RealArith.setupGenRealArith2Ctx Rl realArith1Closure).run with
    | .ok d => do theGenRealArith2Ctx.set (some d); return .ok d
    | .error e => return .error e

/-- Cache for `RealArith2Ctx` (realarith.ml 652-657): the six polynomial
    conversions of the second instance (identical semiring recipe to `RA1c`,
    MINUS `deabs_conv`). -/
initialize realArith2CtxLayer : HolMath.RealArith.RealArith2Ctx ←
  ioOk' "setupRealArith2Ctx" (HolMath.RealArith.setupRealArith2Ctx RaL
    TRUTH NmzP.2 num_CONV
    is_realintconst
    REAL_INT_ADD_CONV REAL_INT_MUL_CONV REAL_INT_POW_CONV
    NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV).run

def RA2c : HolMath.RealArith.RealArith2Ctx := realArith2CtxLayer

/- Public accessors for the realarith.ml bundles. -/

/-- The `realarith.ml` twenty-nine driving lemmas (16-160). -/
def realArithLemmas : HolMath.RealArith.RealArithLemmas := RaL
/-- The `realarith.ml` bootstrapping-framework context (185-256). -/
def genRealArith1Ctx : HolMath.RealArith.GenRealArith1Ctx := GrA1
/-- The `realarith.ml` alien lemmas (477-479). -/
def linearProverAliens : HolMath.RealArith.LinearProverAliens := LpA
/-- The `realarith.ml` bootstrapping-instance context (495-509). -/
def realArith1Ctx : HolMath.RealArith.RealArith1Ctx := RA1c
/-- The `realarith.ml` second-instance context (652-657). -/
def realArith2Ctx : HolMath.RealArith.RealArith2Ctx := RA2c

/-- The `GEN_NNF_CONV` auxiliary theorem bundle (`NNFPths`) that
    `GEN_REAL_ARITH1`/`GEN_REAL_ARITH2` need. -/
def nnfPths : HolCore.Canon.NNFPths := Cn.nnf

/-- `positivstellensatz` (realarith.ml 166-177): the refutation-certificate
    datatype. -/
abbrev positivstellensatz := HolMath.RealArith.positivstellensatz

/-- `GEN_REAL_ARITH1` (realarith.ml 185-379): the BOOTSTRAPPING parametrized
    framework, exposed with its ELEVEN caller-supplied parameters (plus `tm`)
    still open. -/
def GEN_REAL_ARITH1
    (mk_numeric : Rat → Except String term)
    (NUMERIC_EQ_CONV NUMERIC_GE_CONV NUMERIC_GT_CONV : ioconv)
    (POLY_CONV POLY_NEG_CONV POLY_ADD_CONV POLY_MUL_CONV : ioconv)
    (absconv1 absconv2 : ioconv)
    (prover : ((List thm × List thm × List thm) →
               HolMath.RealArith.positivstellensatz → IO (Except String thm)) →
              (List thm × List thm × List thm) → IO (Except String thm))
    (tm : term) : IO (Except String thm) := ExceptT.run do
  let rule ← HolMath.RealArith.GEN_REAL_ARITH1 Cn.nnf GrA1
    PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV WEAK_DNF_CONV
    mk_numeric NUMERIC_EQ_CONV NUMERIC_GE_CONV NUMERIC_GT_CONV
    POLY_CONV POLY_NEG_CONV POLY_ADD_CONV POLY_MUL_CONV
    absconv1 absconv2 prover
  ExceptT.mk (rule tm)

/-- `GEN_REAL_ARITH2` (realarith.ml 517-646): the "slightly less parametrized"
    framework with abs/max/min elimination HARDWIRED, exposed with its NINE
    caller-supplied parameters (plus `tm`) still open.  The two abs-elimination
    conversion slots come from `genRealArith2Ctx`, whose ~8.8s ABSMAXMIN proof
    this accessor therefore forces. -/
def GEN_REAL_ARITH2
    (mkconst : Rat → Except String term)
    (EQ GE GT : ioconv)
    (NORM NEG ADD MUL : ioconv)
    (PROVER : ((List thm × List thm × List thm) →
               HolMath.RealArith.positivstellensatz → IO (Except String thm)) →
              (List thm × List thm × List thm) → IO (Except String thm))
    (tm : term) : IO (Except String thm) := ExceptT.run do
  let GrA2 ← ExceptT.mk genRealArith2IO
  let rule ← HolMath.RealArith.GEN_REAL_ARITH2 Cn.nnf GrA1 GrA2
    PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV WEAK_DNF_CONV
    mkconst EQ GE GT NORM NEG ADD MUL PROVER
  ExceptT.mk (rule tm)

/-- `REAL_ARITH1` (realarith.ml 494): the BOOTSTRAPPING decision procedure.
    It exists to prove version 2's 42-clause ABSMAXMIN proforma
    (`genRealArith2Ctx`); it is NOT the procedure general code should call. -/
def REAL_ARITH1 : term → IO (Except String thm) := fun tm => realArith1Closure tm

/-- Cache for the second `REAL_ARITH` (realarith.ml 651).  Holds an `ioconv`
    closure, so it lives in a plain `Option` ref seeded by `ensureRealAxProcs`. -/
initialize theRealArith2 : IO.Ref (Option ioconv) ← IO.mkRef none

private def realArith2IO : IO (Except String ioconv) := do
  match ← theRealArith2.get with
  | some c => return .ok c
  | none =>
    match ← genRealArith2IO with
    | .error e => return .error e
    | .ok GrA2 =>
      match ← (HolMath.RealArith.REAL_ARITH2 Cn.nnf GrA1 GrA2 RA2c
                 PRESIMP_CONV NNF_CONV CONDS_ELIM_CONV SKOLEM_CONV PRENEX_CONV WEAK_DNF_CONV
                 mk_realintconst REAL_INT_EQ_CONV REAL_INT_GE_CONV REAL_INT_GT_CONV
                 REAL_LINEAR_PROVER).run with
      | .error e => return .error e
      | .ok c => do theRealArith2.set (some c); return .ok c

/-- `REAL_ARITH2` (realarith.ml 651): the instance the rest of HOL Light sees
    at this point — abs/max/min eliminated intelligently by the hardwired
    conversions.

    IMPORTANT: this is NOT the final `REAL_ARITH` the full HOL Light system
    exposes.  `calc_rat.ml` (hol_lib.ml line 97) OVERWRITES `REAL_ARITH` A
    THIRD TIME; until that layer is translated, `REAL_ARITH2` is the latest
    version. -/
def REAL_ARITH2 : term → IO (Except String thm) := fun tm => do
  match ← realArith2IO with
  | .ok c => c tm
  | .error e => return .error e


/- The realarith.ml driving lemmas as bare names, as HOL Light has them. -/
def REAL_LTE_TOTAL        : thm := RaL.REAL_LTE_TOTAL
def REAL_LET_TOTAL        : thm := RaL.REAL_LET_TOTAL
def REAL_LT_IMP_LE        : thm := RaL.REAL_LT_IMP_LE
def REAL_LTE_TRANS        : thm := RaL.REAL_LTE_TRANS
def REAL_LET_TRANS        : thm := RaL.REAL_LET_TRANS
def REAL_LT_TRANS         : thm := RaL.REAL_LT_TRANS
def REAL_LE_ADD           : thm := RaL.REAL_LE_ADD
def REAL_LTE_ANTISYM      : thm := RaL.REAL_LTE_ANTISYM
def REAL_SUB_LE           : thm := RaL.REAL_SUB_LE
def REAL_NEG_SUB          : thm := RaL.REAL_NEG_SUB
def REAL_LE_LT            : thm := RaL.REAL_LE_LT
def REAL_SUB_LT           : thm := RaL.REAL_SUB_LT
def REAL_NOT_LT           : thm := RaL.REAL_NOT_LT
def REAL_SUB_0            : thm := RaL.REAL_SUB_0
def REAL_LT_LE            : thm := RaL.REAL_LT_LE
def REAL_LT_REFL          : thm := RaL.REAL_LT_REFL
def REAL_LTE_ADD          : thm := RaL.REAL_LTE_ADD
def REAL_LET_ADD          : thm := RaL.REAL_LET_ADD
def REAL_LT_ADD           : thm := RaL.REAL_LT_ADD
def REAL_ENTIRE           : thm := RaL.REAL_ENTIRE
def REAL_LE_NEGTOTAL      : thm := RaL.REAL_LE_NEGTOTAL
def REAL_LE_SQUARE        : thm := RaL.REAL_LE_SQUARE
def REAL_MUL_RID          : thm := RaL.REAL_MUL_RID
def REAL_POW_2            : thm := RaL.REAL_POW_2
def REAL_POLY_CLAUSES     : thm := RaL.REAL_POLY_CLAUSES
def REAL_POLY_NEG_CLAUSES : thm := RaL.REAL_POLY_NEG_CLAUSES
def REAL_POS              : thm := RaL.REAL_POS
def REAL_LT_NZ            : thm := RaL.REAL_LT_NZ
def REAL_POS_LT           : thm := RaL.REAL_POS_LT

/- ---------------------------------------------------------------------- -/
/- The conversions of realarith.ml, built at their file positions.  The
   bundle `initialize`s above already ran in declaration order (RaL..RA1c,
   RA2c); this fills the closure-holding refs:
     realarith.ml 494-657: realArith1Closure (built when its ref is first
       touched by the ABSMAXMIN proof), the ~8.8s GenRealArith2Ctx, REAL_ARITH2.
   Each proves its proformas while the `real` overloads are current, as in
   HOL Light.  (calc_int.ml's conversions were built at the end of
   SessionMath/CalcInt.lean.) -/
/- ---------------------------------------------------------------------- -/
initialize ensureRealAxProcs : Unit ← do
  -- realarith.ml 494-657: the ~8.8s ABSMAXMIN proof forces realArith1Closure,
  -- then builds REAL_ARITH2.
  match ← genRealArith2IO with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"GenRealArith2Ctx setup: {e}")
  match ← realArith2IO with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"REAL_ARITH2 setup: {e}")

/-- The `realarith.ml` second-framework context (518-641): the two hardwired
    abs/max/min elimination conversions and the three `pth`s.  Built by
    `ensureRealAxProcs` just above (the ~8.8s ABSMAXMIN proof), in file order;
    this reads the result. -/
initialize genRealArith2Layer : HolMath.RealArith.GenRealArith2Ctx ← do
  match ← genRealArith2IO with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"GenRealArith2Ctx setup: {e}")

/-- The `realarith.ml` second-framework context (see `genRealArith2Layer`). -/
def genRealArith2Ctx : HolMath.RealArith.GenRealArith2Ctx := genRealArith2Layer


end Session
