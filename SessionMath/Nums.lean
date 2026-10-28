/- File: SessionMath/Nums.lean
nums.ml: the natural numbers (`numsLayer`, the bundle `Nm`), built by
`initialize` when this module is imported, numerals, `INDUCT_TAC` and
`new_specification`.
-/
import SessionMath.Compute
import HolMath.Nums

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Simp HolCore.Theorems HolCore.Classic

namespace Session

private def ioOk' {α : Type} (what : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"{what}: {e}")


initialize numsLayer : HolMath.Nums.NumsThms ← do
  let t ← ioOk' "setupNums" (HolMath.Nums.setupNums new_definition MESON_TAC SELECT_RULE
    new_inductive_definition prove_inductive_relations_exist).run
  theInductiveTypeStore.modify (("num", (2, t.num_INDUCTION, t.num_RECURSION)) :: ·)
  pure t

def Nm : HolMath.Nums.NumsThms := numsLayer

-- Expose the nums.ml definitions and theorems.
def ONE_ONE          : thm := Nm.ONE_ONE
def ONTO             : thm := Nm.ONTO
def INFINITY_AX      : thm := Nm.INFINITY_AX
def IND_SUC_0_EXISTS : thm := Nm.IND_SUC_0_EXISTS
def IND_SUC_SPEC     : thm := Nm.IND_SUC_SPEC
def IND_SUC_INJ      : thm := Nm.IND_SUC_INJ
def IND_SUC_0        : thm := Nm.IND_SUC_0
def NUM_REP_RULES    : thm := Nm.NUM_REP_RULES
def NUM_REP_INDUCT   : thm := Nm.NUM_REP_INDUCT
def NUM_REP_CASES    : thm := Nm.NUM_REP_CASES
def num_tydef        : thm × thm := Nm.num_tydef
def ZERO_DEF         : thm := Nm.ZERO_DEF
def SUC_DEF          : thm := Nm.SUC_DEF
def NOT_SUC          : thm := Nm.NOT_SUC
def SUC_INJ          : thm := Nm.SUC_INJ
def num_INDUCTION    : thm := Nm.num_INDUCTION
def num_Axiom        : thm := Nm.num_Axiom
def NUMERAL          : thm := Nm.NUMERAL
def num_RECURSION    : thm := Nm.num_RECURSION
def num_CASES        : thm := Nm.num_CASES
def BIT0_DEF         : thm := Nm.BIT0_DEF
def BIT1_DEF         : thm := Nm.BIT1_DEF

/-- `mk_numeral`. -/
def mk_numeral (n : Rat) : Except String term := HolMath.Nums.mk_numeral Nm.numK n
/-- The `num` numeral constants (for library code that builds a Grobner
    `RingCtx`, as ringtheory.ml's `RING_AND_IDEAL_CONV` calls do). -/
def numeralConstsNum : HolMath.Nums.NumeralConsts := Nm.numK
/-- `mk_small_numeral`. -/
def mk_small_numeral (n : Int) : Except String term :=
  HolMath.Nums.mk_small_numeral Nm.numK n
/-- `dest_small_numeral`. -/
def dest_small_numeral : term → Except String Int := HolMath.Nums.dest_small_numeral
/-- `is_numeral`. -/
def is_numeral : term → Bool := HolMath.Nums.is_numeral

/-- `INDUCT_TAC` (nums.ml), over the rewritten `num_INDUCTION`. -/
def INDUCT_TAC : tactic := HolMath.Nums.INDUCT_TAC num_INDUCTION

initialize theSpecifications : IO.Ref (List HolMath.Nums.specification) ← IO.mkRef []

def new_specification (names : List String) (th : thm) : IO (Except String thm) := do
  let existing ← theSpecifications.get
  match ← HolMath.Nums.new_specification_core Nm.numK new_definition existing names th with
  | .error e => return .error e
  | .ok (sth, entry) => do
      match entry with
      | some e => theSpecifications.set (e :: existing)
      | none => pure ()
      return .ok sth

end Session
