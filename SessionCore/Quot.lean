/- File: SessionCore/Quot.lean
quot.ml: quotient types and the lifting of first-order theorems.  Its
support theorems (`Qs`) are built by `initialize` when this module is
imported.
-/
import SessionCore.TheCops
import HolCore.Quot

open HolCore HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal HolCore.Drule
open HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Theorems HolCore.Classic
open HolCore.Trivia HolCore.Printer

namespace Session


/-- Support lemmas for `quot.ml`, proved once: `SELECT_LEMMA`
    (`|- !x. (@y. x = y) = x`) and `pth` (the big `lift_theorem` implication). -/
structure QuotSupport where
  selectLemma : thm
  pth : thm
  deriving Inhabited

/-- quot.ml (hol_lib.ml 78) proves these at load. -/
initialize Qs : QuotSupport ← do
  match ← (do
    let TAUT (s : String) : ExceptT String IO thm := do
      (Classic.TAUT B C.BOOL_CASES_AX (← parse_term s) : IO (Except String thm))
    let selectConvIO : ioconv := fun t => pure (SELECT_CONV t)
    -- SELECT_LEMMA = prove(`!x:A. (@y. x = y) = x`,
    --   GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [EQ_SYM_EQ] THEN
    --   MATCH_ACCEPT_TAC SELECT_REFL)
    let selectLemma ← (Tactics.prove B (← parse_term "!x:A. (@y. x = y) = x")
      (Tactics.THEN B GEN_TAC
        (Tactics.THEN B
          (Simp.GEN_REWRITE_TAC B (fun c => Simp.landConvIO (Simp.binderConvIO c)) [T.EQ_SYM_EQ])
          (Tactics.MATCH_ACCEPT_TAC B C.SELECT_REFL))) : IO (Except String thm))
    -- pth: STRIP_TAC THEN SUBGOAL_THEN ... ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN ...
    let pthGoal ← parse_term
      ("(!x:Repty. R x x) /\\ (!x y. R x y <=> R y x) /\\ " ++
       "(!x y z. R x y /\\ R y z ==> R x z) /\\ (!a. mk(dest a) = a) /\\ " ++
       "(!r. (?x. r = R x) <=> (dest(mk r) = r)) " ++
       "==> (!x y. R x y <=> (mk(R x) = mk(R y))) /\\ " ++
       "(!P. (!x. P(mk(R x))) <=> (!x. P x)) /\\ " ++
       "(!P. (?x. P(mk(R x))) <=> (?x. P x)) /\\ " ++
       "(!x:Absty. mk(R((@)(dest x))) = x)")
    let subgoal1 ← parse_term
      "!x y. (mk((R:Repty->Repty->bool) x):Absty = mk(R y)) <=> (R x = R y)"
    let subgoal2 ← parse_term
      "dest(mk((R:Repty->Repty->bool) x):Absty) = R x"
    let mmpTaut ← TAUT "(a /\\ b /\\ c) /\\ (b ==> a ==> d) ==> a /\\ b /\\ c /\\ d"
    let xRepty ← parse_term "x:Repty"
    let etaAxSym ← liftExcept (GSYM ETA_AX)
    let pth ← (Tactics.prove B pthGoal
      (Tactics.EVERY B [
        Tactics.STRIP_TAC B,
        Tactics.THENL B (Tactics.SUBGOAL_THEN B subgoal1 (Tactics.ASSUME_TAC B))
          [ASM_MESON_TAC [], Tactics.ALL_TAC],
        Tactics.MATCH_MP_TAC B mmpTaut,
        Tactics.THENL B (Tactics.CONJ_TAC B)
          [Tactics.THEN B (Simp.ASM_REWRITE_TAC B [])
             (Tactics.THEN B (Simp.REWRITE_TAC B [C.FUN_EQ_THM]) (ASM_MESON_TAC [])),
           Tactics.ALL_TAC],
        Tactics.REPEAT B (Tactics.DISCH_THEN B (fun th =>
          match GSYM th with
          | .ok g => Simp.REWRITE_TAC B [g]
          | .error _ => Tactics.ALL_TAC)),
        Tactics.X_GEN_TAC B xRepty,
        Tactics.THENL B (Tactics.SUBGOAL_THEN B subgoal2 (Tactics.SUBST1_TAC B))
          [ASM_MESON_TAC [], Tactics.ALL_TAC],
        Simp.GEN_REWRITE_TAC B (fun c => Simp.landConvIO (Simp.randConvIO c)) [etaAxSym],
        Tactics.FIRST_ASSUM (fun th => Simp.GEN_REWRITE_TAC B id [th]),
        Tactics.THEN B (Tactics.CONV_TAC B selectConvIO) (ASM_MESON_TAC []) ]) : IO (Except String thm))
    pure ({ selectLemma, pth } : QuotSupport) : ExceptT String IO QuotSupport).run with
  | .ok q => pure q
  | .error e => throw (IO.userError s!"Quot support setup failed: {e}")

/-- `ETA_CONV` (class.ml), closed over its `pth` and `etaT`; `quot.ml`'s
    `lift_function` uses it. -/
def ETA_CONV (tm : term) : Except String thm :=
  Classic.ETA_CONV C.etaPth C.etaT tm

/-- `define_quotient_type tyname (absname, repname) eqv`. -/
def define_quotient_type (tyname : String) (absrep : String × String) (eqv : term) :
    IO (Except String (thm × thm)) :=
  Quot.define_quotient_type B tyname absrep eqv

/-- `lift_function tybij2 (refl_th, trans_th) fname wth`. -/
def lift_function (tybij2 : thm) (reflTrans : thm × thm) (fname : String) (wth : thm) :
    IO (Except String (thm × thm)) :=
  Quot.lift_function B Qs.selectLemma ETA_CONV tybij2 reflTrans fname wth

/-- `lift_theorem tybij (refl_th, sym_th, trans_th) trths th`. -/
def lift_theorem (tybij : thm × thm) (reflSymTrans : thm × thm × thm)
    (trths : List thm) (th : thm) : IO (Except String thm) :=
  Quot.lift_theorem B Qs.pth tybij reflSymTrans trths th

end Session
