/- File: Trivia.lean
Trivial odds and ends.
Original       John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026 -/

import HolCore.Bool
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics
import HolCore.Itab
import HolCore.Simp
import HolCore.Parser
import HolCore.Theorems
import HolCore.IndDefs
import HolCore.Classic

open HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Equal
     HolCore.Drule HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Parser
     HolCore.Theorems HolCore.IndDefs HolCore.Classic

namespace HolCore.Trivia

set_option maxRecDepth 4000

/-- Parse a term in the `ExceptT String IO` monad. -/
private def pt (s : String) : ExceptT String IO term := parse_term s

/-- Theorems established by `trivia.ml`. -/
structure TriviaThms where
  o_THM   : thm
  o_ASSOC : thm
  I_THM   : thm
  I_O_ID  : thm
  EXISTS_ONE_REP : thm
  one     : thm
  one_axiom : thm
  one_INDUCT : thm
  one_RECURSION : thm
  one_Axiom : thm
  FORALL_ONE_THM : thm
  EXISTS_ONE_THM : thm
  ETA_ONE : thm
  deriving Inhabited

/-- Establish the `trivia.ml` theorem layer.
    `C` provides `FUN_EQ_THM` (and later `NOT_EXISTS_THM`/`TAUT`);
    `o_DEF`/`I_DEF` are the combinator definitions declared in Session. -/
def setupTrivia (B : BoolThms) (T : TheoremThms) (C : ClassThms)
    (o_DEF I_DEF : thm) (existsOneRep one_tydef _one_DEF : thm) :
    ExceptT String IO TriviaThms := do
  let prove := Tactics.prove B
  let REWRITE_TAC := Simp.REWRITE_TAC B
  let PURE_REWRITE_TAC := Simp.PURE_REWRITE_TAC B
  let CONV_TAC := Tactics.CONV_TAC B
  let GEN_TAC := Tactics.GEN_TAC B
  let REFL_TAC := Tactics.REFL_TAC B
  let STRIP_TAC := Tactics.STRIP_TAC B
  -- DEPTH_CONV / REDEPTH_CONV BETA_CONV, lifted to ioconv for CONV_TAC
  let depthBeta : ioconv := fun t => pure (DEPTH_CONV BETA_CONV t)
  let redepthBeta : ioconv := fun t => pure (REDEPTH_CONV BETA_CONV t)

  -- Combinators. We don't bother with S and K, which seem of little use.
  let o_THM ← (prove (← pt "!f:B->C. !g:A->B. !x:A. (f o g) x = f(g(x))")
      (THEN B (PURE_REWRITE_TAC [o_DEF])
        (THEN B (CONV_TAC depthBeta) (THEN B (REPEAT B GEN_TAC) REFL_TAC)))
      : IO (Except String thm))
  let o_ASSOC ← (prove (← pt "!f:C->D. !g:B->C. !h:A->B. f o (g o h) = (f o g) o h")
      (THEN B (REPEAT B GEN_TAC) (THEN B (REWRITE_TAC [o_DEF])
        (THEN B (CONV_TAC redepthBeta) REFL_TAC)))
      : IO (Except String thm))
  let I_THM ← (prove (← pt "!x:A. I x = x") (REWRITE_TAC [I_DEF]) : IO (Except String thm))
  let I_O_ID ← (prove (← pt "!f:A->B. (I o f = f) /\\ (f o I = f)")
      (THEN B (REPEAT B STRIP_TAC) (REWRITE_TAC [C.FUN_EQ_THM, o_DEF, I_THM]))
      : IO (Except String thm))

  -- The theory "1" (a 1-element type).
  let MP_TAC := Tactics.MP_TAC B
  let DISCH_TAC := Tactics.DISCH_TAC B
  let ONCE_REWRITE_TAC := Simp.ONCE_REWRITE_TAC B
  let ASM_REWRITE_TAC := Simp.ASM_REWRITE_TAC B
  let EQ_TAC := Tactics.EQ_TAC B
  let MATCH_ACCEPT_TAC := Tactics.MATCH_ACCEPT_TAC B
  let EXISTS_TAC := Tactics.EXISTS_TAC B
  let BETA_TAC := Tactics.BETA_TAC B
  let DISCH_THEN := Tactics.DISCH_THEN B
  let GEN_REWRITE_TAC := Simp.GEN_REWRITE_TAC B
  let cLetC1 ← liftExcept (B.CONJUNCT1 one_tydef)
  let cLetC2 ← liftExcept (B.CONJUNCT2 one_tydef)
  let oneRepA ← pt "one_REP a"
  -- EXISTS_ONE_REP: reuse the `existsOneRep` proved in Session (passed in for
  -- the bundle; not recomputed here).
  let EXISTS_ONE_REP := existsOneRep
  -- one : !v:1. v = one
  let one ← (prove (← pt "!v:1. v = one")
      (THEN B (MP_TAC (← liftExcept (do B.GEN_ALL (← B.SPEC oneRepA cLetC2))))
        (THEN B (REWRITE_TAC [cLetC1]) (THEN B DISCH_TAC
          (THEN B (ONCE_REWRITE_TAC [(← liftExcept (GSYM cLetC1))]) (ASM_REWRITE_TAC [])))))
      : IO (Except String thm))
  let one_axiom ← (prove (← pt "!f g. f = (g:A->1)")
      (THEN B (REPEAT B GEN_TAC) (THEN B (ONCE_REWRITE_TAC [C.FUN_EQ_THM])
        (THEN B GEN_TAC (THEN B (ONCE_REWRITE_TAC [one]) REFL_TAC)))) : IO (Except String thm))
  let one_INDUCT ← (prove (← pt "!P. P one ==> !x. P x")
      (THEN B (ONCE_REWRITE_TAC [one]) (REWRITE_TAC [])) : IO (Except String thm))
  let one_RECURSION ← (prove (← pt "!e:A. ?fn. fn one = e")
      (THEN B GEN_TAC (THEN B (EXISTS_TAC (← pt "\\x:1. e:A")) (THEN B BETA_TAC REFL_TAC)))
      : IO (Except String thm))
  let one_Axiom ← (prove (← pt "!e:A. ?!fn. fn one = e")
      (THEN B GEN_TAC (THEN B (REWRITE_TAC [T.EXISTS_UNIQUE_THM, one_RECURSION])
        (THEN B (REPEAT B STRIP_TAC) (THEN B (ONCE_REWRITE_TAC [C.FUN_EQ_THM])
          (THEN B (ONCE_REWRITE_TAC [one]) (ASM_REWRITE_TAC [])))))) : IO (Except String thm))
  let FORALL_ONE_THM ← (prove (← pt "(!x. P x) <=> P one")
      (THEN B EQ_TAC (THEN B (REWRITE_TAC [one_INDUCT]) (DISCH_THEN MATCH_ACCEPT_TAC)))
      : IO (Except String thm))
  let iffNegLemma ← (Classic.TAUT B C.BOOL_CASES_AX (← pt "(p <=> q) <=> (~p <=> ~q)")
                      : IO (Except String thm))
  let EXISTS_ONE_THM ← (prove (← pt "(?x. P x) <=> P one")
      (THEN B (GEN_REWRITE_TAC id [iffNegLemma])
        (REWRITE_TAC [C.NOT_EXISTS_THM, FORALL_ONE_THM])) : IO (Except String thm))
  let ETA_ONE ← (prove (← pt "!f:1->A. (\\x. f one) = f")
      (THEN B (REWRITE_TAC [C.FUN_EQ_THM]) (THEN B (REPEAT B GEN_TAC)
        (THEN B (ONCE_REWRITE_TAC [one]) REFL_TAC))) : IO (Except String thm))

  return { o_THM, o_ASSOC, I_THM, I_O_ID,
           EXISTS_ONE_REP, one, one_axiom, one_INDUCT, one_RECURSION, one_Axiom,
           FORALL_ONE_THM, EXISTS_ONE_THM, ETA_ONE }

end HolCore.Trivia
