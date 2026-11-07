/- File: Hol100/Pythagoras.lean
Translation of HOL Light's 100/pythagoras.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionMultiLib.Vectors
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionMultiLib.Misc SessionMultiLib.Vectors
namespace Hol100.Pythagoras

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- ========================================================================= -/
/- A "proof" of Pythagoras's theorem. Of course something similar is         -/
/- implicit in the definition of "norm", but maybe this is still nontrivial. -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Multivariate/misc.ml";;
#eval SessionMultiLib.Misc.ensureMisc

#eval phrase 2
-- needs "Multivariate/vectors.ml";;
#eval SessionMultiLib.Vectors.ensureVectors

/- ------------------------------------------------------------------------- -/
/- Direct vector proof (could replace 2 by N and the proof still runs).      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def PYTHAGORAS : thm := keep "PYTHAGORAS" fun _ => (do
  prove ([[!A B C:real^2.
        orthogonal (A - B) (C - B)
        ==> norm(C - A) pow 2 = norm(B - A) pow 2 + norm(C - B) pow 2]])
   (REWRITE_TAC [NORM_POW_2, orthogonal, DOT_LSUB, DOT_RSUB, DOT_SYM] THEN
    CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval PYTHAGORAS

/- ------------------------------------------------------------------------- -/
/- A more explicit and laborious "componentwise" specifically for 2-vectors. -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
-- let PYTHAGORAS = ... (rebinds PYTHAGORAS)
def PYTHAGORAS' : thm := keep "PYTHAGORAS'" fun _ => (do
  prove ([[!A B C:real^2.
        orthogonal (A - B) (C - B)
        ==> norm(C - A) pow 2 = norm(B - A) pow 2 + norm(C - B) pow 2]])
   (SIMP_TAC [NORM_POW_2, orthogonal, dot, SUM_2, DIMINDEX_2,
           VECTOR_SUB_COMPONENT, ARITH] THEN
    CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval PYTHAGORAS'

end Hol100.Pythagoras
