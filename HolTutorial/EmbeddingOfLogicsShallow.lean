/- File: HolTutorial/EmbeddingOfLogicsShallow.lean
Translation of HOL Light's Tutorial/Embedding_of_logics_shallow.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolTutorial.Common
open HolCore.Kernel Session HolLight.Syntax HolTutorial
namespace HolTutorial.EmbeddingOfLogicsShallow

#eval phrase 1
#eval parse_as_prefix "Not"

#eval phrase 2
#eval parse_as_infix ("&&", (16, "right"))

#eval phrase 3
#eval parse_as_infix ("||", (15, "right"))

#eval phrase 4
#eval parse_as_infix ("-->", (14, "right"))

#eval phrase 5
#eval parse_as_infix ("<->", (13, "right"))

#eval phrase 6
unsafe def false_def : thm := keep "false_def" fun _ => define [[False = \t:num. F]]
#eval false_def

#eval phrase 7
unsafe def true_def : thm := keep "true_def" fun _ => define [[True = \t:num. T]]
#eval true_def

#eval phrase 8
unsafe def not_def : thm := keep "not_def" fun _ => define [[Not p = \t:num. ~(p t)]]
#eval not_def

#eval phrase 9
unsafe def and_def : thm := keep "and_def" fun _ => define [[p && q = \t:num. p t /\ q t]]
#eval and_def

#eval phrase 10
unsafe def or_def : thm := keep "or_def" fun _ => define [[p || q = \t:num. p t \/ q t]]
#eval or_def

#eval phrase 11
unsafe def imp_def : thm := keep "imp_def" fun _ => define [[p --> q = \t:num. p t ==> q t]]
#eval imp_def

#eval phrase 12
unsafe def iff_def : thm := keep "iff_def" fun _ => define [[p <-> q = \t:num. p t <=> q t]]
#eval iff_def

#eval phrase 13
unsafe def forever : thm := keep "forever" fun _ => define [[forever p = \t:num. !t'. t <= t' ==> p t']]
#eval forever

#eval phrase 14
unsafe def sometime : thm := keep "sometime" fun _ => define [[sometime p = \t:num. ?t'. t <= t' /\ p t']]
#eval sometime

#eval phrase 15
unsafe def next : thm := keep "next" fun _ => define [[next p = \t:num. p(t + 1)]]
#eval next

#eval phrase 16
#eval parse_as_infix ("until", (17, "right"))

#eval phrase 17
unsafe def «until» : thm := keep "until" fun _ => define
  [[p until q =
    \t:num. ?t'. t <= t' /\ (!t''. t <= t'' /\ t'' < t' ==> p t'') /\ q t']]
#eval «until»

end HolTutorial.EmbeddingOfLogicsShallow
