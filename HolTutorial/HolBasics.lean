/- File: HolTutorial/HolBasics.lean
Translation of HOL Light's Tutorial/HOL_basics.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/

import HolTutorial.Common

open HolCore.Kernel Session HolLight.Syntax HolTutorial

namespace HolTutorial.HolBasics

#eval phrase 1
#eval ARITH_RULE
  [[(a * x + b * y + a * y) EXP 3 + (b * x) EXP 3 +
    (a * x + b * y + b * x) EXP 3 + (a * y) EXP 3 =
    (a * x + a * y + b * x) EXP 3 + (b * y) EXP 3 +
    (a * y + b * y + b * x) EXP 3 + (a * x) EXP 3]]

end HolTutorial.HolBasics
