/- File: HolTutorial/AbstractionsAndQuantifiers.lean
Translation of HOL Light's Tutorial/Abstractions_and_quantifiers.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolTutorial.Common
open HolCore.Kernel Session HolLight.Syntax HolTutorial

namespace HolTutorial.AbstractionsAndQuantifiers

#eval phrase 1
#eval MESON []
  [[((?x. !y. P(x) <=> P(y)) <=> ((?x. Q(x)) <=> (!y. Q(y)))) <=>
    ((?x. !y. Q(x) <=> Q(y)) <=> ((?x. P(x)) <=> (!y. P(y))))]]

#eval phrase 2
#eval MESON []
  [[(!x y z. P x y /\ P y z ==> P x z) /\
   (!x y z. Q x y /\ Q y z ==> Q x z) /\
   (!x y. P x y ==> P y x) /\
   (!x y. P x y \/ Q x y)
   ==> (!x y. P x y) \/ (!x y. Q x y)]]

-- let ewd1062 = MESON[] ... (the binding is never reused; printed as HOL Light does)
#eval phrase 3
#eval MESON []
  [[(!x. x <= x) /\
    (!x y z. x <= y /\ y <= z ==> x <= z) /\
    (!x y. f(x) <= y <=> x <= g(y))
    ==> (!x y. x <= y ==> f(x) <= f(y)) /\
        (!x y. x <= y ==> g(x) <= g(y))]]

-- let ewd1062 = MESON[] ... (rebinds ewd1062; still never reused)
#eval phrase 4
#eval MESON []
  [[(!x. R x x) /\
    (!x y z. R x y /\ R y z ==> R x z) /\
    (!x y. R (f x) y <=> R x (g y))
    ==> (!x y. R x y ==> R (f x) (f y)) /\
        (!x y. R x y ==> R (g x) (g y))]]

#eval phrase 5
#eval MESON [] [[(?!x. g(f x) = x) <=> (?!y. f(g y) = y)]]

#eval phrase 6
#eval MESON [ADD_ASSOC, ADD_SYM] [[m + (n + p) = n + (m + p)]]

end HolTutorial.AbstractionsAndQuantifiers
