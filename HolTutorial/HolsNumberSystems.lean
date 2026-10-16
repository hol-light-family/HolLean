/- File: HolTutorial/HolsNumberSystems.lean
Translation of HOL Light's Tutorial/HOLs_number_systems.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/

import HolTutorial.Common

open HolCore.Kernel Session HolLight.Syntax HolTutorial

namespace HolTutorial.HolsNumberSystems

#eval phrase 1
#eval REAL_ARITH3 [[!x y:real. (abs(x) - abs(y)) <= abs(x - y)]]

#eval phrase 2
#eval INT_ARITH
  [[!a b a' b' D:int.
       (a pow 2 - D * b pow 2) * (a' pow 2 - D * b' pow 2) =
       (a * a' + D * b * b') pow 2 - D * (a * b' + a' * b) pow 2]]

#eval phrase 3
#eval REAL_ARITH3
  [[!x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11:real.
          x3 = abs(x2) - x1 /\
          x4 = abs(x3) - x2 /\
          x5 = abs(x4) - x3 /\
          x6 = abs(x5) - x4 /\
          x7 = abs(x6) - x5 /\
          x8 = abs(x7) - x6 /\
          x9 = abs(x8) - x7 /\
          x10 = abs(x9) - x8 /\
          x11 = abs(x10) - x9
          ==> x1 = x10 /\ x2 = x11]]

#eval phrase 4
#eval REAL_ARITH3 [[!x y:real. x < y ==> x < (x + y) / &2 /\ (x + y) / &2 < y]]

#eval phrase 5
#eval REAL_ARITH3
  [[((x1 pow 2 + x2 pow 2 + x3 pow 2 + x4 pow 2) pow 2) =
    ((&1 / &6) * ((x1 + x2) pow 4 + (x1 + x3) pow 4 + (x1 + x4) pow 4 +
                  (x2 + x3) pow 4 + (x2 + x4) pow 4 + (x3 + x4) pow 4) +
     (&1 / &6) * ((x1 - x2) pow 4 + (x1 - x3) pow 4 + (x1 - x4) pow 4 +
                  (x2 - x3) pow 4 + (x2 - x4) pow 4 + (x3 - x4) pow 4))]]

#eval phrase 6
#eval ARITH_RULE [[x < 2 ==> 2 * x + 1 < 4]]

#eval phrase 7
/-**** Fails
ARITH_RULE `~(2 * m + 1 = 2 * n)`;;
 ****-/

#eval ARITH_RULE [[x < 2 EXP 30 ==> (429496730 * x) DIV (2 EXP 32) = x DIV 10]]

#eval phrase 8
/-**** Fails
ARITH_RULE `x <= 2 EXP 30 ==> (429496730 * x) DIV (2 EXP 32) = x DIV 10`;;
 ****-/

/-**** Fails
ARITH_RULE `1 <= x /\ 1 <= y ==> 1 <= x * y`;;
 ****-/

/-**** Fails
REAL_ARITH `!x y:real. x = y ==> x * y = y pow 2`;;
 ****-/

#eval prioritize_real

#eval phrase 9
#eval REAL_RING
  [[s = (a + b + c) / &2
     ==> s * (s - b) * (s - c) + s * (s - c) * (s - a) +
         s * (s - a) * (s - b) - (s - a) * (s - b) * (s - c) =
         a * b * c]]

#eval phrase 10
#eval REAL_RING [[a pow 2 = &2 /\ x pow 2 + a * x + &1 = &0 ==> x pow 4 + &1 = &0]]

#eval phrase 11
#eval REAL_RING
  [[(a * x pow 2 + b * x + c = &0) /\
    (a * y pow 2 + b * y + c = &0) /\
    ~(x = y)
    ==> (a * x * y = c) /\ (a * (x + y) + b = &0)]]

#eval phrase 12
#eval REAL_RING
  [[p = (&3 * a1 - a2 pow 2) / &3 /\
    q = (&9 * a1 * a2 - &27 * a0 - &2 * a2 pow 3) / &27 /\
    x = z + a2 / &3 /\
    x * w = w pow 2 - p / &3
    ==> (z pow 3 + a2 * z pow 2 + a1 * z + a0 = &0 <=>
         if p = &0 then x pow 3 = q
         else (w pow 3) pow 2 - q * (w pow 3) - p pow 3 / &27 = &0)]]

#eval phrase 13
#eval REAL_FIELD [[&0 < x ==> &1 / x - &1 / (&1 + x) = &1 / (x * (&1 + x))]]

#eval phrase 14
#eval REAL_FIELD
  [[s pow 2 = b pow 2 - &4 * a * c
   ==> (a * x pow 2 + b * x + c = &0 <=>
        if a = &0 then
           if b = &0 then
              if c = &0 then T else F
           else x = --c / b
        else x = (--b + s) / (&2 * a) \/ x = (--b + --s) / (&2 * a))]]

-- Phrases 15 onwards (SOS examples, COOPER_RULE, Rqe/REAL_QELIM_CONV) wait for
-- the file named in tools/tutorialdiff/HOLs_number_systems/stop: Examples/sos.ml
-- and cooper.ml, Rqe are not translated.

end HolTutorial.HolsNumberSystems
