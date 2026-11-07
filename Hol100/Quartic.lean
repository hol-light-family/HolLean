/- File: Hol100/Quartic.lean
Translation of HOL Light's 100/quartic.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
namespace Hol100.Quartic

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- Solution of the quartic.  The file rebinds QUARTIC_1 twice and
   QUARTIC_CASES twice; the later bindings are QUARTIC_1_2, QUARTIC_1_3,
   QUARTIC_CASES_2 and QUARTIC_CASES_3 here. -/

#eval phrase 1
#eval Session.prioritize_real

#eval phrase 2
def QUARTIC_1 : thm := keep "QUARTIC_1" fun _ => (do
  prove ([[y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   R = &0 /\
   s pow 2 = y pow 2 - &4 * d /\
   D pow 2 = &3 * a pow 2 / &4 - &2 * b + &2 * s /\
   x = --a / &4 + R / &2 + D / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0]])
   (CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval QUARTIC_1

#eval phrase 3
def QUARTIC_2 : thm := keep "QUARTIC_2" fun _ => (do
  prove ([[y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   R = &0 /\
   s pow 2 = y pow 2 - &4 * d /\
   D pow 2 = &3 * a pow 2 / &4 - &2 * b + &2 * s /\
   x = --a / &4 + R / &2 - D / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0]])
   (CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval QUARTIC_2

#eval phrase 4
def QUARTIC_3 : thm := keep "QUARTIC_3" fun _ => (do
  prove ([[y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   R = &0 /\
   s pow 2 = y pow 2 - &4 * d /\
   E pow 2 = &3 * a pow 2 / &4 - &2 * b - &2 * s /\
   x = --a / &4 - R / &2 + E / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0]])
   (CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval QUARTIC_3

#eval phrase 5
def QUARTIC_4 : thm := keep "QUARTIC_4" fun _ => (do
  prove ([[y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   R = &0 /\
   s pow 2 = y pow 2 - &4 * d /\
   E pow 2 = &3 * a pow 2 / &4 - &2 * b - &2 * s /\
   x = --a / &4 - R / &2 - E / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0]])
   (CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval QUARTIC_4

#eval phrase 6
def QUARTIC_1' : thm := keep "QUARTIC_1'" fun _ => (do
  prove ([[y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   ~(R = &0) /\
   D pow 2 = &3 * a pow 2 / &4 - R pow 2 - &2 * b +
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R) /\
   x = --a / &4 + R / &2 + D / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0]])
   (CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval QUARTIC_1'

#eval phrase 7
def QUARTIC_2' : thm := keep "QUARTIC_2'" fun _ => (do
  prove ([[y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   ~(R = &0) /\
   D pow 2 = &3 * a pow 2 / &4 - R pow 2 - &2 * b +
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R) /\
   x = --a / &4 + R / &2 - D / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0]])
   (CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval QUARTIC_2'

#eval phrase 8
def QUARTIC_3' : thm := keep "QUARTIC_3'" fun _ => (do
  prove ([[y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   ~(R = &0) /\
   E pow 2 = &3 * a pow 2 / &4 - R pow 2 - &2 * b -
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R) /\
   x = --a / &4 - R / &2 + E / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0]])
   (CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval QUARTIC_3'

#eval phrase 9
def QUARTIC_4' : thm := keep "QUARTIC_4'" fun _ => (do
  prove ([[y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   ~(R = &0) /\
   E pow 2 = &3 * a pow 2 / &4 - R pow 2 - &2 * b -
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R) /\
   x = --a / &4 - R / &2 - E / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0]])
   (CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval QUARTIC_4'

#eval phrase 10
-- let QUARTIC_1 = ... (rebinds QUARTIC_1)
def QUARTIC_1_2 : thm := keep "QUARTIC_1_2" fun _ => (do
  prove ([[y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   s pow 2 = y pow 2 - &4 * d /\
   (D pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b + &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b +
                   (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   x = --a / &4 + R / &2 + D / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0]])
   (CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval QUARTIC_1_2

#eval phrase 11
-- let QUARTIC_1 = ... (rebinds QUARTIC_1)
def QUARTIC_1_3 : thm := keep "QUARTIC_1_3" fun _ => (do
  prove ([[y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   s pow 2 = y pow 2 - &4 * d /\
   (D pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b + &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b +
                   (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   (E pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b - &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b -
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   (x = --a / &4 + R / &2 + D / &2 \/
    x = --a / &4 - R / &2 + E / &2)
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0]])
   (CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval QUARTIC_1_3

#eval phrase 12
def QUARTIC_CASES : thm := keep "QUARTIC_CASES" fun _ => (do
  prove ([[y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   s pow 2 = y pow 2 - &4 * d /\
   (D pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b + &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b +
                   (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   (E pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b - &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b -
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   (x = --a / &4 + R / &2 + D / &2 \/
    x = --a / &4 + R / &2 - D / &2 \/
    x = --a / &4 - R / &2 + E / &2 \/
    x = --a / &4 - R / &2 - E / &2)
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0]])
   (COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval QUARTIC_CASES

#eval phrase 13
-- let QUARTIC_CASES = ... (rebinds QUARTIC_CASES)
def QUARTIC_CASES_2 : thm := keep "QUARTIC_CASES_2" fun _ => (do
  prove ([[y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   s pow 2 = y pow 2 - &4 * d /\
   (D pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b + &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b +
                   (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   (E pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b - &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b -
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R))
   ==> (x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0 <=>
        x = --a / &4 + R / &2 + D / &2 \/
        x = --a / &4 + R / &2 - D / &2 \/
        x = --a / &4 - R / &2 + E / &2 \/
        x = --a / &4 - R / &2 - E / &2)]])
   (COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval QUARTIC_CASES_2

#eval phrase 14
-- let QUARTIC_CASES = ... (rebinds QUARTIC_CASES)
def QUARTIC_CASES_3 : thm := keep "QUARTIC_CASES_3" fun _ => (do
  prove ([[y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   s pow 2 = y pow 2 - &4 * d /\
   (D pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b + &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b +
                   (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   (E pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b - &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b -
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R))
   ==> (x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0 <=>
        x = --a / &4 + R / &2 + D / &2 \/
        x = --a / &4 + R / &2 - D / &2 \/
        x = --a / &4 - R / &2 + E / &2 \/
        x = --a / &4 - R / &2 - E / &2)]])
   (CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval QUARTIC_CASES_3

end Hol100.Quartic
