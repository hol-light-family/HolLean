/- File: HolTutorial/InductiveDefinitions.lean
Translation of HOL Light's Tutorial/Inductive_definitions.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/

import HolTutorial.Common
import SessionLibrary

open HolCore.Kernel Session HolLight.Syntax HolTutorial

namespace HolTutorial.InductiveDefinitions

/- The session's IO-valued rules lifted into `ExceptT String IO`, so tactic
   scripts read as in OCaml. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- ------------------------------------------------------------------------- -/
/- Bug puzzle.                                                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 1
#eval prioritize_real

#eval phrase 2
unsafe def move : thm := keep "move" fun _ => new_definition
 [[move ((ax,ay),(bx,by),(cx,cy)) ((ax',ay'),(bx',by'),(cx',cy')) <=>
        (?a. ax' = ax + a * (cx - bx) /\ ay' = ay + a * (cy - by) /\
             bx' = bx /\ by' = by /\ cx' = cx /\ cy' = cy) \/
        (?b. bx' = bx + b * (ax - cx) /\ by' = by + b * (ay - cy) /\
             ax' = ax /\ ay' = ay /\ cx' = cx /\ cy' = cy) \/
        (?c. ax' = ax /\ ay' = ay /\ bx' = bx /\ by' = by /\
             cx' = cx + c * (bx - ax) /\ cy' = cy + c * (by - ay))]]
#eval move

#eval phrase 3
unsafe def reachable_triple : thm × thm × thm := keep "reachable" fun _ =>
  match unsafeIO (new_inductive_definition
   [[(!p. reachable p p) /\
     (!p q r. move p q /\ reachable q r ==> reachable p r)]]) with
  | .ok (.ok t) => t
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
unsafe def reachable_RULES : thm := reachable_triple.1
unsafe def reachable_INDUCT : thm := reachable_triple.2.1
unsafe def reachable_CASES : thm := reachable_triple.2.2
#eval (do IO.println (← HolCore.Printer.string_of_thm reachable_RULES)
          IO.println (← HolCore.Printer.string_of_thm reachable_INDUCT)
          IO.println (← HolCore.Printer.string_of_thm reachable_CASES) : IO Unit)

#eval phrase 4
unsafe def oriented_area : thm := keep "oriented_area" fun _ => new_definition
 [[oriented_area ((ax,ay),(bx,by),(cx,cy)) =
      ((bx - ax) * (cy - ay) - (cx - ax) * (by - ay)) / &2]]
#eval oriented_area

#eval phrase 5
unsafe def MOVE_INVARIANT : thm := keep "MOVE_INVARIANT" fun _ => (do
  prove ([[!p p'. move p p' ==> oriented_area p = oriented_area p']])
   (REWRITE_TAC [FORALL_PAIR_THM, move, oriented_area] THEN CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval MOVE_INVARIANT

#eval phrase 6
unsafe def REACHABLE_INVARIANT : thm := keep "REACHABLE_INVARIANT" fun _ => (do
  prove ([[!p p'. reachable p p' ==> oriented_area p = oriented_area p']])
   (MATCH_MP_TAC reachable_INDUCT THEN MESON_TAC [MOVE_INVARIANT])
  : ExceptT String IO thm).run
#eval REACHABLE_INVARIANT

#eval phrase 7
unsafe def IMPOSSIBILITY_B : thm := keep "IMPOSSIBILITY_B" fun _ => (do
  prove ([[~(reachable ((&0,&0),(&3,&0),(&0,&3)) ((&1,&2),(&2,&5),(-- &2,&3)) \/
     reachable ((&0,&0),(&3,&0),(&0,&3)) ((&1,&2),(-- &2,&3),(&2,&5)) \/
     reachable ((&0,&0),(&3,&0),(&0,&3)) ((&2,&5),(&1,&2),(-- &2,&3)) \/
     reachable ((&0,&0),(&3,&0),(&0,&3)) ((&2,&5),(-- &2,&3),(&1,&2)) \/
     reachable ((&0,&0),(&3,&0),(&0,&3)) ((-- &2,&3),(&1,&2),(&2,&5)) \/
     reachable ((&0,&0),(&3,&0),(&0,&3)) ((-- &2,&3),(&2,&5),(&1,&2)))]])
   (STRIP_TAC THEN FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP REACHABLE_INVARIANT) THEN
    REWRITE_TAC [oriented_area] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval IMPOSSIBILITY_B

/- ------------------------------------------------------------------------- -/
/- Verification of a simple concurrent program.                              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 8
unsafe def init : thm := keep "init" fun _ => new_definition
 [[init (x,y,pc1,pc2,sem) <=>
        pc1 = 10 /\ pc2 = 10 /\ x = 0 /\ y = 0 /\ sem = 1]]
#eval init

#eval phrase 9
unsafe def trans : thm := keep "trans" fun _ => new_definition
 [[trans (x,y,pc1,pc2,sem) (x',y',pc1',pc2',sem') <=>
        pc1 = 10 /\ sem > 0 /\ pc1' = 20 /\ sem' = sem - 1 /\
                   (x',y',pc2') = (x,y,pc2) \/
        pc2 = 10 /\ sem > 0 /\ pc2' = 20 /\ sem' = sem - 1 /\
                   (x',y',pc1') = (x,y,pc1) \/
        pc1 = 20 /\ pc1' = 30 /\ x' = x + 1 /\
                   (y',pc2',sem') = (y,pc2,sem) \/
        pc2 = 20 /\ pc2' = 30 /\ y' = y + 1 /\ x' = x /\
                   pc1' = pc1 /\ sem' = sem \/
        pc1 = 30 /\ pc1' = 10 /\ sem' = sem + 1 /\
                   (x',y',pc2') = (x,y,pc2) \/
        pc2 = 30 /\ pc2' = 10 /\ sem' = sem + 1 /\
                   (x',y',pc1') = (x,y,pc1)]]
#eval trans

#eval phrase 10
unsafe def mutex : thm := keep "mutex" fun _ => new_definition
 [[mutex (x,y,pc1,pc2,sem) <=> pc1 = 10 \/ pc2 = 10]]
#eval mutex

#eval phrase 11
unsafe def indinv : thm := keep "indinv" fun _ => new_definition
 [[indinv (x:num,y:num,pc1,pc2,sem) <=>
        sem + (if pc1 = 10 then 0 else 1) + (if pc2 = 10 then 0 else 1) = 1]]
#eval indinv

#eval phrase 12
-- needs "Library/rstc.ml";;
#eval SessionLibrary.RSTC.ensureRSTC

#eval phrase 13
unsafe def INDUCTIVE_INVARIANT : thm := keep "INDUCTIVE_INVARIANT" fun _ => (do
  prove ([[!init invariant transition P.
        (!s. init s ==> invariant s) /\
        (!s s'. invariant s /\ transition s s' ==> invariant s') /\
        (!s. invariant s ==> P s)
        ==> !s s':A. init s /\ RTC transition s s' ==> P s']])
   (REPEAT GEN_TAC THEN MP_TAC (← HolLight.ISPECL
     [(← HolLight.q r"transition:A->A->bool"),
      (← HolLight.q r"\s s':A. invariant s ==> invariant s'")] SessionLibrary.RSTC.RTC_INDUCT) THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval INDUCTIVE_INVARIANT

#eval phrase 14
unsafe def MUTEX : thm := keep "MUTEX" fun _ => (do
  prove ([[!s s'. init s /\ RTC trans s s' ==> mutex s']])
   (MATCH_MP_TAC INDUCTIVE_INVARIANT THEN EXISTS_TAC (← HolLight.q r"indinv") THEN
    REWRITE_TAC [init, trans, indinv, mutex, FORALL_PAIR_THM, PAIR_EQ] THEN
    ARITH_TAC)
  : ExceptT String IO thm).run
#eval MUTEX

end HolTutorial.InductiveDefinitions
