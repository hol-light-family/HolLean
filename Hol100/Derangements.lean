/- File: Hol100/Derangements.lean
Translation of HOL Light's 100/derangements.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Transc
import SessionLibrary.CalcReal
import SessionLibrary.Floor
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Floor SessionLibrary.Analysis SessionLibrary.Transc SessionLibrary.CalcReal
namespace Hol100.Derangements

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def nc (tm : term) : ExceptT String IO thm := ExceptT.mk (num_CONV tm)
private def rf (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_FIELD tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- #88: Formula for the number of derangements: round[n!/e]                  -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/transc.ml";;
#eval SessionLibrary.Transc.ensureTransc

#eval phrase 2
-- needs "Library/calc_real.ml";;
#eval SessionLibrary.CalcReal.ensureCalcReal

#eval phrase 3
-- needs "Library/floor.ml";;
#eval SessionLibrary.Floor.ensureFloor

#eval phrase 4
-- let PAIR_BETA_THM = GEN_BETA_CONV `(\(x,y). P x y) (a,b)`;;
def PAIR_BETA_THM : thm := keep "PAIR_BETA_THM" fun _ => (do
  ExceptT.mk (GEN_BETA_CONV (← ExceptT.mk [[(\(x,y). P x y) (a,b)]]))
  : ExceptT String IO thm).run
#eval PAIR_BETA_THM

/- ------------------------------------------------------------------------- -/
/- Domain and range of a relation.                                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def domain : thm := keep "domain" fun _ => new_definition
 [[domain r = {x | ?y. r(x,y)}]]
#eval domain

#eval phrase 6
def range : thm := keep "range" fun _ => new_definition
 [[range r = {y | ?x. r(x,y)}]]
#eval range

/- ------------------------------------------------------------------------- -/
/- Relational composition.                                                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 7
-- parse_as_infix("%",(26, "right"));;
#eval (parse_as_infix ("%", (26, "right")) : IO Unit)

#eval phrase 8
def compose : thm := keep "compose" fun _ => new_definition
 [[(r % s) (x,y) <=> ?z. r(x,z) /\ s(z,y)]]
#eval compose

/- ------------------------------------------------------------------------- -/
/- Identity relation on a domain.                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 9
def id : thm := keep "id" fun _ => new_definition
 [[id(s) (x,y) <=> x IN s /\ x = y]]
#eval id

/- ------------------------------------------------------------------------- -/
/- Converse relation.                                                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 10
def converse : thm := keep "converse" fun _ => new_definition
 [[converse(r) (x,y) = r(y,x)]]
#eval converse

/- ------------------------------------------------------------------------- -/
/- Transposition.                                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 11
def swap : thm := keep "swap" fun _ => new_definition
 [[swap(a,b) (x,y) <=> x = a /\ y = b \/ x = b /\ y = a]]
#eval swap

/- ------------------------------------------------------------------------- -/
/- When a relation "pairs up" two sets bijectively.                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 12
-- parse_as_infix("pairsup",(12,"right"));;
#eval (parse_as_infix ("pairsup", (12, "right")) : IO Unit)

#eval phrase 13
def pairsup : thm := keep "pairsup" fun _ => new_definition
 [[r pairsup (s,t) <=> (r % converse(r) = id(s)) /\ (converse(r) % r = id(t))]]
#eval pairsup

/- ------------------------------------------------------------------------- -/
/- Special case of a permutation.                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 14
-- parse_as_infix("permutes",(12,"right"));;
#eval (parse_as_infix ("permutes", (12, "right")) : IO Unit)

#eval phrase 15
def permutes : thm := keep "permutes" fun _ => new_definition
 [[r permutes s <=> r pairsup (s,s)]]
#eval permutes

/- ------------------------------------------------------------------------- -/
/- Even more special case of derangement.                                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 16
-- parse_as_infix("deranges",(12,"right"));;
#eval (parse_as_infix ("deranges", (12, "right")) : IO Unit)

#eval phrase 17
def deranges : thm := keep "deranges" fun _ => new_definition
 [[r deranges s <=> r permutes s /\ !x. ~(r(x,x))]]
#eval deranges

/- ------------------------------------------------------------------------- -/
/- Trivial tactic for properties of relations.                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 18
-- let REL_TAC = ...;;
def REL_TAC : HolCore.Tactics.tactic :=
  POP_ASSUM_LIST (fun _ => ALL_TAC) THEN
  REWRITE_TAC [FUN_EQ_THM, FORALL_PAIR_THM, EXISTS_PAIR_THM, PAIR_BETA_THM,
              permutes, pairsup, domain, range, compose, id, converse, swap,
              deranges, IN_INSERT, IN_DELETE, NOT_IN_EMPTY, IN_ELIM_THM] THEN
  REWRITE_TAC [IN, EMPTY, INSERT, DELETE, UNION, IN_ELIM_THM, PAIR_EQ,
              id, converse, swap] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
  REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o check (is_var o HolCore.Equal.lhs o concl))) THEN
  REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o HolLight.SYM o check (is_var o HolCore.Equal.rhs o concl))) THEN
  ASM_MESON_TAC []
#eval IO.println "<fun>"

#eval phrase 19
-- let REL_RULE tm = prove(tm,REL_TAC);;
def REL_RULE (tm : term) : ExceptT String IO thm := prove tm REL_TAC
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Some general properties of relations.                                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 20
def CONVERSE_COMPOSE : thm := keep "CONVERSE_COMPOSE" fun _ => (do
  prove ([[!r s. converse(r % s) = converse(s) % converse(r)]])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval CONVERSE_COMPOSE

#eval phrase 21
def CONVERSE_CONVERSE : thm := keep "CONVERSE_CONVERSE" fun _ => (do
  prove ([[!r. converse(converse r) = r]])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval CONVERSE_CONVERSE

/- ------------------------------------------------------------------------- -/
/- More "explicit" definition of pairing and permutation.                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 22
def PAIRSUP_EXPLICIT : thm := keep "PAIRSUP_EXPLICIT" fun _ => (do
  prove ([[!p s t.
        p pairsup (s,t) <=>
        (!x y. p(x,y) ==> x IN s /\ y IN t) /\
        (!x. x IN s ==> ?!y. y IN t /\ p(x,y)) /\
        (!y. y IN t ==> ?!x. x IN s /\ p(x,y))]])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval PAIRSUP_EXPLICIT

#eval phrase 23
def PERMUTES_EXPLICIT : thm := keep "PERMUTES_EXPLICIT" fun _ => (do
  prove ([[!p s. p permutes s <=>
         (!x y. p(x,y) ==> x IN s /\ y IN s) /\
         (!x. x IN s ==> ?!y. y IN s /\ p(x,y)) /\
         (!y. y IN s ==> ?!x. x IN s /\ p(x,y))]])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval PERMUTES_EXPLICIT

/- ------------------------------------------------------------------------- -/
/- Other low-level properties.                                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 24
def PAIRSUP_DOMRAN : thm := keep "PAIRSUP_DOMRAN" fun _ => (do
  prove ([[!p s t. p pairsup (s,t) ==> domain p = s /\ range p = t]])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval PAIRSUP_DOMRAN

#eval phrase 25
def PERMUTES_DOMRAN : thm := keep "PERMUTES_DOMRAN" fun _ => (do
  prove ([[!p s. p permutes s ==> domain p = s /\ range p = s]])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval PERMUTES_DOMRAN

#eval phrase 26
def PAIRSUP_FUNCTIONAL : thm := keep "PAIRSUP_FUNCTIONAL" fun _ => (do
  prove ([[!p s t. p pairsup (s,t) ==> !x y y'. p(x,y) /\ p(x,y') ==> y = y']])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval PAIRSUP_FUNCTIONAL

#eval phrase 27
def PERMUTES_FUNCTIONAL : thm := keep "PERMUTES_FUNCTIONAL" fun _ => (do
  prove ([[!p s. p permutes s ==> !x y y'. p(x,y) /\ p(x,y') ==> y = y']])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval PERMUTES_FUNCTIONAL

#eval phrase 28
def PAIRSUP_COFUNCTIONAL : thm := keep "PAIRSUP_COFUNCTIONAL" fun _ => (do
  prove ([[!p s t. p pairsup (s,t) ==> !x x' y. p(x,y) /\ p(x',y) ==> x = x']])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval PAIRSUP_COFUNCTIONAL

#eval phrase 29
def PERMUTES_COFUNCTIONAL : thm := keep "PERMUTES_COFUNCTIONAL" fun _ => (do
  prove ([[!p s. p permutes s ==> !x x' y. p(x,y) /\ p(x',y) ==> x = x']])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval PERMUTES_COFUNCTIONAL

/- ------------------------------------------------------------------------- -/
/- Some more abstract properties.                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 30
def PAIRSUP_ID : thm := keep "PAIRSUP_ID" fun _ => (do
  prove ([[!s. id(s) pairsup (s,s)]])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval PAIRSUP_ID

#eval phrase 31
def PERMUTES_ID : thm := keep "PERMUTES_ID" fun _ => (do
  prove ([[!s. id(s) permutes s]])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval PERMUTES_ID

#eval phrase 32
def PAIRSUP_CONVERSE : thm := keep "PAIRSUP_CONVERSE" fun _ => (do
  prove ([[!p s t. p pairsup (s,t) ==> converse(p) pairsup (t,s)]])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval PAIRSUP_CONVERSE

#eval phrase 33
def PERMUTES_CONVERSE : thm := keep "PERMUTES_CONVERSE" fun _ => (do
  prove ([[!p s. p permutes s ==> converse(p) permutes s]])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval PERMUTES_CONVERSE

#eval phrase 34
def PAIRSUP_COMPOSE : thm := keep "PAIRSUP_COMPOSE" fun _ => (do
  prove ([[!p p' s t u. p pairsup (s,t) /\ p' pairsup (t,u) ==> (p % p') pairsup (s,u)]])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval PAIRSUP_COMPOSE

#eval phrase 35
def PERMUTES_COMPOSE : thm := keep "PERMUTES_COMPOSE" fun _ => (do
  prove ([[!p p' s. p permutes s /\ p' permutes s ==> (p % p') permutes s]])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval PERMUTES_COMPOSE

/- ------------------------------------------------------------------------- -/
/- Transpositions are permutations.                                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 36
def PERMUTES_SWAP : thm := keep "PERMUTES_SWAP" fun _ => (do
  prove ([[swap(a,b) permutes {a,b}]])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval PERMUTES_SWAP

/- ------------------------------------------------------------------------- -/
/- Clausal theorems for cases on first set.                                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 37
def PAIRSUP_EMPTY : thm := keep "PAIRSUP_EMPTY" fun _ => (do
  prove ([[p pairsup ({},{}) <=> (p = {})]])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval PAIRSUP_EMPTY

#eval phrase 38
def PAIRSUP_INSERT : thm := keep "PAIRSUP_INSERT" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[x IN s ==> x INSERT s = s]])
  prove ([[!x:A s t:B->bool p.
        p pairsup (x INSERT s,t) <=>
          if x IN s then p pairsup (s,t)
          else ?y q. y IN t /\ p = (x,y) INSERT q /\ q pairsup (s,t DELETE y)]])
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [h1] THEN EQ_TAC THENL
     [ALL_TAC,
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC] THEN
    DISCH_TAC THEN SUBGOAL_THEN ([[?y. y IN t /\ p(x:A,y:B)]]) MP_TAC THENL
     [POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN REL_TAC, ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[y:B]]) THEN STRIP_TAC THEN
    EXISTS_TAC ([[p DELETE (x:A,y:B)]]) THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN REL_TAC)
  : ExceptT String IO thm).run
#eval PAIRSUP_INSERT

/- ------------------------------------------------------------------------- -/
/- Number of pairings and permutations.                                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 39
def NUMBER_OF_PAIRINGS : thm := keep "NUMBER_OF_PAIRINGS" fun _ => (do
  let lemma ← prove ([[{p | ?y. y IN t /\ A y p} = UNIONS {{p | A y p} | y IN t} /\
     {p | ?q. p = (a,y) INSERT q /\ A y q} =
           IMAGE (\q. (a,y) INSERT q) {q | A y q}]])
     (CONJ_TAC THEN GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
      REWRITE_TAC [IN_ELIM_THM, IN_UNIONS, IN_IMAGE] THEN SET_TAC [])
  let h1 ← sr (← ExceptT.mk [[{x | x = a} = {a}]])
  prove ([[!n s:A->bool t:B->bool.
        s HAS_SIZE n /\ t HAS_SIZE n
        ==> {p | p pairsup (s,t)} HAS_SIZE (FACT n)]])
   (INDUCT_TAC THEN REPEAT GEN_TAC THENL
     [REWRITE_TAC [HAS_SIZE_CLAUSES] THEN
      SIMP_TAC [PAIRSUP_EMPTY, h1] THEN
      SIMP_TAC [HAS_SIZE, CARD_CLAUSES, FINITE_RULES, NOT_IN_EMPTY, ARITH, FACT],
      ALL_TAC] THEN
    GEN_REWRITE_TAC (HolCore.Lib.funpow 2 HolLight.LAND_CONV) [HAS_SIZE_CLAUSES] THEN
    REWRITE_TAC [HAS_SIZE_SUC] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_REWRITE_TAC [PAIRSUP_INSERT, RIGHT_EXISTS_AND_THM, lemma, FACT] THEN
    MATCH_MP_TAC HAS_SIZE_UNIONS THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC [HAS_SIZE_SUC],
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
      ASM_SIMP_TAC [] THEN REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC,
      REPEAT STRIP_TAC THEN REWRITE_TAC [DISJOINT] THEN
      GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
      REWRITE_TAC [IN_INTER, IN_IMAGE, NOT_IN_EMPTY] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC])
  : ExceptT String IO thm).run
#eval NUMBER_OF_PAIRINGS

#eval phrase 40
def NUMBER_OF_PERMUTATIONS : thm := keep "NUMBER_OF_PERMUTATIONS" fun _ => (do
  prove ([[!s n. s HAS_SIZE n ==> {p | p permutes s} HAS_SIZE (FACT n)]])
   (SIMP_TAC [permutes, NUMBER_OF_PAIRINGS])
  : ExceptT String IO thm).run
#eval NUMBER_OF_PERMUTATIONS

/- ------------------------------------------------------------------------- -/
/- Number of derangements (we need to justify this later).                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 41
def derangements : thm := keep "derangements" fun _ => define
 [[(derangements 0 = 1) /\
  (derangements 1 = 0) /\
  (derangements(n + 2) = (n + 1) * (derangements n + derangements(n + 1)))]]
#eval derangements

#eval phrase 42
def DERANGEMENT_INDUCT : thm := keep "DERANGEMENT_INDUCT" fun _ => (do
  prove ([[!P. P 0 /\ P 1 /\ (!n. P n /\ P(n + 1) ==> P(n + 2)) ==> !n. P n]])
   (GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[!n. P n /\ P(n + 1)]]) (fun th => MESON_TAC [th]) THEN
    INDUCT_TAC THEN ASM_SIMP_TAC [ADD1, (← HolLight.GSYM ADD_ASSOC)] THEN
    ASM_SIMP_TAC [ARITH])
  : ExceptT String IO thm).run
#eval DERANGEMENT_INDUCT

/- ------------------------------------------------------------------------- -/
/- Expanding a derangement.                                                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 43
def DERANGEMENT_ADD2 : thm := keep "DERANGEMENT_ADD2" fun _ => (do
  prove ([[!p s x y.
        p deranges s /\ ~(x IN s) /\ ~(y IN s) /\ ~(x = y)
        ==> ((x,y) INSERT (y,x) INSERT p) deranges (x INSERT y INSERT s)]])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval DERANGEMENT_ADD2

#eval phrase 44
def DERANGEMENT_ADD1 : thm := keep "DERANGEMENT_ADD1" fun _ => (do
  prove ([[!p s y x. p deranges s /\ ~(y IN s) /\ p(x,z)
             ==> ((x,y) INSERT (y,z) INSERT (p DELETE (x,z)))
                 deranges (y INSERT s)]])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval DERANGEMENT_ADD1

/- ------------------------------------------------------------------------- -/
/- Number of derangements.                                                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 45
def DERANGEMENT_EMPTY : thm := keep "DERANGEMENT_EMPTY" fun _ => (do
  prove ([[!p. p deranges {} <=> p = {}]])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval DERANGEMENT_EMPTY

#eval phrase 46
def DERANGEMENT_SING : thm := keep "DERANGEMENT_SING" fun _ => (do
  prove ([[!x p. ~(p deranges {x})]])
   (REL_TAC)
  : ExceptT String IO thm).run
#eval DERANGEMENT_SING

#eval phrase 47
def NUMBER_OF_DERANGEMENTS : thm := keep "NUMBER_OF_DERANGEMENTS" fun _ => (do
  let h14 ← tt (← ExceptT.mk [[(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b]])
  let h13 ← tt (← ExceptT.mk [[(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b]])
  let h12 ← tt (← ExceptT.mk [[~(a /\ b) <=> a ==> ~b]])
  let h11 ← sr (← ExceptT.mk [[a INSERT b INSERT s = a INSERT b INSERT t
        ==> ~(a IN s) /\ ~(a IN t) /\ ~(b IN s) /\ ~(b IN t) ==> s = t]])
  let h10 ← tt (← ExceptT.mk [[a ==> b ==> c <=> b ==> a ==> c]])
  let h9 ← tt (← ExceptT.mk [[(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b]])
  let h8 ← tt (← ExceptT.mk [[(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b]])
  let h7 ← tt (← ExceptT.mk [[(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b]])
  let h6 ← tt (← ExceptT.mk [[(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b]])
  let h5 ← sr (← ExceptT.mk [[y IN s ==> s = y INSERT (s DELETE y)]])
  let h4 ← tt (← ExceptT.mk [[(a /\ b) /\ c /\ d <=> c /\ d /\ a /\ b]])
  let h3 ← tt (← ExceptT.mk [[a \/ b ==> c <=> (a ==> c) /\ (b ==> c)]])
  let h2 ← tt (← ExceptT.mk [[(a <=> b) <=> (b ==> a) /\ (a ==> b)]])
  let h1 ← ar (← ExceptT.mk [[n + 2 = SUC(n + 1)]])
  prove ([[!n s:A->bool. s HAS_SIZE n ==> {p | p deranges s} HAS_SIZE (derangements n)]])
   (MATCH_MP_TAC DERANGEMENT_INDUCT THEN REWRITE_TAC [derangements] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC (HolLight.ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN REPEAT STRIP_TAC THEN
      EXISTS_TAC ([[{}:A#A->bool]]) THEN
      ASM_REWRITE_TAC [DERANGEMENT_EMPTY, EXTENSION, IN_ELIM_THM] THEN
      REWRITE_TAC [NOT_IN_EMPTY, IN_SING] THEN MESON_TAC [MEMBER_NOT_EMPTY],
      CONV_TAC (HolLight.ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [DERANGEMENT_SING] THEN SET_TAC [],
      ALL_TAC] THEN
    X_GEN_TAC ([[n:num]]) THEN STRIP_TAC THEN X_GEN_TAC ([[t:A->bool]]) THEN
    REWRITE_TAC [h1, HAS_SIZE_CLAUSES] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[x:A]]), ([[s:A->bool]])] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN ([[{p | p deranges (x:A INSERT s)} =
        (IMAGE (\(y,p). (x,y) INSERT (y,x) INSERT p)
               {(y,p) | y IN s /\ p IN {p | p deranges (s DELETE y)}}) UNION
        (IMAGE (\(y,p). let z = @z. p(x,z) in
                        (x,y) INSERT (y,z) INSERT (p DELETE (x,z)))
               {(y,p) | y IN s /\
                        p IN {p | p deranges (x INSERT (s DELETE y))}})]]) SUBST1_TAC THENL
     [GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
      REWRITE_TAC [h2] THEN
      REWRITE_TAC [FORALL_AND_THM] THEN CONJ_TAC THENL
       [REWRITE_TAC [IN_UNION, h3,
                    FORALL_AND_THM, FORALL_IN_IMAGE] THEN
        REWRITE_TAC [FORALL_PAIR_THM, PAIR_BETA_THM, IN_ELIM_THM, PAIR_EQ] THEN
        ONCE_REWRITE_TAC [h4] THEN
        REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
        CONJ_TAC THEN MAP_EVERY X_GEN_TAC [([[y:A]]), ([[p:A#A->bool]])] THEN
        STRIP_TAC THENL
         [FIRST_ASSUM (SUBST1_TAC o HolLight.MATCH_MP h5) THEN
          MATCH_MP_TAC DERANGEMENT_ADD2 THEN ASM_REWRITE_TAC [IN_DELETE] THEN
          ASM_MESON_TAC [],
          ALL_TAC] THEN
        ABBREV_TAC ([[z = @z. p(x:A,z:A)]]) THEN
        SUBGOAL_THEN ([[(p:A#A->bool)(x:A,z:A)]]) STRIP_ASSUME_TAC THENL
         [REPEAT (FIRST_X_ASSUM (SUBST1_TAC o HolLight.SYM)) THEN
          CONV_TAC (pureC SELECT_CONV) THEN
          REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC,
          ALL_TAC] THEN
        SUBGOAL_THEN ([[z:A IN s]]) STRIP_ASSUME_TAC THENL
         [REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC, ALL_TAC] THEN
        REWRITE_TAC [LET_DEF, LET_END_DEF] THEN
        SUBGOAL_THEN ([[(x:A) INSERT s = y INSERT (x INSERT (s DELETE y))]]) SUBST1_TAC THENL
         [REPEAT (POP_ASSUM MP_TAC) THEN SET_TAC [], ALL_TAC] THEN
        MATCH_MP_TAC DERANGEMENT_ADD1 THEN ASM_REWRITE_TAC [] THEN
        ASM_REWRITE_TAC [IN_DELETE, IN_INSERT] THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      X_GEN_TAC ([[p:A#A->bool]]) THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[?y. y IN s /\ p(x:A,y:A)]]) STRIP_ASSUME_TAC THENL
       [REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC, ALL_TAC] THEN
      REWRITE_TAC [IN_UNION] THEN ASM_CASES_TAC ([[(p:A#A->bool)(y,x)]]) THENL
       [DISJ1_TAC THEN REWRITE_TAC [IN_IMAGE] THEN
        EXISTS_TAC ([[y:A,(p DELETE (y,x)) DELETE (x:A,y:A)]]) THEN
        CONJ_TAC THENL
         [REWRITE_TAC [PAIR_BETA_THM] THEN MAP_EVERY UNDISCH_TAC [([[(p:A#A->bool)(x,y)]]), ([[(p:A#A->bool)(y,x)]])] THEN SET_TAC [],
          ALL_TAC] THEN
        REWRITE_TAC [IN_ELIM_THM, PAIR_EQ] THEN
        ONCE_REWRITE_TAC [h6] THEN
        ASM_REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
        REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN ([[?z. p(y:A,z:A)]]) STRIP_ASSUME_TAC THENL
       [REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC, ALL_TAC] THEN
      SUBGOAL_THEN ([[z:A IN s]]) ASSUME_TAC THENL
       [REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC, ALL_TAC] THEN
      DISJ2_TAC THEN REWRITE_TAC [IN_IMAGE, EXISTS_PAIR_THM, PAIR_BETA_THM] THEN
      EXISTS_TAC ([[y:A]]) THEN
      EXISTS_TAC ([[(x:A,z:A) INSERT ((p DELETE (x,y)) DELETE (y,z))]]) THEN
      SUBGOAL_THEN ([[(@w:A. ((x,z) INSERT (p DELETE (x,y) DELETE (y,z))) (x,w)) = z]]) SUBST1_TAC THENL
       [MATCH_MP_TAC SELECT_UNIQUE THEN REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [LET_DEF, LET_END_DEF] THEN CONJ_TAC THENL
       [REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, PAIR_BETA_THM] THEN
        REWRITE_TAC [IN, INSERT, DELETE, PAIR_BETA_THM, IN_ELIM_THM, PAIR_EQ] THEN
        MAP_EVERY X_GEN_TAC [([[u:A]]), ([[v:A]])] THEN
        ASM_CASES_TAC ([[u:A = x]]) THEN ASM_REWRITE_TAC [] THENL
         [ALL_TAC, REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC] THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [IN_ELIM_THM, PAIR_EQ] THEN
      ONCE_REWRITE_TAC [h7] THEN
      ASM_REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [LEFT_ADD_DISTRIB] THEN MATCH_MP_TAC HAS_SIZE_UNION THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
       [REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_THM, PAIR_BETA_THM, PAIR_EQ] THEN
        ONCE_REWRITE_TAC [h8] THEN
        REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
        REWRITE_TAC [FUN_EQ_THM, INSERT, IN_ELIM_THM, FORALL_PAIR_THM,
                    PAIR_EQ] THEN
        UNDISCH_TAC ([[~(x:A IN s)]]) THEN REL_TAC,
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_SIZE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC ([[(s:A->bool) HAS_SIZE (n + 1)]]) THEN
      SIMP_TAC [HAS_SIZE, FINITE_DELETE, CARD_DELETE] THEN
      ASM_REWRITE_TAC [ADD_SUB],
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
       [REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_THM, PAIR_BETA_THM, PAIR_EQ] THEN
        ONCE_REWRITE_TAC [h9] THEN
        REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN MAP_EVERY X_GEN_TAC [([[y:A]]), ([[p:(A#A)->bool]]), ([[y':A]]), ([[p':(A#A->bool)]])] THEN
        DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
        DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
        MAP_EVERY ABBREV_TAC [([[z = @z. p(x:A,z:A)]]), ([[z' = @z. p'(x:A,z:A)]])] THEN
        REWRITE_TAC [LET_DEF, LET_END_DEF] THEN
        SUBGOAL_THEN ([[p(x:A,z:A) /\ p'(x:A,z':A)]]) STRIP_ASSUME_TAC THENL
         [REPEAT (FIRST_X_ASSUM (SUBST1_TAC o HolLight.SYM)) THEN
          CONJ_TAC THEN CONV_TAC (pureC SELECT_CONV) THEN
          REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC,
          ALL_TAC] THEN
        REPEAT (FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o HolLight.SYM)) THEN
        SUBGOAL_THEN ([[z:A IN s /\ z':A IN s]]) STRIP_ASSUME_TAC THENL
         [REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC, ALL_TAC] THEN
        DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MATCH_MP_TAC (← tt (← ExceptT.mk [[a /\ (a ==> b) ==> a /\ b]])) THEN
                             CONJ_TAC THEN MP_TAC th)) THENL
         [DISCH_THEN (MP_TAC o HolCore.Lib.C HolLight.AP_THM ([[(x:A,y:A)]])) THEN
          REWRITE_TAC [INSERT, DELETE, IN_ELIM_THM, PAIR_BETA_THM, PAIR_EQ] THEN
          REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC,
          ALL_TAC] THEN
        ONCE_REWRITE_TAC [h10] THEN
        DISCH_THEN (SUBST_ALL_TAC o HolLight.SYM) THEN
        ASM_CASES_TAC ([[z':A = z]]) THEN ASM_REWRITE_TAC [] THENL
         [FIRST_X_ASSUM SUBST_ALL_TAC,
          DISCH_THEN (MP_TAC o HolCore.Lib.C HolLight.AP_THM ([[(y:A,z:A)]])) THEN
          REWRITE_TAC [INSERT, DELETE, IN_ELIM_THM, PAIR_BETA_THM, PAIR_EQ] THEN
          REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC] THEN
        DISCH_THEN (MP_TAC o HolLight.MATCH_MP h11) THEN
        REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC,
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_SIZE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [] THEN UNDISCH_TAC ([[(s:A->bool) HAS_SIZE n + 1]]) THEN
      ASM_SIMP_TAC [HAS_SIZE, FINITE_INSERT, FINITE_DELETE] THEN
      ASM_SIMP_TAC [CARD_DELETE, CARD_CLAUSES, FINITE_DELETE] THEN
      ASM_REWRITE_TAC [IN_DELETE] THEN ARITH_TAC,
      REWRITE_TAC [DISJOINT] THEN
      GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
      REWRITE_TAC [NOT_IN_EMPTY, IN_INTER, h12] THEN
      REWRITE_TAC [FORALL_IN_IMAGE] THEN REWRITE_TAC [FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [([[y:A]]), ([[p:A#A->bool]])] THEN
      REWRITE_TAC [IN_ELIM_THM, PAIR_BETA_THM, PAIR_EQ] THEN
      ONCE_REWRITE_TAC [h13] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
      STRIP_TAC THEN REWRITE_TAC [IN_IMAGE, EXISTS_PAIR_THM, NOT_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[z:A]]), ([[q:A#A->bool]])] THEN
      REWRITE_TAC [PAIR_BETA_THM, IN_ELIM_THM, PAIR_EQ] THEN
      ONCE_REWRITE_TAC [h14] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      ABBREV_TAC ([[w = @w. q(x:A,w:A)]]) THEN
      SUBGOAL_THEN ([[(q:A#A->bool)(x:A,w:A)]]) STRIP_ASSUME_TAC THENL
       [REPEAT (FIRST_X_ASSUM (SUBST1_TAC o HolLight.SYM)) THEN
        CONV_TAC (pureC SELECT_CONV) THEN
        REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN ([[w:A IN s]]) STRIP_ASSUME_TAC THENL
       [REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC, ALL_TAC] THEN
      REWRITE_TAC [LET_DEF, LET_END_DEF] THEN FIRST_X_ASSUM ((fun (_ : thm) => ALL_TAC) o HolLight.SYM) THEN
      ASM_CASES_TAC ([[w:A = z]]) THEN ASM_REWRITE_TAC [] THENL
       [REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC, ALL_TAC] THEN
      ASM_CASES_TAC ([[w:A = y]]) THEN ASM_REWRITE_TAC [] THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC,
        ALL_TAC] THEN
      ASM_CASES_TAC ([[y:A = z]]) THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC, ALL_TAC] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN REL_TAC])
  : ExceptT String IO thm).run
#eval NUMBER_OF_DERANGEMENTS

/- ------------------------------------------------------------------------- -/
/- Trivia.                                                                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 48
def SUM_1 : thm := keep "SUM_1" fun _ => (do
  let h1 ← nc (← ExceptT.mk [[1]])
  prove ([[sum(0..1) f = f 0 + f 1]])
   (REWRITE_TAC [h1, SUM_CLAUSES_NUMSEG, LE_0])
  : ExceptT String IO thm).run
#eval SUM_1

#eval phrase 49
def SUM_2 : thm := keep "SUM_2" fun _ => (do
  let h2 ← nc (← ExceptT.mk [[1]])
  let h1 ← nc (← ExceptT.mk [[2]])
  prove ([[sum(0..2) f = f 0 + f 1 + f 2]])
   (SIMP_TAC [h1, h2, SUM_CLAUSES_NUMSEG, LE_0,
             REAL_ADD_AC])
  : ExceptT String IO thm).run
#eval SUM_2

/- ------------------------------------------------------------------------- -/
/- The key result.                                                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 50
def DERANGEMENTS : thm := keep "DERANGEMENTS" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[SUC(SUC n) = n + 2]])
  let h1 ← ar (← ExceptT.mk [[n + 2 = (n + 1) + 1]])
  prove ([[!n. ~(n = 0)
       ==> &(derangements n) =
           &(FACT n) * sum(0..n) (\k. --(&1) pow k / &(FACT k))]])
   (MATCH_MP_TAC DERANGEMENT_INDUCT THEN REWRITE_TAC [ADD_EQ_0, ARITH_EQ] THEN
    REWRITE_TAC [derangements, SUM_1] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    X_GEN_TAC ([[n:num]]) THEN ASM_CASES_TAC ([[n = 0]]) THEN ASM_REWRITE_TAC [] THENL
     [ASM_REWRITE_TAC [derangements, ARITH, SUM_2, SUM_1] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV,
      ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_MUL), (← HolLight.GSYM REAL_OF_NUM_ADD)] THEN
    DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
    REWRITE_TAC [h1] THEN
    SIMP_TAC [SUM_ADD_SPLIT, LE_0, SUM_SING_NUMSEG] THEN
    REWRITE_TAC [(← HolLight.GSYM ADD1), FACT, (← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
    REWRITE_TAC [real_pow] THEN REWRITE_TAC [h2] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_SUC), (← HolLight.GSYM REAL_OF_NUM_ADD)] THEN
    MP_TAC (← HolLight.SPEC ([[n:num]]) FACT_LT) THEN UNDISCH_TAC ([[~(n = 0)]]) THEN
    REWRITE_TAC [(← HolLight.GSYM LT_NZ), REAL_POW_NEG, (← HolLight.GSYM REAL_OF_NUM_LT), REAL_POW_ONE] THEN
    CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval DERANGEMENTS

/- ------------------------------------------------------------------------- -/
/- A more "explicit" formula. We could sharpen 1/2 to 0.3678794+epsilon      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 51
def DERANGEMENTS_EXP : thm := keep "DERANGEMENTS_EXP" fun _ => (do
  let h6 ← rr (← ExceptT.mk [[&0 < &n + &1]])
  let h5 ← rf (← ExceptT.mk [[&0 < a ==> a * b / ((&n + &1) * a) = b / (&n + &1)]])
  let h4 ← rr (← ExceptT.mk [[abs(a * b - a * (b + c)) = abs(a * c)]])
  let h3 ← ar (← ExceptT.mk [[(0 + n + 1) - 1 = n]])
  let h2 ← rr (← ExceptT.mk [[abs x < a <=> --a < x /\ x < a]])
  let h1 ← ar (← ExceptT.mk [[n < 5 ==> n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4]])
  prove ([[!n. ~(n = 0)
       ==> let e = exp(&1) in
           abs(&(derangements n) - &(FACT n) / e) < &1 / &2]])
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [DERANGEMENTS, LET_DEF, LET_END_DEF] THEN
    REWRITE_TAC [real_div, (← HolLight.GSYM REAL_EXP_NEG)] THEN ASM_CASES_TAC ([[n < 5]]) THENL
     [FIRST_X_ASSUM (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o HolLight.MATCH_MP h1) THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC [ARITH] THEN
      -- REWRITE_TAC(map (num_CONV o mk_small_numeral) (1--5))
      REWRITE_TAC (← (List.range 5).mapM fun i => do
        ExceptT.mk (num_CONV (← ec (mk_small_numeral (Int.ofNat (i + 1)))))) THEN
      REWRITE_TAC [SUM_CLAUSES_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [h2] THEN
      REWRITE_TAC [real_sub] THEN CONJ_TAC THEN CONV_TAC REALCALC_REL_CONV,
      ALL_TAC] THEN
    MP_TAC (← HolLight.SPECL [([[-- &1]]), ([[n + 1]])] MCLAURIN_EXP_LE) THEN
    SIMP_TAC [PSUM_SUM_NUMSEG, ADD_EQ_0, ARITH_EQ] THEN
    REWRITE_TAC [h3, (← HolLight.GSYM real_div)] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[u:real]]) STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [h4] THEN
    REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_DIV, REAL_ABS_POW, REAL_ABS_NEG] THEN
    REWRITE_TAC [REAL_ABS_NUM, REAL_POW_ONE, SessionLibrary.Analysis.REAL_MUL_RID] THEN
    REWRITE_TAC [(← HolLight.GSYM ADD1), FACT, (← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_SUC)] THEN
    SIMP_TAC [REAL_OF_NUM_LT, FACT_LT, h5] THEN
    SIMP_TAC [REAL_LT_LDIV_EQ, h6] THEN
    REWRITE_TAC [real_abs, REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC ([[exp(&1)]]) THEN CONJ_TAC THENL
     [REWRITE_TAC [REAL_EXP_MONO_LE] THEN
      UNDISCH_TAC ([[abs(u) <= abs(-- &1)]]) THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LTE_TRANS THEN EXISTS_TAC ([[&3]]) THEN CONJ_TAC THENL
     [CONV_TAC REALCALC_REL_CONV, ALL_TAC] THEN
    UNDISCH_TAC ([[~(n < 5)]]) THEN REWRITE_TAC [NOT_LT, (← HolLight.GSYM REAL_OF_NUM_LE)] THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval DERANGEMENTS_EXP

/- ------------------------------------------------------------------------- -/
/- Hence the critical "rounding" property.                                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 52
def round : thm := keep "round" fun _ => new_definition
 [[round x = @n. integer(n) /\ n - &1 / &2 <= x /\ x < n + &1 / &2]]
#eval round

#eval phrase 53
def ROUND_WORKS : thm := keep "ROUND_WORKS" fun _ => (do
  prove ([[!x. integer(round x) /\ round x - &1 / &2 <= x /\ x < round x + &1 / &2]])
   (GEN_TAC THEN REWRITE_TAC [round] THEN CONV_TAC (pureC SELECT_CONV) THEN
    EXISTS_TAC ([[floor(x + &1 / &2)]]) THEN MP_TAC (← HolLight.SPEC ([[x + &1 / &2]]) FLOOR) THEN
    SIMP_TAC [INTEGER_CLOSED] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval ROUND_WORKS

#eval phrase 54
-- let DERANGEMENTS_EXP = ... (rebinds DERANGEMENTS_EXP)
def DERANGEMENTS_EXP_2 : thm := keep "DERANGEMENTS_EXP_2" fun _ => (do
  prove ([[!n. ~(n = 0)
       ==> let e = exp(&1) in &(derangements n) = round(&(FACT n) / e)]])
   (REPEAT STRIP_TAC THEN LET_TAC THEN
    MATCH_MP_TAC REAL_EQ_INTEGERS_IMP THEN
    REWRITE_TAC [INTEGER_CLOSED, ROUND_WORKS] THEN
    MP_TAC (← HolLight.SPEC ([[&(FACT n) / e]]) ROUND_WORKS) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP DERANGEMENTS_EXP) THEN
    ASM_REWRITE_TAC [LET_DEF, LET_END_DEF] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval DERANGEMENTS_EXP_2

/- ------------------------------------------------------------------------- -/
/- Put them together.                                                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 55
def THE_DERANGEMENTS_FORMULA : thm := keep "THE_DERANGEMENTS_FORMULA" fun _ => (do
  prove ([[!n s. s HAS_SIZE n /\ ~(n = 0)
         ==> FINITE {p | p deranges s} /\
             let e = exp(&1) in
             &(CARD {p | p deranges s}) = round(&(FACT n) / e)]])
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP NUMBER_OF_DERANGEMENTS) THEN
    ASM_SIMP_TAC [HAS_SIZE, DERANGEMENTS_EXP_2])
  : ExceptT String IO thm).run
#eval THE_DERANGEMENTS_FORMULA

end Hol100.Derangements
