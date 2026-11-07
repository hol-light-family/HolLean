/- File: Hol100/Ballot.lean
Translation of HOL Light's 100/ballot.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Binomial
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Binomial
namespace Hol100.Ballot

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
/-- Run an `IO (Except String α)` once, caching under `name` (OCaml's `let`
    evaluates its right-hand side once), for the `let X,Y,Z = e` bindings
    whose result is a tuple. -/
private def keepIO {α : Type} [Inhabited α] (name : String) (f : Unit → IO (Except String α)) : α :=
  keep name fun _ =>
    match runIO (f ()) with
    | .ok (.ok v) => v
    | .ok (.error e) => panic! s!"keepIO {name}: {e}"
    | .error e => panic! s!"keepIO {name}: {e}"
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def ms (ths : List thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (MESON ths tm)
private def ng (tm : term) : ExceptT String IO thm := ExceptT.mk (NUM_RING tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- Ballot problem.                                                           -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/binomial.ml";;
#eval SessionLibrary.Binomial.ensureBinomial

#eval phrase 2
#eval Session.prioritize_num

/- ------------------------------------------------------------------------- -/
/- Restricted function space.                                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
-- parse_as_infix("-->",(13,"right"));;
#eval (parse_as_infix ("-->", (13, "right")) : IO Unit)

#eval phrase 4
def funspace : thm := keep "funspace" fun _ => new_definition
 [[(s --> t) = {f:A->B | (!x. x IN s ==> f(x) IN t) /\
                        (!x. ~(x IN s) ==> f(x) = @y. T)}]]
#eval funspace

#eval phrase 5
def FUNSPACE_EMPTY : thm := keep "FUNSPACE_EMPTY" fun _ => (do
  prove ([[({} --> t) = {(\x. @y. T)}]])
   (REWRITE_TAC [EXTENSION, IN_SING, funspace, IN_ELIM_THM, NOT_IN_EMPTY] THEN
    REWRITE_TAC [FUN_EQ_THM])
  : ExceptT String IO thm).run
#eval FUNSPACE_EMPTY

#eval phrase 6
def HAS_SIZE_FUNSPACE : thm := keep "HAS_SIZE_FUNSPACE" fun _ => (do
  let h2 ← tt (← ExceptT.mk [[(a /\ b) /\ d <=> d /\ a /\ b]])
  let h1 ← tt (← ExceptT.mk [[(a /\ b /\ c) /\ d <=> d /\ a /\ b /\ c]])
  prove ([[!s:A->bool t:B->bool m n.
        s HAS_SIZE m /\ t HAS_SIZE n ==> (s --> t) HAS_SIZE (n EXP m)]])
   (REWRITE_TAC [HAS_SIZE, (← HolLight.GSYM CONJ_ASSOC)] THEN
    ONCE_REWRITE_TAC [IMP_CONJ] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
     [SIMP_TAC [CARD_CLAUSES, FINITE_RULES, FUNSPACE_EMPTY, NOT_IN_EMPTY] THEN
      REPEAT GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o HolLight.GSYM) THEN
      ASM_REWRITE_TAC [EXP, ARITH],
      ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM HAS_SIZE)] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[(x INSERT s) --> t =
        IMAGE (\(y:B,g) u:A. if u = x then y else g(u))
              {y,g | y IN t /\ g IN s --> t}]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE, funspace, IN_ELIM_THM] THEN
      ONCE_REWRITE_TAC [h1] THEN
      REWRITE_TAC [PAIR_EQ, EXISTS_PAIR_THM, (← HolLight.GSYM CONJ_ASSOC)] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      X_GEN_TAC ([[f:A->B]]) THEN EQ_TAC THENL
       [STRIP_TAC THEN MAP_EVERY EXISTS_TAC [([[(f:A->B) x]]), ([[\u. if u = x then @y. T else (f:A->B) u]])] THEN
        REWRITE_TAC [FUN_EQ_THM] THEN ASM_MESON_TAC [IN_INSERT],
        REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [([[y:B]]), ([[g:A->B]])] THEN
        STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
        ASM_MESON_TAC [IN_INSERT]],
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_THM] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      ONCE_REWRITE_TAC [h2] THEN
      REWRITE_TAC [PAIR_EQ, EXISTS_PAIR_THM, (← HolLight.GSYM CONJ_ASSOC)] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
      REWRITE_TAC [FUN_EQ_THM, funspace, IN_ELIM_THM] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC [IN_INSERT], ALL_TAC] THEN
      X_GEN_TAC ([[u:A]]) THEN ASM_CASES_TAC ([[u:A = x]]) THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    FIRST_X_ASSUM (SUBST_ALL_TAC o HolLight.SYM) THEN ASM_SIMP_TAC [CARD_CLAUSES, EXP] THEN
    MATCH_MP_TAC HAS_SIZE_PRODUCT THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval HAS_SIZE_FUNSPACE

#eval phrase 7
def FINITE_FUNSPACE : thm := keep "FINITE_FUNSPACE" fun _ => (do
  prove ([[!s t. FINITE s /\ FINITE t ==> FINITE(s --> t)]])
   (MESON_TAC [HAS_SIZE_FUNSPACE, HAS_SIZE])
  : ExceptT String IO thm).run
#eval FINITE_FUNSPACE

/- ------------------------------------------------------------------------- -/
/- Definition of the problem.                                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 8
-- let vote_INDUCT,vote_RECURSION = define_type ...
def vote_INDUCT_defs : thm × thm :=
  keepIO "vote_INDUCT_defs" fun _ => define_type
  "vote = A | B"
def vote_INDUCT : thm := vote_INDUCT_defs.1
def vote_RECURSION : thm := vote_INDUCT_defs.2
#eval do IO.println (repr vote_INDUCT); IO.println (repr vote_RECURSION)

#eval phrase 9
def all_countings : thm := keep "all_countings" fun _ => new_definition
 [[all_countings a b =
        let n = a + b in
        CARD {f | f IN (1..n --> {A,B}) /\
                  CARD { i | i IN 1..n /\ f(i) = A} = a /\
                  CARD { i | i IN 1..n /\ f(i) = B} = b}]]
#eval all_countings

#eval phrase 10
def valid_countings : thm := keep "valid_countings" fun _ => new_definition
 [[valid_countings a b =
        let n = a + b in
        CARD {f | f IN (1..n --> {A,B}) /\
                  CARD { i | i IN 1..n /\ f(i) = A} = a /\
                  CARD { i | i IN 1..n /\ f(i) = B} = b /\
                  !m. 1 <= m /\ m <= n
                      ==> CARD { i | i IN 1..m /\ f(i) = A} >
                          CARD { i | i IN 1..m /\ f(i) = B}}]]
#eval valid_countings

/- ------------------------------------------------------------------------- -/
/- Various lemmas.                                                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 11
-- let vote_CASES = cases "vote" and vote_DISTINCT = distinctness "vote"
def vote_CASES : thm := keep "vote_CASES" fun _ => cases "vote"
def vote_DISTINCT : thm := keep "vote_DISTINCT" fun _ => distinctness "vote"
#eval do IO.println (repr vote_CASES); IO.println (repr vote_DISTINCT)

#eval phrase 12
def FINITE_COUNTINGS : thm := keep "FINITE_COUNTINGS" fun _ => (do
  prove ([[FINITE {f | f IN (1..n --> {A,B}) /\ P f}]])
   (MATCH_MP_TAC FINITE_RESTRICT THEN
    MATCH_MP_TAC FINITE_FUNSPACE THEN
    REWRITE_TAC [FINITE_NUMSEG, FINITE_INSERT, FINITE_RULES])
  : ExceptT String IO thm).run
#eval FINITE_COUNTINGS

#eval phrase 13
def UNIV_VOTE : thm := keep "UNIV_VOTE" fun _ => (do
  prove ([[(:vote) = {A,B}]])
   (REWRITE_TAC [EXTENSION, IN_UNIV, IN_INSERT, NOT_IN_EMPTY, vote_CASES])
  : ExceptT String IO thm).run
#eval UNIV_VOTE

#eval phrase 14
def ADD1_NOT_IN_NUMSEG : thm := keep "ADD1_NOT_IN_NUMSEG" fun _ => (do
  prove ([[!m n. ~((n + 1) IN m..n)]])
   (REWRITE_TAC [IN_NUMSEG] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval ADD1_NOT_IN_NUMSEG

#eval phrase 15
def NUMSEG_1_CLAUSES : thm := keep "NUMSEG_1_CLAUSES" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[1 <= SUC n]])
  prove ([[!n. 1..(n+1) = (n + 1) INSERT (1..n)]])
   (REWRITE_TAC [(← HolLight.GSYM ADD1), NUMSEG_CLAUSES, h1])
  : ExceptT String IO thm).run
#eval NUMSEG_1_CLAUSES

#eval phrase 16
def NUMSEG_RESTRICT_SUC : thm := keep "NUMSEG_RESTRICT_SUC" fun _ => (do
  prove ([[{i | i IN 1..(n+1) /\ P i} =
        if P(n + 1) then (n + 1) INSERT {i | i IN 1..n /\ P i}
        else {i | i IN 1..n /\ P i}]])
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [EXTENSION, IN_ELIM_THM, NUMSEG_1_CLAUSES, IN_INSERT] THEN
    ASM_MESON_TAC [ADD1_NOT_IN_NUMSEG])
  : ExceptT String IO thm).run
#eval NUMSEG_RESTRICT_SUC

#eval phrase 17
def CARD_NUMSEG_RESTRICT_SUC : thm := keep "CARD_NUMSEG_RESTRICT_SUC" fun _ => (do
  prove ([[CARD {i | i IN 1..(n+1) /\ P i} =
        if P(n + 1) then CARD {i | i IN 1..n /\ P i} + 1
        else CARD {i | i IN 1..n /\ P i}]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [NUMSEG_RESTRICT_SUC] THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC [CARD_CLAUSES, FINITE_RESTRICT, FINITE_NUMSEG] THEN
    REWRITE_TAC [IN_ELIM_THM, ADD1_NOT_IN_NUMSEG, ADD1])
  : ExceptT String IO thm).run
#eval CARD_NUMSEG_RESTRICT_SUC

#eval phrase 18
def FORALL_RANGE_SUC : thm := keep "FORALL_RANGE_SUC" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[1 <= n + 1]])
  let h1 ← ar (← ExceptT.mk [[i <= n + 1 <=> i <= n \/ i = n + 1]])
  prove ([[(!i. 1 <= i /\ i <= n + 1 ==> P i) <=>
      P(n + 1) /\ (!i. 1 <= i /\ i <= n ==> P i)]])
   (REWRITE_TAC [h1] THEN
    MESON_TAC [h2])
  : ExceptT String IO thm).run
#eval FORALL_RANGE_SUC

#eval phrase 19
def IN_NUMSEG_RESTRICT_FALSE : thm := keep "IN_NUMSEG_RESTRICT_FALSE" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[i <= m /\ m <= n ==> ~(i = n + 1)]])
  prove ([[m <= n
   ==> (i IN 1..m /\ (if i = n + 1 then p i else q i) <=> i IN 1..m /\ q i)]])
   (REWRITE_TAC [IN_NUMSEG] THEN
    MESON_TAC [h1])
  : ExceptT String IO thm).run
#eval IN_NUMSEG_RESTRICT_FALSE

#eval phrase 20
def CARD_NUMSEG_RESTRICT_EXTREMA : thm := keep "CARD_NUMSEG_RESTRICT_EXTREMA" fun _ => (do
  prove ([[(CARD {i | i IN 1..n /\ P i} = n <=> !i. 1 <= i /\ i <= n ==> P i) /\
   (CARD {i | i IN 1..n /\ P i} = 0 <=> !i. 1 <= i /\ i <= n ==> ~(P i))]])
   (SIMP_TAC [CARD_EQ_0, FINITE_RESTRICT, FINITE_NUMSEG] THEN
    MP_TAC (← HolLight.ISPECL [([[{i | i IN 1..n /\ P i}]]), ([[1..n]])] SUBSET_CARD_EQ) THEN
    SIMP_TAC [FINITE_NUMSEG, SUBSET, IN_ELIM_THM, CARD_NUMSEG_1] THEN
    DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
    REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, IN_NUMSEG, IN_ELIM_THM] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval CARD_NUMSEG_RESTRICT_EXTREMA

#eval phrase 21
def VOTE_NOT_EQ : thm := keep "VOTE_NOT_EQ" fun _ => (do
  prove ([[(!x. ~(x = A) <=> x = B) /\
   (!x. ~(x = B) <=> x = A)]])
   (MESON_TAC [vote_CASES, vote_DISTINCT])
  : ExceptT String IO thm).run
#eval VOTE_NOT_EQ

#eval phrase 22
def FUNSPACE_FIXED : thm := keep "FUNSPACE_FIXED" fun _ => (do
  prove ([[{f | f IN (s --> t) /\ (!i. i IN s ==> f i = a)} =
   if s = {} \/ a IN t then {(\i. if i IN s then a else @x. T)} else {}]])
   (REWRITE_TAC [EXTENSION, NOT_IN_EMPTY] THEN GEN_TAC THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC [IN_ELIM_THM, funspace, NOT_IN_EMPTY, IN_SING] THEN
    REWRITE_TAC [FUN_EQ_THM] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval FUNSPACE_FIXED

#eval phrase 23
def COUNTING_LEMMA : thm := keep "COUNTING_LEMMA" fun _ => (do
  let h1 ← ms [] (← ExceptT.mk [[P x ==> x = y ==> P y]])
  prove ([[CARD {f | f IN (1..(n+1) --> {A,B}) /\ P f} =
   CARD {f | f IN (1..n --> {A,B}) /\ P (\i. if i = n + 1 then A else f i)} +
   CARD {f | f IN (1..n --> {A,B}) /\ P (\i. if i = n + 1 then B else f i)}]])
   (MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[CARD {f | f IN (1..(n+1) --> {A,B}) /\ f(n+1) = A /\ P f} +
              CARD {f | f IN (1..(n+1) --> {A,B}) /\ f(n+1) = B /\ P f}]]) THEN
    CONJ_TAC THENL
     [CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
      REWRITE_TAC [FINITE_COUNTINGS, EXTENSION, IN_INTER, IN_UNION] THEN
      REWRITE_TAC [IN_ELIM_THM, NOT_IN_EMPTY] THEN
      MESON_TAC [vote_CASES, vote_DISTINCT],
      ALL_TAC] THEN
    BINOP_TAC THEN
    MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
    EXISTS_TAC ([[\f i. if i = n + 1 then @x:vote. T else f i]]) THENL
     [EXISTS_TAC ([[\f i. if i = n + 1 then A else f i]]),
      EXISTS_TAC ([[\f i. if i = n + 1 then B else f i]])] THEN
    REWRITE_TAC [FINITE_COUNTINGS] THEN
    REWRITE_TAC [IN_ELIM_THM, funspace, (← HolLight.GSYM UNIV_VOTE), IN_UNIV] THEN
    REWRITE_TAC [NUMSEG_1_CLAUSES, IN_INSERT] THEN REPEAT STRIP_TAC THEN
    TRY (FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h1)) THEN
    TRY (GEN_REWRITE_TAC HolCore.Lib.I [FUN_EQ_THM]) THEN ASM_MESON_TAC [ADD1_NOT_IN_NUMSEG])
  : ExceptT String IO thm).run
#eval COUNTING_LEMMA

/- ------------------------------------------------------------------------- -/
/- Recurrence relations.                                                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 24
def ALL_COUNTINGS_0 : thm := keep "ALL_COUNTINGS_0" fun _ => (do
  prove ([[!a. all_countings a 0 = 1 /\ all_countings 0 a = 1]])
   (REWRITE_TAC [all_countings, CARD_NUMSEG_RESTRICT_EXTREMA, (← HolLight.GSYM IN_NUMSEG),
                LET_DEF, LET_END_DEF, ADD_CLAUSES, VOTE_NOT_EQ] THEN
    REWRITE_TAC [FUNSPACE_FIXED, IN_INSERT] THEN
    SIMP_TAC [CARD_CLAUSES, FINITE_RULES, NOT_IN_EMPTY, ARITH_SUC])
  : ExceptT String IO thm).run
#eval ALL_COUNTINGS_0

#eval phrase 25
def VALID_COUNTINGS_0 : thm := keep "VALID_COUNTINGS_0" fun _ => (do
  let lemma ← prove ([[{x} INTER s = if x IN s then {x} else {}]])
     (COND_CASES_TAC THEN HolLight.ASM SET_TAC [])
  let h10 ← sr (← ExceptT.mk [[{x | F} = {} /\ {x | x = a} = {a}]])
  let h9 ← ar (← ExceptT.mk [[1 <= SUC n]])
  let h8 ← sr (← ExceptT.mk [[{x | x = a /\ P x} = {x | x = a /\ P a}]])
  let h7 ← ar (← ExceptT.mk [[b = 0 /\ ~(a = 0) ==> ~(b > a)]])
  let h6 ← ar (← ExceptT.mk [[1 <= SUC n]])
  let h5 ← ar (← ExceptT.mk [[1 <= k /\ k <= a ==> 1 <= k /\ !i. i <= k ==> i <= a]])
  let h4 ← ar (← ExceptT.mk [[b = 0 /\ ~(a = 0) ==> a > b]])
  let h3 ← sr (← ExceptT.mk [[{x | P x /\ Q x /\ R x} =
                             {x | P x /\ Q x} INTER {x | R x}]])
  let h2 ← sr (← ExceptT.mk [[{x | x = a} = {a}]])
  let h1 ← tt (← ExceptT.mk [[a /\ a /\ b <=> a /\ b]])
  prove ([[valid_countings 0 0 = 1 /\
   !a. valid_countings (SUC a) 0 = 1 /\ valid_countings 0 (SUC a) = 0]])
   (REWRITE_TAC [valid_countings, CARD_NUMSEG_RESTRICT_EXTREMA, (← HolLight.GSYM IN_NUMSEG),
                LET_DEF, LET_END_DEF, ADD_CLAUSES, VOTE_NOT_EQ,
                h1] THEN
    REWRITE_TAC [(← HolLight.CONJUNCT1 NUMSEG_CLAUSES), ARITH_EQ, NOT_IN_EMPTY] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [funspace, IN_ELIM_THM, NOT_IN_EMPTY, (← HolLight.GSYM FUN_EQ_THM)] THEN
      REWRITE_TAC [h2] THEN
      SIMP_TAC [CARD_CLAUSES, FINITE_RULES, NOT_IN_EMPTY, ARITH],
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [h3] THEN
    REWRITE_TAC [FUNSPACE_FIXED, IN_INSERT, lemma] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    GEN_TAC THEN CONJ_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [CARD_CLAUSES, FINITE_RULES, NOT_IN_EMPTY, ARITH] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [NOT_FORALL_THM] THENL
     [X_GEN_TAC ([[k:num]]) THEN DISCH_TAC THEN
      MATCH_MP_TAC h4 THEN
      ASM_SIMP_TAC [CARD_NUMSEG_RESTRICT_EXTREMA] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [IN_NUMSEG]) THEN
      DISCH_THEN (ASSUME_TAC o HolLight.MATCH_MP h5) THEN
      ASM_SIMP_TAC [IN_NUMSEG, vote_DISTINCT] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[1]])) THEN POP_ASSUM MP_TAC THEN ARITH_TAC,
      EXISTS_TAC ([[1]]) THEN REWRITE_TAC [NUMSEG_SING, IN_SING] THEN
      REWRITE_TAC [IN_NUMSEG, LE_REFL, h6] THEN
      MATCH_MP_TAC h7 THEN
      ONCE_REWRITE_TAC [h8] THEN
      REWRITE_TAC [IN_NUMSEG, LE_REFL, h9] THEN
      SIMP_TAC [vote_DISTINCT, h10,
               CARD_CLAUSES, FINITE_RULES, NOT_IN_EMPTY, ARITH]])
  : ExceptT String IO thm).run
#eval VALID_COUNTINGS_0

#eval phrase 26
def ALL_COUNTINGS_SUC : thm := keep "ALL_COUNTINGS_SUC" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[(a + 1) + b = a + b + 1]])
  let h1 ← ar (← ExceptT.mk [[(a + 1) + (b + 1) = (a + b + 1) + 1]])
  prove ([[!a b. all_countings (a + 1) (b + 1) =
                all_countings a (b + 1) + all_countings (a + 1) b]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [all_countings] THEN
    SUBST1_TAC h1 THEN
    SUBST1_TAC h2 THEN
    ABBREV_TAC ([[n = a + b + 1]]) THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [COUNTING_LEMMA] THEN
    REWRITE_TAC [] THEN BINOP_TAC THEN
    ONCE_REWRITE_TAC [COND_RAND] THEN ONCE_REWRITE_TAC [COND_RATOR] THEN
    REWRITE_TAC [vote_DISTINCT] THEN
    REWRITE_TAC [CARD_NUMSEG_RESTRICT_SUC] THEN
    SIMP_TAC [IN_NUMSEG_RESTRICT_FALSE, LE_REFL, EQ_ADD_RCANCEL])
  : ExceptT String IO thm).run
#eval ALL_COUNTINGS_SUC

#eval phrase 27
def VALID_COUNTINGS_SUC : thm := keep "VALID_COUNTINGS_SUC" fun _ => (do
  let h4 ← sr (← ExceptT.mk [[{x | F} = EMPTY]])
  let h3 ← ms [] (← ExceptT.mk [[x = a /\ y = b /\ P x y <=> x = a /\ y = b /\ P a b]])
  let h2 ← ar (← ExceptT.mk [[(a + 1) + b = a + b + 1]])
  let h1 ← ar (← ExceptT.mk [[(a + 1) + (b + 1) = (a + b + 1) + 1]])
  prove ([[!a b. valid_countings (a + 1) (b + 1) =
                if a <= b then 0
                else valid_countings a (b + 1) + valid_countings (a + 1) b]])
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC ([[b:num < a]]) THEN ASM_REWRITE_TAC [(← HolLight.GSYM NOT_LT)] THEN
    REWRITE_TAC [valid_countings] THEN
    SUBST1_TAC h1 THEN
    SUBST1_TAC h2 THEN
    ABBREV_TAC ([[n = a + b + 1]]) THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [COUNTING_LEMMA] THEN REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [COND_RAND] THEN ONCE_REWRITE_TAC [COND_RATOR] THEN
    REWRITE_TAC [vote_DISTINCT] THEN
    REWRITE_TAC [FORALL_RANGE_SUC] THEN
    REWRITE_TAC [CARD_NUMSEG_RESTRICT_SUC] THEN
    SIMP_TAC [IN_NUMSEG_RESTRICT_FALSE, LE_REFL, EQ_ADD_RCANCEL] THEN
    SIMP_TAC [h3] THEN
    ASM_REWRITE_TAC [GT, LT_ADD_RCANCEL] THEN
    REWRITE_TAC [h4, CARD_CLAUSES, ADD_CLAUSES])
  : ExceptT String IO thm).run
#eval VALID_COUNTINGS_SUC

/- ------------------------------------------------------------------------- -/
/- Main result.                                                              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 28
def ALL_COUNTINGS : thm := keep "ALL_COUNTINGS" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[a < SUC a]])
  let h1 ← ar (← ExceptT.mk [[1 = a + 1 <=> a = 0]])
  prove ([[!a b. all_countings a b = binom(a + b,a)]])
   (INDUCT_TAC THEN
    REWRITE_TAC [ADD_CLAUSES, BINOM_REFL, binom, ALL_COUNTINGS_0] THEN
    INDUCT_TAC THEN
    REWRITE_TAC [ADD_CLAUSES, BINOM_REFL, binom, ALL_COUNTINGS_0] THEN
    REWRITE_TAC [h1, BINOM_EQ_0,
                h2] THEN
    REWRITE_TAC [ALL_COUNTINGS_SUC, ADD1] THEN
    ASM_REWRITE_TAC [binom, (← HolLight.GSYM ADD1)] THEN
    REWRITE_TAC [ADD_CLAUSES, ADD_AC])
  : ExceptT String IO thm).run
#eval ALL_COUNTINGS

#eval phrase 29
def VALID_COUNTINGS : thm := keep "VALID_COUNTINGS" fun _ => (do
  let h4 ← ar (← ExceptT.mk [[~(a <= b) ==> b <= SUC a /\ SUC b <= a /\ SUC b <= SUC a]])
  let h3 ← ar (← ExceptT.mk [[b + a:num = a + b]])
  let h2 ← ng (← ExceptT.mk [[~(a + b + 1 = 0) /\
    (SUC a + SUC b) *
    ((SUC a + b) * (a + SUC b) * y + (a + SUC b) * (SUC a + b) * z) =
    (SUC a + b) * (a + SUC b) * w
    ==> (SUC a + SUC b) * (y + z) = w]])
  let h1 ← ar (← ExceptT.mk [[a <= b ==> SUC a - SUC b = 0]])
  prove ([[!a b. (a + b) * valid_countings a b = (a - b) * binom(a + b,a)]])
   (INDUCT_TAC THENL
     [REWRITE_TAC [VALID_COUNTINGS_0, SUB_0, MULT_CLAUSES] THEN INDUCT_TAC THEN
      ASM_REWRITE_TAC [VALID_COUNTINGS_0, MULT_CLAUSES, ADD_CLAUSES],
      ALL_TAC] THEN
    INDUCT_TAC THENL
     [REWRITE_TAC [VALID_COUNTINGS_0, ADD_CLAUSES, BINOM_REFL, SUB_0],
      ALL_TAC] THEN
    REWRITE_TAC [ADD1, VALID_COUNTINGS_SUC] THEN REWRITE_TAC [(← HolLight.GSYM ADD1)] THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC [MULT_CLAUSES, h1] THEN
    MATCH_MP_TAC h2 THEN
    ASM_REWRITE_TAC [ADD_EQ_0, ARITH] THEN
    MP_TAC (← HolLight.SPECL [([[SUC b]]), ([[a:num]])] BINOM_FACT) THEN
    MP_TAC (← HolLight.SPECL [([[b:num]]), ([[SUC a]])] BINOM_FACT) THEN
    MP_TAC (← HolLight.SPECL [([[SUC b]]), ([[SUC a]])] BINOM_FACT) THEN
    REWRITE_TAC [ADD_CLAUSES, FACT] THEN
    SUBST1_TAC h3 THEN
    MAP_EVERY (fun t => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC t FACT_LT))) [([[a:num]]), ([[b:num]]), ([[a + b:num]])] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM REAL_OF_NUM_EQ), (← HolLight.GSYM REAL_OF_NUM_MUL), (← HolLight.GSYM REAL_OF_NUM_ADD),
      (← HolLight.GSYM REAL_OF_NUM_SUC), (← HolLight.GSYM REAL_OF_NUM_SUB), REAL_OF_NUM_LE, LT_NZ,
      h4] THEN
    CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval VALID_COUNTINGS

#eval phrase 30
def BALLOT : thm := keep "BALLOT" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[~(a <= b) ==> SUC b <= SUC a]])
  let h1 ← ar (← ExceptT.mk [[a <= b ==> (SUC a - SUC b) = 0]])
  prove ([[!a b. &(valid_countings a b) =
            if a <= b then if b = 0 then &1 else &0
            else (&a - &b) / (&a + &b) *  &(all_countings a b)]])
   (REPEAT INDUCT_TAC THEN REWRITE_TAC [ALL_COUNTINGS_0, VALID_COUNTINGS_0] THEN
    REWRITE_TAC [LE_REFL, REAL_MUL_LID, LE_0, NOT_SUC, (← HolLight.CONJUNCT1 LE)] THEN
    SIMP_TAC [REAL_ADD_RID, REAL_SUB_RZERO, REAL_DIV_REFL, REAL_OF_NUM_EQ,
             NOT_SUC, REAL_MUL_LID] THEN
    MP_TAC (← HolLight.SPECL [([[SUC a]]), ([[SUC b]])] VALID_COUNTINGS) THEN
    REWRITE_TAC [(← HolLight.GSYM ALL_COUNTINGS), LE_SUC] THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC [h1] THEN
    REWRITE_TAC [MULT_EQ_0, MULT_CLAUSES, ADD_EQ_0, NOT_SUC, REAL_OF_NUM_EQ] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM REAL_OF_NUM_EQ), (← HolLight.GSYM REAL_OF_NUM_MUL), (← HolLight.GSYM REAL_OF_NUM_ADD),
                 (← HolLight.GSYM REAL_OF_NUM_SUC), (← HolLight.GSYM REAL_OF_NUM_SUB),
                 h2] THEN
    CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval BALLOT

end Hol100.Ballot
