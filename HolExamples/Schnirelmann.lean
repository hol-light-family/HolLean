/- File: HolExamples/Schnirelmann.lean
Translation of HOL Light's Examples/schnirelmann.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
import SessionMultiLib.Misc
import SessionLibrary.Products
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionMultiLib.Misc SessionLibrary.Products
namespace HolExamples.Schnirelmann

/- Helpers: the session's `prove` lifted into `ExceptT String IO`, so tactic
   scripts read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def rf (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_FIELD tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def nd (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.new_definition tm)

/- A `let A,B = (CONJ_PAIR o prove)(...)` phrase: run the proof once and print
   both theorems as `val A : thm = |- ...` / `val B : thm = |- ...` (compare.py
   strips the `val x : thm =` prefixes). -/
private def runPair (x : ExceptT String IO (thm × thm)) : thm × thm :=
  match runIO x.run with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
private def printTwo (p : thm × thm) : IO Unit := do
  IO.println (← HolCore.Printer.string_of_thm p.1)
  IO.println (← HolCore.Printer.string_of_thm p.2)

-- ========================================================================= --
-- Schnirelmann density and its basic properties (not Mann's theorem yet).   --
-- ========================================================================= --

#eval phrase 1
-- needs "Multivariate/misc.ml";;
#eval SessionMultiLib.Misc.ensureMisc

#eval phrase 2
-- needs "Library/products.ml";;
#eval SessionLibrary.Products.ensureProducts

#eval phrase 3
-- prioritize_real();;
#eval Session.prioritize_real

-- ------------------------------------------------------------------------- --
-- The basic definition.                                                     --
-- ------------------------------------------------------------------------- --

#eval phrase 4
def count : thm := keep "count" fun _ => (do
  nd ([[count s n = CARD (s INTER (1..n))]])
  : ExceptT String IO thm).run
#eval count

#eval phrase 5
def schnirelmann : thm := keep "schnirelmann" fun _ => (do
  nd ([[schnirelmann s = inf { &(count s n) / &n | 1 <= n}]])
  : ExceptT String IO thm).run
#eval schnirelmann

-- ------------------------------------------------------------------------- --
-- Basic properties of the "count" function.                                 --
-- ------------------------------------------------------------------------- --

#eval phrase 6
def COUNT_BOUND : thm := keep "COUNT_BOUND" fun _ => (do
  prove ([[!s. count s n <= n]])
   (GEN_TAC THEN REWRITE_TAC [count] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM CARD_NUMSEG_1)] THEN
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC [FINITE_NUMSEG] THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval COUNT_BOUND

#eval phrase 7
def COUNT_UNIV : thm := keep "COUNT_UNIV" fun _ => (do
  prove ([[!n. count (:num) n = n]])
   (REWRITE_TAC [count, INTER_UNIV, CARD_NUMSEG_1])
  : ExceptT String IO thm).run
#eval COUNT_UNIV

#eval phrase 8
def COUNT_MONO : thm := keep "COUNT_MONO" fun _ => (do
  prove ([[!s t n. s SUBSET t ==> count s n <= count t n]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [count] THEN
    MATCH_MP_TAC CARD_SUBSET THEN
    ASM_SIMP_TAC [FINITE_INTER, FINITE_NUMSEG] THEN HolLight.ASM SET_TAC [])
  : ExceptT String IO thm).run
#eval COUNT_MONO

#eval phrase 9
def COUNT_INSENSITIVE : thm := keep "COUNT_INSENSITIVE" fun _ => (do
  prove ([[!s t n. (!m. 1 <= m ==> (m IN s <=> m IN t))
         ==> count s n = count t n]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [count] THEN
    AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_INTER, IN_NUMSEG] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval COUNT_INSENSITIVE

-- ------------------------------------------------------------------------- --
-- The straightforward properties of Schnirelmann density.                   --
-- ------------------------------------------------------------------------- --

#eval phrase 10
def SCHNIRELMANN_UBOUND_LBOUND : thm × thm :=
  keep "SCHNIRELMANN_UBOUND_LBOUND" fun _ => runPair (do
  -- OCaml builds the tactic (and the `prove` pair) right to left.
  let b1 ← sr ([[(!x. x IN {f x | P x} ==> Q x) <=> !x. P x ==> Q(f x)]])
  let b0 ← HolLight.ISPEC ([[{ &(count s n) / &n | 1 <= n}]]) INF
  HolLight.CONJ_PAIR (← prove
   ([[(!n. 1 <= n ==> schnirelmann s <= &(count s n) / &n) /\
     (!b. (!n. 1 <= n ==> b <= &(count s n) / &n) ==> b <= schnirelmann s)]])
   (MP_TAC b0 THEN
    SIMP_TAC [b1,
             (← HolLight.GSYM schnirelmann)] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [SET_TAC [LE_REFL], ALL_TAC] THEN
      EXISTS_TAC ([[&0]]) THEN SIMP_TAC [REAL_LE_DIV, REAL_POS],
      MESON_TAC []])))
#eval printTwo SCHNIRELMANN_UBOUND_LBOUND
def SCHNIRELMANN_UBOUND : thm := SCHNIRELMANN_UBOUND_LBOUND.1
def SCHNIRELMANN_LBOUND : thm := SCHNIRELMANN_UBOUND_LBOUND.2

#eval phrase 11
def SCHNIRELMANN_UBOUND_MUL : thm := keep "SCHNIRELMANN_UBOUND_MUL" fun _ => (do
  let b1 ← ar ([[n = 0 \/ 1 <= n]])
  prove ([[!n s. schnirelmann s * &n <= &(count s n)]])
   (REPEAT GEN_TAC THEN
    DISJ_CASES_TAC b1 THEN
    ASM_REWRITE_TAC [REAL_MUL_RZERO, REAL_POS] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ), REAL_OF_NUM_LT, LE_1,
                 SCHNIRELMANN_UBOUND])
  : ExceptT String IO thm).run
#eval SCHNIRELMANN_UBOUND_MUL

#eval phrase 12
def SCHNIRELMANN_BOUNDS : thm := keep "SCHNIRELMANN_BOUNDS" fun _ => (do
  let b1 ← sr ([[(!x. x IN {f x | P x} ==> Q x) <=> !x. P x ==> Q(f x)]])
  prove ([[!s. &0 <= schnirelmann s /\ schnirelmann s <= &1]])
   (GEN_TAC THEN REWRITE_TAC [schnirelmann] THEN
    MATCH_MP_TAC REAL_INF_BOUNDS THEN
    CONJ_TAC THENL [SET_TAC [LE_REFL], ALL_TAC] THEN
    SIMP_TAC [b1,
             REAL_LE_DIV, REAL_POS, REAL_LE_LDIV_EQ, REAL_OF_NUM_LT, LE_1] THEN
    REWRITE_TAC [REAL_MUL_LID, REAL_OF_NUM_LE, COUNT_BOUND])
  : ExceptT String IO thm).run
#eval SCHNIRELMANN_BOUNDS

#eval phrase 13
def SCHNIRELMANN_MONO : thm := keep "SCHNIRELMANN_MONO" fun _ => (do
  prove ([[!s t. s SUBSET t ==> schnirelmann s <= schnirelmann t]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SCHNIRELMANN_LBOUND THEN
    X_GEN_TAC ([[n:num]]) THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC ([[&(count s n) / &n]]) THEN ASM_SIMP_TAC [SCHNIRELMANN_UBOUND] THEN
    ASM_SIMP_TAC [REAL_LE_DIV2_EQ, REAL_OF_NUM_LT, LE_1] THEN
    ASM_SIMP_TAC [REAL_OF_NUM_LE, COUNT_MONO])
  : ExceptT String IO thm).run
#eval SCHNIRELMANN_MONO

#eval phrase 14
def SCHNIRELMANN_INSENSITIVE : thm := keep "SCHNIRELMANN_INSENSITIVE" fun _ => (do
  prove ([[!s t. (!n. 1 <= n ==> (n IN s <=> n IN t))
         ==> schnirelmann s = schnirelmann t]])
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP COUNT_INSENSITIVE) THEN
    SIMP_TAC [schnirelmann])
  : ExceptT String IO thm).run
#eval SCHNIRELMANN_INSENSITIVE

#eval phrase 15
def SCHNIRELMANN_SENSITIVE : thm := keep "SCHNIRELMANN_SENSITIVE" fun _ => (do
  let b2 ← ar ([[1 <= k ==> (x <= k - 1 <=> x <= k /\ ~(x = k))]])
  let b1 ← rf ([[&1 <= x ==> (&1 - &1 / x) = (x - &1) / x]])
  prove ([[!s k. 1 <= k /\ ~(k IN s) ==> schnirelmann s <= &1 - &1 / &k]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC ([[&(count s k) / &k]]) THEN
    ASM_SIMP_TAC [SCHNIRELMANN_UBOUND] THEN
    ASM_SIMP_TAC [b1,
                 REAL_OF_NUM_LE, REAL_LE_DIV2_EQ, REAL_OF_NUM_LT, LE_1] THEN
    ASM_SIMP_TAC [REAL_OF_NUM_SUB, REAL_OF_NUM_LE, count] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM CARD_NUMSEG_1)] THEN
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC [FINITE_NUMSEG] THEN
    REWRITE_TAC [SUBSET, IN_NUMSEG, IN_INTER] THEN
    ASM_MESON_TAC [b2])
  : ExceptT String IO thm).run
#eval SCHNIRELMANN_SENSITIVE

#eval phrase 16
def SCHNIRELMANN_SENSITIVE_1 : thm := keep "SCHNIRELMANN_SENSITIVE_1" fun _ => (do
  let b2 ← HolLight.SPEC ([[s:num->bool]]) SCHNIRELMANN_BOUNDS
  let b1 ← HolLight.SPECL [([[s:num->bool]]), ([[1]])] SCHNIRELMANN_SENSITIVE
  prove ([[!s. ~(1 IN s) ==> schnirelmann s = &0]])
   (REPEAT STRIP_TAC THEN
    MP_TAC b1 THEN
    MP_TAC b2 THEN
    ASM_REWRITE_TAC [LE_REFL] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval SCHNIRELMANN_SENSITIVE_1

#eval phrase 17
def SCHNIRELMANN_UNIV : thm := keep "SCHNIRELMANN_UNIV" fun _ => (do
  prove ([[schnirelmann(:num) = &1]])
   (REWRITE_TAC [(← HolLight.GSYM REAL_LE_ANTISYM), SCHNIRELMANN_BOUNDS] THEN
    MATCH_MP_TAC SCHNIRELMANN_LBOUND THEN
    SIMP_TAC [COUNT_UNIV, REAL_DIV_REFL, REAL_OF_NUM_EQ, LE_1, REAL_LE_REFL])
  : ExceptT String IO thm).run
#eval SCHNIRELMANN_UNIV

#eval phrase 18
def SCHNIRELMANN_EQ_1 : thm := keep "SCHNIRELMANN_EQ_1" fun _ => (do
  let b1 ← rr ([[&0 < x ==> s <= &1 - x ==> ~(s = &1)]])
  prove ([[!s. schnirelmann s = &1 <=> !n. 1 <= n ==> n IN s]])
   (GEN_TAC THEN EQ_TAC THENL
     [ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN
      REWRITE_TAC [EXTENSION, NOT_FORALL_THM, IN_UNIV, NOT_IMP] THEN
      DISCH_THEN (CHOOSE_THEN ASSUME_TAC) THEN
      FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP SCHNIRELMANN_SENSITIVE) THEN
      MATCH_MP_TAC b1 THEN
      ASM_SIMP_TAC [REAL_LT_DIV, REAL_OF_NUM_LT, LE_1, ARITH],
      REPEAT STRIP_TAC THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM SCHNIRELMANN_UNIV)] THEN
      MATCH_MP_TAC SCHNIRELMANN_INSENSITIVE THEN
      ASM_REWRITE_TAC [IN_UNIV]])
  : ExceptT String IO thm).run
#eval SCHNIRELMANN_EQ_1

-- ------------------------------------------------------------------------- --
-- Sum-sets.                                                                 --
-- ------------------------------------------------------------------------- --

#eval phrase 19
#eval (parse_as_infix ("+++", (16, "right")) : IO Unit)

#eval phrase 20
def sumset : thm := keep "sumset" fun _ => (do
  nd ([[s +++ t = {x + y:num | x IN s /\ y IN t}]])
  : ExceptT String IO thm).run
#eval sumset

#eval phrase 21
def SUMSET_0 : thm := keep "SUMSET_0" fun _ => (do
  prove ([[!s t. 0 IN s /\ 0 IN t ==> 0 IN (s +++ t)]])
   (SIMP_TAC [sumset, IN_ELIM_THM] THEN MESON_TAC [ADD_CLAUSES])
  : ExceptT String IO thm).run
#eval SUMSET_0

#eval phrase 22
def SUMSET_SUPERSET_LZERO : thm := keep "SUMSET_SUPERSET_LZERO" fun _ => (do
  prove ([[!s t. 0 IN s ==> t SUBSET (s +++ t)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [SUBSET, sumset, IN_ELIM_THM] THEN
    X_GEN_TAC ([[n:num]]) THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [([[0]]), ([[n:num]])] THEN ASM_REWRITE_TAC [ADD_CLAUSES])
  : ExceptT String IO thm).run
#eval SUMSET_SUPERSET_LZERO

#eval phrase 23
def SUMSET_SUPERSET_RZERO : thm := keep "SUMSET_SUPERSET_RZERO" fun _ => (do
  prove ([[!s t. 0 IN t ==> s SUBSET (s +++ t)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [SUBSET, sumset, IN_ELIM_THM] THEN
    X_GEN_TAC ([[n:num]]) THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [([[n:num]]), ([[0]])] THEN ASM_REWRITE_TAC [ADD_CLAUSES])
  : ExceptT String IO thm).run
#eval SUMSET_SUPERSET_RZERO

#eval phrase 24
def SUMSET_SYM : thm := keep "SUMSET_SYM" fun _ => (do
  prove ([[!s t. s +++ t = t +++ s]])
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM, sumset] THEN MESON_TAC [ADD_SYM])
  : ExceptT String IO thm).run
#eval SUMSET_SYM

#eval phrase 25
def SUMSET_ASSOC : thm := keep "SUMSET_ASSOC" fun _ => (do
  prove ([[!s t u. s +++ (t +++ u) = (s +++ t) +++ u]])
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM, sumset] THEN MESON_TAC [ADD_ASSOC])
  : ExceptT String IO thm).run
#eval SUMSET_ASSOC

#eval phrase 26
def NEUTRAL_SUMSET : thm := keep "NEUTRAL_SUMSET" fun _ => (do
  prove ([[neutral(+++) = {0}]])
   (REWRITE_TAC [neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    X_GEN_TAC ([[s:num->bool]]) THEN
    REWRITE_TAC [sumset, IN_ELIM_THM, EXTENSION, IN_SING] THEN EQ_TAC THENL
     [DISCH_THEN (MP_TAC o HolLight.SPEC ([[{0}]])) THEN REWRITE_TAC [IN_SING], ALL_TAC] THEN
    MESON_TAC [ADD_CLAUSES])
  : ExceptT String IO thm).run
#eval NEUTRAL_SUMSET

#eval phrase 27
def MONOIDAL_SUMSET : thm := keep "MONOIDAL_SUMSET" fun _ => (do
  prove ([[monoidal (+++)]])
   (REWRITE_TAC [monoidal, NEUTRAL_SUMSET, SUMSET_ASSOC] THEN
    REWRITE_TAC [(← HolLight.EQT_INTRO (← HolLight.SPEC_ALL SUMSET_SYM))] THEN
    REWRITE_TAC [EXTENSION, sumset, IN_ELIM_THM, IN_SING] THEN
    MESON_TAC [ADD_CLAUSES])
  : ExceptT String IO thm).run
#eval MONOIDAL_SUMSET

#eval phrase 28
def SUMSET_0_ITER : thm := keep "SUMSET_0_ITER" fun _ => (do
  prove ([[!a s. FINITE s /\ (!k. k IN s ==> 0 IN a k) ==> 0 IN iterate(+++) s a]])
   (GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [ITERATE_CLAUSES, MONOIDAL_SUMSET, NEUTRAL_SUMSET, IN_SING] THEN
    SIMP_TAC [IN_INSERT, SUMSET_0])
  : ExceptT String IO thm).run
#eval SUMSET_0_ITER

-- ------------------------------------------------------------------------- --
-- Basic Schnirelmann theorem.                                               --
-- ------------------------------------------------------------------------- --

#eval phrase 29
def SCHNIRELMAN_LEMMA : thm := keep "SCHNIRELMAN_LEMMA" fun _ => (do
  -- OCaml builds the tactic (and the `prove` pair) right to left.
  let b5 ← ar ([[~(n = 0) ==> (x <= n - 1 <=> x <= n /\ ~(x = n))]])
  let b4 ← ar ([[s + t:num >= n ==> a = s /\ b = t ==> n <= a + b]])
  let b3 ← ar ([[~(n = 0) /\ n <= x ==> n - 1 < x]])
  let b2 ← tt ([[(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)]])
  let b1 ← tt ([[(~p ==> F) ==> p]])
  prove ([[!s t n. 0 IN (s INTER t) /\ count s n + count t n >= n ==> n IN (s +++ t)]])
   (REWRITE_TAC [IN_INTER] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC b1 THEN DISCH_TAC THEN
    ASM_CASES_TAC ([[(n:num) IN s]]) THENL
     [ASM_MESON_TAC [SUMSET_SUPERSET_RZERO, SUBSET], ALL_TAC] THEN
    ASM_CASES_TAC ([[(n:num) IN t]]) THENL
     [ASM_MESON_TAC [SUMSET_SUPERSET_LZERO, SUBSET], ALL_TAC] THEN
    ASM_CASES_TAC ([[n = 0]]) THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[~((s INTER (1..n-1)) INTER (IMAGE (\b. n - b) (t INTER (1..n-1))) = {})]])
    MP_TAC THENL
     [MATCH_MP_TAC CARD_UNION_OVERLAP THEN
      SIMP_TAC [FINITE_IMAGE, FINITE_INTER, FINITE_NUMSEG, GT] THEN
      MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC ([[CARD(1..n-1)]]) THEN CONJ_TAC THENL
       [MATCH_MP_TAC CARD_SUBSET THEN
        REWRITE_TAC [SUBSET, IN_UNION, FORALL_IN_IMAGE, FORALL_AND_THM,
                    b2] THEN
        SIMP_TAC [FINITE_NUMSEG, IN_INTER, IN_NUMSEG] THEN ARITH_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [CARD_NUMSEG_1] THEN
      MATCH_MP_TAC b3 THEN
      ASM_REWRITE_TAC [] THEN FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP b4) THEN
      SUBGOAL_THEN ([[CARD(IMAGE (\b. n - b) (t INTER (1..n-1))) = count t (n - 1)]])
      SUBST1_TAC THENL
       [REWRITE_TAC [count] THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
        SIMP_TAC [FINITE_INTER, FINITE_NUMSEG, IN_INTER, IN_NUMSEG] THEN
        ARITH_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [count] THEN CONJ_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC [EXTENSION, IN_INTER, IN_NUMSEG,
        b5] THEN
      ASM_MESON_TAC [],
      UNDISCH_TAC ([[~(n IN s +++ t)]]) THEN
      REWRITE_TAC [] THEN ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN
      REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_IMAGE, IN_NUMSEG,
                  NOT_FORALL_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC ([[a:num]]) THEN REWRITE_TAC [sumset, IN_ELIM_THM] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC ([[b:num]]))) THEN
      MAP_EVERY EXISTS_TAC [([[a:num]]), ([[b:num]])] THEN ASM_REWRITE_TAC [] THEN
      ASM_ARITH_TAC])
  : ExceptT String IO thm).run
#eval SCHNIRELMAN_LEMMA

#eval phrase 30
def SCHNIRELMANN_THEOREM : thm := keep "SCHNIRELMANN_THEOREM" fun _ => (do
  let b1 ← rr ([[a + b >= &1 ==> a <= x /\ b <= y ==> &1 <= x + y]])
  prove ([[!s t. 0 IN (s INTER t) /\ schnirelmann s + schnirelmann t >= &1
         ==> s +++ t = (:num)]])
   (REWRITE_TAC [IN_INTER] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC [EXTENSION, IN_UNIV] THEN X_GEN_TAC ([[n:num]]) THEN
    ASM_CASES_TAC ([[n = 0]]) THENL
     [ASM_MESON_TAC [SUMSET_SUPERSET_LZERO, SUBSET, IN_INTER], ALL_TAC] THEN
    MATCH_MP_TAC SCHNIRELMAN_LEMMA THEN ASM_REWRITE_TAC [IN_INTER] THEN
    REWRITE_TAC [GE, (← HolLight.GSYM REAL_OF_NUM_LE), (← HolLight.GSYM REAL_OF_NUM_ADD)] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM REAL_MUL_LID)] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ), REAL_OF_NUM_LT, LE_1] THEN
    REWRITE_TAC [real_div, REAL_ADD_RDISTRIB] THEN REWRITE_TAC [(← HolLight.GSYM real_div)] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP b1) THEN
    CONJ_TAC THEN MATCH_MP_TAC SCHNIRELMANN_UBOUND THEN ASM_ARITH_TAC)
  : ExceptT String IO thm).run
#eval SCHNIRELMANN_THEOREM

#eval phrase 31
def SCHNIRELMANN_THEOREM_2 : thm := keep "SCHNIRELMANN_THEOREM_2" fun _ => (do
  prove ([[!s. 0 IN s /\ schnirelmann s >= &1 / &2 ==> s +++ s = (:num)]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SCHNIRELMANN_THEOREM THEN
    ASM_REWRITE_TAC [IN_INTER] THEN ASM_REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval SCHNIRELMANN_THEOREM_2

-- ------------------------------------------------------------------------- --
-- Additional additivity properties and full Schnirelmann theorem.           --
-- ------------------------------------------------------------------------- --

#eval phrase 32
def ENUMERATION_LEMMA : thm := keep "ENUMERATION_LEMMA" fun _ => (do
  -- OCaml builds the tactic (and the `prove` pair) right to left.
  let b3 ← tt ([[(a ==> b) /\ a ==> a /\ b]])
  let b2 ← ar ([[1 <= n + 1 /\ ~(n + 1 <= n)]])
  let b1 ← HolLight.ISPEC ([[(<=):num->num->bool]]) TOPOLOGICAL_SORT
  prove ([[!n s p. s HAS_SIZE n /\ (!k. k IN s ==> 1 <= k /\ k <= p)
           ==> ?a:num->num.
                 a(0) = 0 /\
                 a(n + 1) = p + 1 /\
                 s = IMAGE a (1..n) /\
                 (!j k. j <= n /\ k <= n + 1 /\ j < k ==> a(j) < a(k)) /\
                 (!j k. j <= n /\ k <= n + 1 /\ j <= k ==> a(j) <= a(k))]])
   (REPEAT STRIP_TAC THEN
    MP_TAC b1 THEN
    REWRITE_TAC [LE_TRANS, LE_ANTISYM] THEN
    DISCH_THEN (MP_TAC o HolLight.SPECL [([[n:num]]), ([[s:num->bool]])]) THEN
    ASM_REWRITE_TAC [NOT_LE, IN_NUMSEG] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[f:num->num]]) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC ([[\i. if 1 <= i then if i <= n then f i else p + 1 else 0]]) THEN
    ASM_REWRITE_TAC [ARITH, b2] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_NUMSEG] THEN MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC b3 THEN
    CONJ_TAC THENL [MESON_TAC [LE_LT], ALL_TAC] THEN
    SUBGOAL_THEN ([[!k. 1 <= k /\ k <= n ==> 1 <= f(k) /\ f(k) <= p]])
    ASSUME_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [IN_IMAGE, IN_NUMSEG] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [([[i:num]]), ([[j:num]])] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[i:num]]), ([[j:num]])]) THEN ASM_REWRITE_TAC [] THEN
    REPEAT (COND_CASES_TAC THEN ASM_SIMP_TAC []) THEN
    FIRST_X_ASSUM (fun th => fun g => do
      match ← HolLight.SPEC ([[i:num]]) th |>.run, ← HolLight.SPEC ([[j:num]]) th |>.run with
      | .ok ti, .ok tj => (MP_TAC ti THEN MP_TAC tj) g
      | .error e, _ => return .error e
      | _, .error e => return .error e) THEN
    ASM_ARITH_TAC)
  : ExceptT String IO thm).run
#eval ENUMERATION_LEMMA

#eval phrase 33
def CARD_INTER_0_1 : thm := keep "CARD_INTER_0_1" fun _ => (do
  let b1 ← sr ([[a IN s /\ (t = a INSERT u)
        ==> (s INTER t = a INSERT (s INTER u))]])
  prove ([[!n s. 0 IN s ==> CARD(s INTER (0..n)) = SUC(CARD(s INTER (1..n)))]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[s INTER (0..n) = 0 INSERT (s INTER (1..n))]]) SUBST1_TAC THENL
     [MATCH_MP_TAC b1 THEN
      ASM_REWRITE_TAC [EXTENSION, IN_INSERT, IN_NUMSEG] THEN ARITH_TAC,
      SIMP_TAC [CARD_CLAUSES, FINITE_INTER, FINITE_NUMSEG, IN_INTER, ARITH,
               IN_NUMSEG, (← HolLight.GSYM REAL_OF_NUM_SUC)]])
  : ExceptT String IO thm).run
#eval CARD_INTER_0_1

#eval phrase 34
def SCHNIRELMANN_SUMSET : thm := keep "SCHNIRELMANN_SUMSET" fun _ => (do
  -- OCaml builds the tactic (and the `prove` pair) right to left.
  let b13 ← rr ([[(&1 - t) * s * n <= (&1 - t) * a
      ==> ((s + t) - s * t) * n <= t * (n - a) + a]])
  let b12 ← rr ([[(n + &1) - (a + &1) = n - a]])
  let b11 ← rr ([[--(&0 - a + b) = a - b]])
  let b10 ← rr ([[a - b - c:real = --((b - a) + c)]])
  let b9 ← ar ([[a < b ==> 1 <= b - a]])
  let b8 ← sr ([[IMAGE f s INTER t = {} <=> !x. x IN s ==> ~(f x IN t)]])
  let b7 ← ar ([[~(i = j) ==> i + 1 <= j \/ j + 1 <= i]])
  let b6 ← ar ([[a(k) < a(k + 1) /\ a(k + 1) <= n + 1 /\ l <= a(k + 1) - a(k) - 1
        ==> a(k) + l <= n]])
  let b5 ← tt ([[d ==> (a /\ b /\ c <=> d) ==> a /\ c]])
  let b4 ← ar ([[k = 0 \/ 1 <= k]])
  let b3 ← HolLight.SPECL [([[count s n]]), ([[s INTER (1..n)]]), ([[n:num]])] ENUMERATION_LEMMA
  prove ([[!s t. 0 IN (s INTER t)
         ==> schnirelmann(s +++ t)
                >= (schnirelmann s + schnirelmann t) -
                   schnirelmann s * schnirelmann t]])
   (REWRITE_TAC [IN_INTER] THEN REPEAT STRIP_TAC THEN REWRITE_TAC [real_ge] THEN
    MATCH_MP_TAC SCHNIRELMANN_LBOUND THEN X_GEN_TAC ([[n:num]]) THEN STRIP_TAC THEN
    ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_OF_NUM_LT, LE_1] THEN
    MP_TAC b3 THEN
    SIMP_TAC [count, HAS_SIZE, FINITE_INTER, FINITE_NUMSEG] THEN
    SIMP_TAC [IN_INTER, IN_NUMSEG] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[a:num->num]]) STRIP_ASSUME_TAC) THEN
    ABBREV_TAC ([[A = CARD(s INTER (1..n))]]) THEN
    SUBGOAL_THEN ([[!k. k <= A ==> (a:num->num)(k) IN s /\ a(k) <= n]])
    ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [EXTENSION]) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[(a:num->num)(k)]])) THEN
      DISJ_CASES_TAC b4 THEN
      ASM_REWRITE_TAC [LE_0, IN_INTER, IN_NUMSEG] THEN
      MATCH_MP_TAC b5 THEN
      REWRITE_TAC [IN_IMAGE, IN_NUMSEG] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC ([[&(CARD ((s +++ t) INTER (0..n))) - &1]]) THEN CONJ_TAC THENL
     [ALL_TAC,
      ASM_SIMP_TAC [CARD_INTER_0_1, SUMSET_0, (← HolLight.GSYM REAL_OF_NUM_SUC)] THEN
      REAL_ARITH_TAC2] THEN
    REWRITE_TAC [REAL_LE_SUB_LADD] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     ([[&(CARD(UNIONS(IMAGE (\i. (IMAGE (\b. a i + b)
                                      (t INTER (0..(a(i+1) - a(i) - 1)))))
                          (0..A))))]]) THEN
    CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
      SIMP_TAC [FINITE_INTER, FINITE_NUMSEG, UNIONS_SUBSET, FORALL_IN_IMAGE] THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN
      X_GEN_TAC ([[k:num]]) THEN DISCH_TAC THEN X_GEN_TAC ([[l:num]]) THEN
      REWRITE_TAC [IN_INTER] THEN REPEAT STRIP_TAC THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_NUMSEG]) THENL
       [REWRITE_TAC [sumset, IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      REWRITE_TAC [IN_NUMSEG, LE_0] THEN
      MATCH_MP_TAC b6 THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN
      ASM_CASES_TAC ([[k:num = A]]) THEN ASM_REWRITE_TAC [LE_REFL] THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[k + 1]]))) THEN ASM_ARITH_TAC] THEN
    HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) CARD_UNIONS o
      HolCore.Kernel.rand o HolCore.Kernel.rand o HolLight.snd) THEN
    REWRITE_TAC [FORALL_IN_IMAGE, IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    SIMP_TAC [FINITE_IMAGE, FINITE_NUMSEG, FINITE_INTER] THEN
    SUBGOAL_THEN
     ([[!i j. i IN 0..A /\ j IN 0..A /\ ~(i = j)
                 ==> IMAGE (\b. a i + b) (t INTER (0..a (i + 1) - a i - 1)) INTER
                     IMAGE (\b. a j + b) (t INTER (0..a (j + 1) - a j - 1)) = {}]])
    (LABEL_TAC "*") THENL
     [MAP_EVERY X_GEN_TAC [([[i:num]]), ([[j:num]])] THEN STRIP_TAC THEN
      REWRITE_TAC [b8] THEN
      X_GEN_TAC ([[k:num]]) THEN DISCH_TAC THEN REWRITE_TAC [IN_IMAGE] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[l:num]]) STRIP_ASSUME_TAC) THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_NUMSEG, IN_INTER]) THEN
      SUBGOAL_THEN ([[a(i + 1):num <= a(j) \/ a(j + 1) <= a(i)]]) MP_TAC THENL
       [FIRST_X_ASSUM (DISJ_CASES_TAC o HolLight.MATCH_MP b7)
        THENL [DISJ1_TAC, DISJ2_TAC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_ARITH_TAC,
        ALL_TAC] THEN
      SUBGOAL_THEN ([[(a:num->num)(i) < a(i + 1) /\ a(j) < a(j + 1)]])
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC, ALL_TAC] THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    ANTS_TAC THENL
     [X_GEN_TAC ([[i:num]]) THEN DISCH_TAC THEN
      X_GEN_TAC ([[j:num]]) THEN DISCH_TAC THEN
      ASM_CASES_TAC ([[i:num = j]]) THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    HolCore.Lib.W (MP_TAC o HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) NSUM_IMAGE_NONZERO o
      HolCore.Kernel.rand o HolCore.Kernel.rand o HolLight.snd) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [REWRITE_TAC [FINITE_NUMSEG] THEN MAP_EVERY X_GEN_TAC [([[i:num]]), ([[j:num]])] THEN
      STRIP_TAC THEN REMOVE_THEN "*" (MP_TAC o HolLight.SPECL [([[i:num]]), ([[j:num]])]) THEN
      ASM_REWRITE_TAC [INTER_ACI] THEN SIMP_TAC [CARD_CLAUSES],
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [o_DEF] THEN
    SIMP_TAC [EQ_ADD_LCANCEL, CARD_IMAGE_INJ, FINITE_INTER, FINITE_NUMSEG] THEN
    SIMP_TAC [REAL_OF_NUM_SUM, FINITE_INTER, FINITE_NUMSEG] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     ([[sum(0..A) (\i. schnirelmann t * &(a(i + 1) - a(i) - 1) + &1)]]) THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC SUM_LE_NUMSEG THEN REWRITE_TAC [] THEN
      ASM_SIMP_TAC [CARD_INTER_0_1, SUMSET_0, (← HolLight.GSYM REAL_OF_NUM_SUC)] THEN
      SIMP_TAC [(← HolLight.GSYM count), SCHNIRELMANN_UBOUND_MUL, REAL_LE_RADD]] THEN
    REWRITE_TAC [SUM_ADD_NUMSEG, SUM_CONST_NUMSEG] THEN
    REWRITE_TAC [SUB_0, (← HolLight.GSYM REAL_OF_NUM_ADD), REAL_MUL_RID] THEN
    REWRITE_TAC [REAL_ADD_ASSOC, REAL_LE_RADD] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     ([[sum(0..A) (\i. schnirelmann t * (&(a(i + 1)) - &(a i) - &1)) + &A]]) THEN
    CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [REAL_LE_RADD] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      X_GEN_TAC ([[i:num]]) THEN STRIP_TAC THEN
      SUBGOAL_THEN ([[a(i):num < a(i + 1)]]) ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN
      ASM_SIMP_TAC [REAL_OF_NUM_SUB, LT_IMP_LE, b9,
                   REAL_LE_REFL]] THEN
    REWRITE_TAC [SUM_LMUL] THEN
    ONCE_REWRITE_TAC [b10] THEN
    REWRITE_TAC [SUM_NEG, SUM_ADD_NUMSEG, SUM_DIFFS, LE_0] THEN
    ASM_REWRITE_TAC [b11, SUM_CONST_NUMSEG] THEN
    REWRITE_TAC [SUB_0, (← HolLight.GSYM REAL_OF_NUM_ADD), REAL_MUL_RID] THEN
    REWRITE_TAC [b12] THEN
    MATCH_MP_TAC b13 THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN EXPAND_TAC "A" THEN
    REWRITE_TAC [REAL_SUB_LE, SCHNIRELMANN_UBOUND_MUL, (← HolLight.GSYM count)] THEN
    REWRITE_TAC [SCHNIRELMANN_BOUNDS])
  : ExceptT String IO thm).run
#eval SCHNIRELMANN_SUMSET

-- ------------------------------------------------------------------------- --
-- Now an iterative form.                                                    --
-- ------------------------------------------------------------------------- --

#eval phrase 35
def SCHNIRELMANN_SUMSET_GEN : thm := keep "SCHNIRELMANN_SUMSET_GEN" fun _ => (do
  let b2 ← rr ([[&1 - (&1 - s) * (&1 - t) <= u <=>
                              u >= (s + t) - s * t]])
  let b1 ← rr ([[a <= b ==> &1 - b <= &1 - a]])
  prove ([[!a s. FINITE s /\ (!i:A. i IN s ==> 0 IN a i)
         ==> schnirelmann(iterate(+++) s a)
             >= &1 - product s (\i. &1 - schnirelmann(a i))]])
   (GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [PRODUCT_CLAUSES, real_ge, REAL_SUB_REFL, SCHNIRELMANN_BOUNDS] THEN
    MAP_EVERY X_GEN_TAC [([[k:A]]), ([[s:A->bool]])] THEN STRIP_TAC THEN
    DISCH_TAC THEN FIRST_ASSUM (fun th => fun g => do
      if HolCore.Basics.is_imp (concl th) then MP_TAC th g
      else return .error "check") THEN
    ANTS_TAC THENL [ASM_MESON_TAC [IN_INSERT], DISCH_TAC] THEN
    ASM_SIMP_TAC [ITERATE_CLAUSES, MONOIDAL_SUMSET] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC ([[&1 - (&1 - schnirelmann(a(k:A))) *
                     (&1 - schnirelmann(iterate (+++) s a))]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC b1 THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC [REAL_SUB_LE, SCHNIRELMANN_BOUNDS] THEN
      ASM_REAL_ARITH_TAC,
      REWRITE_TAC [b2] THEN
      MATCH_MP_TAC SCHNIRELMANN_SUMSET THEN
      ASM_SIMP_TAC [IN_INTER, IN_INSERT, SUMSET_0_ITER]])
  : ExceptT String IO thm).run
#eval SCHNIRELMANN_SUMSET_GEN

#eval phrase 36
def SCHNIRELMANN_SUMSET_POW : thm := keep "SCHNIRELMANN_SUMSET_POW" fun _ => (do
  let b1 ← HolLight.ISPECL [([[\i:A. (s:num->bool)]]), ([[i:A->bool]])]
      SCHNIRELMANN_SUMSET_GEN
  prove ([[!i s. FINITE i /\ 0 IN s
         ==> schnirelmann(iterate(+++) i (\k:A. s))
             >= &1 - (&1 - schnirelmann s) pow (CARD i)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC b1 THEN
    ASM_SIMP_TAC [PRODUCT_CONST])
  : ExceptT String IO thm).run
#eval SCHNIRELMANN_SUMSET_POW

#eval phrase 37
def SCHNIRELMANN : thm := keep "SCHNIRELMANN" fun _ => (do
  -- OCaml builds the tactic (and the `prove` pair) right to left.
  let b7 ← rr ([[a < &1 / &2 ==> y >= &1 - a ==> x >= &1 - a ==> x + y >= &1]])
  let b6 ← HolLight.SPECL [([[k:A->bool]]), ([[s:num->bool]])] SCHNIRELMANN_SUMSET_POW
  let b5 ← HolLight.SPECL [([[j:A->bool]]), ([[s:num->bool]])] SCHNIRELMANN_SUMSET_POW
  let b4 ← ar ([[n = 2 * n - n]])
  let b3 ← tt ([[(a /\ b /\ c) /\ (a /\ b /\ c ==> d) ==> a /\ b /\ c /\ d]])
  let b2 ← ar ([[n <= 2 * n]])
  let b1 ← HolLight.ISPECL [([[&1 - schnirelmann s]]), ([[&1 / &2]])] REAL_ARCH_POW_INV
  prove ([[!s. 0 IN s /\ schnirelmann s > &0
       ==> ?k. !i. i HAS_SIZE k ==> iterate(+++) i (\a:A. s) = (:num)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [HAS_SIZE] THEN
    MP_TAC b1 THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_TAC ([[n:num]])) THEN EXISTS_TAC ([[2 * n]]) THEN
    X_GEN_TAC ([[i:A->bool]]) THEN STRIP_TAC THEN
    SUBGOAL_THEN
     ([[?j k:A->bool. i = j UNION k /\ j INTER k = {} /\
                    j HAS_SIZE n /\ k HAS_SIZE n]])
     (REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC))
    THENL
     [FIRST_ASSUM (MP_TAC o HolLight.SPEC ([[n:num]]) o HolLight.MATCH_MP CHOOSE_SUBSET) THEN
      ASM_REWRITE_TAC [b2] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[j:A->bool]]) THEN
      STRIP_TAC THEN EXISTS_TAC ([[i DIFF j:A->bool]]) THEN
      MATCH_MP_TAC b3 THEN
      CONJ_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC] THEN STRIP_TAC THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [b4] THEN
      MATCH_MP_TAC HAS_SIZE_DIFF THEN ASM_REWRITE_TAC [HAS_SIZE],
      ALL_TAC] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [(← HolLight.GSYM DISJOINT), HAS_SIZE]) THEN
    ASM_SIMP_TAC [MONOIDAL_SUMSET, ITERATE_UNION] THEN
    MATCH_MP_TAC SCHNIRELMANN_THEOREM THEN
    ASM_SIMP_TAC [SUMSET_0_ITER, IN_INTER] THEN
    MP_TAC b5 THEN
    MP_TAC b6 THEN
    ASM_SIMP_TAC [] THEN MATCH_MP_TAC b7 THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval SCHNIRELMANN

-- ------------------------------------------------------------------------- --
-- A more direct version, without the techicality of 0 and sumsets.          --
-- ------------------------------------------------------------------------- --

#eval phrase 38
def SCHNIRELMANN_DIRECT : thm := keep "SCHNIRELMANN_DIRECT" fun _ => (do
  -- OCaml builds the tactic (and the `prove` pair) right to left.
  let b7 ← ar ([[1 = SUC m \/ 1 <= m]])
  let b6 ← ar ([[~(SUC n <= n)]])
  let b5 ← ar ([[x <= k ==> x <= SUC k]])
  let b4 ← ar ([[~(SUC n <= n)]])
  let b3 ← ar ([[~(1 <= i /\ i <= 0)]])
  let b2 ← ar ([[1 <= SUC k]])
  let b0 ← ar ([[~(SUC n <= n)]])
  prove ([[!s. schnirelmann s > &0
       ==> ?k. !n. ?m f. m <= k /\ (!i. i IN 1..m ==> f(i) IN s) /\
                         n = nsum (1..m) f]])
   (GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     ([[?k. !i:num->bool.
             i HAS_SIZE k ==> iterate (+++) i (\a. 0 INSERT s) = (:num)]])
    MP_TAC THENL
     [MATCH_MP_TAC SCHNIRELMANN THEN REWRITE_TAC [IN_INSERT] THEN
      POP_ASSUM MP_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
      AP_TERM_TAC THEN MATCH_MP_TAC SCHNIRELMANN_INSENSITIVE THEN
      SIMP_TAC [IN_INSERT, LE_1],
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[k:num]]) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[1..k]])) THEN
    REWRITE_TAC [EXTENSION, HAS_SIZE_NUMSEG_1, IN_UNIV] THEN
    MATCH_MP_TAC MONO_FORALL THEN
    SPEC_TAC ([[k:num]], [[k:num]]) THEN POP_ASSUM_LIST (HolCore.Lib.K ALL_TAC) THEN
    INDUCT_TAC THEN SIMP_TAC [NUMSEG_CLAUSES, ARITH, b2] THEN
    SIMP_TAC [ITERATE_CLAUSES, MONOIDAL_SUMSET, FINITE_NUMSEG] THENL
     [REWRITE_TAC [NEUTRAL_SUMSET, IN_SING] THEN GEN_TAC THEN
      DISCH_THEN SUBST1_TAC THEN EXISTS_TAC ([[0]]) THEN
      SIMP_TAC [NSUM_CLAUSES_NUMSEG, CARD_CLAUSES, EMPTY_SUBSET, FINITE_RULES,
               IN_NUMSEG, LE_REFL, ARITH] THEN
      REWRITE_TAC [b3],
      ALL_TAC] THEN
    REWRITE_TAC [IN_NUMSEG, b4] THEN
    ONCE_REWRITE_TAC [sumset] THEN REWRITE_TAC [IN_ELIM_THM, IN_INSERT] THEN
    X_GEN_TAC ([[n:num]]) THEN DISCH_THEN (X_CHOOSE_THEN ([[x:num]]) MP_TAC) THEN
    ASM_CASES_TAC ([[x = 0]]) THEN ASM_REWRITE_TAC [ADD_CLAUSES] THENL
     [ASM_MESON_TAC [IN_NUMSEG, b5], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[y:num]]) STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[y:num]])) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[m:num]]), ([[f:num->num]])] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [([[SUC m]]), ([[\i. if i = SUC m then x:num else f i]])] THEN
    ASM_SIMP_TAC [LE_SUC, LE, NSUM_CLAUSES_NUMSEG] THEN CONJ_TAC THENL
     [ASM_MESON_TAC [b6, IN_NUMSEG], ALL_TAC] THEN
    REWRITE_TAC [b7] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [ADD_SYM] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC NSUM_EQ THEN
    ASM_MESON_TAC [b0, IN_NUMSEG])
  : ExceptT String IO thm).run
#eval SCHNIRELMANN_DIRECT
end HolExamples.Schnirelmann
