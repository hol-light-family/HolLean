/- File: HolLogicArith/Definability.lean
Translation of HOL Light's Arithmetic/definability.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.ArithFol
open HolCore.Kernel HolCore.Lib HolCore.Basics Session HolLight.Syntax HolLogicArith
open scoped HolLight
-- Names from Arithmetic/fol.ml that definability.ml reuses.
open HolLogicArith.ArithFol (termval holds valmod TERMVAL_NUMERAL FVT_NUMERAL
  HOLDS_FORMSUBST FV FORMSUBST_FV FVT TERMSUBST_FVT)

namespace HolLogicArith.Definability

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- `new_recursive_definition` lifted into `ExceptT String IO`. -/
private unsafe def newRec (ax : thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (Session.new_recursive_definition ax tm)

/- Force an `ExceptT String IO (thm × thm)` to its value, panicking with HOL
   Light's message on failure (as the toplevel `let a,b = ...` would throw). -/
private unsafe def runObj (m : ExceptT String IO (thm × thm)) : thm × thm :=
  match unsafeIO m.run with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! s!"OBJECTIFY: {e}"
  | .error e => panic! s!"OBJECTIFY IO: {e}"

-- Prime/rstc library theorems (loaded by make.ml before fol.ml), used in the
-- proofs below.  The toplevel sees them unqualified; alias them here.
private unsafe def PRIME_0 : thm := SessionLibrary.Prime.PRIME_0
private unsafe def PRIME_1 : thm := SessionLibrary.Prime.PRIME_1
private unsafe def PRIME_GE_2 : thm := SessionLibrary.Prime.PRIME_GE_2
private unsafe def EUCLID_BOUND : thm := SessionLibrary.Prime.EUCLID_BOUND
private unsafe def PRIME_POWER_EXISTS_ALT : thm := SessionLibrary.Prime.PRIME_POWER_EXISTS_ALT
private unsafe def RTC : thm := SessionLibrary.RSTC.RTC
private unsafe def RTC_CASES_L : thm := SessionLibrary.RSTC.RTC_CASES_L
private unsafe def RELPOW : thm := SessionLibrary.RSTC.RELPOW
private unsafe def RTC_RELPOW : thm := SessionLibrary.RSTC.RTC_RELPOW
private unsafe def RELPOW_SEQUENCE : thm := SessionLibrary.RSTC.RELPOW_SEQUENCE

-- Replay Arithmetic/fol.ml (the one module definability.ml imports).
#eval HolLogicArith.ArithFol.ensure

#eval phrase 1
#eval Session.prioritize_num

#eval phrase 2
unsafe def NPAIR : thm := keep "NPAIR" fun _ => new_definition
  [[NPAIR x y = (x + y) EXP 2 + x + 1]]
#eval NPAIR

#eval phrase 3
unsafe def NPAIR_NONZERO : thm := keep "NPAIR_NONZERO" fun _ => (do
  prove ([[!x y. ~(NPAIR x y = 0)]])
   (REWRITE_TAC [NPAIR, ADD_EQ_0, ARITH])
  : ExceptT String IO thm).run
#eval NPAIR_NONZERO

#eval phrase 4
unsafe def NPAIR_INJ_LEMMA : thm := keep "NPAIR_INJ_LEMMA" fun _ => (do
  prove ([[x1 + y1 < x2 + y2 ==> NPAIR x1 y1 < NPAIR x2 y2]])
   (HolLight.tactic_of do
     let ar ← ExceptT.mk (ARITH_RULE [[x + y + 1 < u + v + 1 <=> x + y < u + v]])
     pure
      (STRIP_TAC THEN REWRITE_TAC [NPAIR, EXP_2] THEN
       REWRITE_TAC [ar] THEN
       MATCH_MP_TAC LTE_TRANS THEN
       EXISTS_TAC [[SUC(x1 + y1) * SUC(x1 + y1)]] THEN CONJ_TAC THENL
        [ARITH_TAC, ASM_MESON_TAC [LE_TRANS, LE_ADD, LE_MULT2, LE_SUC_LT]]))
  : ExceptT String IO thm).run
#eval NPAIR_INJ_LEMMA

#eval phrase 5
unsafe def NPAIR_INJ : thm := keep "NPAIR_INJ" fun _ => (do
  prove ([[(NPAIR x y = NPAIR x' y') <=> (x = x') /\ (y = y')]])
   (EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[x' + y' = x + y]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [LT_CASES, NPAIR_INJ_LEMMA, LT_REFL],
      UNDISCH_TAC [[NPAIR x y = NPAIR x' y']] THEN
      UNDISCH_TAC [[x' + y' = x + y]] THEN
      SIMP_TAC [NPAIR, EXP_2] THEN ARITH_TAC])
  : ExceptT String IO thm).run
#eval NPAIR_INJ

#eval phrase 6
unsafe def NPAIR_LT : thm := keep "NPAIR_LT" fun _ => (do
  prove ([[!x y. x < NPAIR x y /\ y < NPAIR x y]])
   (HolLight.tactic_of do
     let ar ← ExceptT.mk (ARITH_RULE [[x < a + x + 1]])
     pure
      (REPEAT GEN_TAC THEN REWRITE_TAC [NPAIR] THEN
       REWRITE_TAC [ar] THEN
       MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC [[(x + y) + x + 1]] THEN
       REWRITE_TAC [LE_ADD_RCANCEL, EXP_2, LE_SQUARE_REFL] THEN
       ARITH_TAC))
  : ExceptT String IO thm).run
#eval NPAIR_LT

#eval phrase 7
unsafe def primepow : thm := keep "primepow" fun _ => new_definition
  [[primepow p x <=> prime(p) /\ ?n. x = p EXP n]]
#eval primepow

#eval phrase 8
unsafe def divides_DELTA : thm := keep "divides_DELTA" fun _ => (do
  prove ([[m divides n <=> ?x. x <= n /\ n = m * x]])
   (HolLight.tactic_of do
     let ar ← ExceptT.mk (ARITH_RULE [[~(m = 0) ==> 1 <= m]])
     pure
      (REWRITE_TAC [divides] THEN ASM_CASES_TAC [[m = 0]] THENL
        [ASM_REWRITE_TAC [MULT_CLAUSES] THEN MESON_TAC [LE_REFL], ALL_TAC] THEN
       AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN SIMP_TAC [] THEN
       FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP ar) THEN
       SIMP_TAC [LE_EXISTS, LEFT_IMP_EXISTS_THM,
                 RIGHT_ADD_DISTRIB, MULT_CLAUSES] THEN
       MESON_TAC []))
  : ExceptT String IO thm).run
#eval divides_DELTA

#eval phrase 9
unsafe def prime_DELTA : thm := keep "prime_DELTA" fun _ => (do
  prove ([[prime(p) <=> 2 <= p /\ !n. n < p ==> n divides p ==> n = 1]])
   (ASM_CASES_TAC [[p = 0]] THEN ASM_REWRITE_TAC [ARITH, PRIME_0] THEN
    ASM_CASES_TAC [[p = 1]] THEN ASM_REWRITE_TAC [ARITH, PRIME_1] THEN EQ_TAC THENL
     [ASM_MESON_TAC [prime, LT_REFL, PRIME_GE_2],
      ASM_MESON_TAC [prime, DIVIDES_LE, LE_LT]])
  : ExceptT String IO thm).run
#eval prime_DELTA

#eval phrase 10
unsafe def primepow_DELTA : thm := keep "primepow_DELTA" fun _ => (do
  prove ([[primepow p x <=>
        prime(p) /\ ~(x = 0) /\
        !z. z <= x ==> z divides x ==> z = 1 \/ p divides z]])
   (REWRITE_TAC [primepow] THEN
    ASM_CASES_TAC [[prime(p)]] THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC [[x = 0]] THEN ASM_REWRITE_TAC [] THENL
     [ASM_MESON_TAC [EXP_EQ_0, PRIME_0],
      ASM_SIMP_TAC [PRIME_POWER_EXISTS_ALT] THEN ASM_MESON_TAC [DIVIDES_LE]])
  : ExceptT String IO thm).run
#eval primepow_DELTA

#eval phrase 11
unsafe def PSEQ : thm := keep "PSEQ" fun _ => (do
  newRec Session.num_RECURSION
    [[(PSEQ p f m 0 = 0) /\
      (PSEQ p f m (SUC n) = f m + p * PSEQ p f (SUC m) n)]]
  : ExceptT String IO thm).run
#eval PSEQ

#eval phrase 12
unsafe def PSEQ_SPLIT : thm := keep "PSEQ_SPLIT" fun _ => (do
  prove ([[!f p n m r.
        PSEQ p f m (n + r) = PSEQ p f m n + p EXP n * PSEQ p f (m + n) r]])
   (GEN_TAC THEN GEN_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, EXP, MULT_CLAUSES, PSEQ] THEN
    ASM_REWRITE_TAC [(← HolLight.GSYM ADD_ASSOC), EQ_ADD_LCANCEL] THEN
    REWRITE_TAC [LEFT_ADD_DISTRIB, MULT_AC, ADD_CLAUSES])
  : ExceptT String IO thm).run
#eval PSEQ_SPLIT

#eval phrase 13
unsafe def PSEQ_1 : thm := keep "PSEQ_1" fun _ => (do
  prove ([[PSEQ p f m 1 = f m]])
   (HolLight.tactic_of do
     let nc ← ExceptT.mk (Session.num_CONV [[1]])
     pure
      (REWRITE_TAC [nc, ADD_CLAUSES, MULT_CLAUSES, PSEQ]))
  : ExceptT String IO thm).run
#eval PSEQ_1

#eval phrase 14
unsafe def PSEQ_BOUND : thm := keep "PSEQ_BOUND" fun _ => (do
  prove ([[!n. ~(p = 0) /\ (!i. i < n ==> f i < p) ==> PSEQ p f 0 n < p EXP n]])
   (HolLight.tactic_of do
     let sp ← ExceptT.mk (HolLight.SPECL [ [[f:num->num]], [[p:num]], [[n:num]], [[0]], [[1]] ] PSEQ_SPLIT)
     let ar1 ← ExceptT.mk (ARITH_RULE [[i < n ==> i < SUC n]])
     let ar2 ← ExceptT.mk (ARITH_RULE [[p + p * q = p * (q + 1)]])
     let ar3 ← ExceptT.mk (ARITH_RULE [[x < p ==> x + 1 <= p]])
     pure
      (ASM_CASES_TAC [[p = 0]] THEN ASM_REWRITE_TAC [] THEN
       INDUCT_TAC THENL [REWRITE_TAC [PSEQ, EXP, ARITH], ALL_TAC] THEN
       DISCH_TAC THEN
       MP_TAC sp THEN
       SIMP_TAC [ADD1, ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN
       MATCH_MP_TAC LTE_TRANS THEN
       EXISTS_TAC [[p EXP n + p EXP n * PSEQ p f n 1]] THEN
       ASM_SIMP_TAC [LT_ADD_RCANCEL, ar1] THEN
       REWRITE_TAC [ar2] THEN
       ASM_REWRITE_TAC [EXP_ADD, LE_MULT_LCANCEL, EXP_EQ_0] THEN
       MATCH_MP_TAC ar3 THEN
       ASM_SIMP_TAC [EXP_1, PSEQ_1, LT]))
  : ExceptT String IO thm).run
#eval PSEQ_BOUND

#eval phrase 15
unsafe def RELPOW_LEMMA_1 : thm := keep "RELPOW_LEMMA_1" fun _ => (do
  prove ([[(f 0 = x) /\
   (f n = y) /\
   (!i. i < n ==> R (f i) (f(SUC i)))
   ==> ?p. (?i. i <= n /\ p <= SUC(FACT(f i))) /\
           prime p /\
           (?m. m < p EXP (SUC n) /\
                x < p /\ y < p /\
                (?qx. m = x + p * qx) /\
                (?ry. ry < p EXP n /\ (m = ry + p EXP n * y)) /\
                !q. q < p EXP n
                    ==> primepow p q
                        ==> ?r. r < q /\
                                ?a. a < p /\
                                    ?b. b < p /\
                                        R a b /\
                                        ?s. s <= m /\
                                            (m =
                                             r + q * (a + p * (b + p * s))))]])
   (HolLight.tactic_of do
     let ar0 ← ExceptT.mk (ARITH_RULE [[f(SUC n) <= f(j) \/ f(j) <= f(SUC n)]])
     let arj ← ExceptT.mk (ARITH_RULE [[j <= n ==> j <= SUC n]])
     let eb ← ExceptT.mk (HolLight.SPEC ([[(f:num->num) ibig]]) EUCLID_BOUND)
     let sp1 ← ExceptT.mk (HolLight.SPECL [ [[f:num->num]], [[p:num]], [[n:num]], [[0]], [[1]] ] PSEQ_SPLIT)
     let ari ← ExceptT.mk (ARITH_RULE [[i < n ==> (i + SUC n - i = SUC n)]])
     let sp2 ← ExceptT.mk (HolLight.SPECL [ [[f:num->num]], [[p:num]], [[i:num]], [[0]], [[SUC n - i]] ] PSEQ_SPLIT)
     let ari2 ← ExceptT.mk (ARITH_RULE [[i < n ==> (1 + n - i = SUC n - i)]])
     let sp3 ← ExceptT.mk (HolLight.SPECL [ [[f:num->num]], [[p:num]], [[1]], [[i:num]], [[n - i]] ] PSEQ_SPLIT)
     let ari3 ← ExceptT.mk (ARITH_RULE [[i < n ==> (1 + n - i - 1 = n - i)]])
     let sp4 ← ExceptT.mk (HolLight.SPECL [ [[f:num->num]], [[p:num]], [[1]], [[i + 1]], [[n - i - 1]] ] PSEQ_SPLIT)
     let ari4 ← ExceptT.mk (ARITH_RULE [[i < n ==> i + 1 <= n]])
     let ar1 ← ExceptT.mk (ARITH_RULE [[1 <= x <=> ~(x = 0)]])
     let arle ← ExceptT.mk (ARITH_RULE [[1 * a <= c ==> a <= b + c]])
     pure
      (REPEAT STRIP_TAC THEN
       SUBGOAL_THEN ([[?j. j <= n /\ !i. i <= n ==> f i <= f j]]) MP_TAC THENL
        [SPEC_TAC ([[n:num]], [[n:num]]) THEN POP_ASSUM_LIST (HolCore.Lib.K ALL_TAC) THEN
         INDUCT_TAC THENL
          [SIMP_TAC [LE] THEN MESON_TAC [LE_REFL], ALL_TAC] THEN
         FIRST_ASSUM (X_CHOOSE_THEN ([[j:num]]) STRIP_ASSUME_TAC) THEN
         DISJ_CASES_TAC ar0 THENL
          [EXISTS_TAC [[j:num]] THEN
           ASM_SIMP_TAC [arj] THEN
           REWRITE_TAC [LE] THEN REPEAT STRIP_TAC THEN
           ASM_SIMP_TAC [] THEN ASM_MESON_TAC [],
           EXISTS_TAC [[SUC n]] THEN REWRITE_TAC [LE_REFL] THEN
           REWRITE_TAC [LE] THEN REPEAT STRIP_TAC THEN
           ASM_SIMP_TAC [LE_REFL] THEN ASM_MESON_TAC [LE_TRANS]],
         ALL_TAC] THEN
       DISCH_THEN (X_CHOOSE_THEN ([[ibig:num]]) STRIP_ASSUME_TAC) THEN
       MP_TAC eb THEN
       DISCH_THEN (X_CHOOSE_THEN ([[p:num]]) STRIP_ASSUME_TAC) THEN
       EXISTS_TAC [[p:num]] THEN CONJ_TAC THENL
        [EXISTS_TAC [[ibig:num]] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
       SUBGOAL_THEN ([[~(p = 0)]]) ASSUME_TAC THENL
          [ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN
       CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
       SUBGOAL_THEN ([[!i. i <= n ==> f i < p]]) ASSUME_TAC THENL
        [ASM_MESON_TAC [LET_TRANS], ALL_TAC] THEN
       EXISTS_TAC [[PSEQ p f 0 (SUC n)]] THEN CONJ_TAC THENL
        [MATCH_MP_TAC PSEQ_BOUND THEN ASM_SIMP_TAC [LT_SUC_LE], ALL_TAC] THEN
       CONJ_TAC THENL [ASM_MESON_TAC [LE_0], ALL_TAC] THEN
       CONJ_TAC THENL [ASM_MESON_TAC [LE_REFL], ALL_TAC] THEN
       REPEAT CONJ_TAC THENL
        [ASM_REWRITE_TAC [PSEQ] THEN MESON_TAC [],
         MP_TAC sp1 THEN
         ASM_SIMP_TAC [ADD1, ADD_CLAUSES] THEN
         DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN EXISTS_TAC [[PSEQ p f 0 n]] THEN
         ASM_SIMP_TAC [PSEQ_BOUND, PSEQ_1, LT_IMP_LE],
         ALL_TAC] THEN
       ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[a ==> b ==> c <=> b ==> a ==> c]]))] THEN
       ASM_SIMP_TAC [primepow, LEFT_IMP_EXISTS_THM] THEN
       GEN_TAC THEN X_GEN_TAC [[i:num]] THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
       ASM_REWRITE_TAC [LT_EXP] THEN STRIP_TAC THEN
       MP_TAC sp2 THEN
       ASM_SIMP_TAC [ari] THEN
       DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
       EXISTS_TAC [[PSEQ p f 0 i]] THEN REWRITE_TAC [EQ_ADD_LCANCEL] THEN
       ASM_REWRITE_TAC [EQ_MULT_LCANCEL, EXP_EQ_0, ADD_CLAUSES] THEN
       CONJ_TAC THENL
        [ASM_MESON_TAC [PSEQ_BOUND, LT_TRANS, LT_IMP_LE], ALL_TAC] THEN
       MP_TAC sp3 THEN
       ASM_SIMP_TAC [ari2] THEN
       DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN EXISTS_TAC [[PSEQ p f i 1]] THEN
       ASM_REWRITE_TAC [EQ_ADD_LCANCEL, EQ_MULT_LCANCEL, EXP_1] THEN
       ASM_SIMP_TAC [PSEQ_1, LT_IMP_LE] THEN
       MP_TAC sp4 THEN
       ASM_SIMP_TAC [ari3] THEN
       DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN EXISTS_TAC [[PSEQ p f (i + 1) 1]] THEN
       ASM_REWRITE_TAC [EQ_ADD_LCANCEL, EQ_MULT_LCANCEL, EXP_1] THEN
       ASM_SIMP_TAC [PSEQ_1, ari4] THEN
       ASM_SIMP_TAC [(← HolLight.GSYM ADD1)] THEN REWRITE_TAC [ADD1] THEN
       ONCE_REWRITE_TAC [CONJ_SYM] THEN REWRITE_TAC [UNWIND_THM1] THEN
       REWRITE_TAC [LEFT_ADD_DISTRIB, MULT_ASSOC, ADD_ASSOC] THEN
       MATCH_MP_TAC arle THEN
       REWRITE_TAC [LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
       ASM_REWRITE_TAC [ar1, MULT_EQ_0, EXP_EQ_0]))
  : ExceptT String IO thm).run
#eval RELPOW_LEMMA_1

#eval phrase 16
unsafe def RELPOW_LEMMA_2 : thm := keep "RELPOW_LEMMA_2" fun _ => (do
  prove ([[prime p /\ x < p /\ y < p /\
   (?qx. m = x + p * qx) /\
   (?ry. ry < p EXP n /\ (m = ry + p EXP n * y)) /\
   (!q. q < p EXP n
        ==> primepow p q
            ==> ?r a b s. (m = r + q * (a + p * (b + p * s))) /\
                          r < q /\ a < p /\ b < p /\ R a b)
   ==> RELPOW n R x y]])
   (HolLight.tactic_of do
     let asm1 ← liftExcept (HolCore.Kernel.ASSUME [[y < p]])
     let asm2 ← liftExcept (HolCore.Kernel.ASSUME [[m = ry + p EXP n * y]])
     let ar ← ExceptT.mk (ARITH_RULE [[p + q * p = (q + 1) * p]])
     let taut1 ← ExceptT.mk (TAUT [[(b <=> a) ==> a ==> b]])
     pure
      (STRIP_TAC THEN REWRITE_TAC [RELPOW_SEQUENCE] THEN
       EXISTS_TAC [[\i. (m DIV (p EXP i)) MOD p]] THEN
       SUBGOAL_THEN ([[~(p = 0)]]) ASSUME_TAC THENL
        [ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN
       REWRITE_TAC [EXP, DIV_1] THEN REPEAT CONJ_TAC THENL
        [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC [[qx:num]] THEN
         ASM_REWRITE_TAC [ADD_AC, MULT_AC],
         MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC [[0]] THEN
         REWRITE_TAC [asm1, MULT_CLAUSES, ADD_CLAUSES] THEN
         MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC [[ry:num]] THEN
         REWRITE_TAC [asm2] THEN
         ASM_REWRITE_TAC [ADD_AC, MULT_AC],
         ALL_TAC] THEN
       X_GEN_TAC [[i:num]] THEN DISCH_TAC THEN
       FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[p EXP i]])) THEN
       ASM_SIMP_TAC [LT_EXP, PRIME_GE_2] THEN
       ASM_REWRITE_TAC [primepow] THEN
       HolCore.Lib.W (fun g => HolLight.tactic_of do
         let t ← liftExcept (HolCore.Lib.funpow 2 (fun (m : Except String term) => do HolCore.Equal.lhand (← m)) (pure (HolLight.snd g)))
         pure (SUBGOAL_THEN t (fun th => REWRITE_TAC [th]))) THENL
        [MESON_TAC [], ALL_TAC] THEN
       DISCH_THEN (REPEAT_TCL CHOOSE_THEN MP_TAC) THEN
       DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
       UNDISCH_TAC [[(R:num->num->bool) a b]] THEN
       MATCH_MP_TAC taut1 THEN BINOP_TAC THENL
        [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC [[b + p * s]] THEN
         ASM_REWRITE_TAC [] THEN
         MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC [[r:num]] THEN ASM_REWRITE_TAC [] THEN
         REWRITE_TAC [ADD_AC, MULT_AC],
         MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC [[s:num]] THEN ASM_REWRITE_TAC [] THEN
         MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC [[r + a * p EXP i]] THEN
         CONJ_TAC THENL
          [REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] THEN
           REWRITE_TAC [ADD_AC, MULT_AC], ALL_TAC] THEN
         MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC [[p EXP i + a * p EXP i]] THEN
         ASM_REWRITE_TAC [LT_ADD_RCANCEL] THEN
         REWRITE_TAC [ar] THEN
         ASM_REWRITE_TAC [LE_MULT_RCANCEL, EXP_EQ_0] THEN
         UNDISCH_TAC [[a < p]] THEN ARITH_TAC]))
  : ExceptT String IO thm).run
#eval RELPOW_LEMMA_2

#eval phrase 17
unsafe def RELPOW_LEMMA : thm := keep "RELPOW_LEMMA" fun _ => (do
  prove ([[RELPOW n R x y <=>
        ?m p. prime p /\ x < p /\ y < p /\
              (?qx. m = x + p * qx) /\
              (?ry. ry < p EXP n /\ (m = ry + p EXP n * y)) /\
              !q. q < p EXP n
                  ==> primepow p q
                      ==> ?r a b s. (m = r + q * (a + p * (b + p * s))) /\
                                    r < q /\ a < p /\ b < p /\ R a b]])
   (EQ_TAC THENL
     [ALL_TAC, REWRITE_TAC [RELPOW_LEMMA_2, LEFT_IMP_EXISTS_THM]] THEN
    REWRITE_TAC [RELPOW_SEQUENCE] THEN
    DISCH_THEN (CHOOSE_THEN (MP_TAC o GEN_ALL o HolLight.MATCH_MP RELPOW_LEMMA_1)) THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [SWAP_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
    SIMP_TAC [] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval RELPOW_LEMMA

#eval phrase 18
unsafe def RTC_SIGMA : thm := keep "RTC_SIGMA" fun _ => (do
  prove ([[RTC R x y <=>
        ?m p Q. primepow p Q /\ x < p /\ y < p /\
                (?s. m = x + p * s) /\
                (?r. r < Q /\ (m = r + Q * y)) /\
                !q. q < Q
                    ==> primepow p q
                        ==> ?r a b s. (m = r + q * (a + p * (b + p * s))) /\
                                      r < q /\ a < p /\ b < p /\ R a b]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[(a /\ b) /\ c <=> b /\ a /\ c]])
     pure
      (REWRITE_TAC [RTC_RELPOW] THEN EQ_TAC THENL
        [DISCH_THEN (X_CHOOSE_THEN ([[n:num]]) MP_TAC) THEN
         REWRITE_TAC [RELPOW_LEMMA] THEN
         MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
         MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
         DISCH_TAC THEN EXISTS_TAC [[p EXP n]] THEN ASM_REWRITE_TAC [primepow] THEN
         MESON_TAC [],
         REWRITE_TAC [primepow] THEN
         ONCE_REWRITE_TAC [taut1] THEN
         REWRITE_TAC [(← HolLight.GSYM primepow)] THEN
         GEN_REWRITE_TAC (HolLight.LAND_CONV o HolCore.Lib.funpow 3 HolLight.BINDER_CONV)
          [LEFT_AND_EXISTS_THM] THEN
         GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.BINDER_CONV o HolLight.BINDER_CONV)
          [SWAP_EXISTS_THM] THEN
         REWRITE_TAC [UNWIND_THM2] THEN
         GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.BINDER_CONV) [SWAP_EXISTS_THM] THEN
         GEN_REWRITE_TAC HolLight.LAND_CONV [SWAP_EXISTS_THM] THEN
         REWRITE_TAC [(← HolLight.GSYM RELPOW_LEMMA)]]))
  : ExceptT String IO thm).run
#eval RTC_SIGMA

#eval phrase 19
unsafe def arith_pair : thm := keep "arith_pair" fun _ => new_definition
  [[arith_pair s t = (s ++ t) ** (s ++ t) ++ s ++ Suc Z]]
#eval arith_pair

#eval phrase 20
unsafe def ARITH_PAIR : thm := keep "ARITH_PAIR" fun _ => (do
  prove ([[!s t v. termval v (arith_pair s t) = NPAIR (termval v s) (termval v t)]])
   (REWRITE_TAC [termval, arith_pair, NPAIR, EXP_2, ARITH_SUC])
  : ExceptT String IO thm).run
#eval ARITH_PAIR

#eval phrase 21
unsafe def FVT_PAIR : thm := keep "FVT_PAIR" fun _ => (do
  prove ([[FVT(arith_pair s t) = FVT(s) UNION FVT(t)]])
   (REWRITE_TAC [arith_pair, FVT] THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval FVT_PAIR

/- Parse a quotation once (the OCaml toplevel parses each backtick string once
   when `OBJECTIFY` is defined).  `unsafeIO` resolves the parser's IO here. -/
private unsafe def ptm (s : String) : term :=
  match unsafeIO (HolCore.Parser.parse_term s) with
  | .ok (.ok t) => t
  | .ok (.error e) => panic! s!"parse_term {s}: {e}"
  | .error e => panic! s!"parse_term IO {s}: {e}"

private unsafe def pty (s : String) : hol_type :=
  match unsafeIO (HolCore.Parser.parse_type s) with
  | .ok (.ok t) => t
  | .ok (.error e) => panic! s!"parse_type {s}: {e}"
  | .error e => panic! s!"parse_type IO {s}: {e}"

#eval phrase 22
unsafe def OBJECTIFY : List thm → String → thm → ExceptT String IO (thm × thm) :=
  keep "OBJECTIFY" fun _ =>
  let is_add := is_binop (ptm "(+):num->num->num")
  let is_mul := is_binop (ptm "(*):num->num->num")
  let is_le := is_binop (ptm "(<=):num->num->bool")
  let is_lt := is_binop (ptm "(<):num->num->bool")
  let zero_tm := ptm "0"
  let suc_tm := ptm "SUC"
  let osuc_tm := ptm "Suc"
  let oz_tm := ptm "Z"
  let ov_tm := ptm "V"
  let oadd_tm := ptm "(++)"
  let omul_tm := ptm "(**)"
  let oeq_tm := ptm "(===)"
  let ole_tm := ptm "(<<=)"
  let olt_tm := ptm "(<<)"
  let oiff_tm := ptm "(<->)"
  let oimp_tm := ptm "(-->)"
  let oand_tm := ptm "(&&)"
  let oor_tm := ptm "(||)"
  let onot_tm := ptm "Not"
  let oall_tm := ptm "!!"
  let oex_tm := ptm "??"
  let numeral_tm := ptm "numeral"
  let assign_tm := ptm "(|->):num->term->(num->term)->(num->term)"
  let term_ty := pty "term"
  let form_ty := pty "form"
  let num_ty := pty "num"
  let formsubst_tm := ptm "formsubst"
  let holdsv_tm := ptm "holds v"
  let v_tm := ptm "v:num->num"
  let objectify1 (fn : Func term term → term → Except String term) (op : term)
      (env : Func term term) (tm : term) : Except String term := do
    mk_comb op (← fn env (← rand tm))
  let objectify2 (fn : Func term term → term → Except String term) (op : term)
      (env : Func term term) (tm : term) : Except String term := do
    mk_comb (← mk_comb op (← fn env (← HolCore.Equal.lhand tm))) (← fn env (← rand tm))
  fun defs =>
    let defs' := [TERMVAL_NUMERAL, ARITH_PAIR] ++ defs
    let rec objectify_term (env : Func term term) (tm : term) : Except String term :=
      if is_var tm then do mk_comb ov_tm (← apply env tm)
      else if tm == zero_tm then Except.ok oz_tm
      else if is_numeral tm then do mk_comb numeral_tm tm
      else if is_add tm then objectify2 objectify_term oadd_tm env tm
      else if is_mul tm then objectify2 objectify_term omul_tm env tm
      else if is_comb tm && (match rator tm with | .ok r => r == suc_tm | _ => false)
        then objectify1 objectify_term osuc_tm env tm
      else
        let (f, args) := strip_comb tm
        do
        let args' ← args.mapM (objectify_term env)
        match (do
                let dth ← find
                  (fun th => match (do
                       let rl ← rand (Prod.snd (strip_forall (concl th)))
                       Except.ok (Prod.fst (strip_comb rl)) : Except String term) with
                     | .ok fs => fs == f | _ => false)
                  defs'
                let (l, _r) ← dest_eq (Prod.snd (strip_forall (concl dth)))
                let rl ← rand l
                list_mk_comb (Prod.fst (strip_comb rl)) args'
               : Except String term) with
        | .ok res => Except.ok res
        | .error _ => do
            let ty ← HolCore.Lib.itlistM (fun a acc => Except.ok (hol_type.Tyapp "fun" [type_of a, acc]))
                        args' form_ty
            let v := mk_var (Prod.fst (← dest_var f)) ty
            list_mk_comb v args'
    let rec objectify_formula (env : Func term term) (fm : term) : Except String term :=
      if is_forall fm then do
        let (x, bod) ← dest_forall fm
        let n ← mk_small_numeral (HolCore.Lib.itlist
          (fun t acc => match dest_small_numeral t with | .ok i => max i acc | _ => acc)
          (ran env) (0:Int) + 1)
        mk_comb (← mk_comb oall_tm n) (← objectify_formula ((x |-> n) env) bod)
      else if is_exists fm then do
        let (x, bod) ← dest_exists fm
        let n ← mk_small_numeral (HolCore.Lib.itlist
          (fun t acc => match dest_small_numeral t with | .ok i => max i acc | _ => acc)
          (ran env) (0:Int) + 1)
        mk_comb (← mk_comb oex_tm n) (← objectify_formula ((x |-> n) env) bod)
      else if HolCore.Bool.is_iff fm then objectify2 objectify_formula oiff_tm env fm
      else if is_imp fm then objectify2 objectify_formula oimp_tm env fm
      else if is_conj fm then objectify2 objectify_formula oand_tm env fm
      else if is_disj fm then objectify2 objectify_formula oor_tm env fm
      else if is_neg fm then objectify1 objectify_formula onot_tm env fm
      else if is_le fm then objectify2 objectify_term ole_tm env fm
      else if is_lt fm then objectify2 objectify_term olt_tm env fm
      else if is_eq fm then objectify2 objectify_term oeq_tm env fm
      else objectify_term env fm
    fun nam th => do
      let (ptm0, tm) ← liftExcept (dest_eq (Prod.snd (strip_forall (concl th))))
      let vs := (Prod.snd (strip_comb ptm0)).filter (fun v => type_of v == num_ty)
      let ns := HolCore.Lib.upto 1 (vs.length : Int)
      let env ← liftExcept (HolCore.Lib.itlist2M
        (fun v n acc => do pure ((v |-> (← mk_small_numeral n)) acc))
        vs ns HolCore.Lib.undefined)
      let otm ← liftExcept (objectify_formula env tm)
      let vs' ← liftExcept (vs.mapM (fun v => do pure (mk_var (Prod.fst (← dest_var v)) term_ty)))
      let stm ← liftExcept (HolCore.Lib.itlist2M
        (fun v n a => do
          mk_comb (← mk_comb (← mk_comb assign_tm (← mk_small_numeral n)) v) a)
        vs' ns ov_tm)
      let rside ← liftExcept (do mk_comb (← mk_comb formsubst_tm stm) otm)
      let vs'' := HolCore.Lib.subtract (frees rside) vs' ++ vs'
      let lty ← liftExcept (HolCore.Lib.itlistM (fun a acc => Except.ok (hol_type.Tyapp "fun" [type_of a, acc]))
                    vs'' (type_of rside))
      let lside ← liftExcept (list_mk_comb (mk_var nam lty) vs'')
      let defn := HolCore.Kernel.safe_mk_eq lside rside
      let dth ← ExceptT.mk (Session.new_definition defn)
      let clside ← liftExcept (HolCore.Equal.lhs (Prod.snd (strip_forall (concl dth))))
      let etm ← liftExcept (mk_comb holdsv_tm clside)
      let gsymth ← HolLight.GSYM th
      let thm ← ExceptT.mk
        ((HolLight.REWRITE_CONV ([dth, holds, HOLDS_FORMSUBST] ++ defs') THENC
          HolLight.REWRITE_CONV [termval, ARITH_EQ, o_THM, valmod] THENC
          HolLight.GEN_REWRITE_CONV HolCore.Lib.I [gsymth]) etm)
      let g2 ← liftExcept (GENL (v_tm :: vs') thm)
      let d2 ← liftExcept (DISCH_ALL g2)
      pure (dth, d2)
#eval IO.println "<fun>"

#eval phrase 23
unsafe def FV_TAC : List thm → HolCore.Tactics.tactic :=
  keep "FV_TAC" fun _ => fun ths =>
  HolLight.tactic_of do
    let ths' := ths ++
     [FV, FORMSUBST_FV, FVT, TERMSUBST_FVT, IN_ELIM_THM,
      NOT_IN_EMPTY, IN_UNION, IN_DELETE, IN_SING]
    let taut1 ← ExceptT.mk (TAUT [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]])
    let gca ← HolLight.GSYM CONJ_ASSOC
    let tac :=
       REWRITE_TAC [DISJ_ACI, taut1] THEN
       REWRITE_TAC [EXISTS_OR_THM, gca, UNWIND_THM2, ARITH_EQ] THEN
       REWRITE_TAC [valmod, ARITH_EQ, FVT] THEN REWRITE_TAC [DISJ_ACI]
    pure
     (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
      ASM_REWRITE_TAC ths' THEN tac THEN ASM_SIMP_TAC ths' THEN tac)
#eval IO.println "<fun>"

#eval phrase 24
unsafe def arith_divides_pair : thm × thm := keep "arith_divides_pair" fun _ =>
  runObj (OBJECTIFY [] "arith_divides" divides_DELTA)
unsafe def arith_divides : thm := arith_divides_pair.1
unsafe def ARITH_DIVIDES : thm := arith_divides_pair.2
#eval do IO.println arith_divides; IO.println ARITH_DIVIDES

#eval phrase 25
unsafe def FV_DIVIDES : thm := keep "FV_DIVIDES" fun _ => (do
  prove ([[!s t. FV(arith_divides s t) = FVT(s) UNION FVT(t)]])
   (FV_TAC [arith_divides])
  : ExceptT String IO thm).run
#eval FV_DIVIDES

#eval phrase 26
unsafe def arith_prime_pair : thm × thm := keep "arith_prime_pair" fun _ =>
  runObj (OBJECTIFY [ARITH_DIVIDES] "arith_prime" prime_DELTA)
unsafe def arith_prime : thm := arith_prime_pair.1
unsafe def ARITH_PRIME : thm := arith_prime_pair.2
#eval do IO.println arith_prime; IO.println ARITH_PRIME

#eval phrase 27
unsafe def FV_PRIME : thm := keep "FV_PRIME" fun _ => (do
  prove ([[!t. FV(arith_prime t) = FVT(t)]])
   (FV_TAC [arith_prime, FVT_NUMERAL, FV_DIVIDES])
  : ExceptT String IO thm).run
#eval FV_PRIME

#eval phrase 28
unsafe def arith_primepow_pair : thm × thm := keep "arith_primepow_pair" fun _ =>
  runObj (OBJECTIFY [ARITH_PRIME, ARITH_DIVIDES] "arith_primepow" primepow_DELTA)
unsafe def arith_primepow : thm := arith_primepow_pair.1
unsafe def ARITH_PRIMEPOW : thm := arith_primepow_pair.2
#eval do IO.println arith_primepow; IO.println ARITH_PRIMEPOW

#eval phrase 29
unsafe def FV_PRIMEPOW : thm := keep "FV_PRIMEPOW" fun _ => (do
  prove ([[!s t. FV(arith_primepow s t) = FVT(s) UNION FVT(t)]])
   (FV_TAC [arith_primepow, FVT_NUMERAL, FV_DIVIDES, FV_PRIME])
  : ExceptT String IO thm).run
#eval FV_PRIMEPOW

#eval phrase 30
unsafe def arith_rtc_pair : thm × thm := keep "arith_rtc_pair" fun _ =>
  runObj (do
    let asm ← liftExcept (HolCore.Kernel.ASSUME
      [[!v s t. holds v (R s t) <=> r (termval v s) (termval v t)]])
    OBJECTIFY [ARITH_PRIMEPOW, asm] "arith_rtc" RTC_SIGMA)
unsafe def arith_rtc : thm := arith_rtc_pair.1
unsafe def ARITH_RTC : thm := arith_rtc_pair.2
#eval do IO.println arith_rtc; IO.println ARITH_RTC

#eval phrase 31
unsafe def FV_RTC : thm := keep "FV_RTC" fun _ => (do
  prove ([[!R. (!s t. FV(R s t) = FVT(s) UNION FVT(t))
       ==> !s t. FV(arith_rtc R s t) = FVT(s) UNION FVT(t)]])
   (FV_TAC [arith_rtc, FV_PRIMEPOW])
  : ExceptT String IO thm).run
#eval FV_RTC

#eval phrase 32
unsafe def OBJECTIFY_RTC_pth : thm := keep "OBJECTIFY_RTC_pth" fun _ => (do
  prove ([[(!v x y. holds v (f x y) <=> f' (termval v x) (termval v y))
     ==> !g. (!n. g n = formsubst ((0 |-> n) V)
                                  (arith_rtc f (numeral 0)
                                               (arith_pair (V 0) (numeral 0))))
             ==> !v n. holds v (g n) <=> RTC f' 0 (NPAIR (termval v n) 0)]])
   (DISCH_THEN (MP_TAC o HolLight.MATCH_MP ARITH_RTC) THEN SIMP_TAC [HOLDS_FORMSUBST] THEN
    REWRITE_TAC [termval, o_DEF, ARITH_EQ, valmod,
                ARITH_PAIR, TERMVAL_NUMERAL])
  : ExceptT String IO thm).run
unsafe def OBJECTIFY_RTC : thm → String → thm → ExceptT String IO (thm × thm) :=
  keep "OBJECTIFY_RTC" fun _ => fun defn nam th => do
    let th1 ← HolLight.MATCH_MP OBJECTIFY_RTC_pth defn
    let v := Prod.fst (← liftExcept (dest_forall (concl th1)))
    let th2 ← HolLight.SPEC (mk_var nam (type_of v)) th1
    let dth ← ExceptT.mk (Session.new_definition (← liftExcept (Prod.fst <$> dest_imp (concl th2))))
    let r2 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM th)] (← HolLight.MATCH_MP th2 dth)
    pure (dth, r2)
#eval (do let _ := OBJECTIFY_RTC_pth; IO.println "<fun>" : IO Unit)

#eval phrase 33
unsafe def RTCP : thm := keep "RTCP" fun _ => new_definition
  [[RTCP R m x y <=> RTC (R m) x y]]
#eval RTCP

#eval phrase 34
unsafe def RTCP_SIGMA : thm := keep "RTCP_SIGMA" fun _ => (do
  let inst ← liftExcept (INST [([[(R:num->num->num->bool) m]], [[R:num->num->bool]])] RTC_SIGMA)
  HolLight.REWRITE_RULE [(← HolLight.GSYM RTCP)] inst
  : ExceptT String IO thm).run
#eval RTCP_SIGMA

#eval phrase 35
unsafe def arith_rtcp_pair : thm × thm := keep "arith_rtcp_pair" fun _ =>
  runObj (do
    let asm ← liftExcept (HolCore.Kernel.ASSUME
      [[!v m s t. holds v (R m s t) <=>
                   r (termval v m) (termval v s) (termval v t)]])
    OBJECTIFY [ARITH_PRIMEPOW, asm] "arith_rtcp" RTCP_SIGMA)
unsafe def arith_rtcp : thm := arith_rtcp_pair.1
unsafe def ARITH_RTCP : thm := arith_rtcp_pair.2
#eval do IO.println arith_rtcp; IO.println ARITH_RTCP

#eval phrase 36
unsafe def ARITH_RTC_PARAMETRIZED : thm := keep "ARITH_RTC_PARAMETRIZED" fun _ => (do
  HolLight.REWRITE_RULE [RTCP] ARITH_RTCP
  : ExceptT String IO thm).run
#eval ARITH_RTC_PARAMETRIZED

#eval phrase 37
unsafe def FV_RTCP : thm := keep "FV_RTCP" fun _ => (do
  prove ([[!R. (!s t u. FV(R s t u) = FVT(s) UNION FVT(t) UNION FVT(u))
       ==> !s t u. FV(arith_rtcp R s t u) = FVT(s) UNION FVT(t) UNION FVT(u)]])
   (FV_TAC [arith_rtcp, FV_PRIMEPOW])
  : ExceptT String IO thm).run
#eval FV_RTCP

#eval phrase 38
unsafe def OBJECTIFY_RTCP_pth : thm := keep "OBJECTIFY_RTCP_pth" fun _ => (do
  prove ([[(!v m x y. holds v (f m x y) <=>
                f' (termval v m) (termval v x) (termval v y))
     ==> !g. (!m n. g m n = formsubst ((1 |-> m) ((0 |-> n) V))
                                  (arith_rtcp f (V 1) (numeral 0)
                                               (arith_pair (V 0) (numeral 0))))
             ==> !v m n. holds v (g m n) <=>
                          RTC (f' (termval v m)) 0 (NPAIR (termval v n) 0)]])
   (DISCH_THEN (MP_TAC o HolLight.MATCH_MP ARITH_RTC_PARAMETRIZED) THEN
    SIMP_TAC [HOLDS_FORMSUBST] THEN
    REWRITE_TAC [termval, o_DEF, ARITH_EQ, valmod,
                ARITH_PAIR, TERMVAL_NUMERAL])
  : ExceptT String IO thm).run
unsafe def OBJECTIFY_RTCP : thm → String → thm → ExceptT String IO (thm × thm) :=
  keep "OBJECTIFY_RTCP" fun _ => fun defn nam th => do
    let th1 ← HolLight.MATCH_MP OBJECTIFY_RTCP_pth defn
    let v := Prod.fst (← liftExcept (dest_forall (concl th1)))
    let th2 ← HolLight.SPEC (mk_var nam (type_of v)) th1
    let dth ← ExceptT.mk (Session.new_definition (← liftExcept (Prod.fst <$> dest_imp (concl th2))))
    let r2 ← HolLight.ONCE_REWRITE_RULE [(← HolLight.GSYM th)] (← HolLight.MATCH_MP th2 dth)
    pure (dth, r2)
#eval (do let _ := OBJECTIFY_RTCP_pth; IO.println "<fun>" : IO Unit)

#eval phrase 39
unsafe def PRIMREC_SIGMA : thm := keep "PRIMREC_SIGMA" fun _ => (do
  prove ([[(fn 0 = e) /\
   (!n. fn (SUC n) = f (fn n) n)
   ==> !x y. RTC (\x y. ?n r. (x = NPAIR n r) /\ (y = NPAIR (SUC n) (f r n)))
                 (NPAIR 0 e) (NPAIR x y) <=>
             (fn(x) = y)]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[a /\ b /\ c <=> b /\ a /\ c]])
     pure
      (REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
       ONCE_REWRITE_TAC [RTC_CASES_L] THEN ASM_REWRITE_TAC [NPAIR_INJ, NOT_SUC] THEN
       REWRITE_TAC [SUC_INJ, RIGHT_AND_EXISTS_THM] THEN GEN_TAC THEN
       ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
       GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.BINDER_CONV) [SWAP_EXISTS_THM] THEN
       ONCE_REWRITE_TAC [taut1] THEN
       ASM_REWRITE_TAC [UNWIND_THM2] THEN ASM_MESON_TAC []))
  : ExceptT String IO thm).run
#eval PRIMREC_SIGMA

#eval phrase 40
unsafe def arith_primrecstep : thm := keep "arith_primrecstep" fun _ => new_definition
  [[arith_primrecstep R s t =
        (formsubst ((0 |-> s) ((1 |-> t) V))
                  (?? 2 (?? 3 (?? 4
                  (V 0 === arith_pair (V 2) (V 3) &&
                   V 1 === arith_pair (Suc(V 2)) (V 4) &&
                   R (V 3) (V 2) (V 4))))))]]
#eval arith_primrecstep

#eval phrase 41
unsafe def ARITH_PRIMRECSTEP : thm := keep "ARITH_PRIMRECSTEP" fun _ => (do
  prove ([[(!v x y z. holds v (R x y z) <=>
              (f (termval v x) (termval v y) = termval v z))
    ==> !v s t. holds v (arith_primrecstep R s t) <=>
                ?n r. (termval v s = NPAIR n r) /\
                      (termval v t = NPAIR (SUC n) (f r n))]])
   (STRIP_TAC THEN
    ASM_REWRITE_TAC [arith_primrecstep, holds, HOLDS_FORMSUBST] THEN
    ASM_REWRITE_TAC [termval, valmod, o_DEF, ARITH_EQ, ARITH_PAIR] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval ARITH_PRIMRECSTEP

#eval phrase 42
unsafe def FV_PRIMRECSTEP : thm := keep "FV_PRIMRECSTEP" fun _ => (do
  prove ([[!R. (!s t u. FV(R s t u) SUBSET (FVT(s) UNION FVT(t) UNION FVT(u)))
       ==> !s t. FV(arith_primrecstep R s t) = FVT(s) UNION FVT(t)]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[~a ==> (a \/ b <=> b)]])
     pure
      (REWRITE_TAC [SUBSET, IN_UNION] THEN FV_TAC [arith_primrecstep, FVT_PAIR] THEN
       GEN_TAC THEN MATCH_MP_TAC taut1 THEN
       DISCH_THEN (CHOOSE_THEN
        (CONJUNCTS_THEN2 (ANTE_RES_THEN MP_TAC) ASSUME_TAC)) THEN
       ASM_REWRITE_TAC [FVT, IN_SING]))
  : ExceptT String IO thm).run
#eval FV_PRIMRECSTEP

#eval phrase 43
unsafe def arith_primrec : thm := keep "arith_primrec" fun _ => new_definition
  [[arith_primrec R c s t =
        arith_rtc (arith_primrecstep R)
            (arith_pair Z c) (arith_pair s t)]]
#eval arith_primrec

#eval phrase 44
unsafe def ARITH_PRIMREC : thm := keep "ARITH_PRIMREC" fun _ => (do
  prove ([[!fn e f R c.
        (fn 0 = e) /\ (!n. fn (SUC n) = f (fn n) n) /\
        (!v. termval v c = e) /\
                  (!v x y z. holds v (R x y z) <=>
                             (f (termval v x) (termval v y) = termval v z))
                  ==> !v s t. holds v (arith_primrec R c s t) <=>
                               (fn(termval v s) = termval v t)]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP ARITH_PRIMRECSTEP) THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP ARITH_RTC) THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV (fun t => pure (Session.ETA_CONV t))) THEN
    SIMP_TAC [arith_primrec, ARITH_PAIR, termval] THEN
    ASM_SIMP_TAC [PRIMREC_SIGMA])
  : ExceptT String IO thm).run
#eval ARITH_PRIMREC

#eval phrase 45
unsafe def FV_PRIMREC : thm := keep "FV_PRIMREC" fun _ => (do
  prove ([[!R c. (FVT c = {}) /\
         (!s t u. FV(R s t u) SUBSET (FVT(s) UNION FVT(t) UNION FVT(u)))
         ==> !s t. FV(arith_primrec R c s t) = FVT(s) UNION FVT(t)]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [arith_primrec] THEN
    ASM_SIMP_TAC [FV_RTC, FVT_PAIR, FV_PRIMRECSTEP,
                 UNION_EMPTY, UNION_ACI, FVT])
  : ExceptT String IO thm).run
#eval FV_PRIMREC

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.Definability" do
  replay (
          HolLogicArith.ArithFol.ensure)
  replay (
          Session.prioritize_num)
  replay (
          NPAIR)
  replay (
          NPAIR_NONZERO)
  replay (
          NPAIR_INJ_LEMMA)
  replay (
          NPAIR_INJ)
  replay (
          NPAIR_LT)
  replay (
          primepow)
  replay (
          divides_DELTA)
  replay (
          prime_DELTA)
  replay (
          primepow_DELTA)
  replay (
          PSEQ)
  replay (
          PSEQ_SPLIT)
  replay (
          PSEQ_1)
  replay (
          PSEQ_BOUND)
  replay (
          RELPOW_LEMMA_1)
  replay (
          RELPOW_LEMMA_2)
  replay (
          RELPOW_LEMMA)
  replay (
          RTC_SIGMA)
  replay (
          arith_pair)
  replay (
          ARITH_PAIR)
  replay (
          FVT_PAIR)
  replay (
          IO.println "<fun>")
  replay (
          IO.println "<fun>")
  replay (
          do IO.println arith_divides; IO.println ARITH_DIVIDES)
  replay (
          FV_DIVIDES)
  replay (
          do IO.println arith_prime; IO.println ARITH_PRIME)
  replay (
          FV_PRIME)
  replay (
          do IO.println arith_primepow; IO.println ARITH_PRIMEPOW)
  replay (
          FV_PRIMEPOW)
  replay (
          do IO.println arith_rtc; IO.println ARITH_RTC)
  replay (
          FV_RTC)
  replay (
          (do let _ := OBJECTIFY_RTC_pth; IO.println "<fun>" : IO Unit))
  replay (
          RTCP)
  replay (
          RTCP_SIGMA)
  replay (
          do IO.println arith_rtcp; IO.println ARITH_RTCP)
  replay (
          ARITH_RTC_PARAMETRIZED)
  replay (
          FV_RTCP)
  replay (
          (do let _ := OBJECTIFY_RTCP_pth; IO.println "<fun>" : IO Unit))
  replay (
          PRIMREC_SIGMA)
  replay (
          arith_primrecstep)
  replay (
          ARITH_PRIMRECSTEP)
  replay (
          FV_PRIMRECSTEP)
  replay (
          arith_primrec)
  replay (
          ARITH_PRIMREC)
  replay (
          FV_PRIMREC)
-- @@ENSURE END

end HolLogicArith.Definability
