/- File: HolLogicArith/Tarski.lean
Translation of HOL Light's Arithmetic/tarski.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Definability
open HolCore.Kernel HolCore.Lib HolCore.Basics Session HolLight.Syntax HolLogicArith
open scoped HolLight
-- Names from Arithmetic/fol.ml that tarski.ml reuses.
open HolLogicArith.ArithFol (termval holds valmod arithtrue numeral qsubst
  TERMVAL_NUMERAL FVT_NUMERAL HOLDS_FORMSUBST FV FORMSUBST_FV FVT TERMSUBST_FVT
  term_INDUCT form_INDUCT term_CASES form_CASES term_DISTINCT term_INJ
  form_DISTINCT form_INJ FV_QSUBST HOLDS_QSUBST VARIANT VARIANT_FINITE FV_FINITE
  HOLDS_VALUATION VALMOD_BASIC VALMOD_VALMOD_BASIC)
-- Names from Arithmetic/definability.ml that tarski.ml reuses.
open HolLogicArith.Definability (NPAIR NPAIR_INJ arith_pair ARITH_PAIR FVT_PAIR
  arith_rtc ARITH_RTC FV_RTC PRIMREC_SIGMA)

namespace HolLogicArith.Tarski

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- `new_recursive_definition` lifted into `ExceptT String IO`. -/
private unsafe def newRec (ax : thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (Session.new_recursive_definition ax tm)

-- Replay Arithmetic/definability.ml (the one module tarski.ml imports).
#eval HolLogicArith.Definability.ensure

#eval phrase 1
#eval Session.prioritize_num

#eval phrase 2
unsafe def number : thm := keep "number" fun _ => new_definition
  [[number(x) = 2 * (x DIV 2) + (1 - x MOD 2)]]
#eval number

#eval phrase 3
unsafe def denumber : thm := keep "denumber" fun _ => new_definition
  [[denumber = number]]
#eval denumber

#eval phrase 4
unsafe def NUMBER_DENUMBER : thm := keep "NUMBER_DENUMBER" fun _ => (do
  prove ([[(!s. denumber(number s) = s) /\
   (!n. number(denumber n) = n)]])
   (HolLight.tactic_of do
     let ar1 ← ExceptT.mk (ARITH_RULE [[x < 2 ==> (2 * y + x) DIV 2 = y]])
     let ar2 ← ExceptT.mk (ARITH_RULE [[1 - m < 2]])
     let ar3 ← ExceptT.mk (ARITH_RULE [[x < 2 ==> 1 - (1 - x) = x]])
     pure
      (REWRITE_TAC [number, denumber] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
       SIMP_TAC [ar1,
                MOD_MULT_ADD, MOD_LT, (← HolLight.GSYM DIVISION), ARITH_EQ,
                ar2, ar3]))
  : ExceptT String IO thm).run
#eval NUMBER_DENUMBER

#eval phrase 5
unsafe def NUMBER_INJ : thm := keep "NUMBER_INJ" fun _ => (do
  prove ([[!x y. number(x) = number(y) <=> x = y]])
   (MESON_TAC [NUMBER_DENUMBER])
  : ExceptT String IO thm).run
#eval NUMBER_INJ

#eval phrase 6
unsafe def NUMBER_SURJ : thm := keep "NUMBER_SURJ" fun _ => (do
  prove ([[!y. ?x. number(x) = y]])
   (MESON_TAC [NUMBER_DENUMBER])
  : ExceptT String IO thm).run
#eval NUMBER_SURJ

#eval phrase 7
unsafe def gterm : thm := keep "gterm" fun _ => (do
  newRec ArithFol.term_RECURSION
    [[(gterm (V x) = NPAIR 0 (number x)) /\
      (gterm Z = NPAIR 1 0) /\
      (gterm (Suc t) = NPAIR 2 (gterm t)) /\
      (gterm (s ++ t) = NPAIR 3 (NPAIR (gterm s) (gterm t))) /\
      (gterm (s ** t) = NPAIR 4 (NPAIR (gterm s) (gterm t)))]]
  : ExceptT String IO thm).run
#eval gterm

#eval phrase 8
unsafe def gform : thm := keep "gform" fun _ => (do
  newRec ArithFol.form_RECURSION
    [[(gform False = NPAIR 0 0) /\
      (gform True = NPAIR 0 1) /\
      (gform (s === t) = NPAIR 1 (NPAIR (gterm s) (gterm t))) /\
      (gform (s << t) = NPAIR 2 (NPAIR (gterm s) (gterm t))) /\
      (gform (s <<= t) = NPAIR 3 (NPAIR (gterm s) (gterm t))) /\
      (gform (Not p) = NPAIR 4 (gform p)) /\
      (gform (p && q) = NPAIR 5 (NPAIR (gform p) (gform q))) /\
      (gform (p || q) = NPAIR 6 (NPAIR (gform p) (gform q))) /\
      (gform (p --> q) = NPAIR 7 (NPAIR (gform p) (gform q))) /\
      (gform (p <-> q) = NPAIR 8 (NPAIR (gform p) (gform q))) /\
      (gform (!! x p) = NPAIR 9 (NPAIR (number x) (gform p))) /\
      (gform (?? x p) = NPAIR 10 (NPAIR (number x) (gform p)))]]
  : ExceptT String IO thm).run
#eval gform

#eval phrase 9
unsafe def GTERM_INJ : thm := keep "GTERM_INJ" fun _ => (do
  prove ([[!s t. (gterm s = gterm t) <=> (s = t)]])
   (MATCH_MP_TAC term_INDUCT THEN REPEAT CONJ_TAC THENL
     [ALL_TAC,
      GEN_TAC,
      GEN_TAC THEN DISCH_TAC,
      REPEAT GEN_TAC THEN STRIP_TAC,
      REPEAT GEN_TAC THEN STRIP_TAC] THEN
    MATCH_MP_TAC term_INDUCT THEN
    ASM_REWRITE_TAC [term_DISTINCT, term_INJ, gterm,
                    NPAIR_INJ, NUMBER_INJ, ARITH_EQ])
  : ExceptT String IO thm).run
#eval GTERM_INJ

#eval phrase 10
unsafe def GFORM_INJ : thm := keep "GFORM_INJ" fun _ => (do
  prove ([[!p q. (gform p = gform q) <=> (p = q)]])
   (MATCH_MP_TAC form_INDUCT THEN REPEAT CONJ_TAC THENL
     [ALL_TAC,
      ALL_TAC,
      GEN_TAC THEN GEN_TAC,
      GEN_TAC THEN GEN_TAC,
      GEN_TAC THEN GEN_TAC,
      REPEAT GEN_TAC THEN STRIP_TAC,
      REPEAT GEN_TAC THEN STRIP_TAC,
      REPEAT GEN_TAC THEN STRIP_TAC,
      REPEAT GEN_TAC THEN STRIP_TAC,
      REPEAT GEN_TAC THEN STRIP_TAC,
      REPEAT GEN_TAC THEN STRIP_TAC,
      REPEAT GEN_TAC THEN STRIP_TAC] THEN
    MATCH_MP_TAC form_INDUCT THEN
    ASM_REWRITE_TAC [form_DISTINCT, form_INJ, gform, NPAIR_INJ, ARITH_EQ] THEN
    REWRITE_TAC [GTERM_INJ, NUMBER_INJ])
  : ExceptT String IO thm).run
#eval GFORM_INJ

#eval phrase 11
unsafe def GTERM_CASES : thm := keep "GTERM_CASES" fun _ => (do
  let sp ← ExceptT.mk (HolLight.SPEC ([[u:term]]) term_CASES)
  prove ([[((gterm u = NPAIR 0 (number x)) <=> (u = V x)) /\
   ((gterm u = NPAIR 1 0) <=> (u = Z)) /\
   ((gterm u = NPAIR 2 n) <=> (?t. (u = Suc t) /\ (gterm t = n))) /\
   ((gterm u = NPAIR 3 (NPAIR m n)) <=>
          (?s t. (u = s ++ t) /\ (gterm s = m) /\ (gterm t = n))) /\
   ((gterm u = NPAIR 4 (NPAIR m n)) <=>
          (?s t. (u = s ** t) /\ (gterm s = m) /\ (gterm t = n)))]])
   (STRUCT_CASES_TAC sp THEN
    ASM_REWRITE_TAC [gterm, NPAIR_INJ, ARITH_EQ, NUMBER_INJ,
                    term_DISTINCT, term_INJ] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval GTERM_CASES

#eval phrase 12
unsafe def GFORM_CASES : thm := keep "GFORM_CASES" fun _ => (do
  let sp ← ExceptT.mk (HolLight.SPEC ([[r:form]]) form_CASES)
  prove ([[((gform r = NPAIR 0 0) <=> (r = False)) /\
   ((gform r = NPAIR 0 1) <=> (r = True)) /\
   ((gform r = NPAIR 1 (NPAIR m n)) <=>
        (?s t. (r = s === t) /\ (gterm s = m) /\ (gterm t = n))) /\
   ((gform r = NPAIR 2 (NPAIR m n)) <=>
        (?s t. (r = s << t) /\ (gterm s = m) /\ (gterm t = n))) /\
   ((gform r = NPAIR 3 (NPAIR m n)) <=>
        (?s t. (r = s <<= t) /\ (gterm s = m) /\ (gterm t = n))) /\
   ((gform r = NPAIR 4 n) = (?p. (r = Not p) /\ (gform p = n))) /\
   ((gform r = NPAIR 5 (NPAIR m n)) <=>
        (?p q. (r = p && q) /\ (gform p = m) /\ (gform q = n))) /\
   ((gform r = NPAIR 6 (NPAIR m n)) <=>
        (?p q. (r = p || q) /\ (gform p = m) /\ (gform q = n))) /\
   ((gform r = NPAIR 7 (NPAIR m n)) <=>
        (?p q. (r = p --> q) /\ (gform p = m) /\ (gform q = n))) /\
   ((gform r = NPAIR 8 (NPAIR m n)) <=>
        (?p q. (r = p <-> q) /\ (gform p = m) /\ (gform q = n))) /\
   ((gform r = NPAIR 9 (NPAIR (number x) n)) <=>
        (?p. (r = !!x p) /\ (gform p = n))) /\
   ((gform r = NPAIR 10 (NPAIR (number x) n)) <=>
        (?p. (r = ??x p) /\ (gform p = n)))]])
   (STRUCT_CASES_TAC sp THEN
    ASM_REWRITE_TAC [gform, NPAIR_INJ, ARITH_EQ, NUMBER_INJ,
                    form_DISTINCT, form_INJ] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval GFORM_CASES

#eval phrase 13
unsafe def gnumeral : thm := keep "gnumeral" fun _ => new_definition
  [[gnumeral m n = (gterm(numeral m) = n)]]
#eval gnumeral

#eval phrase 14
unsafe def arith_gnumeral1 : thm := keep "arith_gnumeral1" fun _ => new_definition
  [[arith_gnumeral1 a b = formsubst ((3 |-> a) ((4 |-> b) V))
       (??0 (??1
       (V 3 === arith_pair (V 0) (V 1) &&
        V 4 === arith_pair (Suc(V 0)) (arith_pair (numeral 2) (V 1)))))]]
#eval arith_gnumeral1

#eval phrase 15
unsafe def ARITH_GNUMERAL1 : thm := keep "ARITH_GNUMERAL1" fun _ => (do
  prove ([[!v a b. holds v (arith_gnumeral1 a b) <=>
                ?x y. termval v a = NPAIR x y /\
                      termval v b = NPAIR (SUC x) (NPAIR 2 y)]])
   (REWRITE_TAC [arith_gnumeral1, holds, HOLDS_FORMSUBST] THEN
    REWRITE_TAC [termval, ARITH_EQ, o_THM, valmod, ARITH_PAIR, TERMVAL_NUMERAL])
  : ExceptT String IO thm).run
#eval ARITH_GNUMERAL1

#eval phrase 16
unsafe def FV_GNUMERAL1 : thm := keep "FV_GNUMERAL1" fun _ => (do
  prove ([[!s t. FV(arith_gnumeral1 s t) = FVT s UNION FVT t]])
   (REWRITE_TAC [arith_gnumeral1] THEN Definability.FV_TAC [FVT_PAIR, FVT_NUMERAL])
  : ExceptT String IO thm).run
#eval FV_GNUMERAL1

#eval phrase 17
unsafe def «arith_gnumeral1'» : thm := keep "arith_gnumeral1'" fun _ => new_definition
  [[arith_gnumeral1' x y = arith_rtc arith_gnumeral1 x y]]
#eval «arith_gnumeral1'»

#eval phrase 18
unsafe def «ARITH_GNUMERAL1'» : thm := keep "ARITH_GNUMERAL1'" fun _ => (do
  prove ([[!v s t. holds v (arith_gnumeral1' s t) <=>
              RTC (\a b. ?x y. a = NPAIR x y /\
                               b = NPAIR (SUC x) (NPAIR 2 y))
                  (termval v s) (termval v t)]])
   (REWRITE_TAC [«arith_gnumeral1'»] THEN MATCH_MP_TAC ARITH_RTC THEN
    REWRITE_TAC [ARITH_GNUMERAL1])
  : ExceptT String IO thm).run
#eval «ARITH_GNUMERAL1'»

#eval phrase 19
unsafe def «FV_GNUMERAL1'» : thm := keep "FV_GNUMERAL1'" fun _ => (do
  prove ([[!s t. FV(arith_gnumeral1' s t) = FVT s UNION FVT t]])
   (SIMP_TAC [«arith_gnumeral1'», FV_RTC, FV_GNUMERAL1])
  : ExceptT String IO thm).run
#eval «FV_GNUMERAL1'»

#eval phrase 20
unsafe def arith_gnumeral : thm := keep "arith_gnumeral" fun _ => new_definition
  [[arith_gnumeral n p =
        formsubst ((0 |-> n) ((1 |-> p) V))
            (arith_gnumeral1' (arith_pair Z (numeral 3))
                              (arith_pair (V 0) (V 1)))]]
#eval arith_gnumeral

#eval phrase 21
unsafe def ARITH_GNUMERAL : thm := keep "ARITH_GNUMERAL" fun _ => (do
  let inst ← liftExcept (INST
   [([[(gterm o numeral)]], [[fn:num->num]]),
    ([[3]], [[e:num]]),
    ([[\a:num b:num. NPAIR 2 a]], [[f:num->num->num]])] PRIMREC_SIGMA)
  prove ([[!v s t. holds v (arith_gnumeral s t) <=>
            gnumeral (termval v s) (termval v t)]])
   (REWRITE_TAC [arith_gnumeral, holds, HOLDS_FORMSUBST,
                «ARITH_GNUMERAL1'», ARITH_PAIR, TERMVAL_NUMERAL] THEN
    REWRITE_TAC [termval, ARITH_EQ, o_THM, valmod] THEN
    MP_TAC inst THEN
    ANTS_TAC THENL
     [REWRITE_TAC [gterm, numeral, o_THM] THEN REWRITE_TAC [NPAIR, ARITH],
      SIMP_TAC [gnumeral, o_THM]])
  : ExceptT String IO thm).run
#eval ARITH_GNUMERAL

#eval phrase 22
unsafe def FV_GNUMERAL : thm := keep "FV_GNUMERAL" fun _ => (do
  prove ([[!s t. FV(arith_gnumeral s t) =  FVT(s) UNION FVT(t)]])
   (REWRITE_TAC [arith_gnumeral] THEN
    Definability.FV_TAC [«FV_GNUMERAL1'», FVT_PAIR, FVT_NUMERAL])
  : ExceptT String IO thm).run
#eval FV_GNUMERAL

#eval phrase 23
unsafe def qdiag : thm := keep "qdiag" fun _ => new_definition
  [[qdiag x q = qsubst (x,numeral(gform q)) q]]
#eval qdiag

#eval phrase 24
unsafe def arith_qdiag : thm := keep "arith_qdiag" fun _ => new_definition
  [[arith_qdiag x s t =
        formsubst ((1 |-> s) ((2 |-> t) V))
        (?? 3
           (arith_gnumeral (V 1) (V 3) &&
            arith_pair (numeral 10)  (arith_pair (numeral(number x))
                                                 (arith_pair (numeral 5)
              (arith_pair (arith_pair (numeral 1)
       (arith_pair (arith_pair (numeral 0) (numeral(number x))) (V 3)))
                   (V 1)))) ===
        V 2))]]
#eval arith_qdiag

#eval phrase 25
unsafe def QDIAG_FV : thm := keep "QDIAG_FV" fun _ => (do
  prove ([[FV(qdiag x q) = FV(q) DELETE x]])
   (REWRITE_TAC [qdiag, FV_QSUBST, FVT_NUMERAL, UNION_EMPTY])
  : ExceptT String IO thm).run
#eval QDIAG_FV

#eval phrase 26
unsafe def HOLDS_QDIAG : thm := keep "HOLDS_QDIAG" fun _ => (do
  prove ([[!v x q. holds v (qdiag x q) = holds ((x |-> gform q) v) q]])
   (SIMP_TAC [qdiag, HOLDS_QSUBST, FVT_NUMERAL, NOT_IN_EMPTY, TERMVAL_NUMERAL])
  : ExceptT String IO thm).run
#eval HOLDS_QDIAG

#eval phrase 27
unsafe def ARITH_QDIAG : thm := keep "ARITH_QDIAG" fun _ => (do
  prove ([[(termval v s = gform p)
   ==> (holds v (arith_qdiag x s t) <=> (termval v t = gform(qdiag x p)))]])
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [qdiag, qsubst, arith_qdiag, gform, gterm] THEN
    ASM_REWRITE_TAC [HOLDS_FORMSUBST, holds, termval, TERMVAL_NUMERAL,
     gnumeral, ARITH_GNUMERAL, ARITH_PAIR] THEN
    ASM_REWRITE_TAC [o_DEF, valmod, ARITH_EQ, termval] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval ARITH_QDIAG

#eval phrase 28
unsafe def FV_QDIAG : thm := keep "FV_QDIAG" fun _ => (do
  prove ([[!x s t. FV(arith_qdiag x s t) = FVT(s) UNION FVT(t)]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]])
     pure
      (REWRITE_TAC [arith_qdiag, FORMSUBST_FV, FV, FV_GNUMERAL, FVT_PAIR,
                  UNION_EMPTY, FVT_NUMERAL, FVT, TERMSUBST_FVT] THEN
       REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
       REWRITE_TAC [DISJ_ACI, IN_DELETE, IN_UNION, IN_SING] THEN
       REWRITE_TAC [taut1] THEN
       REWRITE_TAC [EXISTS_OR_THM, (← HolLight.GSYM CONJ_ASSOC), UNWIND_THM2, ARITH_EQ] THEN
       REWRITE_TAC [valmod, ARITH_EQ, DISJ_ACI]))
  : ExceptT String IO thm).run
#eval FV_QDIAG

#eval phrase 29
unsafe def diagonalize : thm := keep "diagonalize" fun _ => new_definition
  [[diagonalize x q =
        let y = VARIANT(x INSERT FV(q)) in
        ??y (arith_qdiag x (V x) (V y) && formsubst ((x |-> V y) V) q)]]
#eval diagonalize

#eval phrase 30
unsafe def FV_DIAGONALIZE : thm := keep "FV_DIAGONALIZE" fun _ => (do
  prove ([[!x q. FV(diagonalize x q) = x INSERT (FV q)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [diagonalize] THEN LET_TAC THEN
    REWRITE_TAC [FV, FV_QDIAG, FORMSUBST_FV, EXTENSION, IN_INSERT, IN_DELETE,
                IN_UNION, IN_ELIM_THM, FVT, NOT_IN_EMPTY] THEN
    X_GEN_TAC [[u:num]] THEN
    SUBGOAL_THEN ([[~(y = x) /\ !z. z IN FV(q) ==> ~(y = z)]]) STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [VARIANT_FINITE, FINITE_INSERT, FV_FINITE, IN_INSERT],
      ALL_TAC] THEN
    ASM_CASES_TAC [[u:num = x]] THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC [[u:num = y]] THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [valmod, COND_RAND, FVT, IN_SING, COND_EXPAND] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval FV_DIAGONALIZE

#eval phrase 31
unsafe def ARITH_DIAGONALIZE : thm := keep "ARITH_DIAGONALIZE" fun _ => (do
  prove ([[(v x = gform p)
   ==> !q. holds v (diagonalize x q) <=> holds ((x |-> gform(qdiag x p)) v) q]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [diagonalize] THEN LET_TAC THEN
    REWRITE_TAC [holds] THEN
    SUBGOAL_THEN ([[!a. holds ((y |-> a) v) (arith_qdiag x (V x) (V y)) <=>
                      (termval ((y |-> a) v) (V y) = gform(qdiag x p))]])
     (fun th => REWRITE_TAC [th])
    THENL
     [GEN_TAC THEN MATCH_MP_TAC ARITH_QDIAG THEN REWRITE_TAC [termval, valmod] THEN
      SUBGOAL_THEN ([[~(x:num = y)]]) (fun th => ASM_REWRITE_TAC [th]) THEN
      ASM_MESON_TAC [VARIANT_FINITE, FINITE_INSERT, FV_FINITE, IN_INSERT],
      ALL_TAC] THEN
    REWRITE_TAC [HOLDS_FORMSUBST, termval, VALMOD_BASIC, UNWIND_THM2] THEN
    MATCH_MP_TAC HOLDS_VALUATION THEN
    X_GEN_TAC [[u:num]] THEN DISCH_TAC THEN
    REWRITE_TAC [o_THM, termval, valmod] THEN
    COND_CASES_TAC THEN REWRITE_TAC [termval] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [VARIANT_FINITE, FINITE_INSERT, FV_FINITE, IN_INSERT])
  : ExceptT String IO thm).run
#eval ARITH_DIAGONALIZE

#eval phrase 32
unsafe def fixpoint : thm := keep "fixpoint" fun _ => new_definition
  [[fixpoint x q = qdiag x (diagonalize x q)]]
#eval fixpoint

#eval phrase 33
unsafe def FV_FIXPOINT : thm := keep "FV_FIXPOINT" fun _ => (do
  prove ([[!x p. FV(fixpoint x p) = FV(p) DELETE x]])
   (REWRITE_TAC [fixpoint, FV_QDIAG, QDIAG_FV, FV_DIAGONALIZE,
                FVT_NUMERAL] THEN
    SET_TAC [])
  : ExceptT String IO thm).run
#eval FV_FIXPOINT

#eval phrase 34
unsafe def HOLDS_FIXPOINT : thm := keep "HOLDS_FIXPOINT" fun _ => (do
  prove ([[!x p v. holds v (fixpoint x p) <=>
           holds ((x |-> gform(fixpoint x p)) v) p]])
   (REPEAT GEN_TAC THEN SIMP_TAC [fixpoint, holds, HOLDS_QDIAG] THEN
    SUBGOAL_THEN
     ([[((x |-> gform(diagonalize x p)) v) x = gform (diagonalize x p)]])
    MP_TAC THENL [REWRITE_TAC [VALMOD_BASIC], ALL_TAC] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
      let m ← HolLight.MATCH_MP ARITH_DIAGONALIZE th
      pure (REWRITE_TAC [m])) THEN
    REWRITE_TAC [VALMOD_VALMOD_BASIC])
  : ExceptT String IO thm).run
#eval HOLDS_FIXPOINT

#eval phrase 35
unsafe def HOLDS_IFF_FIXPOINT : thm := keep "HOLDS_IFF_FIXPOINT" fun _ => (do
  prove ([[!x p v. holds v
        (fixpoint x p <-> qsubst (x,numeral(gform(fixpoint x p))) p)]])
   (SIMP_TAC [holds, HOLDS_FIXPOINT, HOLDS_QSUBST, FVT_NUMERAL, NOT_IN_EMPTY,
             TERMVAL_NUMERAL])
  : ExceptT String IO thm).run
#eval HOLDS_IFF_FIXPOINT

#eval phrase 36
unsafe def CARNAP : thm := keep "CARNAP" fun _ => (do
  prove ([[!x q. ?p. (FV(p) = FV(q) DELETE x) /\
             arithtrue (p <-> qsubst (x,numeral(gform p)) q)]])
   (REPEAT GEN_TAC THEN EXISTS_TAC [[fixpoint x q]] THEN
    REWRITE_TAC [arithtrue, HOLDS_IFF_FIXPOINT, FV_FIXPOINT])
  : ExceptT String IO thm).run
#eval CARNAP

#eval phrase 37
unsafe def definable_by : thm := keep "definable_by" fun _ => new_definition
  [[definable_by P s <=> ?p x. P p /\ (!v. holds v p <=> (v(x)) IN s)]]
#eval definable_by

#eval phrase 38
unsafe def definable : thm := keep "definable" fun _ => new_definition
  [[definable s <=> ?p x. !v. holds v p <=> (v(x)) IN s]]
#eval definable

#eval phrase 39
unsafe def TARSKI_THEOREM : thm := keep "TARSKI_THEOREM" fun _ => (do
  let sp ← ExceptT.mk (HolLight.SPECL [ [[x:num]], [[Not p]] ] CARNAP)
  prove ([[~(definable {gform p | arithtrue p})]])
   (REWRITE_TAC [definable, IN_ELIM_THM, NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[p:form]], [[x:num]] ] THEN DISCH_TAC THEN
    MP_TAC sp THEN
    DISCH_THEN (X_CHOOSE_THEN ([[q:form]]) (MP_TAC o CONJUNCT2)) THEN
    SIMP_TAC [arithtrue, holds, HOLDS_QSUBST, FVT_NUMERAL, NOT_IN_EMPTY] THEN
    ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [VALMOD_BASIC, TERMVAL_NUMERAL] THEN
    REWRITE_TAC [arithtrue, GFORM_INJ] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval TARSKI_THEOREM

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.Tarski" do
  replay (
          HolLogicArith.Definability.ensure)
  replay (
          Session.prioritize_num)
  replay (
          number)
  replay (
          denumber)
  replay (
          NUMBER_DENUMBER)
  replay (
          NUMBER_INJ)
  replay (
          NUMBER_SURJ)
  replay (
          gterm)
  replay (
          gform)
  replay (
          GTERM_INJ)
  replay (
          GFORM_INJ)
  replay (
          GTERM_CASES)
  replay (
          GFORM_CASES)
  replay (
          gnumeral)
  replay (
          arith_gnumeral1)
  replay (
          ARITH_GNUMERAL1)
  replay (
          FV_GNUMERAL1)
  replay (
          «arith_gnumeral1'»)
  replay (
          «ARITH_GNUMERAL1'»)
  replay (
          «FV_GNUMERAL1'»)
  replay (
          arith_gnumeral)
  replay (
          ARITH_GNUMERAL)
  replay (
          FV_GNUMERAL)
  replay (
          qdiag)
  replay (
          arith_qdiag)
  replay (
          QDIAG_FV)
  replay (
          HOLDS_QDIAG)
  replay (
          ARITH_QDIAG)
  replay (
          FV_QDIAG)
  replay (
          diagonalize)
  replay (
          FV_DIAGONALIZE)
  replay (
          ARITH_DIAGONALIZE)
  replay (
          fixpoint)
  replay (
          FV_FIXPOINT)
  replay (
          HOLDS_FIXPOINT)
  replay (
          HOLDS_IFF_FIXPOINT)
  replay (
          CARNAP)
  replay (
          definable_by)
  replay (
          definable)
  replay (
          TARSKI_THEOREM)
-- @@ENSURE END

end HolLogicArith.Tarski
