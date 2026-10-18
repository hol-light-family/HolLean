/- File: HolLogicArith/Godel.lean
Translation of HOL Light's Arithmetic/godel.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.ArithProv
open HolCore.Kernel HolCore.Lib HolCore.Basics Session HolLight.Syntax HolLogicArith
open scoped HolLight
-- Names from Arithmetic/fol.ml that godel.ml reuses.
open HolLogicArith.ArithFol (termval holds valmod arithtrue numeral
  TERMVAL_NUMERAL FVT_NUMERAL HOLDS_FORMSUBST FV FORMSUBST_FV FVT TERMSUBST_FVT
  term_INDUCT form_INDUCT VALMOD_BASIC proves_RULES axiom_RULES form_DISTINCT
  form_INJ formsubst termsubst VARIANT_THM HOLDS_VALUATION closed qsubst)
-- Names from Arithmetic/definability.ml that godel.ml reuses.
open HolLogicArith.Definability (arith_pair ARITH_PAIR FVT_PAIR arith_divides
  arith_prime arith_primepow arith_rtc arith_rtcp arith_primrecstep arith_primrec)
-- Names from Arithmetic/tarski.ml that godel.ml reuses.
open HolLogicArith.Tarski (gform gterm definable_by arith_gnumeral1
  arith_gnumeral qdiag arith_qdiag diagonalize fixpoint FV_FIXPOINT HOLDS_FIXPOINT)
-- Names from Arithmetic/arithprov.ml that godel.ml reuses.
open HolLogicArith.ArithProv (arith_term1 arith_term arith_form1 arith_form
  arith_freeterm1 arith_freeterm arith_freeform1 arith_freeform arith_axiom
  arith_prov1 arith_prov FV_PROV ARITH_PROV PROV_THM)

namespace HolLogicArith.Godel

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- `new_inductive_definition` returns a triple (rules,induct,cases). -/
private unsafe def defInductive (tm : term) : thm × thm × thm :=
  match unsafeIO (Session.new_inductive_definition tm) with
  | .ok (.ok t) => t
  | .ok (.error e) => panic! s!"new_inductive_definition: {e}"
  | .error e => panic! s!"new_inductive_definition IO: {e}"

-- Replay Arithmetic/arithprov.ml (the one module godel.ml imports).
#eval HolLogicArith.ArithProv.ensure

#eval phrase 1
unsafe def sigmapi_triple : thm × thm × thm := keep "sigmapi_triple" fun _ =>
  defInductive
    [[(!b n. sigmapi b n False) /\
      (!b n. sigmapi b n True) /\
      (!b n s t. sigmapi b n (s === t)) /\
      (!b n s t. sigmapi b n (s << t)) /\
      (!b n s t. sigmapi b n (s <<= t)) /\
      (!b n p. sigmapi (~b) n p ==> sigmapi b n (Not p)) /\
      (!b n p q. sigmapi b n p /\ sigmapi b n q ==> sigmapi b n (p && q)) /\
      (!b n p q. sigmapi b n p /\ sigmapi b n q ==> sigmapi b n (p || q)) /\
      (!b n p q. sigmapi (~b) n p /\ sigmapi b n q ==> sigmapi b n (p --> q)) /\
      (!b n p q. (!b. sigmapi b n p) /\ (!b. sigmapi b n q)
               ==> sigmapi b n (p <-> q)) /\
      (!n x p. sigmapi T n p /\ ~(n = 0) ==> sigmapi T n (??x p)) /\
      (!n x p. sigmapi F n p /\ ~(n = 0) ==> sigmapi F n (!!x p)) /\
      (!b n x p t. sigmapi b n p /\ ~(x IN FVT t)
               ==> sigmapi b n (??x (V x << t && p))) /\
      (!b n x p t. sigmapi b n p /\ ~(x IN FVT t)
               ==> sigmapi b n (??x (V x <<= t && p))) /\
      (!b n x p t. sigmapi b n p /\ ~(x IN FVT t)
               ==> sigmapi b n (!!x (V x << t --> p))) /\
      (!b n x p t. sigmapi b n p /\ ~(x IN FVT t)
               ==> sigmapi b n (!!x (V x <<= t --> p))) /\
      (!b c n p. sigmapi b n p ==> sigmapi c (n + 1) p)]]
unsafe def sigmapi_RULES : thm := sigmapi_triple.1
unsafe def sigmapi_INDUCT : thm := sigmapi_triple.2.1
unsafe def sigmapi_CASES : thm := sigmapi_triple.2.2
#eval do IO.println sigmapi_RULES; IO.println sigmapi_INDUCT; IO.println sigmapi_CASES

#eval phrase 2
unsafe def SIGMA : thm := keep "SIGMA" fun _ => new_definition [[SIGMA = sigmapi T]]
#eval SIGMA

#eval phrase 3
unsafe def PI : thm := keep "PI" fun _ => new_definition [[PI = sigmapi F]]
#eval PI

#eval phrase 4
unsafe def DELTA : thm := keep "DELTA" fun _ => new_definition
  [[DELTA n p <=> SIGMA n p /\ PI n p]]
#eval DELTA

#eval phrase 5
unsafe def SIGMAPI_PROP : thm := keep "SIGMAPI_PROP" fun _ => (do
  prove ([[(!n b. sigmapi b n False <=> T) /\
   (!n b. sigmapi b n True <=> T) /\
   (!n b s t. sigmapi b n (s === t) <=> T) /\
   (!n b s t. sigmapi b n (s << t) <=> T) /\
   (!n b s t. sigmapi b n (s <<= t) <=> T) /\
   (!n b p. sigmapi b n (Not p) <=> sigmapi (~b) n p) /\
   (!n b p q. sigmapi b n (p && q) <=> sigmapi b n p /\ sigmapi b n q) /\
   (!n b p q. sigmapi b n (p || q) <=> sigmapi b n p /\ sigmapi b n q) /\
   (!n b p q. sigmapi b n (p --> q) <=> sigmapi (~b) n p /\ sigmapi b n q) /\
   (!n b p q. sigmapi b n (p <-> q) <=> (sigmapi b n p /\ sigmapi (~b) n p) /\
                                        (sigmapi b n q /\ sigmapi (~b) n q))]])
   (HolLight.tactic_of do
     let ar1 ← ExceptT.mk (ARITH_RULE [[~(0 = n + 1)]])
     let ar2 ← ExceptT.mk (ARITH_RULE [[(SUC m = n + 1) <=> (n = m)]])
     let taut1 ← ExceptT.mk (TAUT [[(a \/ b <=> a) <=> (b ==> a)]])
     pure
      (REWRITE_TAC [sigmapi_RULES] THEN
       GEN_REWRITE_TAC HolLight.DEPTH_CONV [AND_FORALL_THM] THEN
       INDUCT_TAC THEN REWRITE_TAC [NOT_SUC, SUC_SUB1] THEN
       REPEAT STRIP_TAC THEN GEN_REWRITE_TAC HolLight.LAND_CONV [sigmapi_CASES] THEN
       REWRITE_TAC [form_DISTINCT, form_INJ] THEN
       REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC), RIGHT_EXISTS_AND_THM, UNWIND_THM1,
                   FORALL_BOOL_THM] THEN
       REWRITE_TAC [ar1] THEN
       REWRITE_TAC [ar2, UNWIND_THM2] THEN
       ASM_REWRITE_TAC [] THEN
       BOOL_CASES_TAC [[b:bool]] THEN ASM_REWRITE_TAC [ADD1] THEN
       REWRITE_TAC [CONJ_ACI] THEN
       REWRITE_TAC [taut1] THEN
       MESON_TAC [sigmapi_RULES]))
  : ExceptT String IO thm).run
#eval SIGMAPI_PROP

#eval phrase 6
unsafe def SIGMAPI_MONO_LEMMA : thm := keep "SIGMAPI_MONO_LEMMA" fun _ => (do
  prove ([[(!b n p. sigmapi b n p ==> sigmapi b (n + 1) p) /\
   (!b n p. ~(n = 0) /\ sigmapi b (n - 1) p ==> sigmapi b n p) /\
   (!b n p. ~(n = 0) /\ sigmapi (~b) (n - 1) p ==> sigmapi b n p)]])
   (HolLight.tactic_of do
     let ar1 ← ExceptT.mk (ARITH_RULE [[~(n = 0) ==> (n = (n - 1) + 1)]])
     pure
      (CONJ_TAC THENL
        [REPEAT STRIP_TAC,
         REPEAT STRIP_TAC THEN
         FIRST_X_ASSUM (SUBST1_TAC oTIO HolLight.MATCH_MP ar1)] THEN
       POP_ASSUM MP_TAC THEN ASM_MESON_TAC [sigmapi_RULES]))
  : ExceptT String IO thm).run
#eval SIGMAPI_MONO_LEMMA

#eval phrase 7
unsafe def SIGMAPI_REV_EXISTS : thm := keep "SIGMAPI_REV_EXISTS" fun _ => (do
  prove ([[!n b x p. sigmapi b n (??x p) ==> sigmapi b n p]])
   (HolLight.tactic_of do
     let ar1 ← ExceptT.mk (ARITH_RULE [[n < n + 1]])
     pure
      (MATCH_MP_TAC num_WF THEN GEN_TAC THEN DISCH_TAC THEN
       REPEAT GEN_TAC THEN GEN_REWRITE_TAC HolLight.LAND_CONV [sigmapi_CASES] THEN
       REWRITE_TAC [form_DISTINCT, form_INJ] THEN
       REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC), RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
       REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [SIGMAPI_PROP] THEN
       ASM_MESON_TAC [ar1, sigmapi_RULES]))
  : ExceptT String IO thm).run
#eval SIGMAPI_REV_EXISTS

#eval phrase 8
unsafe def SIGMAPI_REV_FORALL : thm := keep "SIGMAPI_REV_FORALL" fun _ => (do
  prove ([[!n b x p. sigmapi b n (!!x p) ==> sigmapi b n p]])
   (HolLight.tactic_of do
     let ar1 ← ExceptT.mk (ARITH_RULE [[n < n + 1]])
     pure
      (MATCH_MP_TAC num_WF THEN GEN_TAC THEN DISCH_TAC THEN
       REPEAT GEN_TAC THEN GEN_REWRITE_TAC HolLight.LAND_CONV [sigmapi_CASES] THEN
       REWRITE_TAC [form_DISTINCT, form_INJ] THEN
       REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC), RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
       REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [SIGMAPI_PROP] THEN
       ASM_MESON_TAC [ar1, sigmapi_RULES]))
  : ExceptT String IO thm).run
#eval SIGMAPI_REV_FORALL

#eval phrase 9
unsafe def SIGMAPI_CLAUSES_CODE : thm := keep "SIGMAPI_CLAUSES_CODE" fun _ => (do
  prove ([[(!n b. sigmapi b n False <=> T) /\
   (!n b. sigmapi b n True <=> T) /\
   (!n b s t. sigmapi b n (s === t) <=> T) /\
   (!n b s t. sigmapi b n (s << t) <=> T) /\
   (!n b s t. sigmapi b n (s <<= t) <=> T) /\
   (!n b p. sigmapi b n (Not p) <=> sigmapi (~b) n p) /\
   (!n b p q. sigmapi b n (p && q) <=> sigmapi b n p /\ sigmapi b n q) /\
   (!n b p q. sigmapi b n (p || q) <=> sigmapi b n p /\ sigmapi b n q) /\
   (!n b p q. sigmapi b n (p --> q) <=> sigmapi (~b) n p /\ sigmapi b n q) /\
   (!n b p q. sigmapi b n (p <-> q) <=> (sigmapi b n p /\ sigmapi (~b) n p) /\
                                        (sigmapi b n q /\ sigmapi (~b) n q)) /\
   (!n b x p. sigmapi b n (??x p) <=>
                if b /\ ~(n = 0) \/
                   ?q t. (p = (V x << t && q) \/ p = (V x <<= t && q)) /\
                         ~(x IN FVT t)
                then sigmapi b n p
                else ~(n = 0) /\ sigmapi (~b) (n - 1) (??x p)) /\
   (!n b x p. sigmapi b n (!!x p) <=>
                if ~b /\ ~(n = 0) \/
                   ?q t. (p = (V x << t --> q) \/ p = (V x <<= t --> q)) /\
                         ~(x IN FVT t)
                then sigmapi b n p
                else ~(n = 0) /\ sigmapi (~b) (n - 1) (!!x p))]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[a \/ b \/ c \/ d <=> (b \/ c) \/ (a \/ d)]])
     let taut2 ← ExceptT.mk (TAUT
      [[(if b /\ c \/ d then e else c /\ f) <=>
        d /\ e \/ c /\ ~d /\ (if b then e else f)]])
     let taut3 ← ExceptT.mk (TAUT [[(a <=> a') /\ (~a' ==> (b <=> b'))
                     ==> (a \/ b <=> a' \/ b')]])
     let ar1 ← ExceptT.mk (ARITH_RULE [[~(0 = n + 1)]])
     let ar2 ← ExceptT.mk (ARITH_RULE [[~(n = 0) ==> (n = m + 1 <=> m = n - 1)]])
     let ar3 ← ExceptT.mk (ARITH_RULE [[~(n = 0) ==> 1 <= n]])
     let taut4 ← ExceptT.mk (TAUT [[(a \/ b <=> a) <=> (b ==> a)]])
     let last_rule ← liftExcept (HolCore.Lib.last (Session.CONJUNCTS sigmapi_RULES))
     pure
      (REWRITE_TAC [SIGMAPI_PROP] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
       GEN_REWRITE_TAC HolLight.LAND_CONV [sigmapi_CASES] THEN
       REWRITE_TAC [form_DISTINCT, form_INJ] THEN
       REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC), RIGHT_EXISTS_AND_THM, UNWIND_THM1] THEN
       ONCE_REWRITE_TAC [taut1] THEN
       REWRITE_TAC [CONJ_ASSOC, OR_EXISTS_THM, (← HolLight.GSYM RIGHT_OR_DISTRIB)] THEN
       REWRITE_TAC [taut2] THEN
       MATCH_MP_TAC taut3 THEN
       (CONJ_TAC THENL
         [REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
          REPEAT (AP_TERM_TAC THEN ABS_TAC) THEN
          EQ_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
          REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [SIGMAPI_PROP] THEN
          SIMP_TAC [],
          ALL_TAC]) THEN
       (ASM_CASES_TAC [[n = 0]] THEN ASM_REWRITE_TAC [ar1]) THEN
       ASM_SIMP_TAC [ar2] THEN
       REWRITE_TAC [UNWIND_THM2] THEN
       HolCore.Lib.W (fun g => HolLight.tactic_of do
         let w := HolLight.snd g
         let ex ← liftExcept (HolCore.Basics.find_term HolCore.Basics.is_exists w)
         pure (ASM_CASES_TAC ex)) THEN
       ASM_REWRITE_TAC [CONTRAPOS_THM] THENL
        [DISCH_THEN (DISJ_CASES_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN
         FIRST_X_ASSUM (CHOOSE_THEN (MP_TAC oTIO HolLight.MATCH_MP SIGMAPI_REV_EXISTS)) THEN
         DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP last_rule) THEN
         ASM_SIMP_TAC [SUB_ADD, ar3],
         ASM_CASES_TAC [[b:bool]] THEN
         ASM_REWRITE_TAC [taut4] THENL
          [DISCH_THEN (CHOOSE_THEN (MP_TAC oTIO HolLight.MATCH_MP SIGMAPI_REV_EXISTS)) THEN
           DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP last_rule) THEN
           ASM_SIMP_TAC [SUB_ADD, ar3],
           REWRITE_TAC [EXISTS_BOOL_THM] THEN
           REWRITE_TAC [taut4] THEN
           ONCE_REWRITE_TAC [sigmapi_CASES] THEN
           REWRITE_TAC [form_DISTINCT, form_INJ] THEN ASM_MESON_TAC []],
         DISCH_THEN (DISJ_CASES_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN
         FIRST_X_ASSUM (CHOOSE_THEN (MP_TAC oTIO HolLight.MATCH_MP SIGMAPI_REV_FORALL)) THEN
         DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP last_rule) THEN
         ASM_SIMP_TAC [SUB_ADD, ar3],
         ASM_CASES_TAC [[b:bool]] THEN
         ASM_REWRITE_TAC [taut4] THENL
          [REWRITE_TAC [EXISTS_BOOL_THM] THEN
           REWRITE_TAC [taut4] THEN
           ONCE_REWRITE_TAC [sigmapi_CASES] THEN
           REWRITE_TAC [form_DISTINCT, form_INJ] THEN ASM_MESON_TAC [],
           DISCH_THEN (CHOOSE_THEN (MP_TAC oTIO HolLight.MATCH_MP SIGMAPI_REV_FORALL)) THEN
           DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP last_rule) THEN
           ASM_SIMP_TAC [SUB_ADD, ar3]]]))
  : ExceptT String IO thm).run
#eval SIGMAPI_CLAUSES_CODE

#eval phrase 10
unsafe def SIGMAPI_CLAUSES : thm := keep "SIGMAPI_CLAUSES" fun _ => (do
  prove ([[(!n b. sigmapi b n False <=> T) /\
   (!n b. sigmapi b n True <=> T) /\
   (!n b s t. sigmapi b n (s === t) <=> T) /\
   (!n b s t. sigmapi b n (s << t) <=> T) /\
   (!n b s t. sigmapi b n (s <<= t) <=> T) /\
   (!n b p. sigmapi b n (Not p) <=> sigmapi (~b) n p) /\
   (!n b p q. sigmapi b n (p && q) <=> sigmapi b n p /\ sigmapi b n q) /\
   (!n b p q. sigmapi b n (p || q) <=> sigmapi b n p /\ sigmapi b n q) /\
   (!n b p q. sigmapi b n (p --> q) <=> sigmapi (~b) n p /\ sigmapi b n q) /\
   (!n b p q. sigmapi b n (p <-> q) <=> (sigmapi b n p /\ sigmapi (~b) n p) /\
                                        (sigmapi b n q /\ sigmapi (~b) n q)) /\
   (!n b x p. sigmapi b n (??x p) <=>
                if b /\ ~(n = 0) \/
                   ?q t. (p = (V x << t && q) \/ p = (V x <<= t && q)) /\
                         ~(x IN FVT t)
                then sigmapi b n p
                else 2 <= n /\ sigmapi (~b) (n - 1) p) /\
   (!n b x p. sigmapi b n (!!x p) <=>
                if ~b /\ ~(n = 0) \/
                   ?q t. (p = (V x << t --> q) \/ p = (V x <<= t --> q)) /\
                         ~(x IN FVT t)
                then sigmapi b n p
                else 2 <= n /\ sigmapi (~b) (n - 1) p)]])
   (HolLight.tactic_of do
     let ar1 ← ExceptT.mk (ARITH_RULE [[~(n - 1 = 0) <=> 2 <= n]])
     pure
      (REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
       GEN_REWRITE_TAC HolLight.LAND_CONV [SIGMAPI_CLAUSES_CODE] THEN
       REWRITE_TAC [] THEN
       ASM_CASES_TAC [[n = 0]] THEN ASM_REWRITE_TAC [ARITH] THEN
       BOOL_CASES_TAC [[b:bool]] THEN ASM_REWRITE_TAC [] THEN
       COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
       GEN_REWRITE_TAC HolLight.LAND_CONV [SIGMAPI_CLAUSES_CODE] THEN
       ASM_REWRITE_TAC [ar1] THEN
       MESON_TAC []))
  : ExceptT String IO thm).run
#eval SIGMAPI_CLAUSES

#eval phrase 11
unsafe def SIGMAPI_FORMSUBST : thm := keep "SIGMAPI_FORMSUBST" fun _ => (do
  prove ([[!p v n b. sigmapi b n p ==> sigmapi b n (formsubst v p)]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[(a ==> b /\ c) ==> (a ==> b) /\ (a ==> c)]])
     let taut2 ← ExceptT.mk (TAUT
      [[((if p \/ q then x else y) ==> (if p \/ q' then x' else y')) <=>
        (p /\ x ==> x') /\
        (~p ==> (if q then x else y) ==> (if q' then x' else y'))]])
     let taut3 ← ExceptT.mk (TAUT
      [[(p ==> p') /\ (x ==> x') /\ (y ==> y') /\ (y ==> x)
        ==> (if p then x else y) ==> (if p' then x' else y')]])
     let ar1 ← ExceptT.mk (ARITH_RULE [[2 <= n ==> ~(n = 0)]])
     let taut4 ← ExceptT.mk (TAUT [[((a /\ b) /\ c) /\ d <=> b /\ c /\ a /\ d]])
     let taut5 ← ExceptT.mk (TAUT [[(a \/ b \/ c) /\ ~a <=> ~a /\ b \/ ~a /\ c]])
     pure
      (MATCH_MP_TAC form_INDUCT THEN
       REWRITE_TAC [SIGMAPI_CLAUSES, formsubst] THEN SIMP_TAC [] THEN
       REWRITE_TAC [AND_FORALL_THM] THEN MAP_EVERY X_GEN_TAC [ [[x:num]], [[p:form]] ] THEN
       MATCH_MP_TAC taut1 THEN
       DISCH_TAC THEN REWRITE_TAC [AND_FORALL_THM] THEN
       MAP_EVERY X_GEN_TAC [ [[i:num->term]], [[n:num]], [[b:bool]] ] THEN
       REWRITE_TAC [FV] THEN LET_TAC THEN
       CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN
       REWRITE_TAC [SIGMAPI_CLAUSES] THEN
       ONCE_REWRITE_TAC [taut2] THEN
       ASM_SIMP_TAC [] THEN REWRITE_TAC [DE_MORGAN_THM] THEN
       CONJ_TAC THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN MATCH_MP_TAC taut3 THEN
       ASM_SIMP_TAC [SIGMAPI_MONO_LEMMA, ar1] THEN
       STRIP_TAC THEN ASM_REWRITE_TAC [formsubst, form_INJ, termsubst] THEN
       REWRITE_TAC [form_DISTINCT] THEN
       ONCE_REWRITE_TAC [taut4] THEN
       REWRITE_TAC [UNWIND_THM1, termsubst, VALMOD_BASIC] THEN
       REWRITE_TAC [TERMSUBST_FVT, IN_ELIM_THM, NOT_EXISTS_THM] THEN
       X_GEN_TAC [[y:num]] THEN REWRITE_TAC [valmod] THEN
       (COND_CASES_TAC THENL [ASM_MESON_TAC [], ALL_TAC]) THEN
       DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
       FIRST_X_ASSUM (fun th => HolLight.tactic_of do
         let sth ← liftExcept (HolCore.Equal.SYM th)
         pure (GEN_REWRITE_TAC (HolCore.Lib.funpow 2 HolLight.LAND_CONV) [sth])) THEN
       FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC [FV, FVT] THEN
       REWRITE_TAC [IN_DELETE, IN_UNION, IN_SING, (← HolLight.GSYM DISJ_ASSOC)] THEN
       REWRITE_TAC [taut5] THEN
       (COND_CASES_TAC THENL [ALL_TAC, ASM_MESON_TAC []]) THEN
       HolCore.Lib.W (fun g => HolLight.tactic_of do
         let w := HolLight.snd g
         let t ← liftExcept (do HolCore.Equal.lhand (← rand w))
         let r2 ← liftExcept (do rand (← rand t))
         let vth ← ExceptT.mk (HolLight.SPEC r2 VARIANT_THM)
         pure (MP_TAC vth THEN SPEC_TAC (t, [[u:num]]))) THEN
       REWRITE_TAC [CONTRAPOS_THM, FORMSUBST_FV, IN_ELIM_THM, FV] THEN
       GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC [[y:num]] THEN
       ASM_REWRITE_TAC [valmod, IN_UNION]))
  : ExceptT String IO thm).run
#eval SIGMAPI_FORMSUBST

#eval phrase 12
unsafe def SIGMAPI_TAC : List thm → HolCore.Tactics.tactic :=
  keep "SIGMAPI_TAC" fun _ => fun ths =>
  HolLight.tactic_of do
    let gca ← HolLight.GSYM CONJ_ASSOC
    let ger ← HolLight.GSYM EXISTS_REFL
    let ths' := ths ++
     [SIGMAPI_CLAUSES, form_DISTINCT,
      form_INJ, gca, UNWIND_THM1, ger,
      FVT, IN_SING, ARITH_EQ]
    pure
     (REPEAT STRIP_TAC THEN
      REWRITE_TAC ths THEN
      TRY (MATCH_MP_TAC SIGMAPI_FORMSUBST) THEN
      REWRITE_TAC ths' THEN ASM_SIMP_TAC ths')
#eval IO.println "<fun>"

#eval phrase 13
unsafe def SIGMAPI_DIVIDES : thm := keep "SIGMAPI_DIVIDES" fun _ => (do
  prove ([[!n s t. sigmapi b n (arith_divides s t)]])
   (SIGMAPI_TAC [arith_divides])
  : ExceptT String IO thm).run
#eval SIGMAPI_DIVIDES

#eval phrase 14
unsafe def SIGMAPI_PRIME : thm := keep "SIGMAPI_PRIME" fun _ => (do
  prove ([[!n t. sigmapi b n (arith_prime t)]])
   (SIGMAPI_TAC [arith_prime, SIGMAPI_DIVIDES])
  : ExceptT String IO thm).run
#eval SIGMAPI_PRIME

#eval phrase 15
unsafe def SIGMAPI_PRIMEPOW : thm := keep "SIGMAPI_PRIMEPOW" fun _ => (do
  prove ([[!n s t. sigmapi b n (arith_primepow s t)]])
   (SIGMAPI_TAC [arith_primepow, SIGMAPI_DIVIDES, SIGMAPI_PRIME])
  : ExceptT String IO thm).run
#eval SIGMAPI_PRIMEPOW

#eval phrase 16
unsafe def SIGMAPI_RTC : thm := keep "SIGMAPI_RTC" fun _ => (do
  prove ([[(!s t. sigmapi T 1 (R s t))
   ==> !s t. sigmapi T 1 (arith_rtc R s t)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [arith_rtc] THEN
    MATCH_MP_TAC SIGMAPI_FORMSUBST THEN
    REWRITE_TAC [SIGMAPI_CLAUSES, form_INJ, (← HolLight.GSYM CONJ_ASSOC), UNWIND_THM1,
                (← HolLight.GSYM EXISTS_REFL), FVT, IN_SING, ARITH_EQ, SIGMAPI_DIVIDES,
                SIGMAPI_PRIME, SIGMAPI_PRIMEPOW, form_DISTINCT] THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval SIGMAPI_RTC

#eval phrase 17
unsafe def SIGMAPI_RTCP : thm := keep "SIGMAPI_RTCP" fun _ => (do
  prove ([[(!s t u. sigmapi T 1 (R s t u))
   ==> !s t u. sigmapi T 1 (arith_rtcp R s t u)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [arith_rtcp] THEN
    MATCH_MP_TAC SIGMAPI_FORMSUBST THEN
    REWRITE_TAC [SIGMAPI_CLAUSES, form_INJ, (← HolLight.GSYM CONJ_ASSOC), UNWIND_THM1,
                (← HolLight.GSYM EXISTS_REFL), FVT, IN_SING, ARITH_EQ, SIGMAPI_DIVIDES,
                SIGMAPI_PRIME, SIGMAPI_PRIMEPOW, form_DISTINCT] THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval SIGMAPI_RTCP

#eval phrase 18
unsafe def SIGMAPI_TERM1 : thm := keep "SIGMAPI_TERM1" fun _ => (do
  prove ([[!s t. sigmapi T 1 (arith_term1 s t)]])
   (SIGMAPI_TAC [arith_term1])
  : ExceptT String IO thm).run
#eval SIGMAPI_TERM1

#eval phrase 19
unsafe def SIGMAPI_TERM : thm := keep "SIGMAPI_TERM" fun _ => (do
  prove ([[!t. sigmapi T 1 (arith_term t)]])
   (SIGMAPI_TAC [arith_term, SIGMAPI_RTC, SIGMAPI_TERM1])
  : ExceptT String IO thm).run
#eval SIGMAPI_TERM

#eval phrase 20
unsafe def SIGMAPI_FORM1 : thm := keep "SIGMAPI_FORM1" fun _ => (do
  prove ([[!s t. sigmapi T 1 (arith_form1 s t)]])
   (SIGMAPI_TAC [arith_form1, SIGMAPI_TERM])
  : ExceptT String IO thm).run
#eval SIGMAPI_FORM1

#eval phrase 21
unsafe def SIGMAPI_FORM : thm := keep "SIGMAPI_FORM" fun _ => (do
  prove ([[!t. sigmapi T 1 (arith_form t)]])
   (SIGMAPI_TAC [arith_form, SIGMAPI_RTC, SIGMAPI_FORM1])
  : ExceptT String IO thm).run
#eval SIGMAPI_FORM

#eval phrase 22
unsafe def SIGMAPI_FREETERM1 : thm := keep "SIGMAPI_FREETERM1" fun _ => (do
  prove ([[!s t u. sigmapi T 1 (arith_freeterm1 s t u)]])
   (SIGMAPI_TAC [arith_freeterm1])
  : ExceptT String IO thm).run
#eval SIGMAPI_FREETERM1

#eval phrase 23
unsafe def SIGMAPI_FREETERM : thm := keep "SIGMAPI_FREETERM" fun _ => (do
  prove ([[!s t. sigmapi T 1 (arith_freeterm s t)]])
   (SIGMAPI_TAC [arith_freeterm, SIGMAPI_FREETERM1, SIGMAPI_RTCP])
  : ExceptT String IO thm).run
#eval SIGMAPI_FREETERM

#eval phrase 24
unsafe def SIGMAPI_FREEFORM1 : thm := keep "SIGMAPI_FREEFORM1" fun _ => (do
  prove ([[!s t u. sigmapi T 1 (arith_freeform1 s t u)]])
   (SIGMAPI_TAC [arith_freeform1, SIGMAPI_FREETERM, SIGMAPI_FORM])
  : ExceptT String IO thm).run
#eval SIGMAPI_FREEFORM1

#eval phrase 25
unsafe def SIGMAPI_FREEFORM : thm := keep "SIGMAPI_FREEFORM" fun _ => (do
  prove ([[!s t. sigmapi T 1 (arith_freeform s t)]])
   (SIGMAPI_TAC [arith_freeform, SIGMAPI_FREEFORM1, SIGMAPI_RTCP])
  : ExceptT String IO thm).run
#eval SIGMAPI_FREEFORM

#eval phrase 26
unsafe def SIGMAPI_AXIOM : thm := keep "SIGMAPI_AXIOM" fun _ => (do
  prove ([[!t. sigmapi T 1 (arith_axiom t)]])
   (SIGMAPI_TAC [arith_axiom, SIGMAPI_FREEFORM, SIGMAPI_FREETERM, SIGMAPI_FORM,
               SIGMAPI_TERM])
  : ExceptT String IO thm).run
#eval SIGMAPI_AXIOM

#eval phrase 27
unsafe def SIGMAPI_PROV1 : thm := keep "SIGMAPI_PROV1" fun _ => (do
  prove ([[!A. (!t. sigmapi T 1 (A t)) ==> !s t. sigmapi T 1 (arith_prov1 A s t)]])
   (SIGMAPI_TAC [arith_prov1, SIGMAPI_AXIOM])
  : ExceptT String IO thm).run
#eval SIGMAPI_PROV1

#eval phrase 28
unsafe def SIGMAPI_PROV : thm := keep "SIGMAPI_PROV" fun _ => (do
  prove ([[(!t. sigmapi T 1 (A t)) ==> !t. sigmapi T 1 (arith_prov A t)]])
   (SIGMAPI_TAC [arith_prov, SIGMAPI_PROV1, SIGMAPI_RTC])
  : ExceptT String IO thm).run
#eval SIGMAPI_PROV

#eval phrase 29
unsafe def SIGMAPI_PRIMRECSTEP : thm := keep "SIGMAPI_PRIMRECSTEP" fun _ => (do
  prove ([[(!s t u. sigmapi T 1 (R s t u))
   ==> !s t. sigmapi T 1 (arith_primrecstep R s t)]])
   (SIGMAPI_TAC [arith_primrecstep])
  : ExceptT String IO thm).run
#eval SIGMAPI_PRIMRECSTEP

#eval phrase 30
unsafe def SIGMAPI_PRIMREC : thm := keep "SIGMAPI_PRIMREC" fun _ => (do
  prove ([[(!s t u. sigmapi T 1 (R s t u))
   ==> !s t. sigmapi T 1 (arith_primrec R c s t)]])
   (SIGMAPI_TAC [arith_primrec, SIGMAPI_PRIMRECSTEP, SIGMAPI_RTC])
  : ExceptT String IO thm).run
#eval SIGMAPI_PRIMREC

#eval phrase 31
unsafe def SIGMAPI_GNUMERAL1 : thm := keep "SIGMAPI_GNUMERAL1" fun _ => (do
  prove ([[!s t. sigmapi T 1 (arith_gnumeral1 s t)]])
   (SIGMAPI_TAC [arith_gnumeral1])
  : ExceptT String IO thm).run
#eval SIGMAPI_GNUMERAL1

#eval phrase 32
unsafe def SIGMAPI_GNUMERAL : thm := keep "SIGMAPI_GNUMERAL" fun _ => (do
  prove ([[!s t. sigmapi T 1 (arith_gnumeral s t)]])
   (SIGMAPI_TAC [arith_gnumeral, Tarski.«arith_gnumeral1'»,
               SIGMAPI_GNUMERAL1, SIGMAPI_RTC])
  : ExceptT String IO thm).run
#eval SIGMAPI_GNUMERAL

#eval phrase 33
unsafe def SIGMAPI_QSUBST : thm := keep "SIGMAPI_QSUBST" fun _ => (do
  prove ([[!x n p.  sigmapi T 1 p ==> sigmapi T 1 (qsubst(x,n) p)]])
   (SIGMAPI_TAC [qsubst])
  : ExceptT String IO thm).run
#eval SIGMAPI_QSUBST

#eval phrase 34
unsafe def SIGMAPI_QDIAG : thm := keep "SIGMAPI_QDIAG" fun _ => (do
  prove ([[!x s t. sigmapi T 1 (arith_qdiag x s t)]])
   (SIGMAPI_TAC [arith_qdiag, SIGMAPI_GNUMERAL])
  : ExceptT String IO thm).run
#eval SIGMAPI_QDIAG

#eval phrase 35
unsafe def SIGMAPI_DIAGONALIZE : thm := keep "SIGMAPI_DIAGONALIZE" fun _ => (do
  prove ([[!x p. sigmapi T 1 p ==> sigmapi T 1 (diagonalize x p)]])
   (SIGMAPI_TAC [diagonalize, SIGMAPI_QDIAG,
         SIGMAPI_FORMSUBST, LET_DEF, LET_END_DEF])
  : ExceptT String IO thm).run
#eval SIGMAPI_DIAGONALIZE

#eval phrase 36
unsafe def SIGMAPI_FIXPOINT : thm := keep "SIGMAPI_FIXPOINT" fun _ => (do
  prove ([[!x p. sigmapi T 1 p ==> sigmapi T 1 (fixpoint x p)]])
   (SIGMAPI_TAC [fixpoint, qdiag, SIGMAPI_QSUBST, SIGMAPI_DIAGONALIZE])
  : ExceptT String IO thm).run
#eval SIGMAPI_FIXPOINT

#eval phrase 37
unsafe def hsentence : thm := keep "hsentence" fun _ => new_definition
  [[hsentence Arep =
    fixpoint 0 (arith_prov Arep (arith_pair (numeral 4) (V 0)))]]
#eval hsentence

#eval phrase 38
unsafe def gsentence : thm := keep "gsentence" fun _ => new_definition
  [[gsentence Arep = Not(hsentence Arep)]]
#eval gsentence

#eval phrase 39
unsafe def FV_HSENTENCE : thm := keep "FV_HSENTENCE" fun _ => (do
  prove ([[!Arep. (!t. FV(Arep t) = FVT t) ==> (FV(hsentence Arep) = {})]])
   (SIMP_TAC [hsentence, FV_FIXPOINT, FV_PROV] THEN
    REWRITE_TAC [FVT_PAIR, FVT_NUMERAL, FVT, UNION_EMPTY, DELETE_INSERT,
                EMPTY_DELETE])
  : ExceptT String IO thm).run
#eval FV_HSENTENCE

#eval phrase 40
unsafe def FV_GSENTENCE : thm := keep "FV_GSENTENCE" fun _ => (do
  prove ([[!Arep. (!t. FV(Arep t) = FVT t) ==> (FV(gsentence Arep) = {})]])
   (SIMP_TAC [gsentence, FV_HSENTENCE, FV])
  : ExceptT String IO thm).run
#eval FV_GSENTENCE

#eval phrase 41
unsafe def SIGMAPI_HSENTENCE : thm := keep "SIGMAPI_HSENTENCE" fun _ => (do
  prove ([[!Arep. (!t. sigmapi T 1 (Arep t)) ==> sigmapi T 1 (hsentence Arep)]])
   (SIGMAPI_TAC [hsentence, SIGMAPI_FIXPOINT, SIGMAPI_PROV])
  : ExceptT String IO thm).run
#eval SIGMAPI_HSENTENCE

#eval phrase 42
unsafe def SIGMAPI_GSENTENCE : thm := keep "SIGMAPI_GSENTENCE" fun _ => (do
  prove ([[!Arep. (!t. sigmapi T 1 (Arep t)) ==> sigmapi F 1 (gsentence Arep)]])
   (SIGMAPI_TAC [gsentence, SIGMAPI_HSENTENCE])
  : ExceptT String IO thm).run
#eval SIGMAPI_GSENTENCE

#eval phrase 43
unsafe def HSENTENCE_FIX_STRONG : thm := keep "HSENTENCE_FIX_STRONG" fun _ => (do
  prove ([[!A Arep.
        (!v t. holds v (Arep t) <=> (termval v t) IN IMAGE gform A)
        ==> !v. holds v (hsentence Arep) <=> A |-- Not(hsentence Arep)]])
   (REWRITE_TAC [hsentence, arithtrue, HOLDS_FIXPOINT] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP ARITH_PROV) THEN
    REWRITE_TAC [IN] THEN CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (Session.ETA_CONV t))) THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [ARITH_PAIR, TERMVAL_NUMERAL] THEN
    REWRITE_TAC [termval, valmod, (← HolLight.GSYM gform)] THEN REWRITE_TAC [PROV_THM])
  : ExceptT String IO thm).run
#eval HSENTENCE_FIX_STRONG

#eval phrase 44
unsafe def HSENTENCE_FIX : thm := keep "HSENTENCE_FIX" fun _ => (do
  prove ([[!A Arep.
        (!v t. holds v (Arep t) <=> (termval v t) IN IMAGE gform A)
        ==> (arithtrue(hsentence Arep) <=> A |-- Not(hsentence Arep))]])
   (REWRITE_TAC [arithtrue] THEN MESON_TAC [HSENTENCE_FIX_STRONG])
  : ExceptT String IO thm).run
#eval HSENTENCE_FIX

#eval phrase 45
unsafe def GSENTENCE_FIX : thm := keep "GSENTENCE_FIX" fun _ => (do
  prove ([[!A Arep.
        (!v t. holds v (Arep t) <=> (termval v t) IN IMAGE gform A)
        ==> (arithtrue(gsentence Arep) <=> ~(A |-- gsentence Arep))]])
   (REWRITE_TAC [arithtrue, holds, gsentence] THEN
    MESON_TAC [HSENTENCE_FIX_STRONG])
  : ExceptT String IO thm).run
#eval GSENTENCE_FIX

#eval phrase 46
unsafe def ground : thm := keep "ground" fun _ => new_definition
  [[ground t <=> (FVT t = {})]]
#eval ground

#eval phrase 47
unsafe def complete_for : thm := keep "complete_for" fun _ => new_definition
  [[complete_for P A <=> !p. P p /\ arithtrue p ==> A |-- p]]
#eval complete_for

#eval phrase 48
unsafe def sound_for : thm := keep "sound_for" fun _ => new_definition
  [[sound_for P A <=> !p. P p /\ A |-- p ==> arithtrue p]]
#eval sound_for

#eval phrase 49
unsafe def consistent : thm := keep "consistent" fun _ => new_definition
  [[consistent A <=> ~(?p. A |-- p /\ A |-- Not p)]]
#eval consistent

#eval phrase 50
unsafe def CONSISTENT_ALT : thm := keep "CONSISTENT_ALT" fun _ => (do
  prove ([[!A p. A |-- p /\ A |-- Not p <=> A |-- False]])
   (MESON_TAC [proves_RULES, axiom_RULES])
  : ExceptT String IO thm).run
#eval CONSISTENT_ALT

#eval phrase 51
unsafe def DEFINABLE_BY_ONEVAR : thm := keep "DEFINABLE_BY_ONEVAR" fun _ => (do
  prove ([[definable_by (SIGMA 1) s <=>
        ?p x. SIGMA 1 p /\ (FV p = {x}) /\ !v. holds v p <=> (v x) IN s]])
   (REWRITE_TAC [definable_by, SIGMA] THEN
    EQ_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[p:form]]) (X_CHOOSE_TAC ([[x:num]]))) THEN
    EXISTS_TAC [[(V x === V x) && formsubst (\y. if y = x then V x else Z) p]] THEN
    EXISTS_TAC [[x:num]] THEN ASM_SIMP_TAC [SIGMAPI_CLAUSES, SIGMAPI_FORMSUBST] THEN
    ASM_REWRITE_TAC [HOLDS_FORMSUBST, FORMSUBST_FV, FV, holds] THEN
    REWRITE_TAC [COND_RAND, EXTENSION, IN_ELIM_THM, IN_SING, FVT, IN_UNION,
                COND_EXPAND, NOT_IN_EMPTY, o_THM, termval] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval DEFINABLE_BY_ONEVAR

#eval phrase 52
unsafe def CLOSED_NOT_TRUE : thm := keep "CLOSED_NOT_TRUE" fun _ => (do
  prove ([[!p. closed p ==> (arithtrue(Not p) <=> ~(arithtrue p))]])
   (REWRITE_TAC [closed, arithtrue, holds] THEN
    MESON_TAC [HOLDS_VALUATION, NOT_IN_EMPTY])
  : ExceptT String IO thm).run
#eval CLOSED_NOT_TRUE

#eval phrase 53
unsafe def G1 : thm := keep "G1" fun _ => (do
  prove ([[!A. definable_by (SIGMA 1) (IMAGE gform A)
       ==> ?G. PI 1 G /\ closed G /\
               (sound_for (PI 1 INTER closed) A ==> arithtrue G /\ ~(A |-- G)) /\
               (sound_for (SIGMA 1 INTER closed) A ==> ~(A |-- Not G))]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[a /\ b /\ (a /\ b ==> c /\ d) ==> a /\ b /\ c /\ d]])
     pure
      (GEN_TAC THEN
       REWRITE_TAC [sound_for, INTER, IN_ELIM_THM, DEFINABLE_BY_ONEVAR] THEN
       DISCH_THEN (X_CHOOSE_THEN ([[Arep:form]]) (X_CHOOSE_THEN ([[a:num]])
             STRIP_ASSUME_TAC)) THEN
       MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[A:form->bool]], [[\t. formsubst ((a |-> t) V) Arep]] ]
              GSENTENCE_FIX)) THEN
       REWRITE_TAC [] THEN ANTS_TAC THENL
        [ASM_REWRITE_TAC [HOLDS_FORMSUBST] THEN REWRITE_TAC [termval, valmod, o_THM],
         ALL_TAC] THEN
       STRIP_TAC THEN EXISTS_TAC [[gsentence (\t. formsubst ((a |-> t) V) Arep)]] THEN
       ASM_REWRITE_TAC [] THEN
       MATCH_MP_TAC taut1 THEN
       REPEAT CONJ_TAC THENL
        [REWRITE_TAC [PI] THEN MATCH_MP_TAC SIGMAPI_GSENTENCE THEN
         RULE_ASSUM_TAC (HolLight.REWRITE_RULE [SIGMA]) THEN ASM_SIMP_TAC [SIGMAPI_FORMSUBST],
         REWRITE_TAC [closed] THEN MATCH_MP_TAC FV_GSENTENCE THEN
         ASM_REWRITE_TAC [FORMSUBST_FV, EXTENSION, IN_ELIM_THM, IN_SING,
                         valmod, UNWIND_THM2],
         ALL_TAC] THEN
       ABBREV_TAC [[G = gsentence (\t. formsubst ((a |-> t) V) Arep)]] THEN
       REPEAT STRIP_TAC THENL [ASM_MESON_TAC [IN], ALL_TAC] THEN
       SUBGOAL_THEN ([[arithtrue(Not G)]]) MP_TAC THENL
        [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [IN] THEN
         REWRITE_TAC [SIGMA, SIGMAPI_CLAUSES] THEN ASM_MESON_TAC [closed, FV, PI],
         ALL_TAC] THEN
       FIRST_ASSUM (SUBST1_TAC oTIO HolLight.MATCH_MP CLOSED_NOT_TRUE) THEN
       ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
       SUBGOAL_THEN ([[arithtrue False]]) MP_TAC THENL
        [ALL_TAC, REWRITE_TAC [arithtrue, holds]] THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       REWRITE_TAC [closed, IN, SIGMA, SIGMAPI_CLAUSES, FV] THEN
       ASM_MESON_TAC [CONSISTENT_ALT]))
  : ExceptT String IO thm).run
#eval G1

#eval phrase 54
unsafe def COMPLETE_SOUND_SENTENCE : thm := keep "COMPLETE_SOUND_SENTENCE" fun _ => (do
  prove ([[consistent A /\ complete_for (sigmapi (~b) n INTER closed) A
   ==> sound_for (sigmapi b n INTER closed) A]])
   (REWRITE_TAC [consistent, sound_for, complete_for, IN, INTER, IN_ELIM_THM] THEN
    REWRITE_TAC [NOT_EXISTS_THM] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
      let sp ← ExceptT.mk (HolLight.SPEC ([[Not p]]) th)
      pure (X_GEN_TAC [[p:form]] THEN MP_TAC sp)) THEN
    REWRITE_TAC [SIGMAPI_CLAUSES] THEN
    REWRITE_TAC [closed, FV, arithtrue, holds] THEN
    ASM_MESON_TAC [HOLDS_VALUATION, NOT_IN_EMPTY])
  : ExceptT String IO thm).run
#eval COMPLETE_SOUND_SENTENCE

#eval phrase 55
unsafe def G1_TRAD : thm := keep "G1_TRAD" fun _ => (do
  prove ([[!A. consistent A /\
       complete_for (SIGMA 1 INTER closed) A /\
       definable_by (SIGMA 1) (IMAGE gform A)
       ==> ?G. PI 1 G /\ closed G /\ arithtrue G /\ ~(A |-- G) /\
               (sound_for (SIGMA 1 INTER closed) A ==> ~(A |-- Not G))]])
   (REWRITE_TAC [SIGMA] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← ExceptT.mk (HolLight.SPEC ([[A:form->bool]]) G1)) THEN ASM_REWRITE_TAC [SIGMA, PI] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM_SIMP_TAC [COMPLETE_SOUND_SENTENCE])
  : ExceptT String IO thm).run
#eval G1_TRAD

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.Godel" do
  replay (
          HolLogicArith.ArithProv.ensure)
  replay (
          do IO.println sigmapi_RULES; IO.println sigmapi_INDUCT; IO.println sigmapi_CASES)
  replay (
          SIGMA)
  replay (
          PI)
  replay (
          DELTA)
  replay (
          SIGMAPI_PROP)
  replay (
          SIGMAPI_MONO_LEMMA)
  replay (
          SIGMAPI_REV_EXISTS)
  replay (
          SIGMAPI_REV_FORALL)
  replay (
          SIGMAPI_CLAUSES_CODE)
  replay (
          SIGMAPI_CLAUSES)
  replay (
          SIGMAPI_FORMSUBST)
  replay (
          IO.println "<fun>")
  replay (
          SIGMAPI_DIVIDES)
  replay (
          SIGMAPI_PRIME)
  replay (
          SIGMAPI_PRIMEPOW)
  replay (
          SIGMAPI_RTC)
  replay (
          SIGMAPI_RTCP)
  replay (
          SIGMAPI_TERM1)
  replay (
          SIGMAPI_TERM)
  replay (
          SIGMAPI_FORM1)
  replay (
          SIGMAPI_FORM)
  replay (
          SIGMAPI_FREETERM1)
  replay (
          SIGMAPI_FREETERM)
  replay (
          SIGMAPI_FREEFORM1)
  replay (
          SIGMAPI_FREEFORM)
  replay (
          SIGMAPI_AXIOM)
  replay (
          SIGMAPI_PROV1)
  replay (
          SIGMAPI_PROV)
  replay (
          SIGMAPI_PRIMRECSTEP)
  replay (
          SIGMAPI_PRIMREC)
  replay (
          SIGMAPI_GNUMERAL1)
  replay (
          SIGMAPI_GNUMERAL)
  replay (
          SIGMAPI_QSUBST)
  replay (
          SIGMAPI_QDIAG)
  replay (
          SIGMAPI_DIAGONALIZE)
  replay (
          SIGMAPI_FIXPOINT)
  replay (
          hsentence)
  replay (
          gsentence)
  replay (
          FV_HSENTENCE)
  replay (
          FV_GSENTENCE)
  replay (
          SIGMAPI_HSENTENCE)
  replay (
          SIGMAPI_GSENTENCE)
  replay (
          HSENTENCE_FIX_STRONG)
  replay (
          HSENTENCE_FIX)
  replay (
          GSENTENCE_FIX)
  replay (
          ground)
  replay (
          complete_for)
  replay (
          sound_for)
  replay (
          consistent)
  replay (
          CONSISTENT_ALT)
  replay (
          DEFINABLE_BY_ONEVAR)
  replay (
          CLOSED_NOT_TRUE)
  replay (
          G1)
  replay (
          COMPLETE_SOUND_SENTENCE)
  replay (
          G1_TRAD)
-- @@ENSURE END

end HolLogicArith.Godel
