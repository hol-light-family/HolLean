/- File: HolLogicArith/ArithProv.lean
Translation of HOL Light's Arithmetic/arithprov.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Tarski
open HolCore.Kernel HolCore.Lib HolCore.Basics Session HolLight.Syntax HolLogicArith
open scoped HolLight
-- Names from Arithmetic/fol.ml that arithprov.ml reuses.
open HolLogicArith.ArithFol (termval holds valmod arithtrue numeral
  TERMVAL_NUMERAL FVT_NUMERAL HOLDS_FORMSUBST FV FORMSUBST_FV FVT TERMSUBST_FVT
  term_INDUCT form_INDUCT VALMOD_BASIC proves_RULES proves_INDUCT axiom_CASES
  qsubst)
-- Names from Arithmetic/definability.ml that arithprov.ml reuses.
open HolLogicArith.Definability (NPAIR NPAIR_INJ NPAIR_NONZERO NPAIR_LT
  arith_pair ARITH_PAIR FVT_PAIR arith_rtc ARITH_RTC FV_RTC FV_RTCP
  OBJECTIFY OBJECTIFY_RTC OBJECTIFY_RTCP PRIMREC_SIGMA)
-- Names from Arithmetic/tarski.ml that arithprov.ml reuses.
open HolLogicArith.Tarski (number denumber gterm gform GTERM_INJ GFORM_INJ
  GTERM_CASES GFORM_CASES NUMBER_DENUMBER NUMBER_INJ NUMBER_SURJ definable)
-- RTC library theorems (loaded by make.ml before fol.ml).
open SessionLibrary.RSTC (RTC_INC RTC_TRANS RTC_INDUCT)

namespace HolLogicArith.ArithProv

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- `new_specification` lifted into `ExceptT String IO`. -/
private unsafe def newSpec (names : List String) (th : thm) : ExceptT String IO thm :=
  ExceptT.mk (Session.new_specification names th)

/- Force an `ExceptT String IO (thm × thm)` to its value, panicking with HOL
   Light's message on failure (as the toplevel `let a,b = ...` would throw). -/
private unsafe def runObj (m : ExceptT String IO (thm × thm)) : thm × thm :=
  match unsafeIO m.run with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! s!"OBJECTIFY: {e}"
  | .error e => panic! s!"OBJECTIFY IO: {e}"

-- Replay Arithmetic/tarski.ml (the one module arithprov.ml imports).
#eval HolLogicArith.Tarski.ensure

#eval phrase 1
#eval Session.prioritize_num

#eval phrase 2
unsafe def ALLN_DEF : thm := keep "ALLN_DEF" fun _ => (do
  let th ← prove ([[!P. ?ALLN. !z.
         ALLN z <=>
                if ?x y. z = NPAIR x y
                then P (@x. ?y. NPAIR x y = z) /\
                     ALLN (@y. ?x. NPAIR x y = z)
                else T]])
   (HolLight.tactic_of do
     let wfrec ← HolLight.MATCH_MP WF_REC WF_num
     pure
      (GEN_TAC THEN MATCH_MP_TAC wfrec THEN
       REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
       BINOP_TAC THENL [ALL_TAC, FIRST_ASSUM MATCH_MP_TAC] THEN
       FIRST_ASSUM (REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN
       REWRITE_TAC [NPAIR_INJ, RIGHT_EXISTS_AND_THM, EXISTS_REFL,
                   SELECT_REFL, NPAIR_LT, LEFT_EXISTS_AND_THM]))
  newSpec ["ALLN"] (← HolLight.REWRITE_RULE [SKOLEM_THM] th)
  : ExceptT String IO thm).run
#eval ALLN_DEF

#eval phrase 3
unsafe def ALLN : thm := keep "ALLN" fun _ => (do
  prove ([[(ALLN P 0 <=> T) /\
   (ALLN P (NPAIR x y) <=> P x /\ ALLN P y)]])
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC HolLight.LAND_CONV [ALLN_DEF] THEN
    REWRITE_TAC [NPAIR_NONZERO] THEN
    REWRITE_TAC [NPAIR_INJ, LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM] THEN
    REWRITE_TAC [EXISTS_REFL, (← HolLight.GSYM EXISTS_REFL)])
  : ExceptT String IO thm).run
#eval ALLN

#eval phrase 4
unsafe def TERM1 : thm := keep "TERM1" fun _ => new_definition
  [[TERM1 x y <=>
        (?l u. (x = l) /\ (y = NPAIR (NPAIR 0 u) l)) \/
        (?l. (x = l) /\ (y = NPAIR (NPAIR 1 0) l)) \/
        (?t l. (x = NPAIR t l) /\ (y = NPAIR (NPAIR 2 t) l)) \/
        (?n s t l. ((n = 3) \/ (n = 4)) /\
                   (x = NPAIR s (NPAIR t l)) /\
                   (y = NPAIR (NPAIR n (NPAIR s t)) l))]]
#eval TERM1

#eval phrase 5
unsafe def TERM : thm := keep "TERM" fun _ => new_definition
  [[TERM n <=> RTC TERM1 0 (NPAIR n 0)]]
#eval TERM

#eval phrase 6
unsafe def isagterm : thm := keep "isagterm" fun _ => new_definition
  [[isagterm n <=> ?t. n = gterm t]]
#eval isagterm

#eval phrase 7
unsafe def TERM_LEMMA1 : thm := keep "TERM_LEMMA1" fun _ => (do
  prove ([[!x y. TERM1 x y ==> ALLN isagterm x ==> ALLN isagterm y]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[a \/ b ==> c <=> (a ==> c) /\ (b ==> c)]])
     pure
      (REPEAT GEN_TAC THEN REWRITE_TAC [TERM1] THEN
       REWRITE_TAC [taut1] THEN
       SIMP_TAC [LEFT_IMP_EXISTS_THM, ALLN, isagterm] THEN
       MESON_TAC [gterm, NUMBER_SURJ]))
  : ExceptT String IO thm).run
#eval TERM_LEMMA1

#eval phrase 8
unsafe def TERM_LEMMA2 : thm := keep "TERM_LEMMA2" fun _ => (do
  prove ([[!t a. RTC TERM1 a (NPAIR (gterm t) a)]])
   (MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC [gterm] THEN
    MESON_TAC [RTC_INC, RTC_TRANS, TERM1])
  : ExceptT String IO thm).run
#eval TERM_LEMMA2

#eval phrase 9
unsafe def TERM_THM : thm := keep "TERM_THM" fun _ => (do
  prove ([[!n. TERM n <=> ?t. n = gterm t]])
   (GEN_TAC THEN REWRITE_TAC [TERM] THEN EQ_TAC THENL
     [ALL_TAC, MESON_TAC [TERM_LEMMA2]] THEN
    SUBGOAL_THEN ([[!x y. RTC TERM1 x y ==> ALLN isagterm x ==> ALLN isagterm y]])
     (fun th => MESON_TAC [ALLN, isagterm, th]) THEN
    MATCH_MP_TAC RTC_INDUCT THEN REWRITE_TAC [TERM_LEMMA1] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval TERM_THM

#eval phrase 10
unsafe def FORM1 : thm := keep "FORM1" fun _ => new_definition
  [[FORM1 x y <=>
        (?l. (x = l) /\ (y = NPAIR (NPAIR 0 0) l)) \/
        (?l. (x = l) /\ (y = NPAIR (NPAIR 0 1) l)) \/
        (?n s t l. ((n = 1) \/ (n = 2) \/ (n = 3)) /\
                   TERM s /\ TERM t /\
                   (x = l) /\
                   (y = NPAIR (NPAIR n (NPAIR s t)) l)) \/
        (?p l. (x = NPAIR p l) /\
               (y = NPAIR (NPAIR 4 p) l)) \/
        (?n p q l. ((n = 5) \/ (n = 6) \/ (n = 7) \/ (n = 8)) /\
                   (x = NPAIR p (NPAIR q l)) /\
                   (y = NPAIR (NPAIR n (NPAIR p q)) l)) \/
        (?n u p l. ((n = 9) \/ (n = 10)) /\
                   (x = NPAIR p l) /\
                   (y = NPAIR (NPAIR n (NPAIR u p)) l))]]
#eval FORM1

#eval phrase 11
unsafe def FORM : thm := keep "FORM" fun _ => new_definition
  [[FORM n <=> RTC FORM1 0 (NPAIR n 0)]]
#eval FORM

#eval phrase 12
unsafe def isagform : thm := keep "isagform" fun _ => new_definition
  [[isagform n <=> ?t. n = gform t]]
#eval isagform

#eval phrase 13
unsafe def FORM_LEMMA1 : thm := keep "FORM_LEMMA1" fun _ => (do
  prove ([[!x y. FORM1 x y ==> ALLN isagform x ==> ALLN isagform y]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[a \/ b ==> c <=> (a ==> c) /\ (b ==> c)]])
     pure
      (REPEAT GEN_TAC THEN REWRITE_TAC [FORM1] THEN
       REWRITE_TAC [taut1] THEN
       SIMP_TAC [LEFT_IMP_EXISTS_THM, ALLN, isagform] THEN
       MESON_TAC [gform, TERM_THM, NUMBER_SURJ]))
  : ExceptT String IO thm).run
#eval FORM_LEMMA1

#eval phrase 14
unsafe def FORM_LEMMA2 : thm := keep "FORM_LEMMA2" fun _ => (do
  prove ([[!p a. RTC FORM1 a (NPAIR (gform p) a)]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)]])
     let sp ← ExceptT.mk (HolLight.SPEC_ALL FORM1)
     let (_, imp) ← HolLight.EQ_IMP_RULE sp
     let rr ← HolLight.REWRITE_RULE [taut1] imp
     pure
      (MATCH_MP_TAC form_INDUCT THEN REWRITE_TAC [gform] THEN
       REPEAT CONJ_TAC THEN
       MESON_TAC [RTC_INC, RTC_TRANS, TERM_THM, rr]))
  : ExceptT String IO thm).run
#eval FORM_LEMMA2

#eval phrase 15
unsafe def FORM_THM : thm := keep "FORM_THM" fun _ => (do
  prove ([[!n. FORM n <=> ?p. n = gform p]])
   (GEN_TAC THEN REWRITE_TAC [FORM] THEN EQ_TAC THENL
     [ALL_TAC, MESON_TAC [FORM_LEMMA2]] THEN
    SUBGOAL_THEN ([[!x y. RTC FORM1 x y ==> ALLN isagform x ==> ALLN isagform y]])
     (fun th => MESON_TAC [ALLN, isagform, th]) THEN
    MATCH_MP_TAC RTC_INDUCT THEN REWRITE_TAC [FORM_LEMMA1] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval FORM_THM

#eval phrase 16
unsafe def FREETERM1 : thm := keep "FREETERM1" fun _ => new_definition
  [[FREETERM1 m x y <=>
        (?l u. ~(u = m) /\ (x = l) /\ (y = NPAIR (NPAIR 0 u) l)) \/
        (?l. (x = l) /\ (y = NPAIR (NPAIR 1 0) l)) \/
        (?t l. (x = NPAIR t l) /\ (y = NPAIR (NPAIR 2 t) l)) \/
        (?n s t l. ((n = 3) \/ (n = 4)) /\
                   (x = NPAIR s (NPAIR t l)) /\
                   (y = NPAIR (NPAIR n (NPAIR s t)) l))]]
#eval FREETERM1

#eval phrase 17
unsafe def FREETERM : thm := keep "FREETERM" fun _ => new_definition
  [[FREETERM m n <=> RTC (FREETERM1 m) 0 (NPAIR n 0)]]
#eval FREETERM

#eval phrase 18
unsafe def isafterm : thm := keep "isafterm" fun _ => new_definition
  [[isafterm m n <=> ?t. ~(m IN IMAGE number (FVT t)) /\ (n = gterm t)]]
#eval isafterm

#eval phrase 19
unsafe def ISAFTERM : thm := keep "ISAFTERM" fun _ => (do
  prove ([[(~(number x = m) ==> isafterm m (NPAIR 0 (number x))) /\
   isafterm m (NPAIR 1 0) /\
   (isafterm m t ==> isafterm m (NPAIR 2 t)) /\
   (isafterm m s /\ isafterm m t ==> isafterm m (NPAIR 3 (NPAIR s t))) /\
   (isafterm m s /\ isafterm m t ==> isafterm m (NPAIR 4 (NPAIR s t)))]])
   (REWRITE_TAC [isafterm, gterm] THEN REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC [[V x]],
      EXISTS_TAC [[Z]],
      DISCH_THEN (X_CHOOSE_THEN ([[t:term]]) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC [[Suc t]],
      DISCH_THEN (CONJUNCTS_THEN2
       (X_CHOOSE_THEN ([[s:term]]) STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN ([[t:term]]) STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC [[s ++ t]],
      DISCH_THEN (CONJUNCTS_THEN2
       (X_CHOOSE_THEN ([[s:term]]) STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN ([[t:term]]) STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC [[s ** t]]] THEN
    ASM_REWRITE_TAC [gterm, FVT, IMAGE_UNION, NOT_IN_EMPTY, IN_SING, IN_UNION,
                    IMAGE_CLAUSES])
  : ExceptT String IO thm).run
#eval ISAFTERM

#eval phrase 20
unsafe def FREETERM_LEMMA1 : thm := keep "FREETERM_LEMMA1" fun _ => (do
  prove ([[!m x y. FREETERM1 m x y ==> ALLN (isafterm m) x ==> ALLN (isafterm m) y]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[a \/ b ==> c <=> (a ==> c) /\ (b ==> c)]])
     pure
      (REPEAT GEN_TAC THEN REWRITE_TAC [FREETERM1] THEN
       REWRITE_TAC [taut1] THEN
       SIMP_TAC [LEFT_IMP_EXISTS_THM, ALLN] THEN
       MESON_TAC [ISAFTERM, NUMBER_SURJ]))
  : ExceptT String IO thm).run
#eval FREETERM_LEMMA1

#eval phrase 21
unsafe def FREETERM_LEMMA2 : thm := keep "FREETERM_LEMMA2" fun _ => (do
  prove ([[!m t a. ~(m IN IMAGE number (FVT t))
           ==> RTC (FREETERM1 m) a (NPAIR (gterm t) a)]])
   (GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
    REWRITE_TAC [gterm, FVT, NOT_IN_EMPTY, IN_SING, IN_UNION,
                IMAGE_CLAUSES, IMAGE_UNION] THEN
    REWRITE_TAC [DE_MORGAN_THM] THEN
    REPEAT CONJ_TAC THEN
    TRY (REPEAT GEN_TAC THEN DISCH_THEN
     (fun th => GEN_TAC THEN STRIP_TAC THEN MP_TAC th)) THEN
    ASM_REWRITE_TAC [] THEN
    MESON_TAC [RTC_INC, RTC_TRANS, FREETERM1])
  : ExceptT String IO thm).run
#eval FREETERM_LEMMA2

#eval phrase 22
unsafe def FREETERM_THM : thm := keep "FREETERM_THM" fun _ => (do
  prove ([[!m n. FREETERM m n <=> ?t. ~(m IN IMAGE number (FVT(t))) /\ (n = gterm t)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [FREETERM] THEN EQ_TAC THENL
     [ALL_TAC, MESON_TAC [FREETERM_LEMMA2]] THEN
    SUBGOAL_THEN ([[!x y. RTC (FREETERM1 m) x y
                      ==> ALLN (isafterm m) x ==> ALLN (isafterm m) y]])
     (fun th => MESON_TAC [ALLN, isagterm, isafterm, th]) THEN
    MATCH_MP_TAC RTC_INDUCT THEN REWRITE_TAC [FREETERM_LEMMA1] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval FREETERM_THM

#eval phrase 23
unsafe def FREEFORM1 : thm := keep "FREEFORM1" fun _ => new_definition
  [[FREEFORM1 m x y <=>
        (?l. (x = l) /\ (y = NPAIR (NPAIR 0 0) l)) \/
        (?l. (x = l) /\ (y = NPAIR (NPAIR 0 1) l)) \/
        (?n s t l. ((n = 1) \/ (n = 2) \/ (n = 3)) /\
                   FREETERM m s /\ FREETERM m t /\
                   (x = l) /\
                   (y = NPAIR (NPAIR n (NPAIR s t)) l)) \/
        (?p l. (x = NPAIR p l) /\
               (y = NPAIR (NPAIR 4 p) l)) \/
        (?n p q l. ((n = 5) \/ (n = 6) \/ (n = 7) \/ (n = 8)) /\
                   (x = NPAIR p (NPAIR q l)) /\
                   (y = NPAIR (NPAIR n (NPAIR p q)) l)) \/
        (?n u p l. ((n = 9) \/ (n = 10)) /\
                   (x = NPAIR p l) /\
                   (y = NPAIR (NPAIR n (NPAIR u p)) l)) \/
        (?n p l. ((n = 9) \/ (n = 10)) /\
                 (x = l) /\ FORM p /\
                 (y = NPAIR (NPAIR n (NPAIR m p)) l))]]
#eval FREEFORM1

#eval phrase 24
unsafe def FREEFORM : thm := keep "FREEFORM" fun _ => new_definition
  [[FREEFORM m n <=> RTC (FREEFORM1 m) 0 (NPAIR n 0)]]
#eval FREEFORM

#eval phrase 25
unsafe def isafform : thm := keep "isafform" fun _ => new_definition
  [[isafform m n <=> ?p. ~(m IN IMAGE number (FV p)) /\ (n = gform p)]]
#eval isafform

#eval phrase 26
unsafe def ISAFFORM : thm := keep "ISAFFORM" fun _ => (do
  prove ([[isafform m (NPAIR 0 0) /\
   isafform m (NPAIR 0 1) /\
   (isafterm m s /\ isafterm m t ==> isafform m (NPAIR 1 (NPAIR s t))) /\
   (isafterm m s /\ isafterm m t ==> isafform m (NPAIR 2 (NPAIR s t))) /\
   (isafterm m s /\ isafterm m t ==> isafform m (NPAIR 3 (NPAIR s t))) /\
   (isafform m p ==> isafform m (NPAIR 4 p)) /\
   (isafform m p /\ isafform m q ==> isafform m (NPAIR 5 (NPAIR p q))) /\
   (isafform m p /\ isafform m q ==> isafform m (NPAIR 6 (NPAIR p q))) /\
   (isafform m p /\ isafform m q ==> isafform m (NPAIR 7 (NPAIR p q))) /\
   (isafform m p /\ isafform m q ==> isafform m (NPAIR 8 (NPAIR p q))) /\
   (isafform m p ==> isafform m (NPAIR 9 (NPAIR x p))) /\
   (isafform m p ==> isafform m (NPAIR 10 (NPAIR x p))) /\
   (isagform p ==> isafform m (NPAIR 9 (NPAIR m p))) /\
   (isagform p ==> isafform m (NPAIR 10 (NPAIR m p)))]])
   (HolLight.tactic_of do
     let tac0 := DISCH_THEN (X_CHOOSE_THEN ([[p:form]]) STRIP_ASSUME_TAC)
     let tac1 :=
       DISCH_THEN (CONJUNCTS_THEN2
        (X_CHOOSE_THEN ([[s:term]]) STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN ([[t:term]]) STRIP_ASSUME_TAC))
     let tac2 :=
       DISCH_THEN (CONJUNCTS_THEN2
        (X_CHOOSE_THEN ([[p:form]]) STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN ([[q:form]]) STRIP_ASSUME_TAC))
     pure
      (REWRITE_TAC [isafform, gform, isagform, isafterm] THEN REPEAT CONJ_TAC THENL
        [EXISTS_TAC [[False]],
         EXISTS_TAC [[True]],
         tac1 THEN EXISTS_TAC [[s === t]],
         tac1 THEN EXISTS_TAC [[s << t]],
         tac1 THEN EXISTS_TAC [[s <<= t]],
         tac0 THEN EXISTS_TAC [[Not p]],
         tac2 THEN EXISTS_TAC [[p && q]],
         tac2 THEN EXISTS_TAC [[p || q]],
         tac2 THEN EXISTS_TAC [[p --> q]],
         tac2 THEN EXISTS_TAC [[p <-> q]],
         tac0 THEN EXISTS_TAC [[!!(denumber x) p]],
         tac0 THEN EXISTS_TAC [[??(denumber x) p]],
         tac0 THEN EXISTS_TAC [[!!(denumber m) p]],
         tac0 THEN EXISTS_TAC [[??(denumber m) p]]] THEN
       ASM_REWRITE_TAC [FV, IN_DELETE, NOT_IN_EMPTY, IN_SING, IN_UNION, gform,
                       NUMBER_DENUMBER, IMAGE_CLAUSES, IMAGE_UNION] THEN
       ASM SET_TAC [NUMBER_DENUMBER]))
  : ExceptT String IO thm).run
#eval ISAFFORM

#eval phrase 27
unsafe def FREEFORM_LEMMA1 : thm := keep "FREEFORM_LEMMA1" fun _ => (do
  prove ([[!x y. FREEFORM1 m x y ==> ALLN (isafform m) x ==> ALLN (isafform m) y]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[a \/ b ==> c <=> (a ==> c) /\ (b ==> c)]])
     pure
      (REPEAT GEN_TAC THEN REWRITE_TAC [FREEFORM1] THEN
       REWRITE_TAC [taut1] THEN
       SIMP_TAC [LEFT_IMP_EXISTS_THM, ALLN] THEN
       REWRITE_TAC [FREETERM_THM, (← HolLight.GSYM isafterm)] THEN
       REWRITE_TAC [FORM_THM, (← HolLight.GSYM isagform)] THEN MESON_TAC [ISAFFORM]))
  : ExceptT String IO thm).run
#eval FREEFORM_LEMMA1

#eval phrase 28
unsafe def FREEFORM_LEMMA2 : thm := keep "FREEFORM_LEMMA2" fun _ => (do
  prove ([[!m p a. ~(m IN IMAGE number (FV p))
           ==> RTC (FREEFORM1 m) a (NPAIR (gform p) a)]])
   (HolLight.tactic_of do
     let lemma ← ExceptT.mk (Session.prove
       ([[m IN IMAGE number (s DELETE k) <=>
          m IN IMAGE number s /\ ~(m = number k)]])
       (SET_TAC [NUMBER_INJ]))
     let taut1 ← ExceptT.mk (TAUT [[(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)]])
     let sp ← ExceptT.mk (HolLight.SPEC_ALL FREEFORM1)
     let (_, imp) ← HolLight.EQ_IMP_RULE sp
     let rr ← HolLight.REWRITE_RULE [taut1, FREETERM_THM] imp
     pure
      (GEN_TAC THEN MATCH_MP_TAC form_INDUCT THEN
       REWRITE_TAC [gform, FV, NOT_IN_EMPTY, IN_DELETE, IN_SING, IN_UNION,
                   lemma, IMAGE_UNION, IMAGE_CLAUSES] THEN
       REWRITE_TAC [DE_MORGAN_THM] THEN
       REPEAT CONJ_TAC THEN
       TRY (REPEAT GEN_TAC THEN DISCH_THEN
        (fun th => GEN_TAC THEN STRIP_TAC THEN MP_TAC th)) THEN
       ASM_REWRITE_TAC [] THEN
       MESON_TAC [RTC_INC, RTC_TRANS, FORM_THM, rr]))
  : ExceptT String IO thm).run
#eval FREEFORM_LEMMA2

#eval phrase 29
unsafe def FREEFORM_THM : thm := keep "FREEFORM_THM" fun _ => (do
  prove ([[!m n. FREEFORM m n <=> ?p. ~(m IN IMAGE number (FV p)) /\ (n = gform p)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [FREEFORM] THEN EQ_TAC THENL
     [ALL_TAC, MESON_TAC [FREEFORM_LEMMA2]] THEN
    SUBGOAL_THEN ([[!x y. RTC (FREEFORM1 m) x y
                      ==> ALLN (isafform m) x ==> ALLN (isafform m) y]])
     (fun th => MESON_TAC [ALLN, isagform, isafform, th]) THEN
    MATCH_MP_TAC RTC_INDUCT THEN REWRITE_TAC [FREEFORM_LEMMA1] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval FREEFORM_THM

#eval phrase 30
unsafe def AXIOM_pair : thm × thm := keep "AXIOM_pair" fun _ =>
  runObj (do
    let th0 ← prove
     ([[((?x p. P (number x) (gform p) /\ ~(x IN FV(p))) <=>
         (?x p. FREEFORM x p /\ P x p)) /\
        ((?x t. P (number x) (gterm t) /\ ~(x IN FVT(t))) <=>
         (?x t. FREETERM x t /\ P x t))]])
      (HolLight.tactic_of do
        let taut1 ← ExceptT.mk (TAUT [[(a /\ b) /\ c <=> b /\ a /\ c]])
        pure
         (REWRITE_TAC [FREETERM_THM, FREEFORM_THM] THEN CONJ_TAC THEN
          REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
          ONCE_REWRITE_TAC [taut1] THEN
          GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.BINDER_CONV) [SWAP_EXISTS_THM] THEN
          REWRITE_TAC [UNWIND_THM2, IN_IMAGE] THEN
          ASM_MESON_TAC [IN_IMAGE, NUMBER_DENUMBER]))
    let th1 ← prove
     ([[((?p. P(gform p)) <=> (?p. FORM(p) /\ P p)) /\
        ((?t. P(gterm t)) <=> (?t. TERM(t) /\ P t))]])
      (MESON_TAC [FORM_THM, TERM_THM])
    let th2 ← prove
     ([[(?x. P(number x)) <=> (?x. P x)]])
      (MESON_TAC [NUMBER_DENUMBER])
    let spac ← ExceptT.mk (HolLight.SPEC ([[a:form]]) axiom_CASES)
    let rconc ← liftExcept (HolCore.Equal.rhs (concl spac))
    let th ← ExceptT.mk
      ((HolLight.REWRITE_CONV [(← HolLight.GSYM GFORM_INJ)] THENC
        HolLight.REWRITE_CONV [gform, gterm] THENC
        HolLight.REWRITE_CONV [th0] THENC HolLight.REWRITE_CONV [th1] THENC
        HolLight.REWRITE_CONV [th2] THENC
        HolLight.REWRITE_CONV [RIGHT_AND_EXISTS_THM]) rconc)
    let thrhs ← liftExcept (HolCore.Equal.rhs (concl th))
    let substf ← ExceptT.mk (HolCore.Basics.subst [([[a:num]], [[gform a]])])
    let sub ← ExceptT.mk (substf thrhs)
    let dtm := HolCore.Kernel.safe_mk_eq ([[(AXIOM:num->bool) a]]) sub
    let AXIOM ← ExceptT.mk (Session.new_definition dtm)
    let AXIOM_THM ← prove
     ([[!p. AXIOM(gform p) <=> axiom p]])
      (REWRITE_TAC [axiom_CASES, AXIOM, th])
    pure (AXIOM, AXIOM_THM))
unsafe def AXIOM : thm := AXIOM_pair.1
unsafe def AXIOM_THM : thm := AXIOM_pair.2
#eval do IO.println AXIOM; IO.println AXIOM_THM

#eval phrase 31
unsafe def GTERM_CASES_ALT : thm := keep "GTERM_CASES_ALT" fun _ => (do
  prove ([[(gterm u = NPAIR 0 x <=> u = V(denumber x))]])
   (REWRITE_TAC [(← HolLight.GSYM GTERM_CASES), NUMBER_DENUMBER])
  : ExceptT String IO thm).run
#eval GTERM_CASES_ALT

#eval phrase 32
unsafe def GFORM_CASES_ALT : thm := keep "GFORM_CASES_ALT" fun _ => (do
  prove ([[(gform r = NPAIR 9 (NPAIR x n) <=>
    (?p. r = !!(denumber x) p /\ gform p = n)) /\
   (gform r = NPAIR 10 (NPAIR x n) <=>
    (?p. r = ??(denumber x) p /\ gform p = n))]])
   (REWRITE_TAC [(← HolLight.GSYM GFORM_CASES), NUMBER_DENUMBER])
  : ExceptT String IO thm).run
#eval GFORM_CASES_ALT

#eval phrase 33
unsafe def AXIOM_FORMULA : thm := keep "AXIOM_FORMULA" fun _ => (do
  prove ([[!a. AXIOM a ==> ?p. a = gform p]])
   (REWRITE_TAC [AXIOM, FREEFORM_THM, FREETERM_THM, FORM_THM, TERM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC (HolLight.BINDER_CONV HolLight.SYM_CONV) THEN
    REWRITE_TAC [GFORM_CASES, GTERM_CASES,
                GTERM_CASES_ALT, GFORM_CASES_ALT] THEN
    MESON_TAC [NUMBER_DENUMBER])
  : ExceptT String IO thm).run
#eval AXIOM_FORMULA

#eval phrase 34
unsafe def AXIOM_THM_STRONG : thm := keep "AXIOM_THM_STRONG" fun _ => (do
  prove ([[!a. AXIOM a <=> ?p. axiom p /\ (a = gform p)]])
   (MESON_TAC [AXIOM_THM, AXIOM_FORMULA])
  : ExceptT String IO thm).run
#eval AXIOM_THM_STRONG

#eval phrase 35
unsafe def PROV1 : thm := keep "PROV1" fun _ => new_definition
  [[PROV1 A x y <=>
        (?a. (AXIOM a \/ a IN A) /\ (y = NPAIR a x)) \/
        (?p q l. (x = NPAIR (NPAIR 7 (NPAIR p q)) (NPAIR p l)) /\
                 (y = NPAIR q l)) \/
        (?p u l. (x = NPAIR p l) /\ (y = NPAIR (NPAIR 9 (NPAIR u p)) l))]]
#eval PROV1

#eval phrase 36
unsafe def PROV : thm := keep "PROV" fun _ => new_definition
  [[PROV A n <=> RTC (PROV1 A) 0 (NPAIR n 0)]]
#eval PROV

#eval phrase 37
unsafe def isaprove : thm := keep "isaprove" fun _ => new_definition
  [[isaprove A n <=> ?p. (gform p = n) /\ A |-- p]]
#eval isaprove

#eval phrase 38
unsafe def PROV_LEMMA1 : thm := keep "PROV_LEMMA1" fun _ => (do
  prove ([[!A p q. PROV1 (IMAGE gform A) x y
           ==> ALLN (isaprove A) x ==> ALLN (isaprove A) y]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[a \/ b ==> c <=> (a ==> c) /\ (b ==> c)]])
     pure
      (REPEAT GEN_TAC THEN REWRITE_TAC [PROV1] THEN
       REWRITE_TAC [taut1] THEN
       SIMP_TAC [LEFT_IMP_EXISTS_THM, ALLN] THEN
       REWRITE_TAC [isaprove] THEN REPEAT CONJ_TAC THEN
       REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
        [ASM_MESON_TAC [AXIOM_THM_STRONG, proves_RULES],
         ASM_MESON_TAC [IN_IMAGE, GFORM_INJ, proves_RULES, gform],
         ALL_TAC,
         ASM_MESON_TAC [NUMBER_DENUMBER,
                       IN_IMAGE, GFORM_INJ, proves_RULES, gform]] THEN
       REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
       ONCE_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
       MATCH_MP_TAC form_INDUCT THEN
       REWRITE_TAC [gform, NPAIR_INJ, ARITH_EQ] THEN
       MAP_EVERY X_GEN_TAC [ [[P:form]], [[Q:form]] ] THEN
       DISCH_THEN (K ALL_TAC) THEN
       DISCH_THEN (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC oTIO HolLight.GSYM) MP_TAC) THEN
       ASM_REWRITE_TAC [GFORM_INJ] THEN
       REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC), UNWIND_THM2] THEN
       ASM_MESON_TAC [proves_RULES]))
  : ExceptT String IO thm).run
#eval PROV_LEMMA1

#eval phrase 39
unsafe def PROV_LEMMA2 : thm := keep "PROV_LEMMA2" fun _ => (do
  prove ([[!A p. A |-- p ==> !a. RTC (PROV1 (IMAGE gform A)) a (NPAIR (gform p) a)]])
   (GEN_TAC THEN MATCH_MP_TAC proves_INDUCT THEN REWRITE_TAC [gform] THEN
    MESON_TAC [RTC_INC, RTC_TRANS, PROV1, IN_IMAGE, AXIOM_THM])
  : ExceptT String IO thm).run
#eval PROV_LEMMA2

#eval phrase 40
unsafe def PROV_THM_STRONG : thm := keep "PROV_THM_STRONG" fun _ => (do
  prove ([[!A n. PROV (IMAGE gform A) n <=> ?p. A |-- p /\ (gform p = n)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [PROV] THEN EQ_TAC THENL
     [ALL_TAC, MESON_TAC [PROV_LEMMA2]] THEN
    SUBGOAL_THEN
     ([[!x y. RTC (PROV1 (IMAGE gform A)) x y
           ==> ALLN (isaprove A) x ==> ALLN (isaprove A) y]])
     (fun th => MESON_TAC [ALLN, isaprove, GFORM_INJ, th]) THEN
    MATCH_MP_TAC RTC_INDUCT THEN REWRITE_TAC [PROV_LEMMA1] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval PROV_THM_STRONG

#eval phrase 41
unsafe def PROV_THM : thm := keep "PROV_THM" fun _ => (do
  prove ([[!A p. PROV (IMAGE gform A) (gform p) <=> A |-- p]])
   (MESON_TAC [PROV_THM_STRONG, GFORM_INJ])
  : ExceptT String IO thm).run
#eval PROV_THM

#eval phrase 42
unsafe def arith_term1_pair : thm × thm := keep "arith_term1_pair" fun _ =>
  runObj (OBJECTIFY [] "arith_term1" TERM1)
unsafe def arith_term1 : thm := arith_term1_pair.1
unsafe def ARITH_TERM1 : thm := arith_term1_pair.2
#eval do IO.println arith_term1; IO.println ARITH_TERM1

#eval phrase 43
unsafe def FV_TERM1 : thm := keep "FV_TERM1" fun _ => (do
  prove ([[!s t. FV(arith_term1 s t) = (FVT s) UNION (FVT t)]])
   (Definability.FV_TAC [arith_term1, FVT_PAIR, FVT_NUMERAL])
  : ExceptT String IO thm).run
#eval FV_TERM1

#eval phrase 44
unsafe def arith_term_pair : thm × thm := keep "arith_term_pair" fun _ =>
  runObj (OBJECTIFY_RTC ARITH_TERM1 "arith_term" TERM)
unsafe def arith_term : thm := arith_term_pair.1
unsafe def ARITH_TERM : thm := arith_term_pair.2
#eval do IO.println arith_term; IO.println ARITH_TERM

#eval phrase 45
unsafe def FV_TERM : thm := keep "FV_TERM" fun _ => (do
  prove ([[!t. FV(arith_term t) = FVT t]])
   (Definability.FV_TAC [arith_term, FV_RTC, FV_TERM1, FVT_PAIR, FVT_NUMERAL])
  : ExceptT String IO thm).run
#eval FV_TERM

#eval phrase 46
unsafe def arith_form1_pair : thm × thm := keep "arith_form1_pair" fun _ =>
  runObj (OBJECTIFY [ARITH_TERM] "arith_form1" FORM1)
unsafe def arith_form1 : thm := arith_form1_pair.1
unsafe def ARITH_FORM1 : thm := arith_form1_pair.2
#eval do IO.println arith_form1; IO.println ARITH_FORM1

#eval phrase 47
unsafe def FV_FORM1 : thm := keep "FV_FORM1" fun _ => (do
  prove ([[!s t. FV(arith_form1 s t) = (FVT s) UNION (FVT t)]])
   (Definability.FV_TAC [arith_form1, FV_TERM, FVT_PAIR, FVT_NUMERAL])
  : ExceptT String IO thm).run
#eval FV_FORM1

#eval phrase 48
unsafe def arith_form_pair : thm × thm := keep "arith_form_pair" fun _ =>
  runObj (OBJECTIFY_RTC ARITH_FORM1 "arith_form" FORM)
unsafe def arith_form : thm := arith_form_pair.1
unsafe def ARITH_FORM : thm := arith_form_pair.2
#eval do IO.println arith_form; IO.println ARITH_FORM

#eval phrase 49
unsafe def FV_FORM : thm := keep "FV_FORM" fun _ => (do
  prove ([[!t. FV(arith_form t) = FVT t]])
   (Definability.FV_TAC [arith_form, FV_RTC, FV_FORM1, FVT_PAIR, FVT_NUMERAL])
  : ExceptT String IO thm).run
#eval FV_FORM

#eval phrase 50
unsafe def arith_freeterm1_pair : thm × thm := keep "arith_freeterm1_pair" fun _ =>
  runObj (OBJECTIFY [] "arith_freeterm1" FREETERM1)
unsafe def arith_freeterm1 : thm := arith_freeterm1_pair.1
unsafe def ARITH_FREETERM1 : thm := arith_freeterm1_pair.2
#eval do IO.println arith_freeterm1; IO.println ARITH_FREETERM1

#eval phrase 51
unsafe def FV_FREETERM1 : thm := keep "FV_FREETERM1" fun _ => (do
  prove ([[!s t u. FV(arith_freeterm1 s t u) = (FVT s) UNION (FVT t) UNION (FVT u)]])
   (Definability.FV_TAC [arith_freeterm1, FVT_PAIR, FVT_NUMERAL])
  : ExceptT String IO thm).run
#eval FV_FREETERM1

#eval phrase 52
unsafe def arith_freeterm_pair : thm × thm := keep "arith_freeterm_pair" fun _ =>
  runObj (OBJECTIFY_RTCP ARITH_FREETERM1 "arith_freeterm" FREETERM)
unsafe def arith_freeterm : thm := arith_freeterm_pair.1
unsafe def ARITH_FREETERM : thm := arith_freeterm_pair.2
#eval do IO.println arith_freeterm; IO.println ARITH_FREETERM

#eval phrase 53
unsafe def FV_FREETERM : thm := keep "FV_FREETERM" fun _ => (do
  prove ([[!s t. FV(arith_freeterm s t) = (FVT s) UNION (FVT t)]])
   (Definability.FV_TAC [arith_freeterm, FV_RTCP, FV_FREETERM1, FVT_PAIR, FVT_NUMERAL])
  : ExceptT String IO thm).run
#eval FV_FREETERM

#eval phrase 54
unsafe def arith_freeform1_pair : thm × thm := keep "arith_freeform1_pair" fun _ =>
  runObj (OBJECTIFY [ARITH_FREETERM, ARITH_FORM] "arith_freeform1" FREEFORM1)
unsafe def arith_freeform1 : thm := arith_freeform1_pair.1
unsafe def ARITH_FREEFORM1 : thm := arith_freeform1_pair.2
#eval do IO.println arith_freeform1; IO.println ARITH_FREEFORM1

#eval phrase 55
unsafe def FV_FREEFORM1 : thm := keep "FV_FREEFORM1" fun _ => (do
  prove ([[!s t u. FV(arith_freeform1 s t u) = (FVT s) UNION (FVT t) UNION (FVT u)]])
   (Definability.FV_TAC [arith_freeform1, FV_FREETERM, FV_FORM, FVT_PAIR, FVT_NUMERAL])
  : ExceptT String IO thm).run
#eval FV_FREEFORM1

#eval phrase 56
unsafe def arith_freeform_pair : thm × thm := keep "arith_freeform_pair" fun _ =>
  runObj (OBJECTIFY_RTCP ARITH_FREEFORM1 "arith_freeform" FREEFORM)
unsafe def arith_freeform : thm := arith_freeform_pair.1
unsafe def ARITH_FREEFORM : thm := arith_freeform_pair.2
#eval do IO.println arith_freeform; IO.println ARITH_FREEFORM

#eval phrase 57
unsafe def FV_FREEFORM : thm := keep "FV_FREEFORM" fun _ => (do
  prove ([[!s t. FV(arith_freeform s t) = (FVT s) UNION (FVT t)]])
   (Definability.FV_TAC [arith_freeform, FV_RTCP, FV_FREEFORM1, FVT_PAIR, FVT_NUMERAL])
  : ExceptT String IO thm).run
#eval FV_FREEFORM

#eval phrase 58
unsafe def arith_axiom_pair : thm × thm := keep "arith_axiom_pair" fun _ =>
  runObj (OBJECTIFY [ARITH_FORM, ARITH_FREEFORM, ARITH_FREETERM, ARITH_TERM]
           "arith_axiom" AXIOM)
unsafe def arith_axiom : thm := arith_axiom_pair.1
unsafe def ARITH_AXIOM : thm := arith_axiom_pair.2
#eval do IO.println arith_axiom; IO.println ARITH_AXIOM

#eval phrase 59
unsafe def FV_AXIOM : thm := keep "FV_AXIOM" fun _ => (do
  prove ([[!t. FV(arith_axiom t) = FVT t]])
   (Definability.FV_TAC [arith_axiom, FV_FREETERM, FV_FREEFORM, FV_TERM, FV_FORM,
          FVT_PAIR, FVT_NUMERAL])
  : ExceptT String IO thm).run
#eval FV_AXIOM

#eval phrase 60
unsafe def arith_prov1_pair : thm × thm := keep "arith_prov1_pair" fun _ =>
  runObj (do
    let PROV1' ← HolLight.REWRITE_RULE [IN] PROV1
    let asm ← liftExcept (HolCore.Kernel.ASSUME
      [[!v n. holds v (A n) <=> Ax (termval v n)]])
    OBJECTIFY [asm, ARITH_AXIOM] "arith_prov1" PROV1')
unsafe def arith_prov1 : thm := arith_prov1_pair.1
unsafe def ARITH_PROV1_obj : thm := arith_prov1_pair.2
#eval do IO.println arith_prov1; IO.println ARITH_PROV1_obj

#eval phrase 61
unsafe def ARITH_PROV1 : thm := keep "ARITH_PROV1" fun _ => (do
  prove ([[(!v t. holds v (A t) <=> Ax(termval v t))
   ==> (!v s t.
             holds v (arith_prov1 A s t) <=>
             PROV1 Ax (termval v s) (termval v t))]])
   (REWRITE_TAC [arith_prov1, holds, HOLDS_FORMSUBST] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [termval, valmod, o_THM, ARITH_EQ, ARITH_PAIR,
                    TERMVAL_NUMERAL, ARITH_AXIOM] THEN
    REWRITE_TAC [PROV1, IN])
  : ExceptT String IO thm).run
#eval ARITH_PROV1

#eval phrase 62
unsafe def FV_PROV1 : thm := keep "FV_PROV1" fun _ => (do
  prove ([[(!t. FV(A t) = FVT t) ==> !s t. FV(arith_prov1 A s t) = FVT(s) UNION FVT(t)]])
   (Definability.FV_TAC [arith_prov1, FV_AXIOM, FVT_NUMERAL, FVT_PAIR])
  : ExceptT String IO thm).run
#eval FV_PROV1

#eval phrase 63
unsafe def arith_prov : thm := keep "arith_prov" fun _ => new_definition
  [[arith_prov A n =
    formsubst ((0 |-> n) V)
        (arith_rtc (arith_prov1 A) (numeral 0)
                   (arith_pair (V 0) (numeral 0)))]]
#eval arith_prov

#eval phrase 64
unsafe def ARITH_PROV : thm := keep "ARITH_PROV" fun _ => (do
  prove ([[!Ax A. (!v t. holds v (A t) <=> Ax(termval v t))
          ==> !v n. holds v (arith_prov A n) <=> PROV Ax (termval v n)]])
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP ARITH_PROV1) THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP ARITH_RTC) THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV (fun t => pure (Session.ETA_CONV t))) THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [arith_prov, HOLDS_FORMSUBST] THEN
    REWRITE_TAC [termval, valmod, o_DEF, TERMVAL_NUMERAL, ARITH_PAIR] THEN
    REWRITE_TAC [PROV])
  : ExceptT String IO thm).run
#eval ARITH_PROV

#eval phrase 65
unsafe def FV_PROV : thm := keep "FV_PROV" fun _ => (do
  prove ([[(!t. FV(A t) = FVT t) ==> !t. FV(arith_prov A t) = FVT t]])
   (Definability.FV_TAC [arith_prov, FV_PROV1, FV_RTC, FVT_NUMERAL, FVT_PAIR])
  : ExceptT String IO thm).run
#eval FV_PROV

#eval phrase 66
unsafe def PROV_DEFINABLE : thm := keep "PROV_DEFINABLE" fun _ => (do
  let spc ← ExceptT.mk (HolLight.SPECL [ [[IMAGE gform Ax]], [[\t. formsubst ((x |-> t) V) A]] ]
               ARITH_PROV)
  prove ([[!Ax. definable {gform p | p IN Ax} ==> definable {gform p | Ax |-- p}]])
   (GEN_TAC THEN REWRITE_TAC [definable, IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[A:form]]) (X_CHOOSE_TAC ([[x:num]]))) THEN
    MP_TAC spc THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [HOLDS_FORMSUBST] THEN
      REWRITE_TAC [o_THM, VALMOD_BASIC, IMAGE, IN_ELIM_THM],
      ALL_TAC] THEN
    REWRITE_TAC [PROV_THM_STRONG] THEN DISCH_TAC THEN
    EXISTS_TAC [[arith_prov (\t. formsubst ((x |-> t) V) A) (V x)]] THEN
    ASM_REWRITE_TAC [termval] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval PROV_DEFINABLE

#eval phrase 67
unsafe def GODEL_CRUDE : thm := keep "GODEL_CRUDE" fun _ => (do
  prove ([[!Ax. definable {gform p | p IN Ax} ==> ?p. ~(arithtrue p <=> Ax |-- p)]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[(~c ==> (a <=> b)) ==> a ==> ~b ==> c]])
     pure
      (REPEAT STRIP_TAC THEN MP_TAC Tarski.TARSKI_THEOREM THEN
       FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP PROV_DEFINABLE) THEN
       MATCH_MP_TAC taut1 THEN
       SIMP_TAC [NOT_EXISTS_THM]))
  : ExceptT String IO thm).run
#eval GODEL_CRUDE

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.ArithProv" do
  replay (
          HolLogicArith.Tarski.ensure)
  replay (
          Session.prioritize_num)
  replay (
          ALLN_DEF)
  replay (
          ALLN)
  replay (
          TERM1)
  replay (
          TERM)
  replay (
          isagterm)
  replay (
          TERM_LEMMA1)
  replay (
          TERM_LEMMA2)
  replay (
          TERM_THM)
  replay (
          FORM1)
  replay (
          FORM)
  replay (
          isagform)
  replay (
          FORM_LEMMA1)
  replay (
          FORM_LEMMA2)
  replay (
          FORM_THM)
  replay (
          FREETERM1)
  replay (
          FREETERM)
  replay (
          isafterm)
  replay (
          ISAFTERM)
  replay (
          FREETERM_LEMMA1)
  replay (
          FREETERM_LEMMA2)
  replay (
          FREETERM_THM)
  replay (
          FREEFORM1)
  replay (
          FREEFORM)
  replay (
          isafform)
  replay (
          ISAFFORM)
  replay (
          FREEFORM_LEMMA1)
  replay (
          FREEFORM_LEMMA2)
  replay (
          FREEFORM_THM)
  replay (
          do IO.println AXIOM; IO.println AXIOM_THM)
  replay (
          GTERM_CASES_ALT)
  replay (
          GFORM_CASES_ALT)
  replay (
          AXIOM_FORMULA)
  replay (
          AXIOM_THM_STRONG)
  replay (
          PROV1)
  replay (
          PROV)
  replay (
          isaprove)
  replay (
          PROV_LEMMA1)
  replay (
          PROV_LEMMA2)
  replay (
          PROV_THM_STRONG)
  replay (
          PROV_THM)
  replay (
          do IO.println arith_term1; IO.println ARITH_TERM1)
  replay (
          FV_TERM1)
  replay (
          do IO.println arith_term; IO.println ARITH_TERM)
  replay (
          FV_TERM)
  replay (
          do IO.println arith_form1; IO.println ARITH_FORM1)
  replay (
          FV_FORM1)
  replay (
          do IO.println arith_form; IO.println ARITH_FORM)
  replay (
          FV_FORM)
  replay (
          do IO.println arith_freeterm1; IO.println ARITH_FREETERM1)
  replay (
          FV_FREETERM1)
  replay (
          do IO.println arith_freeterm; IO.println ARITH_FREETERM)
  replay (
          FV_FREETERM)
  replay (
          do IO.println arith_freeform1; IO.println ARITH_FREEFORM1)
  replay (
          FV_FREEFORM1)
  replay (
          do IO.println arith_freeform; IO.println ARITH_FREEFORM)
  replay (
          FV_FREEFORM)
  replay (
          do IO.println arith_axiom; IO.println ARITH_AXIOM)
  replay (
          FV_AXIOM)
  replay (
          do IO.println arith_prov1; IO.println ARITH_PROV1_obj)
  replay (
          ARITH_PROV1)
  replay (
          FV_PROV1)
  replay (
          arith_prov)
  replay (
          ARITH_PROV)
  replay (
          FV_PROV)
  replay (
          PROV_DEFINABLE)
  replay (
          GODEL_CRUDE)
-- @@ENSURE END

end HolLogicArith.ArithProv
