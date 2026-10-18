/- File: HolLogicArith/Unif.lean
Translation of HOL Light's Logic/unif.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Fole
open HolCore.Kernel Session HolLight.Syntax HolLogicArith
open scoped HolLight
open HolLogicArith.Fol
open HolLogicArith.Prenex
open HolLogicArith.Skolem
open HolLogicArith.FolProp
open HolLogicArith.Canon
open HolLogicArith.Fole
open SessionLibrary.RSTC
open HolExamples.MultiWf

namespace HolLogicArith.Unif

/- List definitions/theorems used below are exposed by Session as fields of
   the `listDefs`/`listThms1`/`listThms2` bundles; alias the ones we need. -/
private unsafe def HD : thm := Session.listDefs.HD
private unsafe def TL : thm := Session.listDefs.TL
private unsafe def LENGTH : thm := Session.listDefs.LENGTH
private unsafe def MAP : thm := Session.listDefs.MAP
private unsafe def ALL : thm := Session.listDefs.ALL
private unsafe def EX : thm := Session.listDefs.EX
private unsafe def ITLIST : thm := Session.listDefs.ITLIST
private unsafe def MEM : thm := Session.listDefs.MEM
private unsafe def EL : thm := Session.listDefs.EL
private unsafe def FILTER : thm := Session.listDefs.FILTER
private unsafe def ASSOC : thm := Session.listDefs.ASSOC
private unsafe def ZIP : thm := Session.listDefs.ZIP
private unsafe def APPEND : thm := Session.listDefs.APPEND
private unsafe def ALL2 : thm := Session.listDefs.ALL2
private unsafe def ALL2_DEF : thm := Session.listDefs.ALL2_DEF
private unsafe def MAP2 : thm := Session.listDefs.MAP2
private unsafe def MAP_EQ : thm := Session.listThms1.MAP_EQ
private unsafe def MAP_o : thm := Session.listThms1.MAP_o
private unsafe def LENGTH_MAP : thm := Session.listThms1.LENGTH_MAP
private unsafe def LENGTH_APPEND : thm := Session.listThms1.LENGTH_APPEND
private unsafe def MAP_APPEND : thm := Session.listThms1.MAP_APPEND
private unsafe def APPEND_NIL : thm := Session.listThms1.APPEND_NIL
private unsafe def APPEND_ASSOC : thm := Session.listThms1.APPEND_ASSOC
private unsafe def LENGTH_EQ_NIL : thm := Session.listThms1.LENGTH_EQ_NIL
private unsafe def CONS_11 : thm := Session.listThms1.CONS_11
private unsafe def NOT_CONS_NIL : thm := Session.listThms1.NOT_CONS_NIL
private unsafe def list_CASES : thm := Session.listThms1.list_CASES
private unsafe def ALL_T : thm := Session.listThms1.ALL_T
private unsafe def ALL_MAP : thm := Session.listThms1.ALL_MAP
private unsafe def ALL_IMP : thm := Session.listThms1.ALL_IMP
private unsafe def AND_ALL : thm := Session.listThms1.AND_ALL
private unsafe def EX_MAP : thm := Session.listThms1.EX_MAP
private unsafe def EX_MEM : thm := Session.listThms1.EX_MEM
private unsafe def EX_IMP : thm := Session.listThms1.EX_IMP
private unsafe def EXISTS_EX : thm := Session.listThms1.EXISTS_EX
private unsafe def ALL_MEM : thm := Session.listThms1.ALL_MEM
private unsafe def MEM_MAP : thm := Session.listThms1.MEM_MAP
private unsafe def MEM_APPEND : thm := Session.listThms1.MEM_APPEND
private unsafe def FILTER_APPEND : thm := Session.listThms1.FILTER_APPEND
private unsafe def FILTER_MAP : thm := Session.listThms1.FILTER_MAP
private unsafe def MEM_FILTER : thm := Session.listThms1.MEM_FILTER
private unsafe def MAP_FST_ZIP : thm := Session.listThms1.MAP_FST_ZIP
private unsafe def MAP_SND_ZIP : thm := Session.listThms1.MAP_SND_ZIP
private unsafe def MEM_ASSOC : thm := Session.listThms1.MEM_ASSOC
private unsafe def ALL_APPEND : thm := Session.listThms2.ALL_APPEND

#eval HolLogicArith.Fole.ensure

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- `new_recursive_definition` lifted into `ExceptT String IO`. -/
private unsafe def newRec (ax : thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (Session.new_recursive_definition ax tm)

/- `new_specification` lifted into `ExceptT String IO`. -/
private unsafe def newSpec (names : List String) (th : thm) : ExceptT String IO thm :=
  ExceptT.mk (Session.new_specification names th)

#eval phrase 1
unsafe def LEFT_AND_EX_THM : thm := keep "LEFT_AND_EX_THM" fun _ => (do
  prove ([[!P Q l. EX P l /\ Q <=> EX (\x. P x /\ Q) l]])
   (GEN_TAC THEN GEN_TAC THEN CONV_TAC (HolLight.ONCE_DEPTH_CONV HolLight.SYM_CONV) THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [EX] THEN CONV_TAC TAUT)
  : ExceptT String IO thm).run
#eval LEFT_AND_EX_THM

#eval phrase 2
unsafe def EX_ADHOC : thm := keep "EX_ADHOC" fun _ => (do
  prove ([[!l. (!x. ~(P x) ==> (Q x <=> R x)) ==> (~EX P l ==> (EX Q l <=> EX R l))]])
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [EX] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval EX_ADHOC

#eval phrase 3
unsafe def ALL_ADHOC : thm := keep "ALL_ADHOC" fun _ => (do
  prove ([[!l. ALL (\x. f x = g x) l ==> (EX f l <=> EX g l)]])
   (LIST_INDUCT_TAC THEN REWRITE_TAC [ALL, EX] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval ALL_ADHOC

#eval phrase 4
unsafe def WF_FINITE_LEMMA : thm := keep "WF_FINITE_LEMMA" fun _ => (do
  prove ([[!(<<) s. FINITE s /\
            (!x:A. ~(TC(<<) x x)) /\ (!x y. x << y ==> y IN s)
            ==> WF(<<)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [WF_DCHAIN] THEN
    DISCH_THEN (X_CHOOSE_TAC [[u:num->A]]) THEN
    SUBGOAL_THEN ([[!n. (u:num->A)(n) IN s]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    MP_TAC (← HolLight.ISPECL [ [[u:num->A]], [[s:A->bool]] ] FINITE_IMAGE_INJ) THEN
    REWRITE_TAC [ASSUME [[FINITE(s:A->bool)]], NOT_IMP] THEN
    SUBGOAL_THEN ([[{n | (u:num->A)(n) IN s} = UNIV:num->bool]]) SUBST1_TAC THENL
     [ASM_REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_UNIV], ALL_TAC] THEN
    REWRITE_TAC [num_INFINITE, (← HolLight.GSYM INFINITE)] THEN
    SUBGOAL_THEN ([[!m n. m < n ==> TC(<<) ((u:num->A) n) (u m)]])
     (fun th => ASM_MESON_TAC [th, LT_CASES]) THEN
    SIMP_TAC [LT_EXISTS, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC [[n:num]] THEN GEN_TAC THEN X_GEN_TAC [[d:num]] THEN
    DISCH_THEN ((HolCore.Lib.K ALL_TAC : thm → HolCore.Tactics.tactic)) THEN REWRITE_TAC [ADD_CLAUSES] THEN
    SUBGOAL_THEN ([[!d. RTC(<<) ((u:num->A)(n + d))(u n) ]]) MP_TAC THENL
     [INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, RTC_REFL] THEN
      ASM_MESON_TAC [RTC_TRANS, RTC_INC],
      REWRITE_TAC [RTC, RC_CASES] THEN ASM_MESON_TAC [TC_INC, TC_CASES_R]])
  : ExceptT String IO thm).run
#eval WF_FINITE_LEMMA

#eval phrase 5
unsafe def TC_REV : thm := keep "TC_REV" fun _ => (do
  prove ([[!x:A y. TC (\u v. R v u) x y <=> TC R y x]])
   (REWRITE_TAC [(← ExceptT.mk (TAUT [[(a <=> b) <=> (a ==> b) /\ (b ==> a)]])), FORALL_AND_THM] THEN
    CONJ_TAC THENL [ALL_TAC, ONCE_REWRITE_TAC [SWAP_FORALL_THM]] THEN
    MATCH_MP_TAC TC_INDUCT THEN SIMP_TAC [TC_INC] THEN MESON_TAC [TC_TRANS])
  : ExceptT String IO thm).run
#eval TC_REV

#eval phrase 6
unsafe def WF_DISJ : thm := keep "WF_DISJ" fun _ => (do
  let wf_tc_imp ← (do let (_, b) ← HolLight.EQ_IMP_RULE (← HolLight.SPEC_ALL WF_TC); pure b)
  prove ([[WF(R) /\ WF(\x y. ?z. S x z /\ RTC(R) z y) ==> WF(\x:A y. R x y \/ S x y)]])
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [WF] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC [[P:A->bool]] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> c) ==> (a ==> b) ==> (a ==> c)]])) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[a:A]]) STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP wf_tc_imp) THEN
    REWRITE_TAC [WF] THEN DISCH_THEN (MP_TAC o HolLight.SPEC [[\y:A. P(y) /\ TC R y a]]) THEN
    REWRITE_TAC [] THEN RULE_ASSUM_TAC (HolLight.REWRITE_RULE [RTC, RC_CASES]) THEN
    ASM_MESON_TAC [TC_INC, TC_TRANS])
  : ExceptT String IO thm).run
#eval WF_DISJ

#eval phrase 7
unsafe def WF_ALTERNATION : thm := keep "WF_ALTERNATION" fun _ => (do
  prove ([[WF(\x y. R x y \/ S x y) /\ (!x y z. ~(P x y /\ P y z))
   ==> WF(\(x1:A,y1) (x2,y2). S x1 x2 /\ S y1 y2 \/
                              R x1 x2 /\ (y1 = y2) \/
                              P x2 y2 /\ (x1 = y2) /\ (x2 = y1))]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [WF] THEN X_GEN_TAC [[s:A#A->bool]] THEN
    REWRITE_TAC [EXISTS_PAIR_THM] THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [WF]) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[\x:A. ?y:A. s(x,y) \/ s(y,x)]]) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[a:A]]) (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[b0:A]]) ASSUME_TAC) THEN
    REWRITE_TAC [FORALL_PAIR_THM] THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [ASM_CASES_TAC [[(P:A->A->bool) a b0]] THENL
       [ALL_TAC, ASM_MESON_TAC []] THEN
      ASM_CASES_TAC [[(s:A#A->bool)(b0,a)]] THENL
       [ALL_TAC,
        MAP_EVERY EXISTS_TAC [ [[a:A]], [[b0:A]] ] THEN
        ASM_REWRITE_TAC [] THEN ASM_MESON_TAC []] THEN
      ASM_CASES_TAC [[?y:A. R y (b0:A) /\ s(y,a:A)]] THENL
       [ALL_TAC,
        MAP_EVERY EXISTS_TAC [ [[b0:A]], [[a:A]] ] THEN ASM_REWRITE_TAC [] THEN
        ASM_MESON_TAC []] THEN
      FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [WF]) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[\y:A. s(y,a:A):bool]]) THEN
      REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[b:A]]) STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [ [[b:A]], [[a:A]] ] THEN ASM_MESON_TAC [],
      FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [WF]) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[\y:A. s(y,a:A):bool]]) THEN
      REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[b:A]]) STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC [[(P:A->A->bool) b a /\ s(a,b)]] THENL
       [MAP_EVERY EXISTS_TAC [ [[a:A]], [[b:A]] ],
        MAP_EVERY EXISTS_TAC [ [[b:A]], [[a:A]] ]] THEN
      ASM_REWRITE_TAC [] THEN ASM_MESON_TAC []])
  : ExceptT String IO thm).run
#eval WF_ALTERNATION

#eval phrase 8
unsafe def MULTISET_FILTEREQ : thm := keep "MULTISET_FILTEREQ" fun _ => (do
  prove ([[multiplicity (multiset (\x:A. LENGTH (FILTER ((=) x) l))) a =
        LENGTH (FILTER ((=) a) l)]])
   (MP_TAC (← HolLight.ISPEC ([[\x:A. LENGTH (FILTER ((=) x) l)]])
     (← HolLight.CONJUNCT2 multiset_tybij)) THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> c) /\ a ==> ((a <=> b) ==> c)]])) THEN
    SIMP_TAC [] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC [[{a:A | MEM a l}]] THEN CONJ_TAC THENL
     [SPEC_TAC ([[l:(A)list]], [[l:(A)list]]) THEN LIST_INDUCT_TAC THENL
       [SUBGOAL_THEN ([[{a:A | MEM a []} = EMPTY]])
          (fun th => REWRITE_TAC [th, FINITE_RULES]) THEN
        REWRITE_TAC [EXTENSION, IN_ELIM_THM, MEM, NOT_IN_EMPTY],
        SUBGOAL_THEN ([[{a:A | MEM a (CONS h t)} = h INSERT {a | MEM a t}]])
          (fun th => ASM_SIMP_TAC [th, FINITE_RULES]) THEN
        REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT, MEM] THEN
        REWRITE_TAC [DISJ_ACI]],
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
      SPEC_TAC ([[l:(A)list]], [[l:(A)list]]) THEN LIST_INDUCT_TAC THEN
      REWRITE_TAC [FILTER, LENGTH, MEM] THEN GEN_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [LENGTH, MEM]])
  : ExceptT String IO thm).run
#eval MULTISET_FILTEREQ

#eval phrase 9
unsafe def WF_MULTIZIP : thm := keep "WF_MULTIZIP" fun _ => (do
  let tyAlist ← ExceptT.mk (HolCore.Parser.parse_type "(A)list")
  let lemma ← HolLight.INST_TYPE [(tyAlist, mk_vartype "A")] WF_MEASURE_GEN
  prove ([[WF(R)
   ==> WF(\l1 l2. ?h:A t l0.
             (l2 = CONS h t) /\ (l1 = APPEND l0 t) /\
             (!k. MEM k l0 ==> R k h))]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC [[\l. multiset(\x:A. LENGTH (FILTER ((=) x) l))]] o
                        HolLight.MATCH_MP lemma o HolLight.MATCH_MP MORDER_WF) THEN
    REWRITE_TAC [] THEN
    MATCH_MP_TAC (← HolLight.ONCE_REWRITE_RULE [IMP_CONJ] WF_SUBSET) THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC [morder, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[a:A]], [[l:(A)list]], [[m:(A)list]] ] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN DISCH_TAC THEN
    EXISTS_TAC [[multiset(\x:A. LENGTH (FILTER ((=) x) l))]] THEN
    EXISTS_TAC [[a:A]] THEN
    EXISTS_TAC [[multiset(\x:A. LENGTH (FILTER ((=) x) m))]] THEN
    REWRITE_TAC [mmember, MEXTENSION, MULTISET_FILTEREQ, MUNION, MSING] THEN
    REWRITE_TAC [FILTER_APPEND, LENGTH_APPEND, LENGTH, FILTER, ADD_AC] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC [LENGTH, ADD1, ADD_AC, ADD_CLAUSES], ALL_TAC] THEN
    SUBGOAL_THEN ([[!a:A l. ~(LENGTH (FILTER ((=) a) l) = 0) ==> MEM a l]])
     (fun th => ASM_MESON_TAC [th]) THEN
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [FILTER, LENGTH, MEM] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [LENGTH, MEM])
  : ExceptT String IO thm).run
#eval WF_MULTIZIP

#eval phrase 10
unsafe def WF_MEASURE_OR_NONINC : thm := keep "WF_MEASURE_OR_NONINC" fun _ => (do
  prove ([[!R (m:A->num).
        WF(R) /\ (!x y. R x y ==> m x <= m y)
        ==> WF(\x y. MEASURE m x y \/ R x y)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [WF] THEN
    X_GEN_TAC [[P:A->bool]] THEN DISCH_TAC THEN
    MP_TAC (← HolLight.ISPEC ([[m:A->num]]) WF_MEASURE) THEN REWRITE_TAC [WF, MEASURE] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[P:A->bool]]) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[a:A]]) STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC [[?y. (R:A->A->bool) y a /\ P y]] THENL
     [ALL_TAC, ASM_MESON_TAC []] THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC [[\y. TC (R:A->A->bool) y a /\ P y]] o
                HolLight.GEN_REWRITE_RULE HolCore.Lib.I [WF]) THEN
    ASM_REWRITE_TAC [] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [TC_INC], ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[b:A]] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[(m:A->num)(b) <= m(a)]])
     (fun th => ASM_MESON_TAC [th, TC_INC, TC_TRANS, LTE_TRANS]) THEN
    UNDISCH_TAC [[TC R b (a:A)]] THEN
    MAP_EVERY SPEC_TAC [([[a:A]], [[a:A]]), ([[b:A]], [[b:A]])] THEN
    MATCH_MP_TAC TC_INDUCT THEN ASM_REWRITE_TAC [LE_TRANS])
  : ExceptT String IO thm).run
#eval WF_MEASURE_OR_NONINC

#eval phrase 11
unsafe def WF_PROJ_EQ : thm := keep "WF_PROJ_EQ" fun _ => (do
  prove ([[(!x. P x ==> WF(R x))
   ==> WF(\(x',y') (x:A,y:B). P(x) /\ (x' = x) /\ R x y' y)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [WF_DCHAIN] THEN
    DISCH_THEN (X_CHOOSE_TAC [[s:num->A#B]]) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[FST((s:num->A#B) 0)]]) THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC [[0]]) THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[(s:num->A#B) 0]]) PAIR)) THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[(s:num->A#B) (SUC 0)]]) PAIR)) THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    DISCH_THEN (fun th => HolLight.tactic_of do pure (REWRITE_TAC [(← HolLight.CONJUNCT1 th)])) THEN
    REWRITE_TAC [WF_DCHAIN] THEN
    EXISTS_TAC [[SND o (s:num->A#B)]] THEN
    X_GEN_TAC [[n:num]] THEN REWRITE_TAC [o_THM] THEN
    SUBGOAL_THEN ([[FST((s:num->A#B) 0) = FST(s n)]]) SUBST1_TAC THENL
     [SPEC_TAC ([[n:num]], [[n:num]]) THEN INDUCT_TAC THEN REWRITE_TAC [] THEN
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC [[FST((s:num->A#B) n)]] THEN
      ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[n:num]]) THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[(s:num->A#B) n]]) PAIR)) THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[(s:num->A#B) (SUC n)]]) PAIR)) THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV GEN_BETA_CONV) THEN SIMP_TAC [FST, SND])
  : ExceptT String IO thm).run
#eval WF_PROJ_EQ


#eval phrase 12
unsafe def OCC : thm := keep "OCC" fun _ => new_definition
  [[OCC env (x:num) y <=> ?t. MEM (x,t) env /\ y IN FVT(t)]]
#eval OCC

#eval phrase 13
unsafe def LOOPFREE : thm := keep "LOOPFREE" fun _ => new_definition
  [[LOOPFREE env <=> !z. ~(TC (OCC env) z z)]]
#eval LOOPFREE

#eval phrase 14
unsafe def LOOP_BREAK : thm := keep "LOOP_BREAK" fun _ => (do
  prove ([[!env x t u v.
        TC(OCC (CONS (x,t) env)) u v /\ ~(TC(OCC env) u v)
        ==> ?y. RTC(OCC env) u x /\ y IN FVT(t) /\ RTC(OCC env) y v]])
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    REWRITE_TAC [(← ExceptT.mk (TAUT [[a /\ ~b ==> c <=> a ==> ~b ==> c]]))] THEN
    MATCH_MP_TAC TC_INDUCT_L THEN REPEAT STRIP_TAC THENL
     [UNDISCH_TAC [[OCC (CONS (x,t) env) u v]] THEN
      REWRITE_TAC [OCC, MEM, PAIR_EQ] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[s:term]]) STRIP_ASSUME_TAC) THENL
       [ASM_MESON_TAC [RTC_CASES], ALL_TAC] THEN
      UNDISCH_TAC [[~TC (OCC env) u v]] THEN
      ONCE_REWRITE_TAC [TC_CASES_L] THEN REWRITE_TAC [OCC] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    ASM_CASES_TAC [[TC (OCC env) u v]] THENL
     [UNDISCH_TAC [[OCC (CONS (x,t) env) v z]] THEN
      REWRITE_TAC [OCC, MEM, PAIR_EQ] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[s:term]]) STRIP_ASSUME_TAC) THENL
       [REWRITE_TAC [RTC, RC_CASES] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      UNDISCH_TAC [[~TC (OCC env) u z]] THEN
       MATCH_MP_TAC (← ExceptT.mk (TAUT [[a ==> ~a ==> b]])) THEN
      ONCE_REWRITE_TAC [TC_CASES_L] THEN DISJ2_TAC THEN
      REWRITE_TAC [OCC] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
      let tm ← liftExcept (HolCore.Lib.check HolCore.Basics.is_imp (concl th))
      pure (UNDISCH_TAC tm)) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[y:num]]) STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [] THEN UNDISCH_TAC [[OCC (CONS (x,t) env) v z]] THEN
    REWRITE_TAC [OCC, MEM, PAIR_EQ] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[s:term]]) STRIP_ASSUME_TAC) THENL
     [REWRITE_TAC [RTC, RC_CASES] THEN ASM_MESON_TAC [],
      ASM_MESON_TAC [RTC_CASES_L, OCC]])
  : ExceptT String IO thm).run
#eval LOOP_BREAK

#eval phrase 15
unsafe def LOOPFREE_PRESERVE : thm := keep "LOOPFREE_PRESERVE" fun _ => (do
  prove ([[LOOPFREE env /\ ~(?y. y IN FVT(t) /\ RTC (OCC env) y x)
   ==> LOOPFREE (CONS (x,t) env)]])
   (MESON_TAC [LOOPFREE, RTC_CASES, LOOP_BREAK])
  : ExceptT String IO thm).run
#eval LOOPFREE_PRESERVE

#eval phrase 16
unsafe def LOOPFREE_PRESERVE_EQ : thm := keep "LOOPFREE_PRESERVE_EQ" fun _ => (do
  prove ([[LOOPFREE env
   ==> (LOOPFREE (CONS (x,t) env) = ~(?y. y IN FVT(t) /\ RTC (OCC env) y x))]])
   (MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a /\ ~c ==> b) /\ (c ==> ~b) ==> (a ==> (b <=> ~c))]])) THEN
    REWRITE_TAC [LOOPFREE_PRESERVE] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[y:num]]) STRIP_ASSUME_TAC) THEN
    REWRITE_TAC [LOOPFREE] THEN DISCH_THEN (MP_TAC o HolLight.SPEC [[x:num]]) THEN
    REWRITE_TAC [] THEN ONCE_REWRITE_TAC [TC_RTC_CASES_R] THEN
    EXISTS_TAC [[y:num]] THEN REWRITE_TAC [OCC, MEM, PAIR_EQ] THEN CONJ_TAC THENL
     [EXISTS_TAC [[t:term]] THEN ASM_REWRITE_TAC [],
      UNDISCH_TAC [[RTC (OCC env) y x]] THEN
      MATCH_MP_TAC (← HolLight.REWRITE_RULE [RIGHT_IMP_FORALL_THM] RTC_MONO) THEN
      SIMP_TAC [OCC, MEM, PAIR_EQ] THEN MESON_TAC []])
  : ExceptT String IO thm).run
#eval LOOPFREE_PRESERVE_EQ

#eval phrase 17
unsafe def LOOPFREE_WF : thm := keep "LOOPFREE_WF" fun _ => (do
  prove ([[!env. LOOPFREE env ==> WF(\x y. OCC env y x)]])
   (REWRITE_TAC [LOOPFREE] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC WF_FINITE_LEMMA THEN
    EXISTS_TAC [[set_of_list (MAP FST (env:(num#term)list))]] THEN
    ASM_REWRITE_TAC [FINITE_SET_OF_LIST] THEN
    ONCE_REWRITE_TAC [TC_REV] THEN
    CONV_TAC (HolLight.DEPTH_CONV (fun t => pure (ETA_CONV t))) THEN ASM_REWRITE_TAC [OCC] THEN
    SPEC_TAC ([[env:(num#term)list]], [[env:(num#term)list]]) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [MAP, set_of_list, MEM, IN_INSERT] THEN
    ASM_MESON_TAC [FST])
  : ExceptT String IO thm).run
#eval LOOPFREE_WF

#eval phrase 18
unsafe def LOOPFREE_WF_TERM : thm := keep "LOOPFREE_WF_TERM" fun _ => (do
  prove ([[!env. LOOPFREE(env) ==> WF(\s t. ?y. y IN FVT(t) /\ MEM (y,s) env)]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP LOOPFREE_WF) THEN
    REWRITE_TAC [WF_DCHAIN, OCC, (← ExceptT.mk (TAUT [[~a ==> ~b <=> b ==> a]])), SKOLEM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[s:num->term]]) (X_CHOOSE_THEN ([[x:num->num]])
          STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [ [[x:num->num]], [[\n. s(SUC n):term]] ] THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval LOOPFREE_WF_TERM

#eval phrase 19
unsafe def LOOPCHECK_EXISTS : thm := keep "LOOPCHECK_EXISTS" fun _ => (do
  prove ([[!env x.
     LOOPFREE(env)
     ==> ?loopcheck. !t.
               loopcheck t <=>
                  ?y. y IN FVT(t) /\
                            ((y = x) \/ ?s. MEM (y,s) env /\ loopcheck s)]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP WF_REC o HolLight.MATCH_MP LOOPFREE_WF_TERM) THEN
    REWRITE_TAC [] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval LOOPCHECK_EXISTS

#eval phrase 20
unsafe def loopcheck_raw : thm := keep "loopcheck_raw" fun _ => (do
  newSpec ["loopcheck"]
   (← HolLight.REWRITE_RULE [SKOLEM_THM, RIGHT_IMP_EXISTS_THM] LOOPCHECK_EXISTS)
  : ExceptT String IO thm).run
#eval loopcheck_raw

#eval phrase 21
unsafe def loopcheck : thm := keep "loopcheck" fun _ => (do
  prove ([[!env x.
        LOOPFREE(env)
        ==> (!x y. loopcheck env x (V y) <=>
                   (y = x) \/ ?s. MEM (y,s) env /\ loopcheck env x s) /\
            (!f args. loopcheck env x (Fn f args) <=>
                   EX (loopcheck env x) args)]])
   (REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th => HolLight.tactic_of do
       pure (GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.MATCH_MP loopcheck_raw th)])) THEN
    REWRITE_TAC [FVT, IN_INSERT, NOT_IN_EMPTY, UNWIND_THM2, IN_LIST_UNION] THEN
    REWRITE_TAC [LEFT_AND_EX_THM, EXISTS_EX, EX_MAP, o_THM] THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
       pure (REWRITE_TAC [(← HolLight.GSYM (← HolLight.MATCH_MP loopcheck_raw th))])) THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (ETA_CONV t))) THEN REFL_TAC)
  : ExceptT String IO thm).run
#eval loopcheck

#eval phrase 22
unsafe def LOOPCHECK : thm := keep "LOOPCHECK" fun _ => (do
  prove ([[!env x t. LOOPFREE(env)
             ==> (loopcheck env x t <=> ~LOOPFREE (CONS (x,t) env))]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC [[?y. y IN FVT t /\ RTC (OCC env) y x]] THEN
    ASM_SIMP_TAC [LOOPFREE_PRESERVE_EQ] THEN SPEC_TAC ([[t:term]], [[t:term]]) THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP LOOPFREE_WF_TERM) THEN
    REWRITE_TAC [WF_IND] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC [[t:term]] THEN DISCH_TAC THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
       pure (ONCE_REWRITE_TAC [(← HolLight.MATCH_MP loopcheck_raw th)])) THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)]])) THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC [RTC_CASES_R] THEN
    ASM_CASES_TAC [[x:num = y]] THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [OCC, LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC), RIGHT_EXISTS_AND_THM] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)]])) THEN
    DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC [[y:num]] THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval LOOPCHECK

#eval phrase 23
unsafe def rightsubst : thm := keep "rightsubst" fun _ => new_definition
  [[rightsubst (x,t) (y:num,s) =
     y,termsubst (\z. if z = x then t else V(z)) s]]
#eval rightsubst

#eval phrase 24
unsafe def SOLVE_EXISTS : thm := keep "SOLVE_EXISTS" fun _ => (do
  let lemma ← (do
    prove ([[(if b then x else y) = (if ~b then y else x)]])
     (BOOL_CASES_TAC [[b:bool]] THEN REWRITE_TAC [])
    : ExceptT String IO thm)
  prove ([[?SOLVE. !pr. SOLVE pr =
                  if SND pr = [] then FST pr
                  else SOLVE (CONS (HD(SND pr))
                                   (MAP (rightsubst (HD(SND pr))) (FST pr)),
                              MAP (rightsubst (HD(SND pr))) (TL(SND pr)))]])
   (ONCE_REWRITE_TAC [lemma] THEN REWRITE_TAC [WF_REC_TAIL])
  : ExceptT String IO thm).run
#eval SOLVE_EXISTS

#eval phrase 25
unsafe def SOLVEC_RAW : thm := keep "SOLVEC_RAW" fun _ => (do
  newSpec ["SOLVEC"] SOLVE_EXISTS
  : ExceptT String IO thm).run
#eval SOLVEC_RAW

#eval phrase 26
unsafe def SOLVE_1 : thm := keep "SOLVE_1" fun _ => new_definition
  [[SOLVE sol uns = SOLVEC (sol,uns)]]
#eval SOLVE_1

#eval phrase 27
unsafe def SOLVE : thm := keep "SOLVE" fun _ => (do
  prove ([[(!sol. SOLVE sol [] = sol) /\
   (!sol p oth. SOLVE sol (CONS p oth) =
                SOLVE (CONS p (MAP (rightsubst p) sol))
                      (MAP (rightsubst p) oth))]])
   (REWRITE_TAC [SOLVE_1] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [SOLVEC_RAW] THEN
    REWRITE_TAC [NOT_CONS_NIL, HD, TL])
  : ExceptT String IO thm).run
#eval SOLVE


#eval phrase 28
unsafe def CONFLICTFREE : thm := keep "CONFLICTFREE" fun _ => new_definition
  [[CONFLICTFREE l <=> !x. LENGTH (FILTER (\(y:num,s:term). y = x) l) <= 1]]
#eval CONFLICTFREE

#eval phrase 29
unsafe def SOLVE_PRESERVES_LOOPFREE_LEMMA : thm := keep "SOLVE_PRESERVES_LOOPFREE_LEMMA" fun _ => (do
  prove ([[!p oth x y.
        TC(OCC (MAP (rightsubst p) oth)) x y ==> TC(OCC (CONS p oth)) x y]])
   (ONCE_REWRITE_TAC [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[x:num]], [[t:term]], [[oth:(num#term)list]] ] THEN
    GEN_REWRITE_TAC (HolCore.Lib.funpow 2 HolLight.BINDER_CONV o HolLight.RAND_CONV o HolCore.Lib.funpow 2 HolLight.RATOR_CONV)
      [(← HolLight.GSYM TC_IDEMP)] THEN
    MATCH_MP_TAC TC_MONO THEN MAP_EVERY X_GEN_TAC [ [[u:num]], [[v:num]] ] THEN
    REWRITE_TAC [OCC, MEM_MAP, EXISTS_PAIR_THM, rightsubst, PAIR_EQ] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM, LEFT_AND_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[p:term]], [[y:num]], [[s:term]] ] THEN STRIP_TAC THEN
    UNDISCH_TAC [[v IN FVT p]] THEN ASM_REWRITE_TAC [TERMSUBST_FVT] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN DISCH_THEN (X_CHOOSE_THEN ([[z:num]]) MP_TAC) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [FVT, IN_INSERT, NOT_IN_EMPTY] THENL
     [STRIP_TAC THEN MATCH_MP_TAC TC_TRANS THEN EXISTS_TAC [[x:num]] THEN CONJ_TAC,
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)] THEN
    MATCH_MP_TAC TC_INC THEN REWRITE_TAC [OCC] THEN ASM_MESON_TAC [MEM])
  : ExceptT String IO thm).run
#eval SOLVE_PRESERVES_LOOPFREE_LEMMA

#eval phrase 30
unsafe def SOLVE_PRESERVES_LOOPFREE : thm := keep "SOLVE_PRESERVES_LOOPFREE" fun _ => (do
  prove ([[!p oth. LOOPFREE(CONS p oth) ==> LOOPFREE(MAP (rightsubst p) oth)]])
   (REWRITE_TAC [LOOPFREE] THEN MESON_TAC [SOLVE_PRESERVES_LOOPFREE_LEMMA])
  : ExceptT String IO thm).run
#eval SOLVE_PRESERVES_LOOPFREE

#eval phrase 31
unsafe def SOLVE_PRESERVES_CONFLICTFREE_LEMMA : thm := keep "SOLVE_PRESERVES_CONFLICTFREE_LEMMA" fun _ => (do
  prove ([[!p x. (\(y,s). y = x) o rightsubst p = (\(y,s). y = x)]])
   (REWRITE_TAC [FUN_EQ_THM, o_THM, FORALL_PAIR_THM, rightsubst] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC [EQ_SYM])
  : ExceptT String IO thm).run
#eval SOLVE_PRESERVES_CONFLICTFREE_LEMMA

#eval phrase 32
unsafe def SOLVE_PRESERVES_CONFLICTFREE : thm := keep "SOLVE_PRESERVES_CONFLICTFREE" fun _ => (do
  prove ([[CONFLICTFREE(APPEND sol (CONS p oth))
   ==> CONFLICTFREE(APPEND (CONS p (MAP (rightsubst p) sol))
                           (MAP (rightsubst p) oth))]])
   (REWRITE_TAC [CONFLICTFREE, FILTER_APPEND, FILTER, LENGTH_APPEND,
                FILTER_MAP, LENGTH_MAP] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [LENGTH, LENGTH_MAP] THEN
    REWRITE_TAC [SOLVE_PRESERVES_CONFLICTFREE_LEMMA] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval SOLVE_PRESERVES_CONFLICTFREE

#eval phrase 33
unsafe def SOLVE_PRESERVES_DEFREE : thm := keep "SOLVE_PRESERVES_DEFREE" fun _ => (do
  prove ([[LOOPFREE(CONS p oth) /\
   (!x y s t. MEM (x,t) sol /\ MEM (y,s) (APPEND sol (CONS p oth))
              ==> ~(x IN FVT(s)))
   ==> (!x y s t. MEM (x,t) (CONS p (MAP (rightsubst p) sol)) /\
                  MEM (y,s) (APPEND (CONS p (MAP (rightsubst p) sol))
                                    (MAP (rightsubst p) oth))
                  ==> ~(x IN FVT(s)))]])
   (ONCE_REWRITE_TAC [(← HolLight.GSYM LEFT_IMP_EXISTS_THM)] THEN
    REWRITE_TAC [(← HolLight.GSYM LEFT_AND_EXISTS_THM)] THEN
    SUBGOAL_THEN ([[!x. (?t. MEM (x,t) (CONS p (MAP (rightsubst p) sol))) <=>
                    (?t. MEM (x,t) (CONS p sol))]])
      (fun th => REWRITE_TAC [th])
    THENL
     [GEN_TAC THEN REWRITE_TAC [MEM, EXISTS_OR_THM] THEN AP_TERM_TAC THEN
      REWRITE_TAC [MEM_MAP, EXISTS_PAIR_THM] THEN
      SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[p:num#term]]) PAIR)) THEN
      PURE_REWRITE_TAC [rightsubst, PAIR_EQ] THEN MESON_TAC [], ALL_TAC] THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
    STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC [MEM] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    DISCH_THEN (DISJ_CASES_THEN2 (SUBST_ALL_TAC oTIO HolLight.SYM) ASSUME_TAC) THENL
     [UNDISCH_TAC
       [[MEM (y,s)
         (APPEND (CONS (x,t) (MAP (rightsubst (x,t)) sol))
         (MAP (rightsubst (x,t)) oth))]] THEN
      REWRITE_TAC [APPEND, (← HolLight.GSYM MAP_APPEND)] THEN
      REWRITE_TAC [MEM, MEM_MAP, PAIR_EQ] THEN
      DISCH_THEN (DISJ_CASES_THEN2 (CONJUNCTS_THEN SUBST1_TAC) MP_TAC) THENL
       [ALL_TAC,
        REWRITE_TAC [LEFT_IMP_EXISTS_THM, FORALL_PAIR_THM] THEN
        SIMP_TAC [PAIR_EQ, rightsubst, TERMSUBST_FVT] THEN
        REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[z:num]]) (MP_TAC o HolLight.CONJUNCT2)) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [FVT, IN_INSERT, NOT_IN_EMPTY]] THEN
      UNDISCH_TAC [[LOOPFREE (CONS (x,t) oth)]] THEN REWRITE_TAC [LOOPFREE] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[x:num]]) THEN
      REWRITE_TAC [(← ExceptT.mk (TAUT [[~a ==> ~b <=> b ==> a]]))] THEN DISCH_TAC THEN
      MATCH_MP_TAC TC_INC THEN REWRITE_TAC [OCC] THEN
      EXISTS_TAC [[t:term]] THEN ASM_REWRITE_TAC [MEM], ALL_TAC] THEN
    UNDISCH_TAC
     [[MEM (y,s)
        (APPEND (CONS p (MAP (rightsubst p) sol))
                (MAP (rightsubst p) oth))]] THEN
    REWRITE_TAC [APPEND, MEM] THEN
    DISCH_THEN (DISJ_CASES_THEN2 (SUBST_ALL_TAC oTIO HolLight.SYM) MP_TAC) THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [MEM, APPEND, MEM_APPEND] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM MAP_APPEND), MEM_MAP, LEFT_IMP_EXISTS_THM,
                FORALL_PAIR_THM] THEN
    SUBST_ALL_TAC (← HolLight.SYM (← HolLight.ISPEC ([[p:num#term]]) PAIR)) THEN
    REWRITE_TAC [rightsubst, PAIR_EQ] THEN GEN_TAC THEN X_GEN_TAC [[u:term]] THEN
    MAP_EVERY ABBREV_TAC [ [[z = FST(p:num#term)]], [[r = SND(p:num#term)]] ] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (SUBST_ALL_TAC oTIO HolLight.SYM) SUBST1_TAC) THEN
    REWRITE_TAC [TERMSUBST_FVT, IN_ELIM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[w:num]]) MP_TAC) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [FVT, IN_INSERT, NOT_IN_EMPTY] THENL
     [ALL_TAC,
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (SUBST_ALL_TAC oTIO HolLight.SYM))] THEN
    ASM_MESON_TAC [MEM_APPEND, MEM])
  : ExceptT String IO thm).run
#eval SOLVE_PRESERVES_DEFREE

#eval phrase 34
unsafe def SOLVE_PRESERVES_UNIFIERS : thm := keep "SOLVE_PRESERVES_UNIFIERS" fun _ => (do
  let lemma ← (do
    prove ([[(!x t y s. P y s /\ (x = y) /\ (t = f s) ==> Q x t) <=>
     (!x t s. P x s ==> Q x (f s))]])
     (MESON_TAC [])
    : ExceptT String IO thm)
  prove ([[(!x t. MEM (x,t) (APPEND sol (CONS p oth))
          ==> (i(x) = termsubst i t)) <=>
   (!x t. MEM (x,t) (APPEND (CONS p (MAP (rightsubst p) sol))
                            (MAP (rightsubst p) oth))
          ==> (i(x) = termsubst i t))]])
   (REWRITE_TAC [MEM_APPEND, MEM] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV)
     [(← ExceptT.mk (TAUT [[a \/ b \/ c <=> b \/ a \/ c]]))] THEN
    REWRITE_TAC [(← HolLight.GSYM DISJ_ASSOC), (← HolLight.GSYM MEM_APPEND), (← HolLight.GSYM MAP_APPEND)] THEN
    SPEC_TAC ([[APPEND sol (oth:(num#term)list)]], [[l:(num#term)list]]) THEN
    GEN_TAC THEN REWRITE_TAC [(← ExceptT.mk (TAUT [[a \/ b ==> c <=> (a ==> c) /\ (b ==> c)]]))] THEN
    REWRITE_TAC [FORALL_AND_THM] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)]])) THEN
    SPEC_TAC ([[p:num#term]], [[p:num#term]]) THEN REWRITE_TAC [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[y:num]], [[s:term]] ] THEN
    SIMP_TAC [PAIR_EQ, (← HolLight.GSYM LEFT_IMP_EXISTS_THM)] THEN
    REWRITE_TAC [RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM, EXISTS_REFL] THEN
    DISCH_TAC THEN SIMP_TAC [MEM_MAP, LEFT_IMP_EXISTS_THM, FORALL_PAIR_THM] THEN
    REWRITE_TAC [rightsubst, PAIR_EQ, lemma] THEN
    REWRITE_TAC [TERMSUBST_TERMSUBST, o_DEF] THEN
    SUBGOAL_THEN ([[(\x. termsubst i (if x = y then s else V x)) = i]])
     (fun th => REWRITE_TAC [th]) THEN
    REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [termsubst])
  : ExceptT String IO thm).run
#eval SOLVE_PRESERVES_UNIFIERS

#eval phrase 35
unsafe def SOLVE_WORKS_GENERAL : thm := keep "SOLVE_WORKS_GENERAL" fun _ => (do
  prove ([[!n env sol. (LENGTH env = n) /\
               LOOPFREE(env) /\
               CONFLICTFREE(APPEND sol env) /\
               (!x y s t. MEM (x,t) sol /\ MEM (y,s) (APPEND sol env)
                          ==> ~(x IN FVT(s)))
               ==> CONFLICTFREE(SOLVE sol env) /\
                   (!i. (!x t. MEM (x,t) (APPEND sol env)
                               ==> (i x = termsubst i t)) <=>
                        (!x t. MEM (x,t) (SOLVE sol env)
                               ==> (i x = termsubst i t))) /\
                   !x y s t. MEM (x,t) (SOLVE sol env) /\
                             MEM (y,s) (SOLVE sol env)
                             ==> ~(x IN FVT(s))]])
   (INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH, NOT_SUC] THENL
     [SIMP_TAC [SOLVE, APPEND_NIL] THEN MESON_TAC [], ALL_TAC] THEN
    REWRITE_TAC [SUC_INJ, SOLVE] THEN X_GEN_TAC [[sol:(num#term)list]] THEN
    FIRST_X_ASSUM (fun th => HolLight.tactic_of do
      let c := concl th
      let t1 ← liftExcept (HolCore.Basics.dest_forall c)
      let _ ← liftExcept (HolCore.Lib.check HolCore.Basics.is_imp t1.2)
      pure ((HolCore.Lib.K ALL_TAC : thm → HolCore.Tactics.tactic) th)) THEN
    REWRITE_TAC [SOLVE_PRESERVES_UNIFIERS] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC [LENGTH_MAP, SOLVE_PRESERVES_LOOPFREE,
                 SOLVE_PRESERVES_CONFLICTFREE] THEN
    MATCH_MP_TAC SOLVE_PRESERVES_DEFREE THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval SOLVE_WORKS_GENERAL

#eval phrase 36
unsafe def SOLVE_WORKS : thm := keep "SOLVE_WORKS" fun _ => (do
  prove ([[!env.
        LOOPFREE(env) /\ CONFLICTFREE(env)
        ==> CONFLICTFREE(SOLVE [] env) /\
            (!i. (!x t. MEM (x,t) env ==> (i x = termsubst i t)) <=>
                 (!x t. MEM (x,t) (SOLVE [] env) ==> (i x = termsubst i t))) /\
            !x y s t. MEM (x,t) (SOLVE [] env) /\ MEM (y,s) (SOLVE [] env)
                      ==> ~(x IN FVT s)]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[!x:num t:term. MEM (x,t) env = MEM (x,t) (APPEND [] env)]])
     (fun th => REWRITE_TAC [th]) THENL [REWRITE_TAC [APPEND], ALL_TAC] THEN
    MATCH_MP_TAC SOLVE_WORKS_GENERAL THEN
    ASM_REWRITE_TAC [MEM, APPEND, (← HolLight.GSYM EXISTS_REFL)])
  : ExceptT String IO thm).run
#eval SOLVE_WORKS

#eval phrase 37
unsafe def retval_INDUCT_retval_RECURSION : thm × thm := keep "retval_types" fun _ =>
  match unsafeIO (define_type
    "retval = TT | FF | Exception") with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
unsafe def retval_INDUCT : thm := retval_INDUCT_retval_RECURSION.1
unsafe def retval_RECURSION : thm := retval_INDUCT_retval_RECURSION.2
#eval (do IO.println (← HolCore.Printer.string_of_thm retval_INDUCT)
          IO.println (← HolCore.Printer.string_of_thm retval_RECURSION) : IO Unit)

#eval phrase 38
unsafe def retval_DISTINCT : thm := keep "retval_DISTINCT" fun _ =>
  (ExceptT.mk (Session.prove_constructors_distinct retval_RECURSION) : ExceptT String IO thm).run
#eval retval_DISTINCT

#eval phrase 39
unsafe def ISTRIV_EXISTS : thm := keep "ISTRIV_EXISTS" fun _ => (do
  prove ([[!env x. LOOPFREE(env) /\ CONFLICTFREE(env)
     ==> ?istriv. !t. istriv t =
     if t = V x then TT
     else if ?y. (t = V y) /\ MEM y (MAP FST env)
          then istriv (ASSOC (@y. (t = V y) /\ MEM y (MAP FST env)) env)
     else if x IN FVT(t) then Exception
     else if ?y s. y IN FVT(t) /\ MEM (y,s) env /\ ~(istriv s = FF)
          then Exception else FF]])
   (REWRITE_TAC [CONFLICTFREE] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP WF_REC o HolLight.MATCH_MP LOOPFREE_WF_TERM) THEN
    REWRITE_TAC [] THEN REPEAT STRIP_TAC THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    TRY (HolLight.ASM (fun l => Session.GEN_MESON_TAC 0 10 1 l) []) THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN ([[z:num]]) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC [[z:num]] THEN ASM_REWRITE_TAC [FVT, IN_INSERT, term_INJ] THEN
    SUBGOAL_THEN ([[(@y. (z = y) /\ MEM y (MAP FST (env:(num#term)list))) = z]])
    SUBST1_TAC THENL
      [MATCH_MP_TAC SELECT_UNIQUE THEN
       X_GEN_TAC [[w:num]] THEN REWRITE_TAC [] THEN EQ_TAC THEN
       ASM_SIMP_TAC [], ALL_TAC] THEN
    UNDISCH_TAC [[MEM z (MAP FST (env:(num#term)list))]] THEN
    UNDISCH_TAC [[!x. LENGTH (FILTER (\(y:num,s:term). y = x) env) <= 1]] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[z:num]]) THEN
    SPEC_TAC ([[env:(num#term)list]], [[env:(num#term)list]]) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [MAP, MEM, ASSOC, FILTER] THEN
    SPEC_TAC ([[h:num#term]], [[h:num#term]]) THEN
    ONCE_REWRITE_TAC [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[y:num]], [[s:term]] ] THEN
    REWRITE_TAC [FST, SND] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    ASM_CASES_TAC [[y:num = z]] THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval ISTRIV_EXISTS

#eval phrase 40
unsafe def istriv_raw : thm := keep "istriv_raw" fun _ => (do
  newSpec ["istriv"]
   (← HolLight.REWRITE_RULE [SKOLEM_THM, RIGHT_IMP_EXISTS_THM] ISTRIV_EXISTS)
  : ExceptT String IO thm).run
#eval istriv_raw

#eval phrase 41
unsafe def istriv : thm := keep "istriv" fun _ => (do
  prove ([[!env x.
        LOOPFREE(env) /\ CONFLICTFREE(env)
        ==> (!x y. istriv env x (V y) =
                        if y = x then TT
                        else if MEM y (MAP FST env) then
                           istriv env x (ASSOC y env)
                        else FF) /\
            (!f args. istriv env x (Fn f args) =
                        if EX (\a. ~(istriv env x a = FF)) args
                        then Exception else FF)]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
       pure (GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.MATCH_MP istriv_raw th)])) THEN
    REWRITE_TAC [term_INJ, term_DISTINCT] THENL
     [COND_CASES_TAC THEN REWRITE_TAC [] THEN
      REWRITE_TAC [UNWIND_THM1] THEN
      ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
      ASM_REWRITE_TAC [FVT, IN_INSERT, NOT_IN_EMPTY, UNWIND_THM2] THEN
      COND_CASES_TAC THEN REWRITE_TAC [] THENL
       [AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        MATCH_MP_TAC SELECT_UNIQUE THEN
        X_GEN_TAC [[w:num]] THEN REWRITE_TAC [] THEN EQ_TAC THEN
        ASM_SIMP_TAC [], ALL_TAC] THEN
      COND_CASES_TAC THEN REWRITE_TAC [] THEN
      UNDISCH_TAC [[~MEM y (MAP FST (env:(num#term)list))]] THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[a ==> ~a ==> b]])) THEN
      FIRST_ASSUM (CHOOSE_THEN (MP_TAC o HolLight.CONJUNCT1)) THEN
      SPEC_TAC ([[env:(num#term)list]], [[env:(num#term)list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [MEM, MAP] THEN
      DISCH_THEN (DISJ_CASES_THEN2 (SUBST1_TAC oTIO HolLight.SYM) MP_TAC) THEN
      ASM_SIMP_TAC [FST], ALL_TAC] THEN
    ASM_CASES_TAC [[x IN FVT(Fn f args)]] THEN ASM_REWRITE_TAC [] THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC [[~EX (\a. ~(istriv env x a = FF)) args]] THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[a ==> ~a ==> b]])) THEN
      UNDISCH_TAC [[x IN FVT (Fn f args)]] THEN
      REWRITE_TAC [FVT, IN_LIST_UNION, EX_MAP] THEN
      MATCH_MP_TAC (← HolLight.ONCE_REWRITE_RULE [IMP_CONJ] EX_IMP) THEN
      REWRITE_TAC [o_THM] THEN MATCH_MP_TAC term_INDUCT THEN CONJ_TAC THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      TRY (DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)) THEN
      FIRST_ASSUM (fun th => HolLight.tactic_of do
         pure (ONCE_REWRITE_TAC [(← HolLight.MATCH_MP istriv_raw th)])) THENL
       [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [FVT, IN_INSERT, NOT_IN_EMPTY]) THEN
        ASM_REWRITE_TAC [retval_DISTINCT],
        ASM_REWRITE_TAC [term_DISTINCT, retval_DISTINCT]], ALL_TAC] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [FVT, IN_LIST_UNION, EX_MAP] THEN
    REWRITE_TAC [LEFT_AND_EX_THM] THEN REWRITE_TAC [EXISTS_EX] THEN
    REWRITE_TAC [o_THM] THEN UNDISCH_TAC [[~(x IN FVT (Fn f args))]] THEN
    REWRITE_TAC [FVT, IN_LIST_UNION, EX_MAP] THEN
    MATCH_MP_TAC EX_ADHOC THEN X_GEN_TAC [[t:term]] THEN
    REWRITE_TAC [o_THM] THEN DISCH_TAC THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
      pure (GEN_REWRITE_TAC
       (HolLight.RAND_CONV o HolLight.RAND_CONV o HolLight.LAND_CONV) [(← HolLight.MATCH_MP istriv_raw th)])) THEN
    COND_CASES_TAC THENL
     [UNDISCH_TAC [[~(x IN FVT t)]] THEN
      ASM_REWRITE_TAC [FVT, IN_INSERT, NOT_IN_EMPTY], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC [[?y. (t = V y) /\ MEM y (MAP FST (env:(num#term)list))]] THEN
    ASM_REWRITE_TAC [] THENL
     [ALL_TAC, COND_CASES_TAC THEN ASM_REWRITE_TAC [retval_DISTINCT]] THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN ([[y:num]]) STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [FVT, IN_INSERT, NOT_IN_EMPTY, term_INJ] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN REWRITE_TAC [UNWIND_THM2] THEN
    SUBGOAL_THEN ([[(@z. (y = z) /\ MEM z (MAP FST (env:(num#term)list))) = y]])
    SUBST1_TAC THENL
     [MATCH_MP_TAC SELECT_UNIQUE THEN
      X_GEN_TAC [[w:num]] THEN REWRITE_TAC [] THEN EQ_TAC THEN
      ASM_SIMP_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[!s. MEM (y:num,s:term) env <=> (s = ASSOC y env)]])
     (fun th => MESON_TAC [th]) THEN
    GEN_TAC THEN UNDISCH_TAC [[MEM y (MAP FST (env:(num#term)list))]] THEN
    FIRST_ASSUM (MP_TAC o HolLight.CONJUNCT2) THEN
    SPEC_TAC ([[env:(num#term)list]], [[env:(num#term)list]]) THEN
    POP_ASSUM_LIST (HolCore.Lib.K ALL_TAC) THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [MEM, MAP] THEN
    SPEC_TAC ([[h:num#term]], [[h:num#term]]) THEN
    ONCE_REWRITE_TAC [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[x:num]], [[t:term]] ] THEN
    REWRITE_TAC [FST, SND, PAIR_EQ, ASSOC] THEN
    ASM_CASES_TAC [[x:num = y]] THEN ASM_REWRITE_TAC [] THENL
     [MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> ~a) ==> (a ==> (c \/ b <=> c))]])) THEN
      DISCH_TAC THEN REWRITE_TAC [CONFLICTFREE] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[y:num]]) THEN
      REWRITE_TAC [FILTER, LENGTH] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC [LENGTH, (← ExceptT.mk (ARITH_RULE [[~(SUC n <= 1) <=> ~(n = 0)]]))] THEN
      REWRITE_TAC [LENGTH_EQ_NIL] THEN
      DISCH_THEN (MP_TAC o HolLight.AP_TERM [[MEM (y:num,s:term)]]) THEN
      ASM_REWRITE_TAC [MEM, MEM_FILTER] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REFL_TAC,
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN ([[CONFLICTFREE t]]) (fun th => ASM_MESON_TAC [th]) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [CONFLICTFREE]) THEN
    REWRITE_TAC [CONFLICTFREE, MEM, FILTER] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC [LENGTH] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval istriv


#eval phrase 42
unsafe def EQV : thm := keep "EQV" fun _ => new_definition
  [[EQV env x y = MEM (x,V y) env]]
#eval EQV

#eval phrase 43
unsafe def EQV_IMP_OCC : thm := keep "EQV_IMP_OCC" fun _ => (do
  prove ([[!env x y. EQV env x y ==> OCC env x y]])
   (REWRITE_TAC [EQV, OCC] THEN MESON_TAC [IN_INSERT, FVT])
  : ExceptT String IO thm).run
#eval EQV_IMP_OCC

#eval phrase 44
unsafe def ISTRIV_WORKS : thm := keep "ISTRIV_WORKS" fun _ => (do
  prove ([[!env x t. LOOPFREE(env) /\ CONFLICTFREE(env)
             ==> (istriv env x t =
                    if ?y. (t = V y) /\ RTC (EQV env) y x then TT
                    else if ?y. y IN FVT t /\ RTC (OCC env) y x then Exception
                    else FF)]])
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    GEN_TAC THEN FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP LOOPFREE_WF_TERM o HolLight.CONJUNCT1) THEN
    REWRITE_TAC [WF_IND] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC [[t:term]] THEN DISCH_TAC THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
       pure (ONCE_REWRITE_TAC [(← HolLight.MATCH_MP istriv_raw th)])) THEN
    ASM_CASES_TAC [[t = V x]] THEN ASM_REWRITE_TAC [] THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [term_INJ, RTC_REFL], ALL_TAC] THEN
    ASM_CASES_TAC [[?y. (t = V y) /\ MEM y (MAP FST (env:(num#term)list))]] THEN
    ASM_REWRITE_TAC [] THENL
     [FIRST_X_ASSUM (X_CHOOSE_THEN ([[z:num]]) STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC [term_INJ, UNWIND_THM1] THEN
      SUBGOAL_THEN ([[(@y. (z = y) /\ MEM y (MAP FST (env:(num#term)list))) = z]])
      SUBST1_TAC THENL
       [MATCH_MP_TAC SELECT_UNIQUE THEN
        X_GEN_TAC [[w:num]] THEN REWRITE_TAC [] THEN EQ_TAC THEN
        ASM_SIMP_TAC [], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[ASSOC z (env:(num#term)list)]]) THEN
      ANTS_TAC THENL
       [EXISTS_TAC [[z:num]] THEN ASM_REWRITE_TAC [FVT, IN_INSERT] THEN
        UNDISCH_TAC [[MEM z (MAP FST (env:(num#term)list))]] THEN
        FIRST_ASSUM (MP_TAC o HolLight.CONJUNCT2) THEN REWRITE_TAC [CONFLICTFREE] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC [[z:num]]) THEN
        SPEC_TAC ([[env:(num#term)list]], [[env:(num#term)list]]) THEN
        LIST_INDUCT_TAC THEN REWRITE_TAC [MAP, MEM, ASSOC, FILTER] THEN
        SPEC_TAC ([[h:num#term]], [[h:num#term]]) THEN
        ONCE_REWRITE_TAC [FORALL_PAIR_THM] THEN
        MAP_EVERY X_GEN_TAC [ [[y:num]], [[s:term]] ] THEN
        REWRITE_TAC [FST, SND] THEN
        CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
        ASM_CASES_TAC [[y:num = z]] THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC [FVT, IN_INSERT, NOT_IN_EMPTY, UNWIND_THM2] THEN
      GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.ONCE_DEPTH_CONV) [RTC_CASES_R] THEN
      ASM_CASES_TAC [[x:num = z]] THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [OCC, EQV] THEN
      SUBGOAL_THEN ([[!s. MEM (z:num,s:term) env = (s = ASSOC z env)]])
        (fun th => REWRITE_TAC [th])
      THENL
       [GEN_TAC THEN UNDISCH_TAC [[MEM z (MAP FST (env:(num#term)list))]] THEN
        FIRST_ASSUM (MP_TAC o HolLight.CONJUNCT2) THEN
        SPEC_TAC ([[env:(num#term)list]], [[env:(num#term)list]]) THEN
        POP_ASSUM_LIST (HolCore.Lib.K ALL_TAC) THEN LIST_INDUCT_TAC THEN
        REWRITE_TAC [MEM, MAP] THEN
        SPEC_TAC ([[h:num#term]], [[h:num#term]]) THEN
        ONCE_REWRITE_TAC [FORALL_PAIR_THM] THEN
        MAP_EVERY X_GEN_TAC [ [[x:num]], [[t:term]] ] THEN
        REWRITE_TAC [FST, SND, PAIR_EQ, ASSOC] THEN
        ASM_CASES_TAC [[x:num = z]] THEN ASM_REWRITE_TAC [] THENL
         [MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> ~a) ==> (a ==> (c \/ b <=> c))]])) THEN
          DISCH_TAC THEN REWRITE_TAC [CONFLICTFREE] THEN
          DISCH_THEN (MP_TAC o HolLight.SPEC [[z:num]]) THEN
          REWRITE_TAC [FILTER, LENGTH] THEN
          CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
          REWRITE_TAC [LENGTH, (← ExceptT.mk (ARITH_RULE [[~(SUC n <= 1) <=> ~(n = 0)]]))] THEN
          REWRITE_TAC [LENGTH_EQ_NIL] THEN
          DISCH_THEN (MP_TAC o HolLight.AP_TERM [[MEM (z:num,s:term)]]) THEN
          ASM_REWRITE_TAC [MEM, MEM_FILTER] THEN
          CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REFL_TAC,
          ALL_TAC] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN ([[CONFLICTFREE t]]) (fun th => ASM_MESON_TAC [th]) THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [CONFLICTFREE]) THEN
        REWRITE_TAC [CONFLICTFREE, MEM, FILTER] THEN
        CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
        COND_CASES_TAC THEN REWRITE_TAC [LENGTH] THEN ARITH_TAC, ALL_TAC] THEN
      GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RATOR_CONV o HolLight.LAND_CONV o HolLight.BINDER_CONV o
                       HolLight.LAND_CONV) [EQ_SYM_EQ] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [UNWIND_THM2],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~(?y. (t = V y) /\ RTC (EQV env) y x)]]) ASSUME_TAC THENL
     [UNDISCH_TAC
       [[~(?y. (t = V y) /\ MEM y (MAP FST (env:(num#term)list)))]] THEN
      REWRITE_TAC [(← ExceptT.mk (TAUT [[~a ==> ~b <=> b ==> a]]))] THEN
      ONCE_REWRITE_TAC [RTC_CASES_R] THEN REWRITE_TAC [EQV] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[y:num]] THEN
      ASM_CASES_TAC [[y = x:num]] THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [MEM_MAP] THEN MESON_TAC [FST],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN ASM_CASES_TAC [[x IN FVT(t)]] THEN
    ASM_REWRITE_TAC [] THENL
     [SUBGOAL_THEN ([[?y. y IN FVT t /\ RTC (OCC env) y x]])
       (fun th => REWRITE_TAC [th]) THEN
      ASM_MESON_TAC [RTC_REFL], ALL_TAC] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC [[y:num]] THEN
    REWRITE_TAC [RIGHT_EXISTS_AND_THM] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)]])) THEN
    DISCH_TAC THEN
    ONCE_REWRITE_TAC [RTC_CASES_R] THEN
    ASM_CASES_TAC [[y = x:num]] THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [OCC, LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC), RIGHT_EXISTS_AND_THM] THEN
    AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC [[s:term]] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)]])) THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[s:term]]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_CASES_TAC [[?y. (s = V y) /\ RTC (EQV env) y x]] THEN
    ASM_REWRITE_TAC [retval_DISTINCT] THENL
     [FIRST_X_ASSUM (X_CHOOSE_THEN ([[z:num]]) STRIP_ASSUME_TAC) THEN
      EXISTS_TAC [[z:num]] THEN ASM_REWRITE_TAC [FVT, IN_INSERT] THEN
      ASM_MESON_TAC [RTC_MONO, EQV_IMP_OCC], ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [retval_DISTINCT])
  : ExceptT String IO thm).run
#eval ISTRIV_WORKS

#eval phrase 45
unsafe def SUB1 : thm := keep "SUB1" fun _ => new_definition
  [[SUB1 s t <=> ?f args. (t = Fn f args) /\ MEM s args]]
#eval SUB1

#eval phrase 46
unsafe def WF_SUB1 : thm := keep "WF_SUB1" fun _ => (do
  prove ([[WF(SUB1)]])
   (SIMP_TAC [WF_IND, SUB1, LEFT_IMP_EXISTS_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC term_INDUCT THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [term_DISTINCT, term_INJ] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [(← HolLight.GSYM ALL_MEM)]) THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval WF_SUB1

#eval phrase 47
unsafe def RTC_SUB1 : thm := keep "RTC_SUB1" fun _ => (do
  prove ([[!x t. RTC(SUB1) (V x) t <=> x IN FVT(t)]])
   (GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
    REWRITE_TAC [FVT, IN_INSERT, NOT_IN_EMPTY, IN_LIST_UNION] THEN CONJ_TAC THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [RTC_CASES_L] THEN
    REWRITE_TAC [SUB1, term_INJ, term_DISTINCT] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC [[?y. RTC SUB1 (V x) y /\ MEM y l]] THEN CONJ_TAC THENL
     [MESON_TAC [], ALL_TAC] THEN
    REWRITE_TAC [EX_MAP, o_DEF] THEN
    FIRST_ASSUM (SUBST1_TAC oTIO (fun th => (do let r ← HolLight.MATCH_MP ALL_ADHOC th; HolLight.SYM r : ExceptT String IO thm).run)) THEN
    REWRITE_TAC [EX_MEM])
  : ExceptT String IO thm).run
#eval RTC_SUB1

#eval phrase 48
unsafe def WF_SUBCOMPONENT : thm := keep "WF_SUBCOMPONENT" fun _ => (do
  prove ([[LOOPFREE(env) ==> WF(\s t. ?x. MEM (x,s) env /\ RTC(SUB1) (V x) t)]])
   (REWRITE_TAC [RTC_SUB1] THEN ONCE_REWRITE_TAC [CONJ_SYM] THEN
    REWRITE_TAC [LOOPFREE_WF_TERM])
  : ExceptT String IO thm).run
#eval WF_SUBCOMPONENT

#eval phrase 49
unsafe def WF_DESCENT : thm := keep "WF_DESCENT" fun _ => (do
  prove ([[LOOPFREE(env)
   ==> WF(\s t. (?x. (t = V x) /\ MEM (x,s) env) \/
                (?f args. (t = Fn f args) /\ MEM s args))]])
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [DISJ_SYM] THEN
    MATCH_MP_TAC WF_DISJ THEN REWRITE_TAC [(← HolLight.GSYM SUB1)] THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV (fun t => pure (ETA_CONV t))) THEN REWRITE_TAC [WF_SUB1] THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC), UNWIND_THM2] THEN
    ASM_SIMP_TAC [WF_SUBCOMPONENT])
  : ExceptT String IO thm).run
#eval WF_DESCENT

#eval phrase 50
unsafe def termcases : thm := keep "termcases" fun _ => (do
  newRec term_RECURSION
   [[(termcases cv cf (V v) = cv v) /\
     (termcases cv cf (Fn f args) = cf f args)]]
  : ExceptT String IO thm).run
#eval termcases

#eval phrase 51
unsafe def tpcases_def : thm := keep "tpcases_def" fun _ => new_definition
  [[tpcases c1 c2 c3 (t1,t2) =
        termcases (\v1. termcases
                            (\v2. c2 v1 (V v2))
                            (\f2 args2. c2 v1 (Fn f2 args2)) t2)
                  (\f1 args1. termcases
                                (\v2. c3 f1 args1 v2)
                                (\f2 args2. c1 f1 args1 f2 args2) t2)
                  t1]]
#eval tpcases_def

#eval phrase 52
unsafe def tpcases : thm := keep "tpcases" fun _ => (do
  prove ([[(tpcases c1 c2 c3 (Fn f1 args1,Fn f2 args2) = c1 f1 args1 f2 args2) /\
   (tpcases c1 c2 c3 (V v1,t2) = c2 v1 t2) /\
   (tpcases c1 c2 c3 (Fn f1 args1,V v2) = c3 f1 args1 v2)]])
   (SPEC_TAC ([[t2:term]], [[t2:term]]) THEN MATCH_MP_TAC term_INDUCT THEN
    REWRITE_TAC [tpcases_def, termcases])
  : ExceptT String IO thm).run
#eval tpcases

#eval phrase 53
unsafe def MLEFT : thm := keep "MLEFT" fun _ => new_definition
  [[MLEFT (env,eqs) =
       CARD(FVT(Fn 0 (MAP FST eqs)) UNION
            FVT(Fn 0 (MAP SND eqs)) UNION
            FVT(Fn 0 (MAP SND env)) UNION
            FVT(Fn 0 (MAP (V o FST) env))) -
       CARD(FVT(Fn 0 (MAP (V o FST) env)))]]
#eval MLEFT

#eval phrase 54
unsafe def CRIGHT : thm := keep "CRIGHT" fun _ => new_definition
  [[CRIGHT (env',eqs') (env,eqs) <=>
         LOOPFREE(env) /\
         (env' = env) /\
         ((?f args1 args2 oth.
                (LENGTH args1 = LENGTH args2) /\
                (eqs = CONS (Fn f args1,Fn f args2) oth) /\
                (eqs' = APPEND (ZIP args1 args2) oth)) \/
          (?x t oth. (eqs = CONS (V x,t) oth) /\
                     (MEM x (MAP FST env) /\
                      (eqs' = CONS (ASSOC x env,t) oth) \/
                      ~(MEM x (MAP FST env)) /\
                      (istriv env x t = TT) /\
                      (eqs' = oth))) \/
          (?x f args oth. (eqs = CONS (Fn f args,V x) oth) /\
                          (eqs' = CONS (V x,Fn f args) oth)))]]
#eval CRIGHT

#eval phrase 55
unsafe def CALLORDER : thm := keep "CALLORDER" fun _ => new_definition
  [[CALLORDER (env',eqs') (env,eqs) <=>
        MEASURE MLEFT (env',eqs') (env,eqs) \/
        CRIGHT (env',eqs') (env,eqs)]]
#eval CALLORDER

#eval phrase 56
unsafe def PAIRED_ETA_THM : thm := keep "PAIRED_ETA_THM" fun _ => (do
  prove ([[!g:A#B->C. (\(p1,p2). g (p1,p2)) = g]])
   (REWRITE_TAC [FUN_EQ_THM, FORALL_PAIR_THM] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval PAIRED_ETA_THM

#eval phrase 57
unsafe def WF_CRIGHT : thm := keep "WF_CRIGHT" fun _ => (do
  prove ([[WF CRIGHT]])
   (SUBGOAL_THEN ([[CRIGHT = \(env',eqs') (env,eqs). CRIGHT (env',eqs') (env,eqs)]])
    SUBST1_TAC THENL
     [REWRITE_TAC [PAIRED_ETA_THM] THEN
      CONV_TAC (HolLight.TOP_DEPTH_CONV (fun t => pure (ETA_CONV t))) THEN REFL_TAC, ALL_TAC] THEN
    REWRITE_TAC [CRIGHT] THEN MATCH_MP_TAC WF_PROJ_EQ THEN
    X_GEN_TAC [[env:(num#term)list]] THEN DISCH_TAC THEN REWRITE_TAC [] THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP WF_DESCENT) THEN
    DISCH_THEN (MP_TAC o HolLight.GEN_ALL o HolLight.MATCH_MP (← HolLight.ONCE_REWRITE_RULE
        [IMP_CONJ] WF_ALTERNATION)) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC
     [[\s t. (?f args. s = Fn f args) /\ (?x. t = V x)]]) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL [MESON_TAC [term_DISTINCT], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP WF_MULTIZIP) THEN
    MATCH_MP_TAC (← HolLight.ONCE_REWRITE_RULE
        [IMP_CONJ] WF_SUBSET) THEN
    MAP_EVERY X_GEN_TAC [ [[eqs2:(term#term)list]], [[eqs1:(term#term)list]] ] THEN
    REWRITE_TAC [] THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC
       [ [[(Fn f args1,Fn f args2)]],
        [[oth:(term#term)list]],
        [[(ZIP args1 args2):(term#term)list]] ] THEN
      ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [ [[s:term]], [[t:term]] ] THEN
      CONV_TAC (HolLight.TOP_DEPTH_CONV GEN_BETA_CONV) THEN
      DISCH_TAC THEN DISJ1_TAC THEN
      REWRITE_TAC [LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM] THEN
      MAP_EVERY EXISTS_TAC
       [ [[f:num]], [[args1:term list]], [[f:num]], [[args2:term list]] ] THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [FIRST_ASSUM (SUBST1_TAC oTIO (fun th => (do let r ← HolLight.MATCH_MP MAP_FST_ZIP th; HolLight.SYM r : ExceptT String IO thm).run)),
        FIRST_ASSUM (SUBST1_TAC oTIO (fun th => (do let r ← HolLight.MATCH_MP MAP_SND_ZIP th; HolLight.SYM r : ExceptT String IO thm).run))] THEN
      REWRITE_TAC [MEM_MAP] THEN ASM_MESON_TAC [FST, SND],
      MAP_EVERY EXISTS_TAC
       [ [[(V x,t:term)]],
        [[oth:(term#term)list]],
        [[ [ASSOC x (env:(num#term)list),t:term] ]] ] THEN
      ASM_REWRITE_TAC [APPEND] THEN GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [ [[s:term]], [[u:term]] ] THEN
      CONV_TAC (HolLight.TOP_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC [MEM, PAIR_EQ] THEN
      DISCH_THEN (CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      DISJ2_TAC THEN DISJ1_TAC THEN REWRITE_TAC [] THEN EXISTS_TAC [[x:num]] THEN
      ASM_REWRITE_TAC [MEM_ASSOC],
      MAP_EVERY EXISTS_TAC
       [ [[(V x,t:term)]], [[oth:(term#term)list]], [[ []:(term#term)list ]] ] THEN
      ASM_REWRITE_TAC [APPEND, MEM],
      MAP_EVERY EXISTS_TAC
       [ [[(Fn f args,V x)]], [[oth:(term#term)list]], [[ [V x,Fn f args] ]] ] THEN
      ASM_REWRITE_TAC [APPEND] THEN GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [ [[s:term]], [[u:term]] ] THEN
      CONV_TAC (HolLight.TOP_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC [MEM, PAIR_EQ] THEN
      DISCH_THEN (CONJUNCTS_THEN SUBST_ALL_TAC) THEN REWRITE_TAC [] THEN
      REPEAT DISJ2_TAC THEN MESON_TAC []])
  : ExceptT String IO thm).run
#eval WF_CRIGHT

#eval phrase 58
unsafe def WF_CALLORDER : thm := keep "WF_CALLORDER" fun _ => (do
  prove ([[WF CALLORDER]])
   (SUBGOAL_THEN
     ([[CALLORDER = \(env',eqs') (env,eqs). CALLORDER (env',eqs') (env,eqs)]])
    SUBST1_TAC THENL
     [REWRITE_TAC [PAIRED_ETA_THM] THEN
      CONV_TAC (HolLight.TOP_DEPTH_CONV (fun t => pure (ETA_CONV t))) THEN REFL_TAC, ALL_TAC] THEN
    REWRITE_TAC [CALLORDER] THEN
    REWRITE_TAC [PAIRED_ETA_THM] THEN
    MATCH_MP_TAC WF_MEASURE_OR_NONINC THEN
    REWRITE_TAC [WF_CRIGHT, FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC
     [ [[env':(num#term)list]], [[eqs':(term#term)list]],
      [[env:(num#term)list]], [[eqs:(term#term)list]] ] THEN
    REWRITE_TAC [CRIGHT, MLEFT] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    MATCH_MP_TAC (← ExceptT.mk (ARITH_RULE [[a <= c:num ==> a - b <= c - b]])) THEN
    MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC [FINITE_UNION, FVT_FINITE] THEN
    REWRITE_TAC [SUBSET, IN_UNION] THEN X_GEN_TAC [[x:num]] THEN
    FIRST_X_ASSUM (DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [MAP, MAP_APPEND, FVT, LIST_UNION, LIST_UNION_APPEND] THEN
    REWRITE_TAC [IN_UNION, (← HolLight.GSYM DISJ_ASSOC)] THENL
     [MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a' <=> a) /\ (c' <=> c)
                       ==> a \/ b \/ c \/ d ==> a' \/ b \/ c' \/ d]])) THEN
      ASM_SIMP_TAC [MAP_FST_ZIP, MAP_SND_ZIP],
      MATCH_MP_TAC (← ExceptT.mk (TAUT
        [[(a ==> e)
       ==> a \/ b \/ c \/ d \/ e \/ f
           ==> a' \/ b \/ c \/ d \/ e \/ f]])) THEN
      UNDISCH_TAC [[MEM x' (MAP FST (env:(num#term)list))]] THEN
      SPEC_TAC ([[env:(num#term)list]], [[env:(num#term)list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [MEM, MAP, ASSOC] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC [LIST_UNION, IN_UNION],
      CONV_TAC TAUT,
      CONV_TAC TAUT])
  : ExceptT String IO thm).run
#eval WF_CALLORDER

#eval phrase 59
unsafe def UNIFY_EXISTS_RAW : thm := keep "UNIFY_EXISTS_RAW" fun _ => (do
  prove ([[?unify.
      !pr. unify pr =
              if ~LOOPFREE(FST pr) then NONE
              else if SND pr = [] then SOME(FST pr)
              else tpcases
                        (\f fargs g gargs.
                                if (f = g) /\ (LENGTH fargs = LENGTH gargs)
                                then unify (FST pr,APPEND (ZIP fargs gargs)
                                                          (TL(SND pr)))
                                else NONE)
                        (\x t. if MEM x (MAP FST (FST pr)) then
                                  unify (FST pr,CONS (ASSOC x (FST pr),t)
                                                     (TL(SND pr)))
                               else if istriv (FST pr) x t = Exception then
                                  NONE
                               else if istriv (FST pr) x t = TT then
                                  unify(FST pr,TL(SND pr))
                               else
                                  unify(CONS (x,t) (FST pr),TL(SND pr)))
                        (\f args x. unify (FST pr,
                                           CONS (V x,Fn f args)
                                                (TL(SND pr))))
                        (HD(SND pr))]])
   (MATCH_MP_TAC (← HolLight.MATCH_MP WF_REC WF_CALLORDER) THEN
    MAP_EVERY X_GEN_TAC
     [ [[unify1:(num#term)list#(term#term)list->((num#term)list)option]],
      [[unify2:(num#term)list#(term#term)list->((num#term)list)option]] ] THEN
    GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[env1:(num#term)list]], [[eqs1:(term#term)list]] ] THEN
    DISCH_THEN (MP_TAC o HolLight.GENL
     [ [[env2:(num#term)list]], [[eqs2:(term#term)list]] ] o HolLight.SPEC
      [[(env2,eqs2):(num#term)list#(term#term)list]]) THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC [FST, SND] THEN DISCH_TAC THEN
    ASM_CASES_TAC [[LOOPFREE env1]] THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (← HolLight.ISPEC ([[eqs1:(term#term)list]]) list_CASES) THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THEN REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[hpr:term#term]]) (X_CHOOSE_THEN
     ([[oth:(term#term)list]]) SUBST_ALL_TAC)) THEN
    REWRITE_TAC [NOT_CONS_NIL, HD, TL] THEN
    SUBST_ALL_TAC (← HolLight.GSYM (← HolLight.ISPEC ([[hpr:term#term]]) PAIR)) THEN
    MP_TAC (← HolLight.ISPEC ([[FST(hpr:term#term)]]) term_CASES) THEN
    DISCH_THEN (DISJ_CASES_THEN2
     (X_CHOOSE_THEN ([[x:num]]) SUBST_ALL_TAC)
     (X_CHOOSE_THEN ([[f:num]]) (X_CHOOSE_THEN ([[fargs:term list]]) SUBST_ALL_TAC)))
    THENL
     [ABBREV_TAC [[t = SND(hpr:term#term)]],
      MP_TAC (← HolLight.ISPEC ([[SND(hpr:term#term)]]) term_CASES) THEN
      DISCH_THEN (DISJ_CASES_THEN2
       (X_CHOOSE_THEN ([[x:num]]) SUBST_ALL_TAC)
       (X_CHOOSE_THEN ([[g:num]]) (X_CHOOSE_THEN ([[gargs:term list]])
           SUBST_ALL_TAC)))] THEN
    REWRITE_TAC [tpcases] THENL
     [ALL_TAC,
      FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [CALLORDER] THEN
      DISJ2_TAC THEN ASM_REWRITE_TAC [CRIGHT] THEN
      REPEAT DISJ2_TAC THEN ASM_MESON_TAC [],
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [CALLORDER] THEN DISJ2_TAC THEN ASM_REWRITE_TAC [CRIGHT] THEN
      ASM_MESON_TAC []] THEN
    ASM_CASES_TAC [[MEM x (MAP FST (env1:(num#term)list))]] THEN
    ASM_REWRITE_TAC [] THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [CALLORDER] THEN
      DISJ2_TAC THEN ASM_REWRITE_TAC [CRIGHT] THEN
      DISJ2_TAC THEN DISJ1_TAC THEN ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_CASES_TAC [[istriv env1 x t = Exception]] THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC [[istriv env1 x t = TT]] THEN ASM_REWRITE_TAC [] THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [CALLORDER] THEN
      DISJ2_TAC THEN ASM_REWRITE_TAC [CRIGHT] THEN
      DISJ2_TAC THEN DISJ1_TAC THEN ASM_MESON_TAC [], ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [CALLORDER] THEN
    DISJ1_TAC THEN REWRITE_TAC [MEASURE, MLEFT] THEN
    REWRITE_TAC [MAP, FST, SND, LENGTH] THEN
    MATCH_MP_TAC (← ExceptT.mk (ARITH_RULE
     [[(a' = a) /\ (b' = b + 1) /\ b' <= a' ==> a' - b' < a - b]])) THEN
    SUBGOAL_THEN
     ([[FVT(Fn 0 (CONS ((V o FST) (x,t:term)) (MAP (V o FST) env1))) =
    x INSERT FVT(Fn 0 (MAP (V o FST) (env1:(num#term)list)))]])
    SUBST1_TAC THENL
     [REWRITE_TAC [FVT, MAP, LIST_UNION, o_THM, FST] THEN SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     ([[FVT(Fn 0 (CONS (V x) (MAP FST (oth:(term#term)list)))) =
    x INSERT FVT(Fn 0 (MAP FST oth))]])
    SUBST1_TAC THENL
     [REWRITE_TAC [FVT, MAP, LIST_UNION, o_THM, FST] THEN SET_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     ([[FVT(Fn 0 (CONS t (MAP SND env1))) =
    FVT(t) UNION FVT(Fn 0 (MAP SND (env1:(num#term)list)))]])
    SUBST1_TAC THENL
     [REWRITE_TAC [FVT, MAP, LIST_UNION, o_THM, FST], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[FVT(Fn 0 (CONS t (MAP SND oth))) =
    FVT(t) UNION FVT(Fn 0 (MAP SND (oth:(term#term)list)))]])
    SUBST1_TAC THENL
     [REWRITE_TAC [FVT, MAP, LIST_UNION, o_THM, FST], ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_UNION, DISJ_ACI, IN_INSERT],
      SIMP_TAC [CARD_CLAUSES, FVT_FINITE, ADD1] THEN
      COND_CASES_TAC THEN REWRITE_TAC [] THEN
      UNDISCH_TAC [[x IN FVT (Fn 0 (MAP (V o FST) (env1:(num#term)list)))]] THEN
      UNDISCH_TAC [[~MEM x (MAP FST (env1:(num#term)list))]] THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> a) ==> ~a ==> b ==> c]])) THEN
      SPEC_TAC ([[env1:(num#term)list]], [[env1:(num#term)list]]) THEN
      REWRITE_TAC [FVT] THEN LIST_INDUCT_TAC THEN
      REWRITE_TAC [LIST_UNION, MEM, MAP, NOT_IN_EMPTY] THEN
      REWRITE_TAC [o_THM, FVT, IN_UNION, IN_INSERT, NOT_IN_EMPTY] THEN
      STRIP_TAC THEN ASM_SIMP_TAC [],
      MATCH_MP_TAC CARD_SUBSET THEN
      REWRITE_TAC [FINITE_UNION, FVT_FINITE, FINITE_INSERT] THEN
      REWRITE_TAC [SUBSET, IN_UNION, IN_INSERT] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []])
  : ExceptT String IO thm).run
#eval UNIFY_EXISTS_RAW

#eval phrase 60
unsafe def unify_raw : thm := keep "unify_raw" fun _ => (do
  newSpec ["unify"] UNIFY_EXISTS_RAW
  : ExceptT String IO thm).run
#eval unify_raw

#eval phrase 61
unsafe def unify : thm := keep "unify" fun _ => (do
  prove ([[LOOPFREE(env)
   ==> (unify (env,CONS (Fn f fargs,Fn g gargs) oth) =
            if (f = g) /\ (LENGTH fargs = LENGTH gargs)
            then unify (env,APPEND (ZIP fargs gargs) oth)
            else NONE) /\
       (unify (env,CONS (V x,t) oth) =
            if MEM x (MAP FST env) then unify (env,CONS (ASSOC x env,t) oth)
            else if istriv env x t = Exception then NONE
            else if istriv env x t = TT then unify (env,oth)
            else unify (CONS (x,t) env,oth)) /\
       (unify (env,CONS (Fn f fargs,V x) oth) =
        unify (env,CONS (V x,Fn f fargs) oth))]])
   (DISCH_TAC THEN REPEAT CONJ_TAC THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [unify_raw] THEN
    ASM_REWRITE_TAC [FST, SND, HD, TL, NOT_CONS_NIL, tpcases])
  : ExceptT String IO thm).run
#eval unify


#eval phrase 62
unsafe def unifies : thm := keep "unifies" fun _ => new_definition
  [[unifies i l <=> ALL (\(s,t). termsubst i s = termsubst i t) l]]
#eval unifies

#eval phrase 63
unsafe def OPTION_DISTINCT : thm := keep "OPTION_DISTINCT" fun _ =>
  (ExceptT.mk (Session.prove_constructors_distinct option_RECURSION) : ExceptT String IO thm).run
#eval OPTION_DISTINCT

#eval phrase 64
unsafe def OPTION_INJ : thm := keep "OPTION_INJ" fun _ =>
  (ExceptT.mk (Session.prove_constructors_injective option_RECURSION) : ExceptT String IO thm).run
#eval OPTION_INJ

#eval phrase 65
unsafe def TC_SUB1_IRREFL : thm := keep "TC_SUB1_IRREFL" fun _ => (do
  prove ([[!s t. TC SUB1 s t ==> ~(s = t)]])
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[a ==> ~b <=> b ==> ~a]]))] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC WF_REFL THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (ETA_CONV t))) THEN
    REWRITE_TAC [WF_TC, WF_SUB1])
  : ExceptT String IO thm).run
#eval TC_SUB1_IRREFL

#eval phrase 66
unsafe def UNIFY_OCCURS : thm := keep "UNIFY_OCCURS" fun _ => (do
  prove ([[!env i.
        ALL (\(x,t). i x = termsubst i t) env
        ==> !x y. RTC (OCC env) x y ==> RTC SUB1 (i y) (i x)]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC RTC_INDUCT THEN
    REWRITE_TAC [RTC_REFL] THEN
    CONJ_TAC THENL [ALL_TAC, MESON_TAC [RTC_TRANS]] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [OCC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[t:term]]) STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [(← HolLight.GSYM ALL_MEM)]) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[(x:num,t:term)]]) THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_SIMP_TAC [] THEN
    DISCH_TAC THEN UNDISCH_TAC [[y IN FVT(t)]] THEN SPEC_TAC ([[y:num]], [[y:num]]) THEN
    SPEC_TAC ([[t:term]], [[t:term]]) THEN MATCH_MP_TAC term_INDUCT THEN
    SIMP_TAC [FVT, IN_INSERT, NOT_IN_EMPTY, termsubst, RTC_REFL] THEN
    MAP_EVERY X_GEN_TAC [ [[f:num]], [[args:term list]] ] THEN
    DISCH_TAC THEN X_GEN_TAC [[z:num]] THEN REWRITE_TAC [IN_LIST_UNION] THEN
    REWRITE_TAC [EX_MAP, o_DEF] THEN REWRITE_TAC [(← HolLight.GSYM EX_MEM)] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[s:term]]) STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC RTC_TRANS_L THEN EXISTS_TAC [[termsubst i s]] THEN CONJ_TAC THENL
     [UNDISCH_TAC
       [[ALL (\t. !y. y IN FVT t ==> RTC SUB1 (i y) (termsubst i t)) args]] THEN
      REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN ASM_MESON_TAC [],
      REWRITE_TAC [SUB1] THEN EXISTS_TAC [[f:num]] THEN
      EXISTS_TAC [[MAP (termsubst i) args]] THEN
      REWRITE_TAC [MEM_MAP] THEN ASM_MESON_TAC []])
  : ExceptT String IO thm).run
#eval UNIFY_OCCURS

#eval phrase 67
unsafe def UNIFY_OCCURS_PROPER : thm := keep "UNIFY_OCCURS_PROPER" fun _ => (do
  prove ([[!env i.
        ALL (\(x,t). i x = termsubst i t) env
        ==> !x y. RTC (OCC env) x y
                  ==> RTC (EQV env) x y \/ TC SUB1 (i y) (i x)]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC RTC_INDUCT THEN
    REWRITE_TAC [RTC_REFL] THEN CONJ_TAC THENL
     [ALL_TAC,
      REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC [RTC_TRANS],
        DISJ2_TAC THEN ONCE_REWRITE_TAC [TC_TC_RTC_CASES],
        DISJ2_TAC THEN ONCE_REWRITE_TAC [TC_RTC_TC_CASES],
        ASM_MESON_TAC [TC_TRANS]] THEN
      EXISTS_TAC [[(i:num->term) y]] THEN ASM_REWRITE_TAC [] THEN
      FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP UNIFY_OCCURS) THEN
      ASM_MESON_TAC [EQV_IMP_OCC, RTC_MONO]] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [OCC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[t:term]]) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [(← HolLight.GSYM ALL_MEM)]) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[(x:num,t:term)]]) THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_SIMP_TAC [] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     ([[!t y. y IN FVT t ==> (t = V y) \/ TC SUB1 (i y) (termsubst i t)]])
    MP_TAC THENL
     [ALL_TAC, ASM_MESON_TAC [EQV, RTC_INC]] THEN
    SUBGOAL_THEN ([[!t y. y IN FVT t ==> RTC SUB1 (V y) t]]) MP_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [RTC, RC_CASES] THEN
      SUBGOAL_THEN
       ([[!s t. TC SUB1 s t ==> TC SUB1 (termsubst i s) (termsubst i t)]])
       (fun th => MESON_TAC [th, termsubst]) THEN
      MATCH_MP_TAC TC_INDUCT THEN
      CONJ_TAC THENL [ALL_TAC, MESON_TAC [TC_TRANS]] THEN
      MAP_EVERY X_GEN_TAC [ [[s:term]], [[u:term]] ] THEN
      DISCH_THEN (fun th => HolLight.tactic_of do pure (MATCH_MP_TAC TC_INC THEN MP_TAC th)) THEN
      REWRITE_TAC [SUB1] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[f:num]]) (X_CHOOSE_THEN ([[args:term list]])
          STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [ [[f:num]], [[MAP (termsubst i) args]] ] THEN
      ASM_REWRITE_TAC [termsubst, MEM_MAP] THEN ASM_MESON_TAC []] THEN
    MATCH_MP_TAC term_INDUCT THEN
    SIMP_TAC [FVT, IN_INSERT, NOT_IN_EMPTY, RTC_REFL] THEN
    MAP_EVERY X_GEN_TAC [ [[f:num]], [[args:term list]] ] THEN
    DISCH_TAC THEN REWRITE_TAC [IN_LIST_UNION] THEN
    REWRITE_TAC [EX_MAP, o_DEF] THEN X_GEN_TAC [[z:num]] THEN
    REWRITE_TAC [(← HolLight.GSYM EX_MEM)] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[s:term]]) STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC RTC_TRANS_L THEN EXISTS_TAC [[s:term]] THEN CONJ_TAC THENL
     [UNDISCH_TAC
       [[ALL (\t. !y. y IN FVT t ==> RTC SUB1 (V y) t) args]] THEN
      REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN ASM_MESON_TAC [],
      REWRITE_TAC [SUB1] THEN ASM_MESON_TAC []])
  : ExceptT String IO thm).run
#eval UNIFY_OCCURS_PROPER

#eval phrase 68
unsafe def GOODLOOP_UNIFIABLE : thm := keep "GOODLOOP_UNIFIABLE" fun _ => (do
  prove ([[!env x t.
        LOOPFREE(env) /\ CONFLICTFREE(env) /\ (istriv env x t = TT)
   ==> !i. unifies i (CONS (V x,t) (MAP (\(x,t). V x,t) env)) =
           unifies i (MAP (\(x,t). V x,t) env)]])
   (REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC [ISTRIV_WORKS] THEN
    REPEAT (COND_CASES_TAC THEN REWRITE_TAC [retval_DISTINCT]) THEN
    X_GEN_TAC [[i:num->term]] THEN REWRITE_TAC [unifies, ALL] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[(a /\ b <=> b) <=> (b ==> a)]]))] THEN
    REWRITE_TAC [ALL_MAP, o_DEF] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.LAND_CONV) [(← HolLight.GSYM PAIRED_ETA_THM)] THEN
    REWRITE_TAC [] THEN CONV_TAC (HolLight.REDEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC [termsubst] THEN DISCH_TAC THEN
    UNDISCH_TAC [[?y. (t = V y) /\ RTC (EQV env) y x]] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    SPEC_TAC ([[x:num]], [[x:num]]) THEN ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    ONCE_REWRITE_TAC [IMP_CONJ_ALT] THEN
    SUBGOAL_THEN ([[!x y. RTC (EQV env) x y ==> (i x :term = i y)]])
      (fun th => MESON_TAC [th, termsubst]) THEN
    MATCH_MP_TAC RTC_INDUCT THEN CONJ_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    MAP_EVERY X_GEN_TAC [ [[u:num]], [[v:num]] ] THEN REWRITE_TAC [EQV] THEN
    UNDISCH_TAC [[ALL (\(p1,p2). i p1 = termsubst i p2) env]] THEN
    SPEC_TAC ([[env:(num#term)list]], [[env:(num#term)list]]) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [ALL, MEM] THEN
    GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC [PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] THEN ASM_MESON_TAC [termsubst])
  : ExceptT String IO thm).run
#eval GOODLOOP_UNIFIABLE

#eval phrase 69
unsafe def BADLOOP_UNUNIFIABLE : thm := keep "BADLOOP_UNUNIFIABLE" fun _ => (do
  prove ([[!env x t.
        LOOPFREE(env) /\ CONFLICTFREE(env) /\ (istriv env x t = Exception)
        ==> !i. ~(unifies i (CONS (V x,t) (MAP (\(x,t). V x,t) env)))]])
   (REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC [ISTRIV_WORKS] THEN
    REPEAT (COND_CASES_TAC THEN REWRITE_TAC [retval_DISTINCT]) THEN
    X_GEN_TAC [[i:num->term]] THEN REWRITE_TAC [unifies, ALL] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> ~a) ==> ~(a /\ b)]])) THEN
    REWRITE_TAC [ALL_MAP, o_DEF] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.LAND_CONV) [(← HolLight.GSYM PAIRED_ETA_THM)] THEN
    REWRITE_TAC [] THEN CONV_TAC (HolLight.REDEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC [termsubst] THEN DISCH_TAC THEN
    UNDISCH_TAC [[?y. y IN FVT t /\ RTC (OCC env) y x]] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC [[y:num]] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [NOT_EXISTS_THM]) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[y:num]]) THEN
    ASM_CASES_TAC [[RTC (EQV env) y x]] THEN ASM_REWRITE_TAC [] THENL
     [DISCH_TAC THEN STRIP_TAC THEN MATCH_MP_TAC TC_SUB1_IRREFL THEN
      ONCE_REWRITE_TAC [TC_RTC_TC_CASES] THEN
      EXISTS_TAC [[(i:num->term) y]] THEN CONJ_TAC THENL
       [FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP UNIFY_OCCURS) THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN
       ([[!t y. y IN FVT t ==> (t = V y) \/ TC SUB1 (i y) (termsubst i t)]])
       (fun th => ASM_MESON_TAC [th]) THEN
      SUBGOAL_THEN ([[!t y. y IN FVT t ==> RTC SUB1 (V y) t]]) MP_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [RTC, RC_CASES] THEN
        SUBGOAL_THEN
         ([[!s t. TC SUB1 s t ==> TC SUB1 (termsubst i s) (termsubst i t)]])
         (fun th => MESON_TAC [th, termsubst]) THEN
        MATCH_MP_TAC TC_INDUCT THEN
        CONJ_TAC THENL [ALL_TAC, MESON_TAC [TC_TRANS]] THEN
        MAP_EVERY X_GEN_TAC [ [[s:term]], [[u:term]] ] THEN
        DISCH_THEN (fun th => HolLight.tactic_of do pure (MATCH_MP_TAC TC_INC THEN MP_TAC th)) THEN
        REWRITE_TAC [SUB1] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[f:num]]) (X_CHOOSE_THEN ([[args:term list]])
            STRIP_ASSUME_TAC)) THEN
        MAP_EVERY EXISTS_TAC [ [[f:num]], [[MAP (termsubst i) args]] ] THEN
        ASM_REWRITE_TAC [termsubst, MEM_MAP] THEN ASM_MESON_TAC []] THEN
      MATCH_MP_TAC term_INDUCT THEN
      SIMP_TAC [FVT, IN_INSERT, NOT_IN_EMPTY, RTC_REFL] THEN
      MAP_EVERY X_GEN_TAC [ [[f:num]], [[args:term list]] ] THEN
      DISCH_TAC THEN REWRITE_TAC [IN_LIST_UNION] THEN
      REWRITE_TAC [EX_MAP, o_DEF] THEN X_GEN_TAC [[z:num]] THEN
      REWRITE_TAC [(← HolLight.GSYM EX_MEM)] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[s:term]]) STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC RTC_TRANS_L THEN EXISTS_TAC [[s:term]] THEN CONJ_TAC THENL
       [UNDISCH_TAC
         [[ALL (\t. !y. y IN FVT t ==> RTC SUB1 (V y) t) args]] THEN
        REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN ASM_MESON_TAC [],
        REWRITE_TAC [SUB1] THEN ASM_MESON_TAC []],
      ALL_TAC] THEN
    STRIP_TAC THEN MATCH_MP_TAC TC_SUB1_IRREFL THEN
    ONCE_REWRITE_TAC [TC_TC_RTC_CASES] THEN
    EXISTS_TAC [[(i:num->term) y]] THEN CONJ_TAC THENL
     [FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP UNIFY_OCCURS_PROPER) THEN
      DISCH_THEN (MP_TAC o HolLight.SPECL [ [[y:num]], [[x:num]] ]) THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[!t y. y IN FVT t ==> RTC SUB1 (V y) t]]) MP_TAC THENL
     [ALL_TAC,
      SUBGOAL_THEN
       ([[!s t. RTC SUB1 s t ==> RTC SUB1 (termsubst i s) (termsubst i t)]])
       (fun th => ASM_MESON_TAC [th, termsubst]) THEN
      MATCH_MP_TAC RTC_INDUCT THEN REWRITE_TAC [RTC_REFL] THEN
      CONJ_TAC THENL [ALL_TAC, MESON_TAC [RTC_TRANS]] THEN
      MAP_EVERY X_GEN_TAC [ [[s:term]], [[u:term]] ] THEN
      DISCH_THEN (fun th => HolLight.tactic_of do pure (MATCH_MP_TAC RTC_INC THEN MP_TAC th)) THEN
      REWRITE_TAC [SUB1] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[f:num]]) (X_CHOOSE_THEN ([[args:term list]])
          STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [ [[f:num]], [[MAP (termsubst i) args]] ] THEN
      ASM_REWRITE_TAC [termsubst, MEM_MAP] THEN ASM_MESON_TAC []] THEN
    MATCH_MP_TAC term_INDUCT THEN
    SIMP_TAC [FVT, IN_INSERT, NOT_IN_EMPTY, RTC_REFL] THEN
    MAP_EVERY X_GEN_TAC [ [[f:num]], [[args:term list]] ] THEN
    DISCH_TAC THEN REWRITE_TAC [IN_LIST_UNION] THEN
    REWRITE_TAC [EX_MAP, o_DEF] THEN X_GEN_TAC [[z:num]] THEN
    REWRITE_TAC [(← HolLight.GSYM EX_MEM)] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[s:term]]) STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC RTC_TRANS_L THEN EXISTS_TAC [[s:term]] THEN CONJ_TAC THENL
     [UNDISCH_TAC
       [[ALL (\t. !y. y IN FVT t ==> RTC SUB1 (V y) t) args]] THEN
      REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN ASM_MESON_TAC [],
      REWRITE_TAC [SUB1] THEN ASM_MESON_TAC []])
  : ExceptT String IO thm).run
#eval BADLOOP_UNUNIFIABLE

#eval phrase 70
unsafe def UNIFY_WORKS_RAW : thm := keep "UNIFY_WORKS_RAW" fun _ => (do
  prove ([[!pr. LOOPFREE(FST pr) /\ CONFLICTFREE(FST pr)
        ==> ((unify pr = NONE)
             ==> !i. ~(unifies i (APPEND (MAP (\(x,t). V x,t) (FST pr))
                                         (SND pr)))) /\
            !ans. (unify pr = SOME ans)
                  ==> LOOPFREE(ans) /\ CONFLICTFREE(ans) /\
                      !i. unifies i (APPEND (MAP (\(x,t). V x,t) (FST pr))
                                            (SND pr)) =
                          unifies i (MAP (\(x,t). V x,t) ans)]])
   (MATCH_MP_TAC (← HolLight.REWRITE_RULE [WF_IND] WF_CALLORDER) THEN
    GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[env:(num#term)list]], [[eqs:(term#term)list]] ] THEN
    DISCH_THEN (MP_TAC o HolLight.GENL [ [[env':(num#term)list]], [[eqs':(term#term)list]] ] o
                  HolLight.SPEC [[env':(num#term)list,eqs':(term#term)list]]) THEN
    REWRITE_TAC [FST, SND] THEN DISCH_TAC THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    ONCE_REWRITE_TAC [unify_raw] THEN
    ASM_REWRITE_TAC [FST, SND] THEN
    MP_TAC (← HolLight.ISPEC ([[eqs:(term#term)list]]) list_CASES) THEN
    DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THENL
     [ASM_REWRITE_TAC [APPEND_NIL, OPTION_INJ, OPTION_DISTINCT] THEN
      GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [EXISTS_PAIR_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[s:term]]) (X_CHOOSE_THEN ([[t:term]])
          (X_CHOOSE_THEN ([[oth:(term#term)list]]) SUBST_ALL_TAC))) THEN
    REWRITE_TAC [NOT_CONS_NIL, HD, TL] THEN
    MP_TAC (← HolLight.ISPEC ([[s:term]]) term_CASES) THEN
    DISCH_THEN (DISJ_CASES_THEN2
     (X_CHOOSE_THEN ([[x:num]]) SUBST_ALL_TAC)
     (X_CHOOSE_THEN ([[f:num]]) (X_CHOOSE_THEN ([[fargs:term list]])
          SUBST_ALL_TAC)))
    THENL
     [ALL_TAC,
      MP_TAC (← HolLight.ISPEC ([[t:term]]) term_CASES) THEN
      DISCH_THEN (DISJ_CASES_THEN2
       (X_CHOOSE_THEN ([[x:num]]) SUBST_ALL_TAC)
       (X_CHOOSE_THEN ([[g:num]]) (X_CHOOSE_THEN ([[gargs:term list]])
           SUBST_ALL_TAC)))] THEN
    REWRITE_TAC [tpcases] THENL
     [ASM_CASES_TAC [[MEM x (MAP FST (env:(num#term)list))]] THEN
      ASM_REWRITE_TAC [] THENL
       [FIRST_X_ASSUM (MP_TAC o HolLight.SPECL
         [ [[env:(num#term)list]],
          [[CONS (ASSOC (x:num) env,t) (oth:(term#term)list)]] ]) THEN
        ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
         [ASM_REWRITE_TAC [CALLORDER, CRIGHT] THEN
          DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN ASM_MESON_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN
         ([[!i. unifies i
              (APPEND (MAP (\(x,t). V x,t) env) (CONS (ASSOC x env,t) oth)) =
            unifies i
              (APPEND (MAP (\(x,t). V x,t) env) (CONS (V x,t) oth))]])
         (fun th => REWRITE_TAC [th]) THEN
        X_GEN_TAC [[i:num->term]] THEN
        REWRITE_TAC [unifies, ALL, ALL_APPEND] THEN
        CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
        REWRITE_TAC [ALL_MAP] THEN
        MATCH_MP_TAC (← ExceptT.mk (TAUT
         [[(a ==> (b <=> b')) ==> (a /\ b /\ c <=> a /\ b' /\ c)]])) THEN
        UNDISCH_TAC [[MEM x (MAP FST (env:(num#term)list))]] THEN
        SPEC_TAC ([[env:(num#term)list]], [[env:(num#term)list]]) THEN
        MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC [MEM, ALL, MAP] THEN
        GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
        MAP_EVERY X_GEN_TAC [ [[y:num]], [[s:term]], [[eev:(num#term)list]] ] THEN
        REWRITE_TAC [FST, SND, o_DEF] THEN
        CONV_TAC (HolLight.TOP_DEPTH_CONV GEN_BETA_CONV) THEN
        ASM_CASES_TAC [[x = y:num]] THEN ASM_REWRITE_TAC [ASSOC] THEN
        MESON_TAC [], ALL_TAC] THEN
      ASM_CASES_TAC [[istriv env x t = Exception]] THEN ASM_REWRITE_TAC [] THENL
       [REWRITE_TAC [OPTION_DISTINCT] THEN
        MP_TAC (← HolLight.SPECL [ [[env:(num#term)list]], [[x:num]], [[t:term]] ]
                BADLOOP_UNUNIFIABLE) THEN
        ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [unifies, ALL_APPEND, ALL] THEN
        MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN CONV_TAC TAUT, ALL_TAC] THEN
      ASM_CASES_TAC [[istriv env x t = TT]] THEN ASM_REWRITE_TAC [] THENL
       [FIRST_X_ASSUM (MP_TAC o HolLight.SPECL
          [ [[env:(num#term)list]], [[oth:(term#term)list]] ]) THEN
        ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
         [ASM_REWRITE_TAC [CALLORDER, CRIGHT] THEN
          DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN ASM_MESON_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN
         ([[!i. unifies i
              (APPEND (MAP (\(x,t). V x,t) env) (CONS (V x,t) oth)) =
            unifies i
              (APPEND (MAP (\(x,t). V x,t) env) oth)]])
         (fun th => REWRITE_TAC [th]) THEN
        MP_TAC (← HolLight.SPECL [ [[env:(num#term)list]], [[x:num]], [[t:term]] ]
                GOODLOOP_UNIFIABLE) THEN
        ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [unifies, ALL_APPEND, ALL] THEN
        MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN CONV_TAC TAUT,
        ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPECL
          [ [[CONS (x:num,t:term) env]], [[oth:(term#term)list]] ]) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC [CALLORDER] THEN DISJ1_TAC THEN
        REWRITE_TAC [MEASURE, MLEFT] THEN
        REWRITE_TAC [MAP, FST, SND, LENGTH] THEN
        MATCH_MP_TAC (← ExceptT.mk (ARITH_RULE
         [[(a' = a) /\ (b' = b + 1) /\ b' <= a' ==> a' - b' < a - b]])) THEN
        SUBGOAL_THEN
         ([[FVT(Fn 0 (CONS ((V o FST) (x,t:term)) (MAP (V o FST) env))) =
        x INSERT FVT(Fn 0 (MAP (V o FST) (env:(num#term)list)))]])
        SUBST1_TAC THENL
         [REWRITE_TAC [FVT, MAP, LIST_UNION, o_THM, FST] THEN SET_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN
         ([[FVT(Fn 0 (CONS (V x) (MAP FST (oth:(term#term)list)))) =
        x INSERT FVT(Fn 0 (MAP FST oth))]])
        SUBST1_TAC THENL
         [REWRITE_TAC [FVT, MAP, LIST_UNION, o_THM, FST] THEN SET_TAC [],
          ALL_TAC] THEN
        SUBGOAL_THEN
         ([[FVT(Fn 0 (CONS t (MAP SND env))) =
        FVT(t) UNION FVT(Fn 0 (MAP SND (env:(num#term)list)))]])
        SUBST1_TAC THENL
         [REWRITE_TAC [FVT, MAP, LIST_UNION, o_THM, FST], ALL_TAC] THEN
        SUBGOAL_THEN
         ([[FVT(Fn 0 (CONS t (MAP SND oth))) =
        FVT(t) UNION FVT(Fn 0 (MAP SND (oth:(term#term)list)))]])
        SUBST1_TAC THENL
         [REWRITE_TAC [FVT, MAP, LIST_UNION, o_THM, FST], ALL_TAC] THEN
        REPEAT CONJ_TAC THENL
         [AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_UNION, DISJ_ACI, IN_INSERT],
          SIMP_TAC [CARD_CLAUSES, FVT_FINITE, ADD1] THEN
          COND_CASES_TAC THEN REWRITE_TAC [] THEN
          UNDISCH_TAC
           [[x IN FVT (Fn 0 (MAP (V o FST) (env:(num#term)list)))]] THEN
          UNDISCH_TAC [[~MEM x (MAP FST (env:(num#term)list))]] THEN
          MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> a) ==> ~a ==> b ==> c]])) THEN
          SPEC_TAC ([[env:(num#term)list]], [[env:(num#term)list]]) THEN
          REWRITE_TAC [FVT] THEN LIST_INDUCT_TAC THEN
          REWRITE_TAC [LIST_UNION, MEM, MAP, NOT_IN_EMPTY] THEN
          REWRITE_TAC [o_THM, FVT, IN_UNION, IN_INSERT, NOT_IN_EMPTY] THEN
          STRIP_TAC THEN ASM_SIMP_TAC [],
          MATCH_MP_TAC CARD_SUBSET THEN
          REWRITE_TAC [FINITE_UNION, FVT_FINITE, FINITE_INSERT] THEN
          REWRITE_TAC [SUBSET, IN_UNION, IN_INSERT] THEN
          REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []], ALL_TAC] THEN
      ANTS_TAC THENL
       [MP_TAC (← HolLight.SPECL [ [[env:(num#term)list]], [[x:num]], [[t:term]] ] ISTRIV_WORKS) THEN
        ASM_REWRITE_TAC [] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
        ASM_SIMP_TAC [LOOPFREE_PRESERVE_EQ] THEN
        UNDISCH_TAC [[CONFLICTFREE env]] THEN
        REWRITE_TAC [CONFLICTFREE, LENGTH, FILTER] THEN
        CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC [[y:num]] THEN
        ASM_CASES_TAC [[x:num = y]] THEN ASM_REWRITE_TAC [LENGTH] THEN
        MATCH_MP_TAC (← ExceptT.mk (ARITH_RULE [[(x = 0) ==> y <= z ==> SUC x <= 1]])) THEN
        UNDISCH_THEN ([[x:num = y]]) (SUBST_ALL_TAC oTIO HolLight.SYM) THEN
        REWRITE_TAC [LENGTH_EQ_NIL] THEN
        UNDISCH_TAC [[~(MEM x (MAP FST (env:(num#term)list)))]] THEN
        SPEC_TAC ([[env:(num#term)list]], [[env:(num#term)list]]) THEN
        LIST_INDUCT_TAC THEN
        ASM_REWRITE_TAC [MEM, MAP, FILTER, NOT_CONS_NIL] THEN
        SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[h:num#term]]) PAIR)) THEN
        CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
        REWRITE_TAC [FST, SND] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN
       ([[!i. unifies i (APPEND (MAP (\(x,t). V x,t) (CONS (x,t) env)) oth) =
          unifies i (APPEND (MAP (\(x,t). V x,t) env) (CONS (V x,t) oth))]])
       (fun th => REWRITE_TAC [th]) THEN
      REWRITE_TAC [unifies, ALL_APPEND, ALL, MAP] THEN GEN_TAC THEN
      CONV_TAC (HolLight.TOP_DEPTH_CONV GEN_BETA_CONV) THEN CONV_TAC TAUT,

      FIRST_X_ASSUM (MP_TAC o HolLight.SPECL
       [ [[env:(num#term)list]], [[CONS (V x,Fn f fargs) oth]] ]) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC [CALLORDER, CRIGHT] THEN
        REPEAT DISJ2_TAC THEN ASM_MESON_TAC [], ALL_TAC] THEN
      REWRITE_TAC [unifies, ALL_APPEND, ALL] THEN
      CONV_TAC (HolLight.TOP_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC [EQ_SYM_EQ],

      COND_CASES_TAC THEN ASM_REWRITE_TAC [OPTION_DISTINCT] THENL
       [ALL_TAC,
        REWRITE_TAC [unifies, ALL, ALL_APPEND] THEN
        CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
        REWRITE_TAC [termsubst, term_INJ] THEN
        ASM_MESON_TAC [LENGTH_MAP]] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPECL
       [ [[env:(num#term)list]],
        [[APPEND (ZIP fargs gargs) (oth:(term#term)list)]] ]) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC [CALLORDER, CRIGHT] THEN
        DISJ2_TAC THEN DISJ1_TAC THEN ASM_MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN
       ([[!i. unifies i (APPEND (MAP (\(x,t). V x,t) env)
                            (APPEND (ZIP fargs gargs) oth)) =
          unifies i (APPEND (MAP (\(x,t). V x,t) env)
                            (CONS (Fn g fargs,Fn g gargs) oth))]])
       (fun th => REWRITE_TAC [th]) THEN
      X_GEN_TAC [[i:num->term]] THEN REWRITE_TAC [unifies, ALL, ALL_APPEND] THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC [termsubst, term_INJ] THEN
      FIRST_ASSUM (MP_TAC o HolLight.CONJUNCT2) THEN
      SPEC_TAC ([[gargs:term list]], [[gargs:term list]]) THEN
      SPEC_TAC ([[fargs:term list]], [[fargs:term list]]) THEN
      LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
      ASM_REWRITE_TAC [LENGTH, ALL, MAP, NOT_SUC, ZIP] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      ASM_SIMP_TAC [SUC_INJ, CONS_11]])
  : ExceptT String IO thm).run
#eval UNIFY_WORKS_RAW

#eval phrase 71
unsafe def THE : thm := keep "THE" fun _ => (do
  newRec option_RECURSION
   [[THE(SOME x) = x]]
  : ExceptT String IO thm).run
#eval THE

#eval phrase 72
unsafe def unifier : thm := keep "unifier" fun _ => new_definition
  [[unifier env =
     let sol = SOLVE [] env in ITLIST valmod sol V]]
#eval unifier

#eval phrase 73
unsafe def ITLIST_VALMOD_LEMMA : thm := keep "ITLIST_VALMOD_LEMMA" fun _ => (do
  prove ([[!env x. CONFLICTFREE(env)
           ==> !t. (ITLIST valmod env V x = t) <=>
                   MEM (x,t) env \/ (t = V x) /\ ~(MEM x (MAP FST env))]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [CONFLICTFREE] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[x:num]]) THEN
    SPEC_TAC ([[env:(num#term)list]], [[env:(num#term)list]]) THEN
    LIST_INDUCT_TAC THEN
    REWRITE_TAC [FILTER, LENGTH, ITLIST, MAP, MEM] THENL
     [MESON_TAC [], ALL_TAC] THEN
    SPEC_TAC ([[h:num#term]], [[h:num#term]]) THEN
    GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[z:num]], [[s:term]] ] THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    ASM_CASES_TAC [[z = x:num]] THEN
    ASM_REWRITE_TAC [PAIR_EQ, LENGTH, valmod] THEN
    REWRITE_TAC [(← ExceptT.mk (ARITH_RULE [[SUC n <= 1 <=> (n = 0)]])), LENGTH_EQ_NIL] THEN
    REWRITE_TAC [RIGHT_IMP_FORALL_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> ~c) /\ (b <=> b') ==> a ==> (b <=> b' \/ c)]])) THEN
    CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [EQ_SYM_EQ]] THEN
    DISCH_THEN (MP_TAC o HolLight.AP_TERM [[MEM (x:num,t':term)]]) THEN
    REWRITE_TAC [MEM, MEM_FILTER] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval ITLIST_VALMOD_LEMMA

#eval phrase 74
unsafe def UNIFIER_WORKS : thm := keep "UNIFIER_WORKS" fun _ => (do
  prove ([[!env. LOOPFREE(env) /\ CONFLICTFREE(env)
         ==> unifies (unifier env) (MAP (\(x,t). V x,t) env)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [unifier] THEN LET_TAC THEN
    MP_TAC (← HolLight.SPEC ([[env:(num#term)list]]) SOLVE_WORKS) THEN ASM_REWRITE_TAC [] THEN
    ABBREV_TAC [[i = ITLIST valmod sol V]] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC o HolLight.SPEC [[i:num->term]]) MP_TAC) THEN
    DISCH_TAC THEN
    REWRITE_TAC [unifies, ALL_MAP, o_DEF] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM PAIRED_ETA_THM)] THEN
    REWRITE_TAC [] THEN CONV_TAC (HolLight.REDEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC [termsubst, (← HolLight.GSYM ALL_MEM)] THEN
    GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
    CONV_TAC (HolLight.REDEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC [] THEN
    MAP_EVERY X_GEN_TAC [ [[x:num]], [[t:term]] ] THEN DISCH_TAC THEN
    Fol.EXPAND_TAC "i" THEN ASM_SIMP_TAC [ITLIST_VALMOD_LEMMA] THEN
    SUBGOAL_THEN ([[termsubst i t = t]]) (fun th => ASM_REWRITE_TAC [th]) THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM TERMSUBST_TRIV)] THEN
    MATCH_MP_TAC TERMSUBST_VALUATION THEN X_GEN_TAC [[z:num]] THEN DISCH_TAC THEN
    Fol.EXPAND_TAC "i" THEN ASM_SIMP_TAC [ITLIST_VALMOD_LEMMA] THEN
    DISJ2_TAC THEN REWRITE_TAC [MEM_MAP] THEN
    ONCE_REWRITE_TAC [EXISTS_PAIR_THM] THEN ASM_MESON_TAC [FST])
  : ExceptT String IO thm).run
#eval UNIFIER_WORKS

#eval phrase 75
unsafe def UNIFIER_MGU : thm := keep "UNIFIER_MGU" fun _ => (do
  prove ([[!env. LOOPFREE(env) /\ CONFLICTFREE(env)
         ==> !i. unifies i (MAP (\(x,t). V x,t) env)
                 ==> (termsubst i =
                      termsubst i o
                      termsubst (ITLIST valmod env V))]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM, o_THM] THEN
    X_GEN_TAC [[s:term]] THEN REWRITE_TAC [TERMSUBST_TERMSUBST] THEN
    MATCH_MP_TAC TERMSUBST_VALUATION THEN X_GEN_TAC [[y:num]] THEN
    DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN REWRITE_TAC [o_THM] THEN
    UNDISCH_TAC [[unifies i (MAP (\(x,t). V x,t) env)]] THEN
    REWRITE_TAC [unifies, ALL_MAP, o_DEF] THEN
    GEN_REWRITE_TAC (HolCore.Lib.funpow 2 HolLight.LAND_CONV) [(← HolLight.GSYM PAIRED_ETA_THM)] THEN
    REWRITE_TAC [] THEN CONV_TAC (HolLight.REDEPTH_CONV GEN_BETA_CONV) THEN
    SPEC_TAC ([[env:(num#term)list]], [[env:(num#term)list]]) THEN
    REWRITE_TAC [termsubst] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [ITLIST, TERMSUBST_TRIV, termsubst] THEN
    SPEC_TAC ([[h:num#term]], [[h:num#term]]) THEN
    GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[z:num]], [[s:term]] ] THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC [unifies, ALL, MAP] THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC [valmod] THEN COND_CASES_TAC THEN ASM_SIMP_TAC [] THEN
    UNDISCH_THEN ([[y = z:num]]) (SUBST_ALL_TAC oTIO HolLight.SYM) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (SUBST_ALL_TAC oTIO HolLight.SYM) ASSUME_TAC) THEN
    ASM_SIMP_TAC [])
  : ExceptT String IO thm).run
#eval UNIFIER_MGU

#eval phrase 76
unsafe def UNIFY_WORKS : thm := keep "UNIFY_WORKS" fun _ => (do
  prove ([[!env eqs.
     LOOPFREE(env) /\ CONFLICTFREE(env)
     ==> ((unify (env,eqs) = NONE)
          ==> !i. ~(unifies i (APPEND (MAP (\(x,t). V x,t) env) eqs))) /\
         ((unify (env,eqs) = SOME ans)
          ==> LOOPFREE(ans) /\ CONFLICTFREE(ans) /\
              unifies (unifier ans) (APPEND (MAP (\(x,t). V x,t) env) eqs) /\
              !i. unifies i (APPEND (MAP (\(x,t). V x,t) env) eqs)
                  ==> (termsubst i = termsubst i o termsubst (unifier ans)))]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← HolLight.SPEC ([[env:(num#term)list,eqs:(term#term)list]]) UNIFY_WORKS_RAW) THEN
    ASM_REWRITE_TAC [FST, SND] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[ans:(num#term)list]]) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [unifier] THEN LET_TAC THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV Session.let_CONV) THEN
    MP_TAC (← HolLight.SPEC ([[ans:(num#term)list]]) SOLVE_WORKS) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    MP_TAC (← HolLight.SPEC ([[ans:(num#term)list]]) UNIFIER_WORKS) THEN
    MP_TAC (← HolLight.SPEC ([[sol:(num#term)list]]) UNIFIER_MGU) THEN
    SUBGOAL_THEN ([[LOOPFREE(sol)]]) ASSUME_TAC THENL
     [REWRITE_TAC [LOOPFREE] THEN X_GEN_TAC [[z:num]] THEN
      ONCE_REWRITE_TAC [TC_RTC_CASES_R] THEN
      ONCE_REWRITE_TAC [RTC_CASES_R] THEN
      REWRITE_TAC [OCC] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[!i. unifies i (MAP (\(x,t). V x,t) ans) =
                    unifies i (MAP (\(x,t). V x,t) sol)]])
     (fun th => SIMP_TAC [th])
    THENL
     [GEN_TAC THEN REWRITE_TAC [unifies, ALL_MAP, o_DEF] THEN
      REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN ONCE_REWRITE_TAC [FORALL_PAIR_THM] THEN
      CONV_TAC (HolLight.TOP_DEPTH_CONV GEN_BETA_CONV) THEN
      ASM_REWRITE_TAC [termsubst], ALL_TAC] THEN
    ASM_REWRITE_TAC [unifier] THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV Session.let_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval UNIFY_WORKS

#eval phrase 77
unsafe def UNIFY_WORKS_SIMPLE : thm := keep "UNIFY_WORKS_SIMPLE" fun _ => (do
  prove ([[!eqs. ((unify ([],eqs) = NONE) ==> !i. ~(unifies i eqs)) /\
         ((unify ([],eqs) = SOME ans)
          ==> LOOPFREE(ans) /\ CONFLICTFREE(ans) /\
              unifies (unifier ans) eqs /\
              !i. unifies i eqs
                  ==> (termsubst i = termsubst i o termsubst (unifier ans)))]])
   (GEN_TAC THEN MP_TAC (← HolLight.SPEC ([[[]:(num#term)list]]) UNIFY_WORKS) THEN
    REWRITE_TAC [MAP, APPEND] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC [LOOPFREE, CONFLICTFREE, LENGTH, FILTER, ARITH] THEN
    ONCE_REWRITE_TAC [TC_CASES_L] THEN REWRITE_TAC [OCC, MEM])
  : ExceptT String IO thm).run
#eval UNIFY_WORKS_SIMPLE

#eval phrase 78
unsafe def Unifies_DEF : thm := keep "Unifies_DEF" fun _ => new_definition
  [[Unifies i s <=> !p q. p IN s /\ q IN s ==> (formsubst i p = formsubst i q)]]
#eval Unifies_DEF

#eval phrase 79
unsafe def UNIFIES : thm := keep "UNIFIES" fun _ => (do
  prove ([[Unifies i s <=> ?q. !p. p IN s ==> (formsubst i p = q)]])
   (MESON_TAC [Unifies_DEF])
  : ExceptT String IO thm).run
#eval UNIFIES

#eval phrase 80
unsafe def UNIFIER_FORMPAIR_TERMLIST : thm := keep "UNIFIER_FORMPAIR_TERMLIST" fun _ => (do
  let lemma ← (do
    prove ([[?l. !i. ~(unifies i l)]])
     (EXISTS_TAC [[ [Fn 0 [], Fn 1 [] ] ]] THEN
      REWRITE_TAC [ALL, unifies] THEN CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC [termsubst, term_INJ, ARITH])
    : ExceptT String IO thm)
  prove ([[!p q. qfree(p) /\ qfree(q)
         ==> ?l. !i. (formsubst i p = formsubst i q) <=> unifies i l]])
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC [qfree] THEN
    REPEAT CONJ_TAC THENL
     [ALL_TAC,
      MAP_EVERY X_GEN_TAC [ [[f:num]], [[fargs:term list]] ],
      MAP_EVERY X_GEN_TAC [ [[p:form]], [[q:form]] ] THEN
      DISCH_THEN (fun th => HolLight.tactic_of do pure (STRIP_TAC THEN MP_TAC th)) THEN
      ASM_REWRITE_TAC [] THEN STRIP_TAC] THEN
    MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC [qfree] THEN
    REWRITE_TAC [formsubst, form_DISTINCT, lemma] THENL
     [EXISTS_TAC [[[]:(term#term)list]] THEN REWRITE_TAC [unifies, ALL],
      MAP_EVERY X_GEN_TAC [ [[g:num]], [[gargs:term list]] ] THEN
      REWRITE_TAC [form_INJ] THEN
      ASM_CASES_TAC [[f:num = g]] THEN ASM_REWRITE_TAC [lemma] THEN
      ASM_CASES_TAC [[LENGTH(fargs:term list) = LENGTH(gargs:term list)]] THENL
       [ALL_TAC, ASM_MESON_TAC [LENGTH_MAP, lemma]] THEN
      EXISTS_TAC [[ZIP (fargs:term list) (gargs:term list)]] THEN
      REWRITE_TAC [unifies] THEN X_GEN_TAC [[i:num->term]] THEN
      UNDISCH_TAC [[LENGTH(fargs:term list) = LENGTH(gargs:term list)]] THEN
      SPEC_TAC ([[gargs:term list]], [[gargs:term list]]) THEN
      SPEC_TAC ([[fargs:term list]], [[fargs:term list]]) THEN
      LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
      REWRITE_TAC [LENGTH, NOT_SUC, MAP, ZIP, ALL, SUC_INJ] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV GEN_BETA_CONV) THEN ASM_SIMP_TAC [CONS_11],
      MAP_EVERY X_GEN_TAC [ [[r:form]], [[s:form]] ] THEN
      DISCH_THEN (fun th => HolLight.tactic_of do pure (STRIP_TAC THEN MP_TAC th)) THEN
      ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_SIMP_TAC [form_INJ] THEN
      UNDISCH_TAC
       [[!q. qfree q
          ==> (?l. !i. (formsubst i p = formsubst i q) <=> unifies i l)]] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[r:form]]) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[l1:(term#term)list]])
       (fun th => REWRITE_TAC [th])) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[s:form]]) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[l2:(term#term)list]])
       (fun th => REWRITE_TAC [th])) THEN
      EXISTS_TAC [[APPEND (l1:(term#term)list) l2]] THEN
      REWRITE_TAC [unifies, ALL_APPEND]])
  : ExceptT String IO thm).run
#eval UNIFIER_FORMPAIR_TERMLIST

#eval phrase 81
unsafe def UNIFIER_SUBTERMS : thm := keep "UNIFIER_SUBTERMS" fun _ => (do
  prove ([[!A. FINITE A /\ (!p. p IN A ==> qfree p)
       ==> ?l. !i. Unifies i A = unifies i l]])
   (REPEAT STRIP_TAC THEN
    ABBREV_TAC [[B = {(x:form,y) | x IN A /\ y IN A}]] THEN
    SUBGOAL_THEN ([[!i. Unifies i A =
                    !p q. (p,q) IN B ==> (formsubst i p = formsubst i q)]])
     (fun th => REWRITE_TAC [th])
    THENL
     [Fol.EXPAND_TAC "B" THEN
      REWRITE_TAC [IN_ELIM_THM, Unifies_DEF, PAIR_EQ] THEN MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[!p q. (p,q) IN B ==> qfree p /\ qfree q]]) MP_TAC THENL
     [Fol.EXPAND_TAC "B" THEN
      REWRITE_TAC [IN_ELIM_THM, PAIR_EQ] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[FINITE(B:(form#form)->bool)]]) MP_TAC THENL
     [Fol.EXPAND_TAC "B" THEN MATCH_MP_TAC FINITE_PRODUCT THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
    SPEC_TAC ([[B:(form#form)->bool]], [[B:(form#form)->bool]]) THEN
    POP_ASSUM_LIST (HolCore.Lib.K ALL_TAC) THEN MATCH_MP_TAC FINITE_INDUCT THEN
    CONJ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC [[[]:(term#term)list]] THEN
      REWRITE_TAC [NOT_IN_EMPTY, ALL, unifies], ALL_TAC] THEN
    GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[p:form]], [[q:form]], [[B:(form#form)->bool]] ] THEN
    REWRITE_TAC [IN_INSERT, PAIR_EQ] THEN
    REWRITE_TAC [(← ExceptT.mk (TAUT [[a \/ b ==> c <=> (a ==> c) /\ (b ==> c)]]))] THEN
    SIMP_TAC [FORALL_AND_THM, LEFT_FORALL_IMP_THM, EXISTS_REFL,
             LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do pure (STRIP_TAC THEN MP_TAC th)) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_TAC [[l:(term#term)list]]) THEN
    MP_TAC (← HolLight.SPECL [ [[p:form]], [[q:form]] ] UNIFIER_FORMPAIR_TERMLIST) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_TAC [[m:(term#term)list]]) THEN
    EXISTS_TAC [[APPEND (l:(term#term)list) m]] THEN
    REWRITE_TAC [unifies, ALL_APPEND] THEN
    ASM_REWRITE_TAC [(← HolLight.GSYM unifies)] THEN REWRITE_TAC [CONJ_ACI])
  : ExceptT String IO thm).run
#eval UNIFIER_SUBTERMS

#eval phrase 82
unsafe def MGU_EXISTS : thm := keep "MGU_EXISTS" fun _ => (do
  prove ([[FINITE s /\ (!p. p IN s ==> qfree p)
   ==> ((?i. Unifies i s) <=>
        (?i. Unifies i s /\
             !j. Unifies j s
                 ==> !p. qfree p
                         ==> (formsubst j p = formsubst j (formsubst i p))))]])
   (DISCH_THEN (fun th => HolLight.tactic_of do
       let r ← HolLight.MATCH_MP UNIFIER_SUBTERMS th
       pure (X_CHOOSE_THEN ([[l:(term#term)list]]) (fun th2 => REWRITE_TAC [th2]) r)) THEN
    EQ_TAC THEN DISCH_THEN (X_CHOOSE_THEN ([[i:num->term]]) STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [] THENL [ALL_TAC, ASM_MESON_TAC []] THEN
    EXISTS_TAC [[unifier(THE(unify([],l)))]] THEN
    MP_TAC (← HolLight.GEN ([[ans:(num#term)list]])
      (← HolLight.SPEC ([[l:(term#term)list]]) UNIFY_WORKS_SIMPLE)) THEN
    SPEC_TAC ([[unify ([],l)]], [[u:((num#term)list)option]]) THEN
    MATCH_MP_TAC option_INDUCT THEN
    REWRITE_TAC [(← ExceptT.mk (Session.prove_constructors_distinct option_RECURSION)),
                (← ExceptT.mk (Session.prove_constructors_injective option_RECURSION))] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    X_GEN_TAC [[u:(num#term)list]] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[u:(num#term)list]]) THEN REWRITE_TAC [THE] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC [[j:num->term]] THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC [] THEN
    REWRITE_TAC [FUN_EQ_THM, o_THM] THEN DISCH_THEN (ASSUME_TAC oTIO HolLight.GSYM) THEN
    MATCH_MP_TAC form_INDUCTION THEN
    REWRITE_TAC [formsubst, qfree] THEN SIMP_TAC [] THEN
    REWRITE_TAC [(← HolLight.GSYM MAP_o)] THEN
    REPEAT GEN_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
    ASM_REWRITE_TAC [o_THM, ALL_T])
  : ExceptT String IO thm).run
#eval MGU_EXISTS

#eval phrase 83
unsafe def mgu : thm := keep "mgu" fun _ => new_definition
  [[mgu s = @i. Unifies i s /\
               !j. Unifies j s
                   ==> !p. qfree p
                           ==> (formsubst j p =
                                formsubst j (formsubst i p))]]
#eval mgu

#eval phrase 84
unsafe def MGU : thm := keep "MGU" fun _ => (do
  prove ([[!s. FINITE s /\ (!p. p IN s ==> qfree p) /\ (?i. Unifies i s)
       ==> Unifies (mgu s) s /\
           !i. Unifies i s
               ==> !p. qfree p
                       ==> (formsubst i p =
                            formsubst i (formsubst (mgu s) p))]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [mgu] THEN
    CONV_TAC (fun t => pure (SELECT_CONV t)) THEN ASM_SIMP_TAC [(← HolLight.GSYM MGU_EXISTS)] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval MGU

#eval phrase 85
unsafe def FORMSUBST_TERMSUBST_LEMMA : thm := keep "FORMSUBST_TERMSUBST_LEMMA" fun _ => (do
  prove ([[(!p. qfree(p) ==> (formsubst i p = formsubst j (formsubst k p))) <=>
   (termsubst i = termsubst j o termsubst k)]])
   (REWRITE_TAC [FUN_EQ_THM, o_THM] THEN EQ_TAC THEN DISCH_TAC THENL
     [X_GEN_TAC [[t:term]] THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[Atom p [t] ]])) THEN
      REWRITE_TAC [qfree, formsubst, MAP, form_INJ, CONS_11],
      MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC [qfree] THEN
      SIMP_TAC [formsubst] THEN REWRITE_TAC [form_INJ, (← HolLight.GSYM MAP_o)] THEN
      GEN_TAC THEN MATCH_MP_TAC MAP_EQ THEN ASM_REWRITE_TAC [o_THM, ALL_T]])
  : ExceptT String IO thm).run
#eval FORMSUBST_TERMSUBST_LEMMA

#eval phrase 86
unsafe def ismgu : thm := keep "ismgu" fun _ => new_definition
  [[ismgu s i <=> Unifies i s /\
                 !j. Unifies j s
                     ==> ?k. (termsubst j = termsubst k o termsubst i)]]
#eval ismgu

#eval phrase 87
unsafe def ISMGU : thm := keep "ISMGU" fun _ => (do
  prove ([[ismgu s i <=> Unifies i s /\
                 !j. Unifies j s
                     ==> ?k. !p. qfree(p)
                                 ==> (formsubst j p =
                                      formsubst k (formsubst i p))]])
   (REWRITE_TAC [ismgu, FORMSUBST_TERMSUBST_LEMMA])
  : ExceptT String IO thm).run
#eval ISMGU

#eval phrase 88
unsafe def ISMGU_MGU : thm := keep "ISMGU_MGU" fun _ => (do
  prove ([[!s. FINITE(s) /\ (!p. p IN s ==> qfree p) /\ (?i. Unifies i s)
       ==> ismgu s (mgu s)]])
   (GEN_TAC THEN DISCH_THEN (fun th => HolLight.tactic_of do
       let r ← HolLight.MATCH_MP MGU th
       pure (STRIP_ASSUME_TAC r)) THEN
    ASM_REWRITE_TAC [ISMGU] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval ISMGU_MGU

#eval phrase 89
unsafe def «renaming» : thm := keep "renaming" fun _ => new_definition
  [[renaming i <=> ?j. (termsubst j o termsubst i = I) /\
                      (termsubst i o termsubst j = I)]]
#eval «renaming»

#eval phrase 90
unsafe def RENAMING : thm := keep "RENAMING" fun _ => (do
  prove ([[renaming i ==> (!x. ?y. i(x) = V y) /\
                  (!x x'. (i(x') = i(x)) ==> (x' = x))]])
   (REWRITE_TAC [«renaming», FUN_EQ_THM, o_THM, I_DEF] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[j:num->term]]) (ASSUME_TAC o HolLight.CONJUNCT1)) THEN
    CONJ_TAC THENL
     [X_GEN_TAC [[x:num]] THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[V x]]) THEN
      REWRITE_TAC [termsubst] THEN
      MESON_TAC [term_CASES, termsubst, term_DISTINCT],
      MAP_EVERY X_GEN_TAC [ [[x1:num]], [[x2:num]] ] THEN
      FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC ([[V x1]]) th) THEN
              MP_TAC (← HolLight.SPEC ([[V x2]]) th))) THEN
      REWRITE_TAC [termsubst] THEN MESON_TAC [term_INJ]])
  : ExceptT String IO thm).run
#eval RENAMING

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.Unif" do
  replay (
          HolLogicArith.Fole.ensure)
  replay (
          LEFT_AND_EX_THM)
  replay (
          EX_ADHOC)
  replay (
          ALL_ADHOC)
  replay (
          WF_FINITE_LEMMA)
  replay (
          TC_REV)
  replay (
          WF_DISJ)
  replay (
          WF_ALTERNATION)
  replay (
          MULTISET_FILTEREQ)
  replay (
          WF_MULTIZIP)
  replay (
          WF_MEASURE_OR_NONINC)
  replay (
          WF_PROJ_EQ)
  replay (
          OCC)
  replay (
          LOOPFREE)
  replay (
          LOOP_BREAK)
  replay (
          LOOPFREE_PRESERVE)
  replay (
          LOOPFREE_PRESERVE_EQ)
  replay (
          LOOPFREE_WF)
  replay (
          LOOPFREE_WF_TERM)
  replay (
          LOOPCHECK_EXISTS)
  replay (
          loopcheck_raw)
  replay (
          loopcheck)
  replay (
          LOOPCHECK)
  replay (
          rightsubst)
  replay (
          SOLVE_EXISTS)
  replay (
          SOLVEC_RAW)
  replay (
          SOLVE_1)
  replay (
          SOLVE)
  replay (
          CONFLICTFREE)
  replay (
          SOLVE_PRESERVES_LOOPFREE_LEMMA)
  replay (
          SOLVE_PRESERVES_LOOPFREE)
  replay (
          SOLVE_PRESERVES_CONFLICTFREE_LEMMA)
  replay (
          SOLVE_PRESERVES_CONFLICTFREE)
  replay (
          SOLVE_PRESERVES_DEFREE)
  replay (
          SOLVE_PRESERVES_UNIFIERS)
  replay (
          SOLVE_WORKS_GENERAL)
  replay (
          SOLVE_WORKS)
  replay (
          (do IO.println (← HolCore.Printer.string_of_thm retval_INDUCT)
              IO.println (← HolCore.Printer.string_of_thm retval_RECURSION) : IO Unit))
  replay (
          retval_DISTINCT)
  replay (
          ISTRIV_EXISTS)
  replay (
          istriv_raw)
  replay (
          istriv)
  replay (
          EQV)
  replay (
          EQV_IMP_OCC)
  replay (
          ISTRIV_WORKS)
  replay (
          SUB1)
  replay (
          WF_SUB1)
  replay (
          RTC_SUB1)
  replay (
          WF_SUBCOMPONENT)
  replay (
          WF_DESCENT)
  replay (
          termcases)
  replay (
          tpcases_def)
  replay (
          tpcases)
  replay (
          MLEFT)
  replay (
          CRIGHT)
  replay (
          CALLORDER)
  replay (
          PAIRED_ETA_THM)
  replay (
          WF_CRIGHT)
  replay (
          WF_CALLORDER)
  replay (
          UNIFY_EXISTS_RAW)
  replay (
          unify_raw)
  replay (
          unify)
  replay (
          unifies)
  replay (
          OPTION_DISTINCT)
  replay (
          OPTION_INJ)
  replay (
          TC_SUB1_IRREFL)
  replay (
          UNIFY_OCCURS)
  replay (
          UNIFY_OCCURS_PROPER)
  replay (
          GOODLOOP_UNIFIABLE)
  replay (
          BADLOOP_UNUNIFIABLE)
  replay (
          UNIFY_WORKS_RAW)
  replay (
          THE)
  replay (
          unifier)
  replay (
          ITLIST_VALMOD_LEMMA)
  replay (
          UNIFIER_WORKS)
  replay (
          UNIFIER_MGU)
  replay (
          UNIFY_WORKS)
  replay (
          UNIFY_WORKS_SIMPLE)
  replay (
          Unifies_DEF)
  replay (
          UNIFIES)
  replay (
          UNIFIER_FORMPAIR_TERMLIST)
  replay (
          UNIFIER_SUBTERMS)
  replay (
          MGU_EXISTS)
  replay (
          mgu)
  replay (
          MGU)
  replay (
          FORMSUBST_TERMSUBST_LEMMA)
  replay (
          ismgu)
  replay (
          ISMGU)
  replay (
          ISMGU_MGU)
  replay (
          «renaming»)
  replay (
          RENAMING)
-- @@ENSURE END

end HolLogicArith.Unif
