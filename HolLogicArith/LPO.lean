/- File: HolLogicArith/LPO.lean
Translation of HOL Light's Logic/lpo.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Given
open HolCore.Kernel Session HolLight.Syntax HolLogicArith
open scoped HolLight
open HolLogicArith.Fol
open HolLogicArith.Prenex
open HolLogicArith.Skolem
open HolLogicArith.FolProp
open HolLogicArith.Canon
open HolLogicArith.Fole
open HolLogicArith.Herbrand
open HolLogicArith.Unif
open HolLogicArith.Resolution
open HolLogicArith.Given

namespace HolLogicArith.LPO

/- List definitions/theorems used below are exposed by Session as fields of
   the `listDefs`/`listThms1`/`listThms2` bundles; alias the ones we need. -/
private unsafe def LENGTH : thm := Session.listDefs.LENGTH
private unsafe def MAP : thm := Session.listDefs.MAP
private unsafe def ITLIST : thm := Session.listDefs.ITLIST
private unsafe def MEM : thm := Session.listDefs.MEM
private unsafe def HD : thm := Session.listDefs.HD
private unsafe def TL : thm := Session.listDefs.TL
private unsafe def APPEND : thm := Session.listDefs.APPEND
private unsafe def MEM_MAP : thm := Session.listThms1.MEM_MAP
private unsafe def ALL_MAP : thm := Session.listThms1.ALL_MAP
private unsafe def ALL_MEM : thm := Session.listThms1.ALL_MEM
private unsafe def EX_MEM : thm := Session.listThms1.EX_MEM
private unsafe def LENGTH_MAP : thm := Session.listThms1.LENGTH_MAP
private unsafe def NOT_CONS_NIL : thm := Session.listThms1.NOT_CONS_NIL
private unsafe def LENGTH_EQ_NIL : thm := Session.listThms1.LENGTH_EQ_NIL
private unsafe def MEM_APPEND : thm := Session.listThms1.MEM_APPEND
private unsafe def LENGTH_APPEND : thm := Session.listThms1.LENGTH_APPEND

/- `subseq` / `SUBSEQ_SUC` come from the Library/analysis prelude. -/
private unsafe def subseq : thm := SessionLibrary.Analysis.subseq
private unsafe def SUBSEQ_SUC : thm := SessionLibrary.Analysis.SUBSEQ_SUC

#eval HolLogicArith.Given.ensure

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- `new_recursive_definition` lifted into `ExceptT String IO`. -/
private unsafe def newRec (ax : thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (Session.new_recursive_definition ax tm)

/- `new_inductive_definition`, panicking with HOL Light's message on failure. -/
private unsafe def newInductive (tm : term) : thm × thm × thm :=
  match unsafeIO (Session.new_inductive_definition tm) with
  | .ok (.ok t) => t
  | .ok (.error e) => panic! s!"new_inductive_definition: {e}"
  | .error e => panic! s!"new_inductive_definition IO: {e}"

/- `new_specification` lifted into `ExceptT String IO`. -/
private unsafe def newSpec (names : List String) (th : thm) : ExceptT String IO thm :=
  ExceptT.mk (Session.new_specification names th)

#eval phrase 1
unsafe def ITLIST_ADD_1_POS : thm := keep "ITLIST_ADD_1_POS" fun _ => (do
  prove ([[!l. 0 < ITLIST (+) l 1]])
   (LIST_INDUCT_TAC THEN REWRITE_TAC [ITLIST, ARITH] THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval ITLIST_ADD_1_POS

#eval phrase 2
unsafe def FVT_FUN_EMPTY : thm := keep "FVT_FUN_EMPTY" fun _ => (do
  prove ([[!f a args. MEM a args /\ (FVT(Fn f args) = {}) ==> (FVT a = {})]])
   (REWRITE_TAC [FVT, EXTENSION, NOT_IN_EMPTY, IN_LIST_UNION, MEM_MAP,
                 (← HolLight.GSYM EX_MEM), o_THM] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval FVT_FUN_EMPTY

#eval phrase 3
unsafe def NONWF : thm := keep "NONWF" fun _ => (do
  ExceptT.mk (Session.new_definition
    [[NONWF(R) a <=> ?s:num->A. (s 0 = a) /\ (!n. R (s(SUC n)) (s n))]])
  : ExceptT String IO thm).run
#eval NONWF

#eval phrase 4
unsafe def WF_NONWF : thm := keep "WF_NONWF" fun _ => (do
  prove ([[WF(R) <=> !a. ~(NONWF(R) a)]])
   (REWRITE_TAC [WF_DCHAIN, NONWF] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval WF_NONWF

#eval phrase 5
unsafe def NONWF_SUCCESSOR : thm := keep "NONWF_SUCCESSOR" fun _ => (do
  prove ([[!R a:A b. NONWF(R) b /\ R b a ==> NONWF(R) a]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [NONWF] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[s:num->A]]) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC [[\n. if n = 0 then a:A else s(n - 1)]] THEN
    REWRITE_TAC [NOT_SUC] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [ARITH] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (Session.ARITH_RULE [[~(n = 0) ==> (SUC n - 1 = SUC(n - 1))]]))])
  : ExceptT String IO thm).run
#eval NONWF_SUCCESSOR

#eval phrase 6
unsafe def WF_NONWF_2 : thm := keep "WF_NONWF_2" fun _ => (do
  prove ([[WF(\x:A y. R x y /\ ~(NONWF(R) y))]])
   (REWRITE_TAC [WF_DCHAIN, NONWF] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[s:num->A]]) MP_TAC) THEN
    REWRITE_TAC [FORALL_AND_THM] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[0]]) THEN REWRITE_TAC [] THEN
    EXISTS_TAC [[s:num->A]] THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval WF_NONWF_2

#eval phrase 7
unsafe def NONWF_INDUCT : thm := keep "NONWF_INDUCT" fun _ => (do
  let imp ← do
    let (a, _) ← HolLight.EQ_IMP_RULE WF_IND
    HolLight.MATCH_MP a WF_NONWF_2
  prove ([[(!a. ~(NONWF(R) a) /\ (!b. R b a ==> P(b)) ==> P(a))
   ==> !x. ~(NONWF(R) x) ==> P(x)]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC imp THEN
    REWRITE_TAC [] THEN ASM_MESON_TAC [NONWF_SUCCESSOR])
  : ExceptT String IO thm).run
#eval NONWF_INDUCT

#eval phrase 8
unsafe def WF_MINIMAL_STEP : thm := keep "WF_MINIMAL_STEP" fun _ => (do
  prove ([[!m:A->num a.
        NONWF(R) a
        ==> ?b. NONWF(R) b /\ R b a /\
                (!c. NONWF(R) c /\ R c a ==> m(b) <= m(c))]])
   (REPEAT STRIP_TAC THEN MP_TAC (← ExceptT.mk (HolLight.SPEC
     ([[\n. ?c. NONWF(R) c /\ R c a /\ ((m:A->num)(c) = n)]]) num_WOP)) THEN
    MATCH_MP_TAC (← ExceptT.mk (Session.TAUT [[(b ==> c) /\ a ==> (a <=> b) ==> c]])) THEN
    REWRITE_TAC [] THEN CONJ_TAC THENL [MESON_TAC [NOT_LT], ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [NONWF] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[s:num->A]]) STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [ [[(m:A->num) (s 1)]], [[(s:num->A) 1]] ] THEN
    ASM_REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN EXISTS_TAC [[\n. s(SUC n):A]] THEN
    ASM_REWRITE_TAC [ARITH] THEN ASM_MESON_TAC [(← ExceptT.mk (Session.num_CONV [[1]]))])
  : ExceptT String IO thm).run
#eval WF_MINIMAL_STEP

#eval phrase 9
unsafe def WF_MINIMAL_DCHAIN : thm := keep "WF_MINIMAL_DCHAIN" fun _ => (do
  prove ([[!m:A->num.
     WF(R) <=> ~(?t. (!n. R (t(SUC n)) (t n)) /\
                     (!s. NONWF(R) s ==> m(t 0) <= m(s)) /\
                     (!n s. NONWF(R) s /\ R s (t n) ==> m(t(SUC n)) <= m(s)))]])
   (GEN_TAC THEN REWRITE_TAC [WF_DCHAIN] THEN AP_TERM_TAC THEN
    EQ_TAC THENL [ALL_TAC, MESON_TAC []] THEN DISCH_TAC THEN
    MP_TAC (← ExceptT.mk (HolLight.SPEC ([[\n. ?s. NONWF(R) s /\ ((m:A->num)(s) = n)]]) num_WOP)) THEN
    MATCH_MP_TAC (← ExceptT.mk (Session.TAUT [[a /\ (b ==> c) ==> (a <=> b) ==> c]])) THEN CONJ_TAC THENL
     [REWRITE_TAC [NONWF] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[n_0:num]]) MP_TAC) THEN REWRITE_TAC [] THEN
    DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_THEN ([[a:A]]) STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN ([[!s. NONWF R s ==> (m:A->num)(a) <= m(s)]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [NOT_LT], ALL_TAC] THEN
    MP_TAC (← ExceptT.mk (HolLight.ISPECL
     [ [[a:A]], [[\b (n:num). @c. NONWF(R) c /\ R c b /\
                            !d. NONWF(R) d /\ R d b ==> (m:A->num)(c) <= m(d)]] ]
     num_RECURSION)) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[t:num->A]] THEN REWRITE_TAC [] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC (← ExceptT.mk (Session.TAUT [[!d. b /\ d /\ a /\ c ==> a /\ b /\ c]])) THEN
    EXISTS_TAC [[(!n. NONWF R (t(SUC n):A))]] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    REWRITE_TAC [AND_FORALL_THM] THEN INDUCT_TAC THENL
     [FIRST_ASSUM (SUBST1_TAC oTIO HolLight.SPEC ([[0]])),
      FIRST_ASSUM (SUBST1_TAC oTIO HolLight.SPEC ([[SUC n]]))] THEN
    CONV_TAC (fun t => pure (SELECT_CONV t)) THEN
    MATCH_MP_TAC WF_MINIMAL_STEP THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval WF_MINIMAL_DCHAIN

#eval phrase 10
unsafe def SEQUENCE_SUBSEQUENCE : thm := keep "SEQUENCE_SUBSEQUENCE" fun _ => (do
  prove ([[!P (x:num->A).
        (!n. ?m. n < m /\ P(x m)) ==> ?f. subseq f /\ !n. P(x(f n))]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [SKOLEM_THM, FORALL_AND_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[st:num->num]]) STRIP_ASSUME_TAC) THEN
    MP_TAC (← ExceptT.mk (HolLight.ISPECL [ [[st(0):num]], [[\m:num p:num. st(m):num]] ] num_RECURSION)) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[s:num->num]] THEN REWRITE_TAC [] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC [SUBSEQ_SUC] THEN ASM_MESON_TAC [],
      INDUCT_TAC THEN ASM_MESON_TAC []])
  : ExceptT String IO thm).run
#eval SEQUENCE_SUBSEQUENCE

#eval phrase 11
unsafe def SEQUENCE_PARTITION_LEMMA : thm := keep "SEQUENCE_PARTITION_LEMMA" fun _ => (do
  prove ([[!x:num->A s. FINITE(s) /\ (!n. x(n) IN s)
                ==> ?a f. subseq f /\ (!n. x(f n) = a)]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[?a:A. !n. ?m:num. n < m /\ (x m = a)]]) MP_TAC THENL
     [SUBGOAL_THEN
       ([[!s. FINITE s
          ==> (?n:num. !m. n < m ==> (x(m) IN s))
              ==> ?a:A. !n. ?m. n < m /\ (x m = a)]])
       (fun th => ASM_MESON_TAC [th]) THEN POP_ASSUM_LIST (HolCore.Lib.K ALL_TAC) THEN
      MATCH_MP_TAC FINITE_INDUCT THEN REWRITE_TAC [NOT_IN_EMPTY] THEN
      CONJ_TAC THENL [MESON_TAC [LT], ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [ [[b:A]], [[s:A->bool]] ] THEN
      MATCH_MP_TAC (← ExceptT.mk (Session.TAUT [[(~a /\ c ==> b) ==> (a ==> b) ==> (c ==> b)]])) THEN
      REWRITE_TAC [IN_INSERT, NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP] THEN
      ASM_MESON_TAC [(← ExceptT.mk (Session.ARITH_RULE [[(m + n < p:num ==> m < p /\ n < p)]]))],
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[a:A]] THEN DISCH_TAC THEN
    MP_TAC (← ExceptT.mk (HolLight.ISPEC ([[\x:A. x = a]]) SEQUENCE_SUBSEQUENCE)) THEN ASM_SIMP_TAC [])
  : ExceptT String IO thm).run
#eval SEQUENCE_PARTITION_LEMMA

#eval phrase 12
unsafe def termsize_EXISTS : thm := keep "termsize_EXISTS" fun _ => (do
  prove ([[?termsize.
     (!x. termsize(V x) = 1) /\
     (!f args. termsize(Fn f args) = ITLIST (+) (MAP termsize args) 1)]])
   (MP_TAC (← ExceptT.mk (HolLight.ISPECL [ [[\x:num. 1]],
                 [[\(f:num) (args:term list) (ns:num list). ITLIST (+) ns 1]],
                 [[[]:num list]],
                 [[\(t:term) (ts:term list) (n:num) (ns:num list). CONS n ns]] ]
                term_raw_RECURSION)) THEN
    REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [ITLIST, MAP])
  : ExceptT String IO thm).run
#eval termsize_EXISTS

#eval phrase 13
unsafe def termsize : thm := keep "termsize" fun _ => (do
  newSpec ["termsize"] termsize_EXISTS
  : ExceptT String IO thm).run
#eval termsize

#eval phrase 14
unsafe def LEX_DEF : thm := keep "LEX_DEF" fun _ => (do
  newRec Session.list_RECURSION
    [[(LEX(<<) [] l <=> F) /\
   (LEX(<<) (CONS h t) l <=>
        if l = [] then F
        else if h << HD l then LENGTH t = LENGTH(TL l)
        else (h = HD l) /\ LEX(<<) t (TL l))]]
  : ExceptT String IO thm).run
#eval LEX_DEF

#eval phrase 15
unsafe def LEX : thm := keep "LEX" fun _ => (do
  prove ([[(LEX(<<) [] l <=> F) /\
   (LEX(<<) (CONS h1 t1) [] <=> F) /\
   (LEX(<<) (CONS h1 t1) (CONS h2 t2) <=>
        if h1 << h2 then LENGTH t1 = LENGTH t2
        else (h1 = h2) /\ LEX(<<) t1 t2)]])
   (REWRITE_TAC [LEX_DEF, NOT_CONS_NIL, HD, TL])
  : ExceptT String IO thm).run
#eval LEX

#eval phrase 16
unsafe def LEX_LENGTH : thm := keep "LEX_LENGTH" fun _ => (do
  prove ([[!l1 l2 R. LEX(R) l1 l2 ==> (LENGTH l1 = LENGTH l2)]])
   (LIST_INDUCT_TAC THEN REWRITE_TAC [LEX] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [LEX] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [LENGTH] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval LEX_LENGTH

#eval phrase 17
unsafe def MONO_LEX : thm := keep "MONO_LEX" fun _ => (do
  prove ([[(!x:A y:A. R x y ==> S x y) ==> LEX R x y ==> LEX S x y]])
   (DISCH_TAC THEN SPEC_TAC ([[y:A list]], [[y:A list]]) THEN
    SPEC_TAC ([[x:A list]], [[x:A list]]) THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [LEX] THEN LIST_INDUCT_TAC THEN REWRITE_TAC [LEX] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    ASM_MESON_TAC [LEX_LENGTH])
  : ExceptT String IO thm).run
#eval MONO_LEX

#eval phrase 18
#eval show IO Unit from do
  let l ← Session.get_monotonicity_theorems
  Session.set_monotonicity_theorems (MONO_LEX :: l)

#eval phrase 19
unsafe def LEX_MAP : thm := keep "LEX_MAP" fun _ => (do
  prove ([[!l1 l2. LEX (\x y. R (f x) (f y)) l1 l2 ==> LEX R (MAP f l1) (MAP f l2)]])
   (LIST_INDUCT_TAC THEN REWRITE_TAC [LEX, MAP] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [LEX, MAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [LENGTH_MAP] THEN ASM_SIMP_TAC [])
  : ExceptT String IO thm).run
#eval LEX_MAP

#eval phrase 20
unsafe def LEX_REFL : thm := keep "LEX_REFL" fun _ => (do
  prove ([[!R l. (!x. MEM x l ==> ~(R x x)) ==> ~(LEX(R) l l)]])
   (GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LEX, MEM] THEN
    COND_CASES_TAC THEN REWRITE_TAC [] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval LEX_REFL

#eval phrase 21
unsafe def LEX_LENGTH_CHAIN : thm := keep "LEX_LENGTH_CHAIN" fun _ => (do
  prove ([[!lis R. (!n. LEX(R) (lis(SUC n)) (lis n))
           ==> !n. LENGTH(lis(n)) = LENGTH(lis(0))]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC [] THEN
    ASM_MESON_TAC [LEX_LENGTH])
  : ExceptT String IO thm).run
#eval LEX_LENGTH_CHAIN

#eval phrase 22
unsafe def WF_LEX_STRONG_INDUCT : thm := keep "WF_LEX_STRONG_INDUCT" fun _ => (do
  prove ([[!n lis. (LENGTH(lis 0) = n)
           ==> ~((!n a:A. MEM a (lis n) ==> ~(NONWF(R) a)) /\
                 (!n. LEX(R) (lis(SUC n)) (lis n)))]])
   (INDUCT_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_ASSUM (ASSUME_TAC oTIO (fun th => HolLight.MATCH_MP LEX_LENGTH_CHAIN th)) THEN
      UNDISCH_TAC [[!n. LENGTH (lis n :(A)list) = LENGTH (lis 0)]] THEN
      ASM_REWRITE_TAC [LENGTH_EQ_NIL] THEN ASM_MESON_TAC [LEX],
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC oTIO (fun th => HolLight.MATCH_MP LEX_LENGTH_CHAIN th)) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[?hd tl. !n:num. CONS (hd n :A) (tl n) = lis(n)]]) MP_TAC THENL
     [EXISTS_TAC [[\n:num. HD(lis n):A]] THEN
      EXISTS_TAC [[\n:num. TL(lis n):A list]] THEN
      SUBGOAL_THEN ([[!n:num. ~(lis n :(A)list = [])]]) MP_TAC THENL
       [ASM_MESON_TAC [LEX_LENGTH_CHAIN, LENGTH, NOT_SUC], ALL_TAC] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC [[m:num]] THEN
      REWRITE_TAC [] THEN
      SPEC_TAC ([[(lis:num->(A)list) m]], [[l:(A)list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [HD, TL], ALL_TAC] THEN
    DISCH_THEN (HolLight.REPEAT_TCL CHOOSE_THEN
     (fun th => RULE_ASSUM_TAC (fun t => (do
        HolLight.REWRITE_RULE [(← HolLight.GSYM th)] t : ExceptT String IO thm).run))) THEN
    UNDISCH_TAC [[!n:num a:A. MEM a (CONS (hd n) (tl n)) ==> ~NONWF R a]] THEN
    REWRITE_TAC [MEM, (← ExceptT.mk (Session.TAUT [[(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)]]))] THEN
    SIMP_TAC [FORALL_AND_THM, LEFT_FORALL_IMP_THM, EXISTS_REFL] THEN
    STRIP_TAC THEN UNDISCH_TAC
     ([[!n:num. LEX R (CONS (hd(SUC n):A) (tl(SUC n))) (CONS (hd n) (tl n))]]) THEN
    REWRITE_TAC [LEX] THEN
    UNDISCH_TAC [[!m:num. LENGTH (CONS (hd m :A) (tl m)) = SUC n]] THEN
    REWRITE_TAC [LENGTH, SUC_INJ] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [(← ExceptT.mk (Session.TAUT [[(if p then T else r) <=> p \/ ~p /\ r]]))] THEN
    UNDISCH_TAC [[!n:num a:A. MEM a (tl n) ==> ~NONWF R a]] THEN
    UNDISCH_TAC [[!m. LENGTH ((tl:num->(A)list) m) = n]] THEN
    REWRITE_TAC [IMP_IMP] THEN
    SPEC_TAC ([[tl:num->(A)list]], [[tl:num->(A)list]]) THEN
    ABBREV_TAC [[h:A = hd 0]] THEN
    SUBGOAL_THEN ([[~(NONWF(R) (h:A))]]) MP_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (fun th =>
     UNDISCH_TAC [[!n:num. ~NONWF R (hd n :A)]] THEN
     UNDISCH_TAC [[hd 0 :A = h]] THEN MP_TAC th) THEN
    SPEC_TAC ([[hd:num->A]], [[hd:num->A]]) THEN SPEC_TAC ([[h:A]], [[h:A]]) THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC NONWF_INDUCT THEN X_GEN_TAC [[h:A]] THEN STRIP_TAC THEN
    POP_ASSUM_LIST (fun ths => HolLight.tactic_of do pure (MP_TAC (← HolLight.end_itlist HolLight.CONJ ths))) THEN STRIP_TAC THEN
    X_GEN_TAC [[hd:num->A]] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[?m. R (hd(SUC m):A) (hd m)]]) MP_TAC THENL
     [ASM_MESON_TAC [], ALL_TAC] THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [num_WOP] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[p:num]]) STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[(hd:num->A) (SUC p)]]) THEN ANTS_TAC THENL
     [SUBGOAL_THEN ([[!n. n <= p ==> (hd n :A = h)]])
       (fun th => ASM_MESON_TAC [th, LE_REFL]) THEN
      INDUCT_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [LE_SUC_LT] THEN
      ASM_MESON_TAC [LT_IMP_LE],
      ALL_TAC] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[\n. hd(SUC p + n):A]]) THEN
    ASM_REWRITE_TAC [ADD_CLAUSES, NOT_IMP] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[\n. tl(SUC p + n):A list]]) THEN
    ASM_REWRITE_TAC [] THEN X_GEN_TAC [[m:num]] THEN
    FIRST_ASSUM (MP_TAC oTIO (fun th => (do
       let _ ← liftExcept (HolCore.Lib.check (fun t => HolCore.Basics.is_disj t) (concl th))
       pure th : ExceptT String IO thm).run) oIO (fun th => HolLight.SPEC ([[SUC(p + m)]]) th)) THEN
    REWRITE_TAC [ADD_CLAUSES])
  : ExceptT String IO thm).run
#eval WF_LEX_STRONG_INDUCT

#eval phrase 23
unsafe def WF_LEX_STRONG : thm := keep "WF_LEX_STRONG" fun _ => (do
  prove ([[!R lis. ~((!n a:A. MEM a (lis n) ==> ~(NONWF(R) a)) /\
             (!n. LEX(R) (lis(SUC n)) (lis n)))]])
   (MESON_TAC [WF_LEX_STRONG_INDUCT])
  : ExceptT String IO thm).run
#eval WF_LEX_STRONG

#eval phrase 24
unsafe def LEX_RESTRICT : thm := keep "LEX_RESTRICT" fun _ => (do
  prove ([[!P R l1 l2. LEX R l1 l2 /\
               (!a. MEM a l1 ==> P(a)) /\ (!a. MEM a l2 ==> P(a))
               ==> LEX (\x y. P(x) /\ P(y) /\ R x y) l1 l2]])
   (GEN_TAC THEN GEN_TAC THEN REPEAT LIST_INDUCT_TAC THEN
    REWRITE_TAC [LEX, MEM] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    ASM_SIMP_TAC [] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval LEX_RESTRICT

#eval phrase 25
#eval show IO Unit from do
  let _ ← HolCore.Printer.parse_as_infix ("subterm", (12, "right"))
  pure ()

#eval phrase 26
#eval show IO Unit from do
  let _ ← HolCore.Printer.parse_as_infix ("psubterm", (12, "right"))
  pure ()

#eval phrase 27
unsafe def subterm_triple : thm × thm × thm := keep "subterm_triple" fun _ =>
  newInductive
    [[(!t. t subterm t) /\
   (!s a f args. s subterm a /\ MEM a args ==> s subterm (Fn f args))]]
unsafe def subterm_RULES : thm := subterm_triple.1
unsafe def subterm_INDUCT : thm := subterm_triple.2.1
unsafe def subterm_CASES : thm := subterm_triple.2.2
#eval do IO.println subterm_RULES; IO.println subterm_INDUCT; IO.println subterm_CASES

#eval phrase 28
unsafe def psubterm : thm := keep "psubterm" fun _ => (do
  ExceptT.mk (Session.new_definition
    [[s psubterm t <=> s subterm t /\ ~(s = t)]])
  : ExceptT String IO thm).run
#eval psubterm

#eval phrase 29
unsafe def DESCENDANT_SMALLER : thm := keep "DESCENDANT_SMALLER" fun _ => (do
  prove ([[!f args s. MEM s args ==> termsize s < termsize (Fn f args)]])
   (GEN_TAC THEN REWRITE_TAC [termsize] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [MEM, MAP, ITLIST] THEN
    ASM_MESON_TAC [(← ExceptT.mk (Session.ARITH_RULE [[0 < b ==> a < a + b:num]])),
                   (← ExceptT.mk (Session.ARITH_RULE [[a < c ==> a < b + c:num]])), ITLIST_ADD_1_POS])
  : ExceptT String IO thm).run
#eval DESCENDANT_SMALLER

#eval phrase 30
unsafe def DESCENDANT_DISTINCT : thm := keep "DESCENDANT_DISTINCT" fun _ => (do
  prove ([[!f args. ~(MEM (Fn f args) args)]])
   (MESON_TAC [DESCENDANT_SMALLER, LT_REFL])
  : ExceptT String IO thm).run
#eval DESCENDANT_DISTINCT

#eval phrase 31
unsafe def SUBTERM_REFL : thm := keep "SUBTERM_REFL" fun _ => (do
  prove ([[!t. t subterm t]])
   (REWRITE_TAC [subterm_RULES])
  : ExceptT String IO thm).run
#eval SUBTERM_REFL

#eval phrase 32
unsafe def SUBTERM_TRANS : thm := keep "SUBTERM_TRANS" fun _ => (do
  prove ([[!s t u. s subterm t /\ t subterm u ==> s subterm u]])
   (SUBGOAL_THEN ([[!t u. t subterm u ==> !s. s subterm t ==> s subterm u]])
     (fun th => MESON_TAC [th]) THEN MATCH_MP_TAC subterm_INDUCT THEN
    REWRITE_TAC [] THEN MESON_TAC [subterm_RULES])
  : ExceptT String IO thm).run
#eval SUBTERM_TRANS

#eval phrase 33
unsafe def SUBTERM_ANTISYM : thm := keep "SUBTERM_ANTISYM" fun _ => (do
  prove ([[!s t. s subterm t /\ t subterm s ==> (s = t)]])
   (MATCH_MP_TAC term_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
     [ONCE_REWRITE_TAC [subterm_CASES] THEN SIMP_TAC [term_DISTINCT], ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN STRIP_TAC THEN GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ONCE_REWRITE_TAC [subterm_CASES] THEN REWRITE_TAC [term_INJ] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV HolLight.SYM_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    ASM_MESON_TAC [subterm_RULES, SUBTERM_TRANS])
  : ExceptT String IO thm).run
#eval SUBTERM_ANTISYM

#eval phrase 34
unsafe def SUBTERM_FVT : thm := keep "SUBTERM_FVT" fun _ => (do
  prove ([[!x t. x IN FVT(t) ==> V(x) subterm t]])
   (GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
    SIMP_TAC [FVT, IN_SING, IN_LIST_UNION, SUBTERM_REFL] THEN
    REWRITE_TAC [MEM_MAP, (← HolLight.GSYM EX_MEM), (← HolLight.GSYM ALL_MEM)] THEN
    MESON_TAC [subterm_RULES])
  : ExceptT String IO thm).run
#eval SUBTERM_FVT

#eval phrase 35
unsafe def PSUBTERM_ANTISYM : thm := keep "PSUBTERM_ANTISYM" fun _ => (do
  prove ([[!s t. ~(s psubterm t /\ t psubterm s)]])
   (REWRITE_TAC [psubterm] THEN MESON_TAC [SUBTERM_ANTISYM])
  : ExceptT String IO thm).run
#eval PSUBTERM_ANTISYM

#eval phrase 36
unsafe def SUBTERM_PSUBTERM_TRANS : thm := keep "SUBTERM_PSUBTERM_TRANS" fun _ => (do
  prove ([[!s t u. s subterm t /\ t psubterm u ==> s psubterm u]])
   (REWRITE_TAC [psubterm] THEN MESON_TAC [SUBTERM_TRANS, SUBTERM_ANTISYM])
  : ExceptT String IO thm).run
#eval SUBTERM_PSUBTERM_TRANS

#eval phrase 37
unsafe def PSUBTERM_CASES : thm := keep "PSUBTERM_CASES" fun _ => (do
  prove ([[!s t. s psubterm t <=>
         ?f args u. (t = Fn f args) /\ MEM u args /\ s subterm u]])
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [psubterm] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [subterm_CASES] THEN ASM_MESON_TAC [],
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [ [[f:num]], [[args:term list]], [[a:term]] ] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC SUBTERM_PSUBTERM_TRANS THEN
      EXISTS_TAC [[a:term]] THEN ASM_REWRITE_TAC [psubterm] THEN
      ASM_MESON_TAC [DESCENDANT_DISTINCT, subterm_RULES]])
  : ExceptT String IO thm).run
#eval PSUBTERM_CASES

#eval phrase 38
unsafe def SUBTERM_INSTANTIATION : thm := keep "SUBTERM_INSTANTIATION" fun _ => (do
  prove ([[!i s t. s subterm t ==> (termsubst i s) subterm (termsubst i t)]])
   (GEN_TAC THEN MATCH_MP_TAC subterm_INDUCT THEN
    REWRITE_TAC [termsubst, subterm_RULES] THEN
    ASM_MESON_TAC [MEM_MAP, subterm_RULES])
  : ExceptT String IO thm).run
#eval SUBTERM_INSTANTIATION

#eval phrase 39
unsafe def PSUBTERM_INSTANTIATION : thm := keep "PSUBTERM_INSTANTIATION" fun _ => (do
  prove ([[!i s t. s psubterm t ==> (termsubst i s) psubterm (termsubst i t)]])
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [PSUBTERM_CASES] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[f:num]] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[args:term list]], [[u:term]] ] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [ [[MAP (termsubst i) args]], [[termsubst i u]] ] THEN
    ASM_REWRITE_TAC [MEM_MAP, termsubst] THEN
    ASM_MESON_TAC [SUBTERM_INSTANTIATION])
  : ExceptT String IO thm).run
#eval PSUBTERM_INSTANTIATION

#eval phrase 40
unsafe def lpo_triple : thm × thm × thm := keep "lpo_triple" fun _ =>
  newInductive
    [[(!x s. x IN FVT(s) /\ ~(s = V x) ==> V x << s) /\
   (!fs sargs ft targs si.
          MEM si sargs /\ (Fn ft targs << si \/ (si = Fn ft targs))
          ==> Fn ft targs << Fn fs sargs) /\
   (!fs ft sargs targs.
          (fs > ft \/ (fs = ft) /\ LENGTH sargs > LENGTH targs) /\
          ALL (\ti. ti << Fn fs sargs) targs
          ==> Fn ft targs << Fn fs sargs) /\
   (!f sargs targs.
          ALL (\ti. ti << Fn f sargs) targs /\ LEX(<<) targs sargs
          ==> Fn f targs << Fn f sargs)]]
unsafe def lpo_RULES : thm := lpo_triple.1
unsafe def lpo_INDUCT : thm := lpo_triple.2.1
unsafe def lpo_CASES : thm := lpo_triple.2.2
#eval do IO.println lpo_RULES; IO.println lpo_INDUCT; IO.println lpo_CASES

#eval phrase 41
unsafe def LPO_CASES : thm := keep "LPO_CASES" fun _ => (do
  prove ([[(!s x. (s << V x) <=> F) /\
   (!x t. V x << t <=> x IN FVT(t) /\ ~(t = V x)) /\
   (!f fargs g gargs.
          Fn f fargs << Fn g gargs <=>
                (?gi. MEM gi gargs /\
                      (Fn f fargs << gi \/ (Fn f fargs = gi))) \/
                (!fi. MEM fi fargs ==> fi << Fn g gargs) /\
                ((f < g \/ (f = g) /\ (LENGTH fargs < LENGTH gargs)) \/
                 (f = g) /\ LEX(<<) fargs gargs))]])
   (REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [lpo_CASES] THEN
    REWRITE_TAC [term_DISTINCT, term_INJ, FVT, IN_SING, (← HolLight.GSYM ALL_MEM), GT] THEN
    TRY (CONV_TAC (HolLight.LAND_CONV (HolLight.ONCE_DEPTH_CONV HolLight.SYM_CONV))) THEN
    REWRITE_TAC [(← ExceptT.mk (Session.TAUT [[(a /\ b) /\ c <=> ~(a /\ b ==> ~c)]]))] THEN
    SIMP_TAC [] THEN REWRITE_TAC [NOT_IMP, DE_MORGAN_THM] THEN
    REWRITE_TAC [RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM, EXISTS_REFL] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval LPO_CASES

#eval phrase 42
unsafe def LPO_FVT : thm := keep "LPO_FVT" fun _ => (do
  prove ([[!s t. s << t ==> FVT(s) SUBSET FVT(t)]])
   (MATCH_MP_TAC lpo_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
     [ALL_TAC, SPEC_TAC ([[Fn ft targs]], [[t:term]]), ALL_TAC, ALL_TAC] THEN
    SIMP_TAC [FVT, SUBSET, IN_SING, IN_LIST_UNION,
              (← HolLight.GSYM EX_MEM), (← HolLight.GSYM ALL_MEM), MEM_MAP] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval LPO_FVT

#eval phrase 43
unsafe def LPO_TRANS_INDUCT : thm := keep "LPO_TRANS_INDUCT" fun _ => (do
  let lr0 ← liftExcept (HolCore.Lib.el 0 (Session.CONJUNCTS lpo_RULES))
  let lr1 ← liftExcept (HolCore.Lib.el 1 (Session.CONJUNCTS lpo_RULES))
  prove ([[!n r s t.
        (termsize r + termsize s + termsize t = n) /\ t << s /\ s << r
        ==> t << r]])
   (MATCH_MP_TAC num_WF THEN X_GEN_TAC [[n:num]] THEN DISCH_TAC THEN
    REPEAT GEN_TAC THEN DISJ_CASES_THEN MP_TAC (← ExceptT.mk (HolLight.SPEC ([[t:term]]) term_CASES)) THENL
     [DISCH_THEN (X_CHOOSE_THEN ([[x:num]]) SUBST_ALL_TAC) THEN STRIP_TAC THEN
      MATCH_MP_TAC lr0 THEN CONJ_TAC THENL
       [(HolLight.tactic_of do
          let m1 ← HolLight.MATCH_MP LPO_FVT (← ExceptT.mk (HolLight.ASSUME [[V x << s]]))
          let m2 ← HolLight.MATCH_MP LPO_FVT (← ExceptT.mk (HolLight.ASSUME [[s << r]]))
          pure (MP_TAC m1 THEN MP_TAC m2 THEN
            REWRITE_TAC [FVT, SUBSET, IN_SING] THEN MESON_TAC [])),
        ASM_MESON_TAC [LPO_CASES]],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[h:num]]) (X_CHOOSE_THEN ([[ts:term list]])
      SUBST_ALL_TAC)) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (SUBST_ALL_TAC oTIO HolLight.SYM) MP_TAC) THEN
    DISJ_CASES_THEN MP_TAC (← ExceptT.mk (HolLight.SPEC ([[r:term]]) term_CASES)) THENL
     [ASM_MESON_TAC [LPO_CASES], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[f:num]]) (X_CHOOSE_THEN ([[rs:term list]])
      SUBST_ALL_TAC)) THEN
    DISJ_CASES_THEN MP_TAC (← ExceptT.mk (HolLight.SPEC ([[s:term]]) term_CASES)) THENL
     [ASM_MESON_TAC [LPO_CASES], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[g:num]]) (X_CHOOSE_THEN ([[ss:term list]])
      SUBST_ALL_TAC)) THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [RIGHT_IMP_FORALL_THM]) THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IMP_IMP]) THEN
    ASM_CASES_TAC [[?ri. MEM ri rs /\ (Fn g ss << ri \/ (Fn g ss = ri))]] THENL
     [FIRST_X_ASSUM (X_CHOOSE_THEN ([[ri:term]])
       (HolLight.REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      MATCH_MP_TAC lr1 THEN
      EXISTS_TAC [[ri:term]] THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM DISJ_CASES_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
      DISJ1_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC [[termsize ri + termsize(Fn g ss) + termsize (Fn h ts)]] THEN
      EXISTS_TAC [[Fn g ss]] THEN ASM_REWRITE_TAC [LT_ADD_RCANCEL] THEN
      MATCH_MP_TAC DESCENDANT_SMALLER THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!si. MEM si ss ==> si << Fn f rs]]) ASSUME_TAC THENL
     [UNDISCH_TAC [[Fn g ss << Fn f rs]] THEN
      HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [lpo_CASES] THEN
      REWRITE_TAC [term_DISTINCT, term_INJ, (← HolLight.GSYM ALL_MEM)] THEN
      ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_CASES_TAC [[?si. MEM si ss /\ (Fn h ts << si \/ (Fn h ts = si))]] THENL
     [FIRST_X_ASSUM (X_CHOOSE_THEN ([[si:term]])
       (HolLight.REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      FIRST_X_ASSUM DISJ_CASES_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
      FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (MATCH_MP_TAC th THEN EXISTS_TAC
          [[termsize(Fn f rs) + termsize si + termsize (Fn h ts)]])) THEN
      EXISTS_TAC [[si:term]] THEN
      ASM_SIMP_TAC [LT_ADD_LCANCEL, LT_ADD_RCANCEL] THEN
      MATCH_MP_TAC DESCENDANT_SMALLER THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[!ti. MEM ti ts ==> ti << Fn g ss]]) ASSUME_TAC THENL
     [UNDISCH_TAC [[Fn h ts << Fn g ss]] THEN
      HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [lpo_CASES] THEN
      REWRITE_TAC [term_DISTINCT, term_INJ, (← HolLight.GSYM ALL_MEM)] THEN
      ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[!ti. MEM ti ts ==> ti << Fn f rs]]) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (MATCH_MP_TAC th THEN EXISTS_TAC
         [[termsize (Fn f rs) + termsize (Fn g ss) + termsize ti]])) THEN
      EXISTS_TAC [[Fn g ss]] THEN
      ASM_SIMP_TAC [LT_ADD_LCANCEL, DESCENDANT_SMALLER], ALL_TAC] THEN
    UNDISCH_TAC [[Fn h ts << Fn g ss]] THEN UNDISCH_TAC [[Fn g ss << Fn f rs]] THEN
    ONCE_REWRITE_TAC [LPO_CASES] THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [ASM_MESON_TAC [LT_TRANS, LEX_LENGTH], ALL_TAC] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [ASM_MESON_TAC [LT_TRANS, LEX_LENGTH], ALL_TAC] THEN
    DISJ2_TAC THEN DISJ2_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC oT Session.CONJUNCT2) THEN FIRST_X_ASSUM (MP_TAC oT Session.CONJUNCT2) THEN
    SUBGOAL_THEN
     ([[!r s t. MEM r rs /\ MEM s ss /\ MEM t ts /\
            t << s /\ s << r ==> t << r]])
    MP_TAC THENL
     [MAP_EVERY X_GEN_TAC [ [[a:term]], [[b:term]], [[c:term]] ] THEN STRIP_TAC THEN
      FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (MATCH_MP_TAC th THEN EXISTS_TAC
         [[termsize a + termsize b + termsize c]])) THEN
      EXISTS_TAC [[b:term]] THEN ASM_REWRITE_TAC [] THEN
      REPEAT (MATCH_MP_TAC LT_ADD2 THEN CONJ_TAC) THEN
      ASM_SIMP_TAC [DESCENDANT_SMALLER], ALL_TAC] THEN
    MAP_EVERY (fun s => SPEC_TAC (s, s))
     [ [[rs:term list]], [[ss:term list]], [[ts:term list]] ] THEN
    POP_ASSUM_LIST (HolCore.Lib.K ALL_TAC) THEN
    REPEAT LIST_INDUCT_TAC THEN REWRITE_TAC [LEX, MEM] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    TRY (HolLight.ASM (fun l => Session.GEN_MESON_TAC 0 15 1 l) [LEX_LENGTH]) THEN DISCH_TAC THEN
    MATCH_MP_TAC (← ExceptT.mk (Session.TAUT [[(a1 /\ a2 ==> a3) /\ (b1 ==> b2 ==> b3)
                     ==> a1 /\ b1 ==> a2 /\ b2 ==> a3 /\ b3]])) THEN
    SIMP_TAC [] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval LPO_TRANS_INDUCT

#eval phrase 44
unsafe def LPO_TRANS : thm := keep "LPO_TRANS" fun _ => (do
  prove ([[!s t u. s << t /\ t << u ==> s << u]])
   (MESON_TAC [LPO_TRANS_INDUCT])
  : ExceptT String IO thm).run
#eval LPO_TRANS

#eval phrase 45
unsafe def LPO_SUBTERM_LEMMA : thm := keep "LPO_SUBTERM_LEMMA" fun _ => (do
  prove ([[!f args a. MEM a args ==> a << Fn f args]])
   (GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
    ONCE_REWRITE_TAC [LPO_CASES] THEN CONJ_TAC THENL
     [ALL_TAC, MESON_TAC []] THEN
    REWRITE_TAC [FVT, IN_LIST_UNION, (← HolLight.GSYM EX_MEM), (← HolLight.GSYM ALL_MEM), MEM_MAP] THEN
    X_GEN_TAC [[x:num]] THEN DISCH_TAC THEN REWRITE_TAC [term_DISTINCT] THEN
    EXISTS_TAC [[FVT(V x)]] THEN REWRITE_TAC [FVT, IN_SING] THEN
    EXISTS_TAC [[V x]] THEN ASM_REWRITE_TAC [FVT])
  : ExceptT String IO thm).run
#eval LPO_SUBTERM_LEMMA

#eval phrase 46
unsafe def LPO_SUBTERM : thm := keep "LPO_SUBTERM" fun _ => (do
  prove ([[!s t. s subterm t ==> (s = t) \/ s << t]])
   (MATCH_MP_TAC subterm_INDUCT THEN REWRITE_TAC [] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC [LPO_SUBTERM_LEMMA],
      DISJ2_TAC THEN MATCH_MP_TAC LPO_TRANS THEN
      EXISTS_TAC [[a:term]] THEN ASM_SIMP_TAC [LPO_SUBTERM_LEMMA]])
  : ExceptT String IO thm).run
#eval LPO_SUBTERM

#eval phrase 47
unsafe def LPO_PSUBTERM : thm := keep "LPO_PSUBTERM" fun _ => (do
  prove ([[!s t. s psubterm t ==> s << t]])
   (REWRITE_TAC [psubterm] THEN MESON_TAC [LPO_SUBTERM])
  : ExceptT String IO thm).run
#eval LPO_PSUBTERM

#eval phrase 48
unsafe def LPO_INSTANTIATION : thm := keep "LPO_INSTANTIATION" fun _ => (do
  let lr1 ← liftExcept (HolCore.Lib.el 1 (Session.CONJUNCTS lpo_RULES))
  let lr2 ← liftExcept (HolCore.Lib.el 2 (Session.CONJUNCTS lpo_RULES))
  let lr3 ← liftExcept (HolCore.Lib.el 3 (Session.CONJUNCTS lpo_RULES))
  let gsymAllMem ← HolLight.GSYM ALL_MEM
  prove ([[!i s t. s << t ==> termsubst i s << termsubst i t]])
   (GEN_TAC THEN MATCH_MP_TAC lpo_INDUCT THEN REPEAT CONJ_TAC THEN
    REPEAT GEN_TAC THEN DISCH_THEN (HolLight.REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THENL
     [MATCH_MP_TAC LPO_PSUBTERM THEN MATCH_MP_TAC PSUBTERM_INSTANTIATION THEN
      ASM_REWRITE_TAC [psubterm] THEN ASM_SIMP_TAC [SUBTERM_FVT],
      REWRITE_TAC [termsubst] THEN
      MATCH_MP_TAC lr1 THEN
      REWRITE_TAC [MEM_MAP] THEN ASM_MESON_TAC [termsubst],
      REWRITE_TAC [termsubst] THEN
      MATCH_MP_TAC lr2 THEN
      ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC oTIO (fun th => HolLight.GEN_REWRITE_RULE HolCore.Lib.I [gsymAllMem] th)) THEN
      REWRITE_TAC [(← HolLight.GSYM ALL_MEM), MEM_MAP, termsubst, LENGTH_MAP] THEN
      ASM_MESON_TAC [],
      REWRITE_TAC [termsubst] THEN
      MATCH_MP_TAC lr3 THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [ALL_MAP, o_DEF] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [termsubst]) THEN ASM_SIMP_TAC [LEX_MAP]])
  : ExceptT String IO thm).run
#eval LPO_INSTANTIATION

#eval phrase 49
unsafe def LPO_CONGRUENCE : thm := keep "LPO_CONGRUENCE" fun _ => (do
  let lrlast ← liftExcept (HolCore.Lib.last (Session.CONJUNCTS lpo_RULES))
  prove ([[!s t. s << t
         ==> Fn f (APPEND largs (CONS s rargs))
              << Fn f (APPEND largs (CONS t rargs))]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC lrlast THEN
    CONJ_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN X_GEN_TAC [[u:term]] THEN DISCH_TAC THEN
      ASM_CASES_TAC [[u:term = s]] THENL
       [MATCH_MP_TAC LPO_TRANS THEN EXISTS_TAC [[t:term]] THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LPO_PSUBTERM THEN
        ONCE_REWRITE_TAC [PSUBTERM_CASES] THEN
        MAP_EVERY EXISTS_TAC
         [ [[f:num]], [[APPEND largs (CONS (t:term) rargs)]], [[t:term]] ] THEN
        ASM_REWRITE_TAC [MEM, SUBTERM_REFL, MEM_APPEND],
        MATCH_MP_TAC LPO_PSUBTERM THEN ONCE_REWRITE_TAC [PSUBTERM_CASES] THEN
        MAP_EVERY EXISTS_TAC
         [ [[f:num]], [[APPEND largs (CONS (t:term) rargs)]], [[u:term]] ] THEN
        REWRITE_TAC [SUBTERM_REFL] THEN
        ASM_MESON_TAC [MEM, MEM_APPEND]],
      SPEC_TAC ([[largs:term list]], [[largs:term list]]) THEN
      LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LEX, APPEND] THEN
      COND_CASES_TAC THEN REWRITE_TAC [LENGTH, LENGTH_APPEND]])
  : ExceptT String IO thm).run
#eval LPO_CONGRUENCE

#eval phrase 50
unsafe def LPO_REFL : thm := keep "LPO_REFL" fun _ => (do
  prove ([[!t. ~(t << t)]])
   (MATCH_MP_TAC term_INDUCT THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [LPO_CASES] THEN REWRITE_TAC [] THEN
    REWRITE_TAC [(← HolLight.GSYM ALL_MEM), LT_REFL] THEN
    ASM_SIMP_TAC [LEX_REFL] THEN
    ASM_MESON_TAC [LPO_PSUBTERM, LPO_TRANS,
      PSUBTERM_CASES, SUBTERM_REFL, DESCENDANT_SMALLER, LT_REFL])
  : ExceptT String IO thm).run
#eval LPO_REFL

#eval phrase 51
unsafe def LPO_WF : thm := keep "LPO_WF" fun _ => (do
  let wmd ← do
    let (_, b) ← HolLight.EQ_IMP_RULE (← HolLight.SPEC_ALL WF_MINIMAL_DCHAIN)
    HolLight.GEN_ALL b
  let memAssume ← HolLight.ASSUME [[MEM (a:term) (args((k:num->num) n))]]
  prove ([[!A. FINITE(A)
       ==> WF(\s t. functions_term(s) SUBSET A /\
                    functions_term(t) SUBSET A /\
                    s << t)]])
   (GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC wmd THEN
    EXISTS_TAC [[termsize]] THEN REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[t:num->term]])
     (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC [FORALL_AND_THM] THEN
    DISCH_THEN (STRIP_ASSUME_TAC oT Session.CONJUNCT2) THEN
    SUBGOAL_THEN
      ([[!n:num. ?f args. (t(n) = Fn f args) /\
                      ALL (\t. ~(NONWF(\s t. functions_term(s) SUBSET A /\
                                             functions_term(t) SUBSET A /\
                                             s << t) t)) args]])
    MP_TAC THENL
     [GEN_TAC THEN MP_TAC (← ExceptT.mk (HolLight.SPEC ([[(t:num->term) n]]) term_CASES)) THEN
      DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
       [ASM_MESON_TAC [LPO_CASES], ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[f:num]] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[args:term list]] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN
      X_GEN_TAC [[u:term]] THEN DISCH_TAC THEN DISCH_TAC THEN
      ASM_CASES_TAC [[n = 0]] THENL
       [FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[u:term]]) THEN
        ASM_REWRITE_TAC [] THEN UNDISCH_THEN ([[n = 0]]) SUBST_ALL_TAC THEN
        ASM_SIMP_TAC [NOT_LE, DESCENDANT_SMALLER], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [ [[n - 1]], [[u:term]] ]) THEN
      ASM_SIMP_TAC [(← ExceptT.mk (Session.ARITH_RULE [[~(n = 0) ==> (SUC(n - 1) = n)]]))] THEN
      REWRITE_TAC [NOT_IMP, (← HolLight.GSYM CONJ_ASSOC), NOT_LE] THEN REPEAT CONJ_TAC THENL
       [UNDISCH_THEN
         ([[!n:num. functions_term (t n) SUBSET A]]) (MP_TAC o HolLight.SPEC [[n:num]]) THEN
        ASM_REWRITE_TAC [functions_term, SUBSET, IN_LIST_UNION, IN_INSERT,
                        MEM_MAP, (← HolLight.GSYM EX_MEM)] THEN
        ASM_MESON_TAC [],
        MATCH_MP_TAC LPO_TRANS THEN EXISTS_TAC [[(t:num->term)(n)]] THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LPO_PSUBTERM THEN
          ONCE_REWRITE_TAC [PSUBTERM_CASES] THEN
          MAP_EVERY EXISTS_TAC [ [[f:num]], [[args:term list]], [[u:term]] ] THEN
          ASM_REWRITE_TAC [SUBTERM_REFL],
          FIRST_ASSUM (fun th => HolLight.tactic_of do
            let ar ← HolLight.MATCH_MP (← ExceptT.mk (Session.ARITH_RULE [[~(n = 0) ==> (n = SUC(n - 1))]])) th
            pure (HolLight.GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [ar])) THEN
          ASM_REWRITE_TAC []],
        MATCH_MP_TAC DESCENDANT_SMALLER THEN ASM_REWRITE_TAC []], ALL_TAC] THEN
    REWRITE_TAC [SKOLEM_THM, FORALL_AND_THM, (← HolLight.GSYM ALL_MEM)] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[fn:num->num]]) (X_CHOOSE_THEN ([[args:num->term list]])
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     ([[?far:num#num s. subseq s /\
                    (!n:num. fn(s n),LENGTH(args(s n):term list) = far)]])
    MP_TAC THENL
     [MATCH_MP_TAC SEQUENCE_PARTITION_LEMMA THEN
      EXISTS_TAC [[A:num#num->bool]] THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC [[n:num]] THEN
      UNDISCH_TAC [[!n:num. functions_term (t n) SUBSET A]] THEN
      DISCH_THEN (MP_TAC oTIO (fun th => HolLight.REWRITE_RULE [SUBSET] th) o HolLight.SPEC [[n:num]]) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [functions_term, IN_INSERT],
      ALL_TAC] THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [EXISTS_PAIR_THM] THEN
    REWRITE_TAC [PAIR_EQ, FORALL_AND_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[f:num]]) (X_CHOOSE_THEN ([[ar:num]])
     (X_CHOOSE_THEN ([[k:num->num]]) STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN ([[!m n. m <= n ==> t(n) << t(m) \/ (t(n) = t(m))]])
    ASSUME_TAC THENL
     [SUBGOAL_THEN ([[!n d. t(n + d) << t(n) \/ (t(n + d) = t(n))]])
       (fun th => MESON_TAC [th, LE_EXISTS]) THEN
      GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES] THEN
      ASM_MESON_TAC [LPO_TRANS], ALL_TAC] THEN
    SUBGOAL_THEN ([[!m n. m < n ==> t(n) << t(m)]]) MP_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM LE_SUC_LT)] THEN
      ASM_MESON_TAC [LPO_TRANS], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o HolLight.GEN [[n:num]] o
      (fun th => HolLight.SPECL [ [[(k:num->num) n]], [[k(SUC n):num]] ] th)) THEN
    FIRST_ASSUM (ASSUME_TAC oTIO (fun th => HolLight.GEN_REWRITE_RULE HolCore.Lib.I [SUBSEQ_SUC] th)) THEN
    ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [LPO_CASES] THEN
    REWRITE_TAC [LT_REFL] THEN
    SUBGOAL_THEN ([[!a n:num. MEM a (args n) ==> functions_term a SUBSET A]])
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN
      UNDISCH_THEN
           ([[!n:num. functions_term (t n) SUBSET A]])
           (MP_TAC o HolLight.SPEC [[n:num]]) THEN
      ASM_REWRITE_TAC [functions_term, SUBSET, IN_LIST_UNION, IN_INSERT,
                      MEM_MAP, (← HolLight.GSYM EX_MEM)] THEN
      ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[!n a. ~(MEM a (args ((k:num->num) n)) /\
            (Fn f (args (k (SUC n))) << a \/ (Fn f (args (k (SUC n))) = a)))]])
     (fun th => REWRITE_TAC [th])
    THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC [DE_MORGAN_THM] THEN
      MATCH_MP_TAC (← ExceptT.mk (Session.TAUT [[(a ==> b) ==> ~a \/ b]])) THEN DISCH_TAC THEN
      FIRST_ASSUM (MP_TAC oTIO (fun th => HolLight.GEN_REWRITE_RULE HolLight.RAND_CONV [NONWF] th) oIO
                (fun th => HolLight.MATCH_MP th memAssume)) THEN
      REWRITE_TAC [NONWF, (← ExceptT.mk (Session.TAUT [[~p ==> ~q /\ ~r <=> q \/ r ==> p]]))] THEN
      DISCH_TAC THEN EXISTS_TAC
       [[\r:num. if r = 0 then a:term else t(k(SUC n) + r)]] THEN
      REWRITE_TAC [NOT_SUC] THEN X_GEN_TAC [[m:num]] THEN
      COND_CASES_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
        FIRST_ASSUM (MP_TAC o HolLight.SPECL [ [[k(SUC n):num]], [[k(SUC n) + m]] ]) THEN
        REWRITE_TAC [LE_ADD] THEN UNDISCH_TAC [[!n:num. t(SUC n) << t n]] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC [[k(SUC n) + m]]) THEN
        REWRITE_TAC [ADD_CLAUSES] THEN
        FIRST_X_ASSUM (MP_TAC oTIO (fun th => (do
           let _ ← liftExcept (HolCore.Lib.check (fun t => HolCore.Basics.is_disj t) (concl th))
           pure th : ExceptT String IO thm).run)) THEN
        ASM_REWRITE_TAC [] THEN MESON_TAC [LPO_TRANS], ALL_TAC] THEN
      ASM_MESON_TAC [ADD_CLAUSES],
      ALL_TAC] THEN
    REWRITE_TAC [FORALL_AND_THM] THEN STRIP_TAC THEN
    MP_TAC (← ExceptT.mk (HolLight.ISPECL [ [[(\s t.
                     functions_term s SUBSET A /\
                     functions_term t SUBSET A /\
                     s << t)]], [[\n:num. (args:num->term list)(k n)]] ]
      WF_LEX_STRONG)) THEN
    ASM_REWRITE_TAC [] THEN
    GEN_TAC THEN MATCH_MP_TAC LEX_RESTRICT THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [LT_REFL])
  : ExceptT String IO thm).run
#eval LPO_WF

#eval phrase 52
unsafe def LPO_SUBTERM_NOT : thm := keep "LPO_SUBTERM_NOT" fun _ => (do
  prove ([[!t s. s subterm t ==> ~(t << s)]])
   (MESON_TAC [LPO_SUBTERM, LPO_TRANS, LPO_REFL])
  : ExceptT String IO thm).run
#eval LPO_SUBTERM_NOT

#eval phrase 53
unsafe def LEX_TOTAL : thm := keep "LEX_TOTAL" fun _ => (do
  prove ([[!fargs gargs.
        (LENGTH fargs = LENGTH gargs) /\
        (!fi gi. MEM fi fargs /\ MEM gi gargs
                 ==> fi << gi \/ gi << fi \/ (fi = gi))
        ==> LEX(<<) fargs gargs \/ LEX(<<) gargs fargs \/ (fargs = gargs)]])
   (MATCH_MP_TAC Session.list_INDUCT THEN REWRITE_TAC [LEX, MEM, LENGTH, NOT_SUC] THEN
    CONJ_TAC THENL [MESON_TAC [LENGTH_EQ_NIL], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [ [[s:term]], [[ss:term list]] ] THEN DISCH_TAC THEN
    MATCH_MP_TAC Session.list_INDUCT THEN REWRITE_TAC [LEX, MEM, LENGTH, NOT_SUC] THEN
    MAP_EVERY X_GEN_TAC [ [[t:term]], [[ts:term list]] ] THEN
    DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN SIMP_TAC [SUC_INJ] THEN
    STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[ts:term list]]) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval LEX_TOTAL

#eval phrase 54
unsafe def LPO_GROUND_COMPLETE : thm := keep "LPO_GROUND_COMPLETE" fun _ => (do
  prove ([[!s t. (FVT(s) = {}) /\ (FVT(t) = {}) ==> s << t \/ t << s \/ (s = t)]])
   (SUBGOAL_THEN
      ([[!n s t. (termsize(s) + termsize(t) = n) /\ (FVT(s) = {}) /\ (FVT(t) = {})
             ==> s << t \/ t << s \/ (s = t)]])
      (fun th => MESON_TAC [th]) THEN
    MATCH_MP_TAC num_WF THEN X_GEN_TAC [[n:num]] THEN DISCH_TAC THEN
    MATCH_MP_TAC term_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC [FVT, EXTENSION, IN_SING, NOT_IN_EMPTY] THEN MESON_TAC [],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [ [[f:num]], [[fargs:term list]] ] THEN
    DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
    MATCH_MP_TAC term_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC [FVT, EXTENSION, IN_SING, NOT_IN_EMPTY] THEN MESON_TAC [],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [ [[g:num]], [[gargs:term list]] ] THEN
    DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN STRIP_TAC THEN
    SUBGOAL_THEN
     ([[(!fi. MEM fi fargs
          ==> fi << Fn g gargs \/ Fn g gargs << fi \/ (fi = Fn g gargs)) /\
    (!gi. MEM gi gargs
          ==> gi << Fn f fargs \/ Fn f fargs << gi \/ (gi = Fn f fargs)) /\
    (!fi gi. MEM fi fargs /\ MEM gi gargs
          ==> fi << gi \/ gi << fi \/ (fi = gi))]])
    STRIP_ASSUME_TAC THENL
     [UNDISCH_THEN ([[termsize (Fn f fargs) + termsize (Fn g gargs) = n]])
          (SUBST_ALL_TAC oTIO HolLight.SYM) THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [RIGHT_IMP_FORALL_THM,
                    IMP_IMP]) THEN
      REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC [(← ExceptT.mk (Session.TAUT [[a /\ b /\ c /\ d <=> b /\ a /\ c /\ d]]))] THEN
      REWRITE_TAC [UNWIND_THM1] THEN
      ASM_SIMP_TAC [LT_ADD_LCANCEL, LT_ADD_RCANCEL, DESCENDANT_SMALLER,
                   (← ExceptT.mk (Session.ARITH_RULE [[a + b < b + c <=> a < c]])), LT_ADD2] THEN
      ASM_MESON_TAC [FVT_FUN_EMPTY],
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [LPO_CASES] THEN
    SUBGOAL_THEN
     ([[(?a. MEM a gargs /\ (Fn f fargs << a \/ (Fn f fargs = a))) \/
    ~(?a. MEM a gargs /\ (Fn f fargs << a \/ (Fn f fargs = a))) /\
    (!a. MEM a gargs ==> a << Fn f fargs)]])
    DISJ_CASES_TAC THENL [ASM_MESON_TAC [], ASM_REWRITE_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[(?a. MEM a fargs /\ (Fn g gargs << a \/ (Fn g gargs = a))) \/
    ~(?a. MEM a fargs /\ (Fn g gargs << a \/ (Fn g gargs = a))) /\
    (!a. MEM a fargs ==> a << Fn g gargs)]])
    DISJ_CASES_TAC THENL [ASM_MESON_TAC [], ASM_REWRITE_TAC [], ALL_TAC] THEN
    ASM_REWRITE_TAC [term_INJ] THEN
    HolLight.REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (← ExceptT.mk (HolLight.SPECL [ [[f:num]], [[g:num]] ] LT_CASES)) THEN
    ASM_REWRITE_TAC [LT_REFL] THEN
    HolLight.REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (← ExceptT.mk (HolLight.SPECL [ [[LENGTH(fargs:term list)]], [[LENGTH(gargs:term list)]] ] LT_CASES)) THEN
    ASM_REWRITE_TAC [LT_REFL] THEN
    MATCH_MP_TAC LEX_TOTAL THEN ASM_SIMP_TAC [])
  : ExceptT String IO thm).run
#eval LPO_GROUND_COMPLETE

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.LPO" do
  replay (
          HolLogicArith.Given.ensure)
  replay (
          ITLIST_ADD_1_POS)
  replay (
          FVT_FUN_EMPTY)
  replay (
          NONWF)
  replay (
          WF_NONWF)
  replay (
          NONWF_SUCCESSOR)
  replay (
          WF_NONWF_2)
  replay (
          NONWF_INDUCT)
  replay (
          WF_MINIMAL_STEP)
  replay (
          WF_MINIMAL_DCHAIN)
  replay (
          SEQUENCE_SUBSEQUENCE)
  replay (
          SEQUENCE_PARTITION_LEMMA)
  replay (
          termsize_EXISTS)
  replay (
          termsize)
  replay (
          LEX_DEF)
  replay (
          LEX)
  replay (
          LEX_LENGTH)
  replay (
          MONO_LEX)
  replay (
          show IO Unit from do
      let l ← Session.get_monotonicity_theorems
      Session.set_monotonicity_theorems (MONO_LEX :: l))
  replay (
          LEX_MAP)
  replay (
          LEX_REFL)
  replay (
          LEX_LENGTH_CHAIN)
  replay (
          WF_LEX_STRONG_INDUCT)
  replay (
          WF_LEX_STRONG)
  replay (
          LEX_RESTRICT)
  replay (
          show IO Unit from do
      let _ ← HolCore.Printer.parse_as_infix ("subterm", (12, "right"))
      pure ())
  replay (
          show IO Unit from do
      let _ ← HolCore.Printer.parse_as_infix ("psubterm", (12, "right"))
      pure ())
  replay (
          do IO.println subterm_RULES; IO.println subterm_INDUCT; IO.println subterm_CASES)
  replay (
          psubterm)
  replay (
          DESCENDANT_SMALLER)
  replay (
          DESCENDANT_DISTINCT)
  replay (
          SUBTERM_REFL)
  replay (
          SUBTERM_TRANS)
  replay (
          SUBTERM_ANTISYM)
  replay (
          SUBTERM_FVT)
  replay (
          PSUBTERM_ANTISYM)
  replay (
          SUBTERM_PSUBTERM_TRANS)
  replay (
          PSUBTERM_CASES)
  replay (
          SUBTERM_INSTANTIATION)
  replay (
          PSUBTERM_INSTANTIATION)
  replay (
          do IO.println lpo_RULES; IO.println lpo_INDUCT; IO.println lpo_CASES)
  replay (
          LPO_CASES)
  replay (
          LPO_FVT)
  replay (
          LPO_TRANS_INDUCT)
  replay (
          LPO_TRANS)
  replay (
          LPO_SUBTERM_LEMMA)
  replay (
          LPO_SUBTERM)
  replay (
          LPO_PSUBTERM)
  replay (
          LPO_INSTANTIATION)
  replay (
          LPO_CONGRUENCE)
  replay (
          LPO_REFL)
  replay (
          LPO_WF)
  replay (
          LPO_SUBTERM_NOT)
  replay (
          LEX_TOTAL)
  replay (
          LPO_GROUND_COMPLETE)
-- @@ENSURE END

end HolLogicArith.LPO
