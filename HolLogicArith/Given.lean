/- File: HolLogicArith/Given.lean
Translation of HOL Light's Logic/given.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Resolution
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

namespace HolLogicArith.Given

/- List definitions/theorems used below are exposed by Session as fields of
   the `listDefs`/`listThms1`/`listThms2` bundles; alias the ones we need. -/
private unsafe def LENGTH : thm := Session.listDefs.LENGTH
private unsafe def MAP : thm := Session.listDefs.MAP
private unsafe def ITLIST : thm := Session.listDefs.ITLIST
private unsafe def MEM : thm := Session.listDefs.MEM
private unsafe def EX : thm := Session.listDefs.EX
private unsafe def FILTER : thm := Session.listDefs.FILTER
private unsafe def EL : thm := Session.listDefs.EL
private unsafe def HD : thm := Session.listDefs.HD
private unsafe def TL : thm := Session.listDefs.TL
private unsafe def APPEND : thm := Session.listDefs.APPEND
private unsafe def MAP_o : thm := Session.listThms1.MAP_o
private unsafe def MAP_EQ : thm := Session.listThms1.MAP_EQ
private unsafe def MAP_EQ_DEGEN : thm := Session.listThms1.MAP_EQ_DEGEN
private unsafe def list_CASES : thm := Session.listThms1.list_CASES
private unsafe def ALL_T : thm := Session.listThms1.ALL_T
private unsafe def I_THM : thm := Session.I_THM
private unsafe def NOT_CONS_NIL : thm := Session.listThms1.NOT_CONS_NIL
private unsafe def CONS_11 : thm := Session.listThms1.CONS_11
private unsafe def LENGTH_EQ_NIL : thm := Session.listThms1.LENGTH_EQ_NIL
private unsafe def MEM_EL : thm := Session.listThms2.MEM_EL

#eval HolLogicArith.Resolution.ensure

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- `new_recursive_definition` lifted into `ExceptT String IO`. -/
private unsafe def newRec (ax : thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (Session.new_recursive_definition ax tm)

#eval phrase 1
unsafe def FIRSTN : thm := keep "FIRSTN" fun _ => (do
  newRec num_RECURSION
    [[(FIRSTN 0 l = []) /\
      (FIRSTN (SUC n) l = if l = [] then [] else CONS (HD l) (FIRSTN n (TL l)))]]
  : ExceptT String IO thm).run
#eval FIRSTN

#eval phrase 2
unsafe def FIRSTN_TRIVIAL : thm := keep "FIRSTN_TRIVIAL" fun _ => (do
  prove ([[!n l. LENGTH l <= n ==> (FIRSTN n l = l)]])
   (INDUCT_TAC THEN SIMP_TAC [LE, FIRSTN, LENGTH_EQ_NIL] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [NOT_CONS_NIL] THEN
    REWRITE_TAC [HD, TL, LENGTH, CONS_11, SUC_INJ] THEN
    ASM_MESON_TAC [(← ExceptT.mk (ARITH_RULE [[SUC x <= y ==> x <= y]])), LE_REFL])
  : ExceptT String IO thm).run
#eval FIRSTN_TRIVIAL

#eval phrase 3
unsafe def FIRSTN_EMPTY : thm := keep "FIRSTN_EMPTY" fun _ => (do
  prove ([[!n. FIRSTN n [] = [] ]])
   (MESON_TAC [FIRSTN_TRIVIAL, LENGTH, LE_0])
  : ExceptT String IO thm).run
#eval FIRSTN_EMPTY

#eval phrase 4
unsafe def FIRSTN_SUBLIST : thm := keep "FIRSTN_SUBLIST" fun _ => (do
  prove ([[!x n l. MEM x (FIRSTN n l) ==> MEM x l]])
   (GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [FIRSTN, MEM] THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [NOT_CONS_NIL, HD, TL, MEM] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval FIRSTN_SUBLIST

#eval phrase 5
unsafe def FIRSTN_SUC : thm := keep "FIRSTN_SUC" fun _ => (do
  prove ([[!x n l. MEM x (FIRSTN (SUC n) l)
           ==> MEM x (APPEND (FIRSTN n l) [EL n l]) ]])
   (GEN_TAC THEN INDUCT_TAC THENL
     [REWRITE_TAC [FIRSTN] THEN
      GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [MEM, APPEND, EL],
      ALL_TAC] THEN
    LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC [FIRSTN] THEN
    REWRITE_TAC [NOT_CONS_NIL, MEM] THEN
    REWRITE_TAC [HD, TL, EL, MEM, APPEND] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval FIRSTN_SUC

#eval phrase 6
unsafe def FIRSTN_SHORT : thm := keep "FIRSTN_SHORT" fun _ => (do
  prove ([[!n l. LENGTH l <= n ==> (FIRSTN (SUC n) l = FIRSTN n l)]])
   (MESON_TAC [FIRSTN_TRIVIAL, (← ExceptT.mk (ARITH_RULE [[x <= n ==> x <= SUC n]]))])
  : ExceptT String IO thm).run
#eval FIRSTN_SHORT

#eval phrase 7
unsafe def tautologous : thm := keep "tautologous" fun _ => new_definition
  [[tautologous cl <=> ?p. p IN cl /\ ~~p IN cl]]
#eval tautologous

#eval phrase 8
#eval parse_as_infix ("subsumes", (12, "right"))

#eval phrase 9
unsafe def subsumes : thm := keep "subsumes" fun _ => new_definition
  [[cl subsumes cl' <=> ?i. IMAGE (formsubst i) cl SUBSET cl']]
#eval subsumes

#eval phrase 10
unsafe def subsumes_REFL : thm := keep "subsumes_REFL" fun _ => (do
  prove ([[!cl. cl subsumes cl]])
   (GEN_TAC THEN REWRITE_TAC [subsumes] THEN
    EXISTS_TAC [[V]] THEN
    REWRITE_TAC [SUBSET, IN_IMAGE, FORMSUBST_TRIV] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval subsumes_REFL

#eval phrase 11
unsafe def subsumes_TRANS : thm := keep "subsumes_TRANS" fun _ => (do
  prove ([[!cl1 cl2 cl3. clause cl1 /\ cl1 subsumes cl2 /\ cl2 subsumes cl3
                 ==> cl1 subsumes cl3]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [subsumes, clause] THEN
    DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC ([[i:num->term]])) MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_TAC ([[j:num->term]])) THEN
    EXISTS_TAC [[termsubst j o (i:num->term)]] THEN
    UNDISCH_TAC [[IMAGE (formsubst i) cl1 SUBSET cl2]] THEN
    UNDISCH_TAC [[IMAGE (formsubst j) cl2 SUBSET cl3]] THEN
    REWRITE_TAC [SUBSET, IN_IMAGE] THEN
    SUBGOAL_THEN
     ([[!p. p IN cl1
        ==> (formsubst (termsubst j o i) p = formsubst j (formsubst i p))]])
     (fun th => MESON_TAC [th]) THEN
    SUBGOAL_THEN
     ([[!p. qfree(p)
        ==> (formsubst (termsubst j o i) p = formsubst j (formsubst i p))]])
     (fun th => ASM_MESON_TAC [th, QFREE_LITERAL]) THEN
    MATCH_MP_TAC form_INDUCTION THEN
    SIMP_TAC [qfree, formsubst, o_THM, (← HolLight.GSYM TERMSUBST_TERMSUBST)] THEN
    REWRITE_TAC [(← HolLight.GSYM MAP_o)] THEN
    REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [FUN_EQ_THM, TERMSUBST_TERMSUBST, o_THM])
  : ExceptT String IO thm).run
#eval subsumes_TRANS

#eval phrase 12
#eval parse_as_infix ("SUBSUMES", (12, "right"))

#eval phrase 13
unsafe def SUBSUMES : thm := keep "SUBSUMES" fun _ => new_definition
  [[s SUBSUMES s' <=> !cl'. cl' IN s' ==> ?cl. cl IN s /\ cl subsumes cl']]
#eval SUBSUMES

#eval phrase 14
unsafe def SUBSUMES_REFL : thm := keep "SUBSUMES_REFL" fun _ => (do
  prove ([[!s. s SUBSUMES s]])
   (REWRITE_TAC [SUBSUMES] THEN MESON_TAC [subsumes_REFL])
  : ExceptT String IO thm).run
#eval SUBSUMES_REFL

#eval phrase 15
unsafe def SUBSUMES_UNION : thm := keep "SUBSUMES_UNION" fun _ => (do
  prove ([[s SUBSUMES s' /\ t SUBSUMES t' ==> (s UNION t) SUBSUMES (s' UNION t')]])
   (REWRITE_TAC [SUBSUMES, IN_UNION] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval SUBSUMES_UNION

#eval phrase 16
unsafe def SUBSUMES_TRANS : thm := keep "SUBSUMES_TRANS" fun _ => (do
  prove ([[!s t u. (!c. c IN s ==> clause c) /\ s SUBSUMES t /\ t SUBSUMES u
           ==> s SUBSUMES u]])
   (REWRITE_TAC [SUBSUMES] THEN MESON_TAC [subsumes_TRANS])
  : ExceptT String IO thm).run
#eval SUBSUMES_TRANS

#eval phrase 17
unsafe def SUBSUMES_SUBSET : thm := keep "SUBSUMES_SUBSET" fun _ => (do
  prove ([[!s t u. s SUBSUMES t /\ s SUBSET u ==> u SUBSUMES t]])
   (REWRITE_TAC [SUBSUMES, SUBSET] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval SUBSUMES_SUBSET

#eval phrase 18
unsafe def SUBSUMES_CLAUSES : thm := keep "SUBSUMES_CLAUSES" fun _ => (do
  prove ([[(!s. s SUBSUMES {}) /\
   (!s. s SUBSUMES (x INSERT t) <=> s SUBSUMES {x} /\ s SUBSUMES t)]])
   (REWRITE_TAC [SUBSUMES, IN_INSERT, NOT_IN_EMPTY] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval SUBSUMES_CLAUSES

#eval phrase 19
unsafe def SUBSUMES_SUBSET_REFL : thm := keep "SUBSUMES_SUBSET_REFL" fun _ => (do
  prove ([[!s t. s SUBSET t ==> t SUBSUMES s]])
   (MESON_TAC [SUBSUMES_SUBSET, SUBSUMES_REFL])
  : ExceptT String IO thm).run
#eval SUBSUMES_SUBSET_REFL

#eval phrase 20
unsafe def allresolvents : thm := keep "allresolvents" fun _ => new_definition
  [[allresolvents s1 s2 =
        {c | ?c1 c2. c1 IN s1 /\ c2 IN s2 /\ isaresolvent c (c1,c2)}]]
#eval allresolvents

#eval phrase 21
unsafe def allntresolvents : thm := keep "allntresolvents" fun _ => new_definition
  [[allntresolvents s1 s2 =
        {r | r IN allresolvents s1 s2 /\ ~(tautologous r)}]]
#eval allntresolvents

#eval phrase 22
unsafe def TERMSUBST_TERMSUBST_o : thm := keep "TERMSUBST_TERMSUBST_o" fun _ => (do
  prove ([[termsubst (termsubst j o i) = termsubst j o termsubst i]])
   (REWRITE_TAC [FUN_EQ_THM, o_THM, TERMSUBST_TERMSUBST])
  : ExceptT String IO thm).run
#eval TERMSUBST_TERMSUBST_o

#eval phrase 23
unsafe def FORMSUBST_FORMSUBST : thm := keep "FORMSUBST_FORMSUBST" fun _ => (do
  prove ([[!p i j. qfree(p)
           ==> (formsubst j (formsubst i p) = formsubst (termsubst j o i) p)]])
   (REPEAT GEN_TAC THEN SPEC_TAC ([[p:form]], [[p:form]]) THEN
    MATCH_MP_TAC form_INDUCTION THEN SIMP_TAC [formsubst, qfree] THEN
    REWRITE_TAC [(← HolLight.GSYM MAP_o), TERMSUBST_TERMSUBST_o])
  : ExceptT String IO thm).run
#eval FORMSUBST_FORMSUBST

#eval phrase 24
unsafe def ISARESOLVENT_SYM : thm := keep "ISARESOLVENT_SYM" fun _ => (do
  prove ([[!c1 c2 cl.
        clause c1 /\ clause c2 /\ isaresolvent cl (c2,c1)
        ==> ?cl'. isaresolvent cl' (c1,c2) /\ cl' subsumes cl]])
   (REPEAT STRIP_TAC THEN UNDISCH_TAC [[isaresolvent cl (c2,c1)]] THEN
    REWRITE_TAC [isaresolvent] THEN
    ABBREV_TAC [[r1 = rename c1 (FVS c2)]] THEN
    ABBREV_TAC [[c1' = IMAGE (formsubst r1) c1]] THEN
    CONV_TAC (HolLight.LAND_CONV (HolLight.ONCE_DEPTH_CONV Session.let_CONV)) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[ps2:form->bool]])
          (X_CHOOSE_THEN ([[ps1:form->bool]]) MP_TAC)) THEN
    CONV_TAC (HolLight.LAND_CONV (HolLight.ONCE_DEPTH_CONV Session.let_CONV)) THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    ABBREV_TAC [[r2 = rename c2 (FVS c1)]] THEN
    ABBREV_TAC [[c2' = IMAGE (formsubst r2) c2]] THEN
    MP_TAC (← HolLight.SPECL [ [[c1:form->bool]], [[FVS c2]] ] rename) THEN
    ASM_SIMP_TAC [FVS_CLAUSE_FINITE] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [«renaming»] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[s1:num->term]]) STRIP_ASSUME_TAC) THEN
    MP_TAC (← HolLight.SPECL [ [[c2:form->bool]], [[FVS c1]] ] rename) THEN
    ASM_SIMP_TAC [FVS_CLAUSE_FINITE] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [«renaming»] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[s2:num->term]]) STRIP_ASSUME_TAC) THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV Session.let_CONV) THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    EXISTS_TAC [[IMAGE (formsubst s1) ps1]] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    EXISTS_TAC [[IMAGE (formsubst r2) ps2]] THEN
    REWRITE_TAC [LEFT_EXISTS_AND_THM] THEN
    HolCore.Lib.W (fun g => HolLight.tactic_of do
      let (_, bod) ← liftExcept (HolCore.Basics.dest_exists (HolLight.snd g))
      let t ← liftExcept (do
        let l ← HolCore.Equal.lhand bod
        HolCore.Lib.funpow 6 (fun (m : Except String term) => do HolCore.Kernel.rand (← m)) (pure l))
      pure (EXISTS_TAC t)) THEN
    REWRITE_TAC [] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a /\ b /\ c /\ d /\ e) /\ (e ==> f)
                     ==> (a /\ b /\ c /\ d /\ e) /\ f]])) THEN
    CONJ_TAC THENL
     [REPEAT CONJ_TAC THENL
       [UNDISCH_TAC [[ps1 SUBSET c1':form->bool]] THEN Fol.EXPAND_TAC "c1'" THEN
        REWRITE_TAC [SUBSET, IN_IMAGE] THEN
        SUBGOAL_THEN ([[!p. p IN c1 ==> (formsubst s1 (formsubst r1 p) = p)]])
          (fun th => MESON_TAC [th]) THEN
        SUBGOAL_THEN
         ([[!p. qfree p
            ==> (formsubst V p = formsubst s1 (formsubst r1 p))]])
         (fun th => ASM_MESON_TAC [th, FORMSUBST_TRIV,
                                  clause, QFREE_LITERAL]) THEN
        ASM_REWRITE_TAC [FORMSUBST_TERMSUBST_LEMMA] THEN
        REWRITE_TAC [FUN_EQ_THM, TERMSUBST_TRIV, I_DEF],
        UNDISCH_TAC [[ps2 SUBSET c2:form->bool]] THEN Fol.EXPAND_TAC "c2'" THEN
        REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_IMAGE] THEN MESON_TAC [],
        UNDISCH_TAC [[~(ps1:form->bool = {})]] THEN
        REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, IN_IMAGE] THEN MESON_TAC [],
        UNDISCH_TAC [[~(ps2:form->bool = {})]] THEN
        REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, IN_IMAGE] THEN MESON_TAC [],
        FIRST_X_ASSUM (X_CHOOSE_THEN ([[i:num->term]]) MP_TAC) THEN
        REWRITE_TAC [UNIFIES, IN_UNION, IN_IMAGE, IN_ELIM_THM] THEN
        REWRITE_TAC [(← ExceptT.mk (TAUT [[(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)]]))] THEN
        SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN REWRITE_TAC [FORALL_AND_THM] THEN
        X_GEN_TAC [[P:form]] THEN
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        DISCH_THEN (MP_TAC o HolLight.GEN [[p:form]] oTIO HolLight.SPECL [ [[~~p]], [[p:form]] ]) THEN
        REWRITE_TAC [] THEN DISCH_TAC THEN
        EXISTS_TAC [[\x. if x IN FVS(IMAGE (formsubst s1) ps1)
                      then termsubst i (r1 x)
                      else termsubst i (s2 x)]] THEN
        EXISTS_TAC [[~~P]] THEN CONJ_TAC THENL
         [X_GEN_TAC [[rrr:form]] THEN X_GEN_TAC [[p:form]] THEN
          DISCH_THEN (ASSUME_TAC oT Session.CONJUNCT2) THEN
          MATCH_MP_TAC EQ_TRANS THEN
          EXISTS_TAC [[formsubst (\x. termsubst i (r1 x)) (formsubst s1 p)]] THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC FORMSUBST_VALUATION THEN X_GEN_TAC [[x:num]] THEN
            DISCH_TAC THEN REWRITE_TAC [] THEN
            SUBGOAL_THEN ([[x IN FVS(IMAGE (formsubst s1) ps1)]])
              (fun th => REWRITE_TAC [th]) THEN
            REWRITE_TAC [IN_UNIONS, FVS, IN_ELIM_THM, IN_IMAGE] THEN
            ASM_MESON_TAC [], ALL_TAC] THEN
          SUBGOAL_THEN ([[P = formsubst i (~~p)]]) SUBST1_TAC THENL
           [ASM_MESON_TAC [], ALL_TAC] THEN
          SUBGOAL_THEN ([[literal p]]) MP_TAC THENL
           [UNDISCH_TAC [[ps1 SUBSET c1':form->bool]] THEN
            Fol.EXPAND_TAC "c1'" THEN REWRITE_TAC [IN_IMAGE, SUBSET] THEN
            DISCH_THEN (MP_TAC o HolLight.SPEC [[p:form]]) THEN
            ASM_SIMP_TAC [LEFT_IMP_EXISTS_THM, FORMSUBST_LITERAL] THEN
            ASM_MESON_TAC [clause], ALL_TAC] THEN
          SIMP_TAC [(← HolLight.GSYM FORMSUBST_NEGATE), NEGATE_NEGATE] THEN
          DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP QFREE_LITERAL) THEN
          SIMP_TAC [FORMSUBST_FORMSUBST, (← HolLight.GSYM o_DEF)] THEN
          UNDISCH_TAC [[ps1 SUBSET c1':form->bool]] THEN
          Fol.EXPAND_TAC "c1'" THEN REWRITE_TAC [SUBSET, IN_IMAGE] THEN
          DISCH_THEN (MP_TAC o HolLight.SPEC [[p:form]]) THEN ASM_REWRITE_TAC [] THEN
          DISCH_THEN (X_CHOOSE_THEN ([[q:form]])
           (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
          SIMP_TAC [QFREE_FORMSUBST, FORMSUBST_FORMSUBST] THEN
          SPEC_TAC ([[q:form]], [[q:form]]) THEN
          MATCH_MP_TAC form_INDUCTION THEN SIMP_TAC [formsubst, qfree] THEN
          REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
          REWRITE_TAC [TERMSUBST_TERMSUBST_o] THEN
          ASM_REWRITE_TAC [(← HolLight.GSYM o_ASSOC)] THEN REWRITE_TAC [o_DEF, I_DEF],
          ALL_TAC] THEN
        X_GEN_TAC [[rrr:form]] THEN X_GEN_TAC [[p:form]] THEN
        DISCH_THEN (MP_TAC oT Session.CONJUNCT1) THEN
        DISCH_THEN (X_CHOOSE_THEN ([[q:form]])
          (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
        REWRITE_TAC [FORMSUBST_NEGATE] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC [[formsubst (\x. termsubst i (s2 x)) (formsubst r2 q)]] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC FORMSUBST_VALUATION THEN X_GEN_TAC [[x:num]] THEN
          DISCH_TAC THEN REWRITE_TAC [] THEN
          SUBGOAL_THEN ([[~(x IN FVS(IMAGE (formsubst s1) ps1))]])
            (fun th => REWRITE_TAC [th]) THEN
          UNDISCH_TAC [[FVS c2' INTER FVS c1 = {}]] THEN Fol.EXPAND_TAC "c2'" THEN
          REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
          DISCH_THEN (MP_TAC o HolLight.SPEC [[x:num]]) THEN
          UNDISCH_TAC [[x IN FV(formsubst r2 q)]] THEN
          MATCH_MP_TAC (← ExceptT.mk (TAUT
           [[(a ==> a') /\ (b ==> b') ==> a ==> ~(a' /\ b') ==> ~b]])) THEN
          CONJ_TAC THENL
           [REWRITE_TAC [FVS, IN_UNIONS, IN_IMAGE, IN_ELIM_THM] THEN
            ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
          REWRITE_TAC [FVS, IN_UNIONS, IN_IMAGE, IN_ELIM_THM] THEN
          UNDISCH_TAC [[ps1 SUBSET c1':form->bool]] THEN
          REWRITE_TAC [SUBSET] THEN
          Fol.EXPAND_TAC "c1'" THEN REWRITE_TAC [IN_IMAGE] THEN
          SUBGOAL_THEN ([[!p. p IN c1 ==> (formsubst s1 (formsubst r1 p) = p)]])
            (fun th => MESON_TAC [th]) THEN
          SUBGOAL_THEN ([[!p. qfree(p) ==> (formsubst s1 (formsubst r1 p) = p)]])
            (fun th => ASM_MESON_TAC [th, clause, QFREE_LITERAL]) THEN
          SIMP_TAC [FORMSUBST_FORMSUBST] THEN
          MATCH_MP_TAC form_INDUCTION THEN SIMP_TAC [formsubst, qfree] THEN
          REPEAT GEN_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ_DEGEN THEN
          ASM_REWRITE_TAC [TERMSUBST_TERMSUBST_o] THEN
          REWRITE_TAC [I_THM, ALL_T], ALL_TAC] THEN
        SUBGOAL_THEN ([[qfree q]]) MP_TAC THENL
         [ASM_MESON_TAC [SUBSET, clause, QFREE_LITERAL], ALL_TAC] THEN
        SIMP_TAC [FORMSUBST_FORMSUBST] THEN
        SUBGOAL_THEN ([[formsubst i q = P]]) (SUBST1_TAC oTIO HolLight.SYM) THENL
         [ASM_MESON_TAC [], ALL_TAC] THEN
        REWRITE_TAC [(← HolLight.GSYM o_DEF)] THEN
        SPEC_TAC ([[q:form]], [[q:form]]) THEN
        MATCH_MP_TAC form_INDUCTION THEN SIMP_TAC [formsubst, qfree] THEN
        REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC [TERMSUBST_TERMSUBST_o] THEN
        ASM_REWRITE_TAC [(← HolLight.GSYM o_ASSOC)] THEN REWRITE_TAC [o_DEF, I_DEF] THEN
        CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (ETA_CONV t))) THEN REFL_TAC],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[?ps0. ps0 SUBSET c1 /\ ~(ps0 = {}) /\
                      (ps1 = IMAGE (formsubst r1) ps0)]])
    MP_TAC THENL
     [EXISTS_TAC [[{p | p IN c1 /\ (formsubst r1 p) IN ps1}]] THEN
      UNDISCH_TAC [[~(ps1:form->bool = {})]] THEN
      UNDISCH_TAC [[ps1 SUBSET c1':form->bool]] THEN Fol.EXPAND_TAC "c1'" THEN
      REWRITE_TAC [EXTENSION, SUBSET, IN_ELIM_THM, NOT_IN_EMPTY,
                  IN_IMAGE] THEN
      MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[ps0:form->bool]]) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN SUBST_ALL_TAC THEN Fol.EXPAND_TAC "c2'" THEN
    REWRITE_TAC [(← HolLight.GSYM IMAGE_o)] THEN
    SUBGOAL_THEN ([[IMAGE (formsubst s1 o formsubst r1) ps0 = ps0]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE, o_THM] THEN
      X_GEN_TAC [[p:form]] THEN
      SUBGOAL_THEN ([[!p. p IN ps0 ==> (formsubst s1 (formsubst r1 p) = p)]])
          (fun th => MESON_TAC [th]) THEN
      SUBGOAL_THEN ([[!p. qfree p ==> (formsubst s1 (formsubst r1 p) = p)]])
          (fun th => ASM_MESON_TAC [clause, SUBSET, QFREE_LITERAL, th]) THEN
      MATCH_MP_TAC form_INDUCTION THEN SIMP_TAC [formsubst, qfree] THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM MAP_o)] THEN
      SIMP_TAC [MAP_EQ_DEGEN, I_DEF, ALL_T], ALL_TAC] THEN
    DISCH_TAC THEN
    ABBREV_TAC [[i = mgu (ps0 UNION {~~p | p IN IMAGE (formsubst r2) ps2})]] THEN
    ABBREV_TAC [[j = mgu (ps2 UNION {~~p | p IN IMAGE (formsubst r1) ps0})]] THEN
    Fol.EXPAND_TAC "c1'" THEN
    MP_TAC (← HolLight.SPEC ([[ps0 UNION {~~p | p IN IMAGE (formsubst r2) ps2}]]) MGU) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN ([[{~~ p | p IN IMAGE (formsubst r2) ps2} =
                      IMAGE (~~) (IMAGE (formsubst r2) ps2)]])
        SUBST1_TAC THENL
         [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE] THEN MESON_TAC [],
          ALL_TAC] THEN
        REWRITE_TAC [FINITE_UNION] THEN CONJ_TAC THEN
        REPEAT (MATCH_MP_TAC FINITE_IMAGE) THEN
        ASM_MESON_TAC [FINITE_SUBSET, clause], ALL_TAC] THEN
      REWRITE_TAC [IN_UNION, IN_ELIM_THM, IN_IMAGE] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [QFREE_NEGATE, QFREE_FORMSUBST] THEN
      ASM_MESON_TAC [SUBSET, clause, QFREE_LITERAL], ALL_TAC] THEN
    STRIP_TAC THEN
    MP_TAC (← HolLight.SPEC ([[ps2 UNION {~~ p | p IN IMAGE (formsubst r1) ps0}]]) MGU) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN ([[{~~ p | p IN IMAGE (formsubst r1) ps0} =
                      IMAGE (~~) (IMAGE (formsubst r1) ps0)]])
        SUBST1_TAC THENL
         [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_IMAGE] THEN MESON_TAC [],
          ALL_TAC] THEN
        REWRITE_TAC [FINITE_UNION] THEN CONJ_TAC THEN
        REPEAT (MATCH_MP_TAC FINITE_IMAGE) THEN
        ASM_MESON_TAC [FINITE_SUBSET, clause], ALL_TAC] THEN
      REWRITE_TAC [IN_UNION, IN_ELIM_THM, IN_IMAGE] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [QFREE_NEGATE, QFREE_FORMSUBST] THEN
      ASM_MESON_TAC [SUBSET, clause, QFREE_LITERAL], ALL_TAC] THEN
    STRIP_TAC THEN
    UNDISCH_TAC
     [[!i'. Unifies i' (ps0 UNION {~~ p | p IN IMAGE (formsubst r2) ps2})
            ==> (!p. qfree p
                     ==> (formsubst i' p = formsubst i' (formsubst i p)))]] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC
      [[\x. if x IN FVS(c1) then termsubst j (r1 x)
         else termsubst j (s2 x)]]) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC
       [[Unifies j (ps2 UNION {~~ p | p IN IMAGE (formsubst r1) ps0})]] THEN
      REWRITE_TAC [UNIFIES] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[P:form]]) MP_TAC) THEN
      REWRITE_TAC [UNIFIES, IN_UNION, IN_IMAGE, IN_ELIM_THM] THEN
      REWRITE_TAC [(← ExceptT.mk (TAUT [[(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)]]))] THEN
      SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN REWRITE_TAC [FORALL_AND_THM] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN (MP_TAC o HolLight.GEN [[p:form]] oTIO HolLight.SPECL [ [[~~p]], [[p:form]] ]) THEN
      REWRITE_TAC [] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      DISCH_THEN (MP_TAC o HolLight.GEN [[p:form]] oTIO HolLight.SPECL [ [[formsubst r1 p]], [[p:form]] ]) THEN
      ASM_REWRITE_TAC [FORMSUBST_NEGATE] THEN DISCH_TAC THEN
      EXISTS_TAC [[~~P]] THEN CONJ_TAC THENL
       [X_GEN_TAC [[p:form]] THEN DISCH_TAC THEN
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC [[formsubst (termsubst j o r1) p]] THEN CONJ_TAC THENL
         [MATCH_MP_TAC FORMSUBST_VALUATION THEN
          X_GEN_TAC [[x:num]] THEN DISCH_TAC THEN REWRITE_TAC [o_THM] THEN
          SUBGOAL_THEN ([[x IN FVS(c1)]]) (fun th => REWRITE_TAC [th]) THEN
          ASM_REWRITE_TAC [FVS, IN_UNIONS, IN_ELIM_THM] THEN
          ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
        SUBGOAL_THEN ([[P = ~~(formsubst j (formsubst r1 p))]]) SUBST1_TAC THENL
         [ASM_MESON_TAC [], ALL_TAC] THEN
        SUBGOAL_THEN ([[~~(~~(formsubst j (formsubst r1 p))) =
                      formsubst j (formsubst r1 p)]])
        SUBST1_TAC THENL
         [MATCH_MP_TAC NEGATE_NEGATE THEN
          REWRITE_TAC [FORMSUBST_LITERAL] THEN
          ASM_MESON_TAC [SUBSET, clause], ALL_TAC] THEN
        MATCH_MP_TAC (← HolLight.GSYM FORMSUBST_FORMSUBST) THEN
        ASM_MESON_TAC [SUBSET, clause, QFREE_LITERAL], ALL_TAC] THEN
      X_GEN_TAC [[rrr:form]] THEN X_GEN_TAC [[p:form]] THEN
      REWRITE_TAC [LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC [[q:form]] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      AP_TERM_TAC THEN
      SUBGOAL_THEN ([[formsubst j q = P]]) (SUBST1_TAC oTIO HolLight.SYM) THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC [[formsubst (termsubst j o s2) (formsubst r2 q)]] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FORMSUBST_VALUATION THEN
        X_GEN_TAC [[x:num]] THEN DISCH_TAC THEN REWRITE_TAC [] THEN
        SUBGOAL_THEN ([[~(x IN FVS(c1))]]) (fun th => REWRITE_TAC [o_THM, th]) THEN
        UNDISCH_TAC [[FVS c2' INTER FVS c1 = {}]] THEN Fol.EXPAND_TAC "c2'" THEN
        REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC [[x:num]]) THEN
        MATCH_MP_TAC (← ExceptT.mk (TAUT [[a ==> ~(a /\ b) ==> ~b]])) THEN
        UNDISCH_TAC [[x IN FV (formsubst r2 q)]] THEN
        UNDISCH_TAC [[q:form IN ps2]] THEN
        UNDISCH_TAC [[ps2 SUBSET c2:form->bool]] THEN
        REWRITE_TAC [SUBSET, FVS, IN_UNIONS, IN_IMAGE, IN_ELIM_THM] THEN
        MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[qfree q]]) MP_TAC THENL
       [ASM_MESON_TAC [SUBSET, clause, QFREE_LITERAL], ALL_TAC] THEN
      SIMP_TAC [FORMSUBST_FORMSUBST] THEN
      SPEC_TAC ([[q:form]], [[q:form]]) THEN MATCH_MP_TAC form_INDUCTION THEN
      SIMP_TAC [qfree, formsubst] THEN REPEAT GEN_TAC THEN
      AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
      REWRITE_TAC [TERMSUBST_TERMSUBST_o] THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM o_ASSOC)] THEN REWRITE_TAC [o_DEF, I_DEF, ALL_T],
      ALL_TAC] THEN
    ABBREV_TAC [[k = \x. if x IN FVS(c1) then termsubst j (r1 x)
                      else termsubst j (s2 x)]] THEN
    DISCH_TAC THEN REWRITE_TAC [subsumes] THEN
    EXISTS_TAC [[k:num->term]] THEN REWRITE_TAC [(← HolLight.GSYM IMAGE_o)] THEN
    SUBGOAL_THEN
     ([[IMAGE (formsubst k o formsubst i)
            (c1 DIFF ps0 UNION c2' DIFF IMAGE (formsubst r2) ps2) =
      IMAGE (formsubst k)
            (c1 DIFF ps0 UNION c2' DIFF IMAGE (formsubst r2) ps2)]])
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE] THEN
      SUBGOAL_THEN
       ([[!p. p IN (c1 DIFF ps0 UNION c2' DIFF IMAGE (formsubst r2) ps2)
            ==> qfree p]])
       (fun th => ASM_MESON_TAC [o_THM, th]) THEN
      REWRITE_TAC [IN_UNION, IN_IMAGE, IN_DIFF] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
       [ASM_MESON_TAC [QFREE_LITERAL, clause], ALL_TAC] THEN
      UNDISCH_TAC [[p:form IN c2']] THEN Fol.EXPAND_TAC "c2'" THEN
      SIMP_TAC [IN_IMAGE, LEFT_IMP_EXISTS_THM, QFREE_FORMSUBST] THEN
      ASM_MESON_TAC [QFREE_LITERAL, clause], ALL_TAC] THEN
    REWRITE_TAC [IN_IMAGE, SUBSET, IN_ELIM_THM] THEN
    X_GEN_TAC [[p:form]] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[q:form]]) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    REWRITE_TAC [IN_UNION] THEN STRIP_TAC THENL
     [EXISTS_TAC [[formsubst r1 q]] THEN CONJ_TAC THENL
       [SUBGOAL_THEN ([[qfree q]]) MP_TAC THENL
         [ASM_MESON_TAC [IN_DIFF, clause, QFREE_LITERAL], ALL_TAC] THEN
        SIMP_TAC [FORMSUBST_FORMSUBST] THEN DISCH_TAC THEN
        MATCH_MP_TAC FORMSUBST_VALUATION THEN
        X_GEN_TAC [[x:num]] THEN DISCH_TAC THEN Fol.EXPAND_TAC "k" THEN
        SUBGOAL_THEN ([[x IN FVS(c1)]]) (fun th => REWRITE_TAC [th, o_THM]) THEN
        REWRITE_TAC [FVS, IN_UNIONS, IN_ELIM_THM] THEN ASM_MESON_TAC [IN_DIFF],
        ALL_TAC] THEN
      DISJ2_TAC THEN Fol.EXPAND_TAC "c1'" THEN
      UNDISCH_TAC [[q:form IN c1 DIFF ps0]] THEN
      REWRITE_TAC [IN_DIFF, IN_IMAGE] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[r:form]]) MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN (MP_TAC o HolLight.AP_TERM [[formsubst s1]]) THEN
      SUBGOAL_THEN ([[(formsubst s1 (formsubst r1 q) = q) /\
                    (formsubst s1 (formsubst r1 r) = r)]])
        (fun th => ASM_MESON_TAC [th]) THEN
      SUBGOAL_THEN ([[!p. qfree p ==> (formsubst s1 (formsubst r1 p) = p)]])
        (fun th => ASM_MESON_TAC [th, SUBSET, clause, QFREE_LITERAL]) THEN
      HolLight.GEN_REWRITE_TAC (HolLight.BINDER_CONV o HolLight.RAND_CONV o HolLight.RAND_CONV)
       [(← HolLight.GSYM FORMSUBST_TRIV)] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV HolLight.SYM_CONV) THEN
      REWRITE_TAC [FORMSUBST_TERMSUBST_LEMMA] THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [FUN_EQ_THM, TERMSUBST_TRIV, I_DEF],
      ALL_TAC] THEN
    EXISTS_TAC [[formsubst s2 q]] THEN CONJ_TAC THENL
     [SUBGOAL_THEN ([[qfree q]]) MP_TAC THENL
       [UNDISCH_TAC [[q IN c2' DIFF IMAGE (formsubst r2) ps2]] THEN
        Fol.EXPAND_TAC "c2'" THEN REWRITE_TAC [IN_DIFF] THEN
        DISCH_THEN (MP_TAC oT Session.CONJUNCT1) THEN
        REWRITE_TAC [IN_IMAGE] THEN
        ASM_MESON_TAC [clause, QFREE_LITERAL, QFREE_FORMSUBST], ALL_TAC] THEN
      SIMP_TAC [FORMSUBST_FORMSUBST] THEN DISCH_TAC THEN
      MATCH_MP_TAC FORMSUBST_VALUATION THEN
      X_GEN_TAC [[x:num]] THEN DISCH_TAC THEN Fol.EXPAND_TAC "k" THEN
      SUBGOAL_THEN ([[~(x IN FVS(c1))]]) (fun th => REWRITE_TAC [th, o_THM]) THEN
      UNDISCH_TAC [[FVS c2' INTER FVS c1 = {}]] THEN
      REWRITE_TAC [EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[x:num]]) THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[a ==> ~(a /\ b) ==> ~b]])) THEN
      REWRITE_TAC [FVS, IN_UNIONS, IN_ELIM_THM] THEN ASM_MESON_TAC [IN_DIFF],
      ALL_TAC] THEN
    DISJ1_TAC THEN
    UNDISCH_TAC [[q IN c2' DIFF IMAGE (formsubst r2) ps2]] THEN
    Fol.EXPAND_TAC "c2'" THEN
    REWRITE_TAC [IN_DIFF, IN_IMAGE] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> a') /\ (b ==> b') ==> a /\ b ==> a' /\ b']])) THEN
    CONJ_TAC THENL
     [DISCH_THEN (X_CHOOSE_THEN ([[r:form]]) STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[formsubst s2 (formsubst r2 r) = r]])
       (fun th => ASM_MESON_TAC [th]) THEN
      SUBGOAL_THEN ([[qfree r]]) MP_TAC THENL
       [ASM_MESON_TAC [clause, QFREE_LITERAL], ALL_TAC] THEN
      SPEC_TAC ([[r:form]], [[r:form]]) THEN
      HolLight.GEN_REWRITE_TAC (HolLight.BINDER_CONV o HolLight.RAND_CONV o HolLight.RAND_CONV)
       [(← HolLight.GSYM FORMSUBST_TRIV)] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV HolLight.SYM_CONV) THEN
      REWRITE_TAC [FORMSUBST_TERMSUBST_LEMMA] THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [FUN_EQ_THM, TERMSUBST_TRIV, I_DEF],
      ALL_TAC] THEN
    REWRITE_TAC [(← ExceptT.mk (TAUT [[~a ==> ~b <=> b ==> a]]))] THEN
    DISCH_TAC THEN
    EXISTS_TAC [[formsubst s2 q]] THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC HolLight.SYM_CONV THEN HolLight.GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM FORMSUBST_TRIV)] THEN
    SUBGOAL_THEN ([[qfree q]]) MP_TAC THENL
     [ASM_MESON_TAC [QFREE_FORMSUBST, SUBSET, clause, QFREE_LITERAL],
      ALL_TAC] THEN
    SPEC_TAC ([[q:form]], [[q:form]]) THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV HolLight.SYM_CONV) THEN
    REWRITE_TAC [FORMSUBST_TERMSUBST_LEMMA] THEN
    ASM_REWRITE_TAC [FUN_EQ_THM, TERMSUBST_TRIV, I_DEF])
  : ExceptT String IO thm).run
#eval ISARESOLVENT_SYM

#eval phrase 25
unsafe def ALLRESOLVENTS_SYM : thm := keep "ALLRESOLVENTS_SYM" fun _ => (do
  prove ([[(!c. c IN A ==> clause c) /\ (!c. c IN B ==> clause c)
   ==> (allresolvents A B) SUBSUMES (allresolvents B A)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [SUBSUMES, allresolvents, IN_ELIM_THM] THEN
    X_GEN_TAC [[cl:form->bool]] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[c2:form->bool]])
          (X_CHOOSE_THEN ([[c1:form->bool]]) STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN EXISTS_TAC [[c1:form->bool]] THEN
    ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN EXISTS_TAC [[c2:form->bool]] THEN
    ASM_SIMP_TAC [ISARESOLVENT_SYM])
  : ExceptT String IO thm).run
#eval ALLRESOLVENTS_SYM

#eval phrase 26
unsafe def ALLRESOLVENTS_UNION : thm := keep "ALLRESOLVENTS_UNION" fun _ => (do
  prove ([[(allresolvents (A UNION B) C =
        (allresolvents A C) UNION (allresolvents B C)) /\
   (allresolvents A (B UNION C) =
        (allresolvents A B) UNION (allresolvents A C))]])
   (REWRITE_TAC [EXTENSION, allresolvents, IN_ELIM_THM, IN_UNION] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval ALLRESOLVENTS_UNION

#eval phrase 27
unsafe def ALLRESOLVENTS_STEP : thm := keep "ALLRESOLVENTS_STEP" fun _ => (do
  prove ([[(!c. c IN B ==> clause(c)) /\
   (!c. c IN C ==> clause(c))
   ==> ((allresolvents B (A UNION B)) UNION
        (allresolvents C (A UNION B UNION C)))
       SUBSUMES (allresolvents(B UNION C) (A UNION B UNION C))]])
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [ALLRESOLVENTS_UNION, UNION_ASSOC] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (Session.AC UNION_ACI
     [[a UNION b UNION c UNION d UNION e UNION f =
      a UNION b UNION d UNION (c UNION e) UNION f]]))] THEN
    HolLight.GEN_REWRITE_TAC (HolLight.LAND_CONV o HolCore.Lib.funpow 3 HolLight.RAND_CONV) [(← ExceptT.mk (Session.AC UNION_ACI
     [[A UNION B = (A UNION A) UNION B]]))] THEN
    REPEAT (MATCH_MP_TAC SUBSUMES_UNION THEN ASM_REWRITE_TAC [SUBSUMES_REFL]) THEN
    ASM_SIMP_TAC [ALLRESOLVENTS_SYM])
  : ExceptT String IO thm).run
#eval ALLRESOLVENTS_STEP

#eval phrase 28
unsafe def resolvents : thm := keep "resolvents" fun _ => new_definition
  [[resolvents cl cls = list_of_set(allresolvents {cl} (set_of_list cls))]]
#eval resolvents

#eval phrase 29
unsafe def CLAUSE_UNION : thm := keep "CLAUSE_UNION" fun _ => (do
  prove ([[!c1 c2. clause(c1 UNION c2) <=> clause(c1) /\ clause(c2)]])
   (REWRITE_TAC [clause, FINITE_UNION, IN_UNION] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval CLAUSE_UNION

#eval phrase 30
unsafe def CLAUSE_SUBSET : thm := keep "CLAUSE_SUBSET" fun _ => (do
  prove ([[!c1 c2. clause c2 /\ c1 SUBSET c2 ==> clause c1]])
   (REWRITE_TAC [clause] THEN MESON_TAC [SUBSET, FINITE_SUBSET])
  : ExceptT String IO thm).run
#eval CLAUSE_SUBSET

#eval phrase 31
unsafe def CLAUSE_DIFF : thm := keep "CLAUSE_DIFF" fun _ => (do
  prove ([[!c1 c2. clause c1 ==> clause (c1 DIFF c2)]])
   (MESON_TAC [CLAUSE_SUBSET, IN_DIFF, SUBSET])
  : ExceptT String IO thm).run
#eval CLAUSE_DIFF

#eval phrase 32
unsafe def ISARESOLVENT_CLAUSE : thm := keep "ISARESOLVENT_CLAUSE" fun _ => (do
  prove ([[!p q r. clause p /\ clause q /\ isaresolvent r (p,q) ==> clause r]])
   (REWRITE_TAC [isaresolvent] THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV Session.let_CONV) THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IMAGE_FORMSUBST_CLAUSE THEN
    ASM_SIMP_TAC [IMAGE_FORMSUBST_CLAUSE, CLAUSE_UNION, CLAUSE_DIFF])
  : ExceptT String IO thm).run
#eval ISARESOLVENT_CLAUSE

#eval phrase 33
unsafe def ALLRESOLVENTS_CLAUSE : thm := keep "ALLRESOLVENTS_CLAUSE" fun _ => (do
  prove ([[(!c. c IN s ==> clause c) /\ (!c. c IN t ==> clause c)
   ==> !c. c IN allresolvents s t ==> clause c]])
   (REWRITE_TAC [allresolvents, IN_ELIM_THM, isaresolvent] THEN
    CONV_TAC (HolLight.TOP_DEPTH_CONV Session.let_CONV) THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC IMAGE_FORMSUBST_CLAUSE THEN
    ASM_SIMP_TAC [IMAGE_FORMSUBST_CLAUSE, CLAUSE_UNION, CLAUSE_DIFF])
  : ExceptT String IO thm).run
#eval ALLRESOLVENTS_CLAUSE

#eval phrase 34
unsafe def ISARESOLVENT_FINITE : thm := keep "ISARESOLVENT_FINITE" fun _ => (do
  prove ([[!c1 c2. clause(c1) /\ clause(c2)
           ==> FINITE {c | isaresolvent c (c1,c2)}]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [isaresolvent] THEN
    LET_TAC THEN
    SUBGOAL_THEN ([[clause cl2']]) ASSUME_TAC THENL
     [Fol.EXPAND_TAC "cl2'" THEN ASM_SIMP_TAC [IMAGE_FORMSUBST_CLAUSE],
      ALL_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     [[IMAGE (\pss. let i = mgu (FST(pss) UNION {~~ p | p IN SND(pss)}) in
                       IMAGE (formsubst i)
                             (c1 DIFF (FST pss) UNION cl2' DIFF (SND pss)))
            {ps1,ps2 | ps1 IN {ps1 | ps1 SUBSET c1} /\
                       ps2 IN {ps2 | ps2 SUBSET cl2'}}]] THEN
    CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [SUBSET, IN_IMAGE, IN_ELIM_THM] THEN
      X_GEN_TAC [[c:form->bool]] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [ [[ps1:form->bool]], [[ps2:form->bool]] ] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN STRIP_TAC THEN
      EXISTS_TAC [[ps1:form->bool,ps2:form->bool]] THEN
      ASM_REWRITE_TAC [] THEN ASM_MESON_TAC []] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_PRODUCT THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [clause]) THEN ASM_SIMP_TAC [FINITE_POWERSET])
  : ExceptT String IO thm).run
#eval ISARESOLVENT_FINITE

#eval phrase 35
unsafe def ALLRESOLVENTS_FINITE : thm := keep "ALLRESOLVENTS_FINITE" fun _ => (do
  prove ([[!s t. FINITE(s) /\ FINITE(t) /\
         (!c. c IN s ==> clause c) /\
         (!c. c IN t ==> clause c)
         ==> FINITE(allresolvents s t)]])
   (REPEAT STRIP_TAC THEN SUBGOAL_THEN
     ([[allresolvents s t =
        UNIONS (IMAGE (\cs. {c | isaresolvent c cs})
                      {c1,c2 | c1 IN s /\ c2 IN t})]])
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, allresolvents, IN_UNIONS, IN_IMAGE,
                  IN_ELIM_THM] THEN
      X_GEN_TAC [[c:form->bool]] THEN
      EQ_TAC THENL [ALL_TAC, MESON_TAC []] THEN
      STRIP_TAC THEN EXISTS_TAC [[{c | isaresolvent c (c1,c2)}]] THEN
      REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC [FINITE_UNIONS, FINITE_IMAGE, FINITE_PRODUCT] THEN
    REWRITE_TAC [IN_IMAGE] THEN X_GEN_TAC [[u:(form->bool)->bool]] THEN
    DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
    HolLight.GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.TOP_DEPTH_CONV) [IN_ELIM_THM, BETA_THM] THEN
    STRIP_TAC THEN ASM_SIMP_TAC [ISARESOLVENT_FINITE])
  : ExceptT String IO thm).run
#eval ALLRESOLVENTS_FINITE

#eval phrase 36
unsafe def replace : thm := keep "replace" fun _ => (do
  newRec Session.list_RECURSION
    [[(replace cl [] = [cl]) /\
      (replace cl (CONS c cls) =
           if cl subsumes c then CONS cl cls else CONS c (replace cl cls))]]
  : ExceptT String IO thm).run
#eval replace

#eval phrase 37
unsafe def REPLACE : thm := keep "REPLACE" fun _ => (do
  prove ([[!cl lis. (!c. MEM c lis ==> clause c) /\ clause cl
            ==> (!c. MEM c (replace cl lis) ==> clause c) /\
                set_of_list(replace cl lis) SUBSUMES set_of_list(CONS cl lis)]])
   (GEN_TAC THEN LIST_INDUCT_TAC THEN
    SIMP_TAC [replace, SUBSUMES_REFL, MEM] THEN
    REWRITE_TAC [(← ExceptT.mk (TAUT [[(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)]]))] THEN
    REWRITE_TAC [FORALL_AND_THM] THEN STRIP_TAC THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
      let _ ← liftExcept (HolCore.Lib.check (fun t => HolCore.Basics.is_imp t) (concl th))
      pure (UNDISCH_TAC (concl th))) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC [MEM, set_of_list] THENL
     [UNDISCH_TAC [[set_of_list(replace cl t) SUBSUMES
                      set_of_list(CONS cl t)]],
      UNDISCH_TAC
       [[set_of_list(replace cl t) SUBSUMES set_of_list(CONS cl t)]]] THEN
    REWRITE_TAC [SUBSUMES, IN_INSERT, set_of_list] THEN
    REWRITE_TAC [IN_SET_OF_LIST] THEN ASM_MESON_TAC [subsumes_REFL])
  : ExceptT String IO thm).run
#eval REPLACE

#eval phrase 38
unsafe def incorporate : thm := keep "incorporate" fun _ => new_definition
  [[incorporate gcl cl current =
        if tautologous cl \/ EX (\c. c subsumes cl) (CONS gcl current)
        then current else replace cl current]]
#eval incorporate

#eval phrase 39
unsafe def INCORPORATE : thm := keep "INCORPORATE" fun _ => (do
  prove ([[!gcl cl current.
        (!c. MEM c current ==> clause c) /\ clause gcl /\ clause cl
        ==> (!c. MEM c (incorporate gcl cl current) ==> clause c) /\
            set_of_list(incorporate gcl cl current)
                SUBSUMES set_of_list(current) /\
            (tautologous cl \/
             (gcl INSERT set_of_list(incorporate gcl cl current))
                SUBSUMES set_of_list(CONS cl current))]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [incorporate] THEN
    ASM_CASES_TAC [[tautologous cl]] THEN ASM_REWRITE_TAC [SUBSUMES_REFL] THEN
    ASM_CASES_TAC [[EX (\c. c subsumes cl) (CONS gcl current)]] THEN
    ASM_REWRITE_TAC [SUBSUMES_REFL] THENL
     [REWRITE_TAC [set_of_list] THEN ONCE_REWRITE_TAC [SUBSUMES_CLAUSES] THEN
      REWRITE_TAC [(← HolLight.GSYM (← liftExcept (Session.CONJUNCT2 set_of_list)))] THEN CONJ_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC SUBSUMES_SUBSET THEN
        EXISTS_TAC [[set_of_list(current:(form->bool)list)]] THEN
        REWRITE_TAC [SUBSUMES_REFL] THEN
        SIMP_TAC [SUBSET, set_of_list, IN_INSERT]] THEN
      UNDISCH_TAC [[EX (\c. c subsumes cl) (CONS gcl current)]] THEN
      SPEC_TAC ([[CONS (gcl:form->bool) current]], [[l:(form->bool)list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [EX] THEN
      ASM_REWRITE_TAC [set_of_list] THEN STRIP_TAC THEN
      MATCH_MP_TAC SUBSUMES_SUBSET THENL
       [EXISTS_TAC [[{h:form->bool}]],
        EXISTS_TAC [[set_of_list(t:(form->bool)list)]]] THEN
      ASM_SIMP_TAC [SUBSET, IN_INSERT, NOT_IN_EMPTY] THEN
      REWRITE_TAC [SUBSUMES, IN_INSERT, NOT_IN_EMPTY] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    MP_TAC (← HolLight.SPECL [ [[cl:form->bool]], [[current:(form->bool)list]] ] REPLACE) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC [[set_of_list(replace cl current) SUBSUMES
                 set_of_list (CONS cl current)]] THEN
    REWRITE_TAC [SUBSUMES, set_of_list, IN_INSERT, NOT_IN_EMPTY] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval INCORPORATE

#eval phrase 40
unsafe def insert_def : thm := keep "insert_def" fun _ => new_definition
  [[insert x l = if MEM x l then l else CONS x l]]
#eval insert_def

#eval phrase 41
unsafe def step : thm := keep "step" fun _ => new_definition
  [[step (used,unused) =
        if unused = [] then (used,unused) else
        let new = resolvents (HD unused) (CONS (HD unused) used) in
        (insert (HD unused) used,
         ITLIST (incorporate (HD unused)) new (TL unused))]]
#eval step

#eval phrase 42
unsafe def STEP : thm := keep "STEP" fun _ => (do
  prove ([[(step(used,[]) = (used,[])) /\
   (step(used,CONS cl cls) =
        let new = resolvents cl (CONS cl used) in
        insert cl used,ITLIST (incorporate cl) new cls)]])
   (REPEAT STRIP_TAC THEN HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [step] THEN
    REWRITE_TAC [NOT_CONS_NIL, HD, TL])
  : ExceptT String IO thm).run
#eval STEP

#eval phrase 43
unsafe def given : thm := keep "given" fun _ => (do
  newRec num_RECURSION
    [[(given 0 p = p) /\
      (given (SUC n) p = step(given n p))]]
  : ExceptT String IO thm).run
#eval given

#eval phrase 44
unsafe def Used_DEF : thm := keep "Used_DEF" fun _ => new_definition
  [[Used init n = set_of_list(FST(given n init))]]
#eval Used_DEF

#eval phrase 45
unsafe def Unused_DEF : thm := keep "Unused_DEF" fun _ => new_definition
  [[Unused init n = set_of_list(SND(given n init))]]
#eval Unused_DEF

#eval phrase 46
unsafe def Sub_DEF : thm := keep "Sub_DEF" fun _ => (do
  newRec num_RECURSION
    [[(Sub init 0 = {}) /\
      (Sub init (SUC n) = if SND(given n init) = [] then Sub init n
                       else HD(SND(given n init)) INSERT (Sub init n))]]
  : ExceptT String IO thm).run
#eval Sub_DEF

#eval phrase 47
unsafe def TAUTOLOGOUS_INSTANCE : thm := keep "TAUTOLOGOUS_INSTANCE" fun _ => (do
  prove ([[!i cl. tautologous cl ==> tautologous (IMAGE (formsubst i) cl)]])
   (REWRITE_TAC [tautologous, IN_IMAGE] THEN
    MESON_TAC [FORMSUBST_NEGATE])
  : ExceptT String IO thm).run
#eval TAUTOLOGOUS_INSTANCE

#eval phrase 48
unsafe def NONTAUTOLOGOUS_SUBSUMES : thm := keep "NONTAUTOLOGOUS_SUBSUMES" fun _ => (do
  prove ([[cl subsumes cl' /\ ~(tautologous cl') ==> ~(tautologous cl)]])
   (REWRITE_TAC [subsumes, SUBSET, tautologous, IN_IMAGE] THEN
    MESON_TAC [FORMSUBST_NEGATE])
  : ExceptT String IO thm).run
#eval NONTAUTOLOGOUS_SUBSUMES

#eval phrase 49
unsafe def ALLNTRESOLVENTS_STEP : thm := keep "ALLNTRESOLVENTS_STEP" fun _ => (do
  prove ([[(!c. c IN B ==> clause(c)) /\
   (!c. c IN C ==> clause(c))
   ==> ((allntresolvents B (A UNION B)) UNION
        (allntresolvents C (A UNION B UNION C)))
       SUBSUMES (allntresolvents(B UNION C) (A UNION B UNION C))]])
   (STRIP_TAC THEN MP_TAC ALLRESOLVENTS_STEP THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [SUBSUMES, allntresolvents, IN_ELIM_THM, IN_UNION] THEN
    MESON_TAC [NONTAUTOLOGOUS_SUBSUMES])
  : ExceptT String IO thm).run
#eval ALLNTRESOLVENTS_STEP

#eval phrase 50
unsafe def ALLNTRESOLVENTS_UNION : thm := keep "ALLNTRESOLVENTS_UNION" fun _ => (do
  prove ([[(allntresolvents (A UNION B) C =
        (allntresolvents A C) UNION (allntresolvents B C)) /\
   (allntresolvents A (B UNION C) =
        (allntresolvents A B) UNION (allntresolvents A C))]])
   (REWRITE_TAC [EXTENSION, allntresolvents, allresolvents,
                IN_ELIM_THM, IN_UNION] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval ALLNTRESOLVENTS_UNION

#eval phrase 51
unsafe def SET_OF_LIST_INSERT : thm := keep "SET_OF_LIST_INSERT" fun _ => (do
  prove ([[!x s. set_of_list(insert x s) = x INSERT set_of_list(s)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [insert_def] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [set_of_list] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [(← HolLight.GSYM IN_SET_OF_LIST)] THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval SET_OF_LIST_INSERT

#eval phrase 52
unsafe def SET_OF_LIST_FILTER : thm := keep "SET_OF_LIST_FILTER" fun _ => (do
  prove ([[!P l. set_of_list(FILTER P l) = {x | x IN set_of_list l /\ P x}]])
   (GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [FILTER, set_of_list] THENL
     [REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY], ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [set_of_list] THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY, IN_INSERT] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval SET_OF_LIST_FILTER

#eval phrase 53
unsafe def USED_SUB : thm := keep "USED_SUB" fun _ => (do
  prove ([[!used unused n.
        Used(used,unused) n = set_of_list(used) UNION Sub(used,unused) n]])
   (GEN_TAC THEN GEN_TAC THEN
    REWRITE_TAC [Used_DEF, Unused_DEF] THEN INDUCT_TAC THEN
    REWRITE_TAC [Sub_DEF, given, UNION_EMPTY] THEN
    ABBREV_TAC [[ppp = given n (used,unused)]] THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[ppp:(form->bool)list#(form->bool)list]]) PAIR)) THEN
    PURE_REWRITE_TAC [step] THEN ASM_REWRITE_TAC [] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN
    REWRITE_TAC [FST, SET_OF_LIST_INSERT] THEN
    ASM_REWRITE_TAC [] THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval USED_SUB

#eval phrase 54
unsafe def GIVEN_INVARIANT : thm := keep "GIVEN_INVARIANT" fun _ => (do
  let lemma1 ← prove ([[x INSERT s = s UNION {x}]]) (SET_TAC [])
  let lemma2 ← prove
   ([[(x INSERT s) UNION t = (s UNION (t UNION {x})) UNION (t UNION {x})]])
    (SET_TAC [])
  let _lemma3 ← prove
   ([[s UNION t = (s UNION t) UNION t]]) (SET_TAC [])
  let lemma4 ← prove
   ([[s UNION {x} = (x INSERT s) UNION {x}]]) (SET_TAC [])
  let lemma5 ← prove
   ([[(h INSERT s) UNION t = (s UNION t) UNION {h}]]) (SET_TAC [])
  prove ([[!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !n. (!c. c IN Used(used,unused) n ==> clause c) /\
                (!c. c IN Unused(used,unused) n ==> clause c) /\
                (!c. c IN Sub(used,unused) n ==> clause c) /\
                (Sub(used,unused) n UNION Unused(used,unused) n) SUBSUMES
                allntresolvents
                        (Sub(used,unused) n)
                        (set_of_list(used) UNION Sub(used,unused) n)]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
     [REWRITE_TAC [Sub_DEF, UNION_EMPTY] THEN
      ASM_REWRITE_TAC [Unused_DEF, given, Used_DEF, IN_SET_OF_LIST, NOT_IN_EMPTY] THEN
      MATCH_MP_TAC SUBSUMES_TRANS THEN
      EXISTS_TAC [[allresolvents {} (Used (used,unused) 0)]] THEN
      ASM_REWRITE_TAC [Unused_DEF, given, Used_DEF, IN_SET_OF_LIST] THEN CONJ_TAC THENL
       [SUBGOAL_THEN ([[allresolvents {} (set_of_list used) = {}]])
        SUBST1_TAC THENL
         [REWRITE_TAC [allresolvents, EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY],
          REWRITE_TAC [SUBSUMES, NOT_IN_EMPTY]],
        MATCH_MP_TAC SUBSUMES_SUBSET THEN
        EXISTS_TAC [[allntresolvents {} (set_of_list used)]] THEN
        REWRITE_TAC [SUBSUMES_REFL] THEN
        SIMP_TAC [SUBSET, allntresolvents, IN_ELIM_THM]],
      ALL_TAC] THEN
    FIRST_ASSUM (fun th => HolLight.tactic_of do
      let _ ← liftExcept (HolCore.Lib.check (fun t => HolCore.Basics.is_conj t) (concl th))
      pure (UNDISCH_TAC (concl th))) THEN
    REWRITE_TAC [Sub_DEF, Unused_DEF, Used_DEF, given] THEN
    ABBREV_TAC [[ppp = given n (used,unused)]] THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[ppp:(form->bool)list#(form->bool)list]]) PAIR)) THEN
    ABBREV_TAC [[used0 = FST(ppp:(form->bool)list#(form->bool)list)]] THEN
    ABBREV_TAC [[unused0 = SND(ppp:(form->bool)list#(form->bool)list)]] THEN
    REWRITE_TAC [FST, SND] THEN
    ABBREV_TAC [[sub0 = Sub (used,unused) n]] THEN STRIP_TAC THEN
    REWRITE_TAC [step] THEN
    DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC
     (← HolLight.ISPEC ([[unused0:(form->bool)list]]) list_CASES)
    THENL
     [REWRITE_TAC [] THEN ASM_REWRITE_TAC [set_of_list, NOT_IN_EMPTY],
      ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[cl:form->bool]])
          (X_CHOOSE_THEN ([[cls:(form->bool)list]])
                  SUBST_ALL_TAC)) THEN
    REWRITE_TAC [NOT_CONS_NIL, HD, TL] THEN LET_TAC THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN REWRITE_TAC [FST, SND] THEN
    SUBGOAL_THEN ([[clause cl]]) ASSUME_TAC THENL
     [UNDISCH_TAC [[!c. c IN set_of_list (CONS cl cls) ==> clause c]] THEN
      REWRITE_TAC [set_of_list, IN_INSERT] THEN MESON_TAC [], ALL_TAC] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC [insert_def] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [set_of_list, IN_INSERT] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[b /\ a /\ c ==> a /\ b /\ c]])) THEN CONJ_TAC THENL
     [REWRITE_TAC [set_of_list, IN_INSERT] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[!c. MEM c new ==> clause c]]) ASSUME_TAC THENL
     [Fol.EXPAND_TAC "new" THEN REWRITE_TAC [resolvents, set_of_list] THEN
      SUBGOAL_THEN ([[!c. MEM c (list_of_set (allresolvents {cl}
                                  (cl INSERT set_of_list used0))) <=>
                        c IN (allresolvents {cl} (cl INSERT set_of_list used0))]])
       (fun th => REWRITE_TAC [th])
      THENL
       [MATCH_MP_TAC MEM_LIST_OF_SET THEN
        MATCH_MP_TAC ALLRESOLVENTS_FINITE THEN
        SIMP_TAC [FINITE_RULES, FINITE_SET_OF_LIST],
        MATCH_MP_TAC ALLRESOLVENTS_CLAUSE] THEN
      ASM_SIMP_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
      ASM_MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[a /\ (a ==> b) ==> a /\ b]])) THEN CONJ_TAC THENL
     [REWRITE_TAC [IN_SET_OF_LIST] THEN
      UNDISCH_TAC [[!c. MEM c new ==> clause c]] THEN
      SPEC_TAC ([[new:(form->bool)list]], [[more:(form->bool)list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [ITLIST, MEM] THENL
       [UNDISCH_TAC [[!c. c IN set_of_list (CONS cl cls) ==> clause c]] THEN
        REWRITE_TAC [IN_SET_OF_LIST, MEM] THEN MESON_TAC [], ALL_TAC] THEN
      ASM_MESON_TAC [INCORPORATE], ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC SUBSUMES_TRANS THEN
    EXISTS_TAC
     [[allntresolvents sub0 (set_of_list(used) UNION sub0) UNION
      allntresolvents {cl} (set_of_list(used) UNION sub0 UNION {cl})]] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [IN_UNION, IN_INSERT, NOT_IN_EMPTY] THEN ASM_MESON_TAC [],
      ALL_TAC,
      HolLight.GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.ONCE_DEPTH_CONV) [lemma1] THEN
      MATCH_MP_TAC ALLNTRESOLVENTS_STEP THEN
      ASM_SIMP_TAC [IN_INSERT, NOT_IN_EMPTY]] THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [lemma2] THEN
    MATCH_MP_TAC SUBSUMES_UNION THEN CONJ_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM lemma1)] THEN
      MATCH_MP_TAC SUBSUMES_TRANS THEN
      EXISTS_TAC [[sub0 UNION set_of_list(CONS (cl:form->bool) cls)]] THEN
      ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
       [REWRITE_TAC [IN_UNION, IN_INSERT] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      MATCH_MP_TAC SUBSUMES_UNION THEN REWRITE_TAC [SUBSUMES_REFL] THEN
      REWRITE_TAC [set_of_list] THEN ONCE_REWRITE_TAC [lemma1] THEN
      MATCH_MP_TAC SUBSUMES_UNION THEN REWRITE_TAC [SUBSUMES_REFL] THEN
      UNDISCH_TAC [[!c. MEM c new ==> clause c]] THEN
      UNDISCH_TAC [[!c. c IN set_of_list (ITLIST (incorporate cl) new cls)
                       ==> clause c]] THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> a /\ c) ==> a ==> b ==> c]])) THEN
      SPEC_TAC ([[new:(form->bool)list]], [[added:(form->bool)list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [ITLIST, MEM, SUBSUMES_REFL] THENL
       [UNDISCH_TAC [[!c. c IN set_of_list (CONS cl cls) ==> clause c]] THEN
        REWRITE_TAC [set_of_list, IN_INSERT] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      DISCH_TAC THEN
      MP_TAC (← HolLight.SPECL [ [[cl:form->bool]], [[h:form->bool]],
                    [[ITLIST (incorporate cl) t cls]] ]
                   INCORPORATE) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC [(← HolLight.GSYM IN_SET_OF_LIST)], ALL_TAC] THEN
      SIMP_TAC [IN_SET_OF_LIST] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (HolCore.Lib.K ALL_TAC)) THEN
      MATCH_MP_TAC SUBSUMES_TRANS THEN
      EXISTS_TAC [[set_of_list(ITLIST (incorporate cl) t cls)]] THEN
      ASM_SIMP_TAC [] THEN ASM_REWRITE_TAC [IN_SET_OF_LIST], ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM UNION_ASSOC)] THEN
    SUBGOAL_THEN ([[set_of_list(used:(form->bool)list) UNION sub0 =
                  set_of_list(used0)]])
    SUBST1_TAC THENL
     [MAP_EVERY (fun s => Fol.EXPAND_TAC s) ["sub0", "used0", "ppp"] THEN
      REWRITE_TAC [(← HolLight.GSYM Used_DEF)] THEN REWRITE_TAC [USED_SUB], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[allntresolvents {cl} (set_of_list used0 UNION {cl}) =
      set_of_list(FILTER (\c. ~(tautologous c)) new)]])
    SUBST1_TAC THENL
     [REWRITE_TAC [SET_OF_LIST_FILTER] THEN Fol.EXPAND_TAC "new" THEN
      REWRITE_TAC [resolvents] THEN
      SUBGOAL_THEN ([[set_of_list(list_of_set
                          (allresolvents {cl}
                                         (set_of_list(CONS cl used0)))) =
                    allresolvents {cl} (set_of_list(CONS cl used0))]])
      SUBST1_TAC THENL
       [REWRITE_TAC [set_of_list] THEN
        MATCH_MP_TAC SET_OF_LIST_OF_SET THEN
        MATCH_MP_TAC ALLRESOLVENTS_FINITE THEN
        SIMP_TAC [FINITE_RULES, FINITE_SET_OF_LIST] THEN
        ASM_SIMP_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
        ASM_MESON_TAC [], ALL_TAC] THEN
      REWRITE_TAC [EXTENSION, allntresolvents, IN_ELIM_THM, set_of_list] THEN
      REWRITE_TAC [(← HolLight.GSYM lemma1)], ALL_TAC] THEN
    UNDISCH_TAC [[!c. MEM c new ==> clause c]] THEN
    UNDISCH_TAC [[!c. c IN set_of_list (ITLIST (incorporate cl) new cls)
                       ==> clause c]] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[(b ==> a /\ c) ==> a ==> b ==> c]])) THEN
    SPEC_TAC ([[new:(form->bool)list]], [[added:(form->bool)list]]) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [ITLIST, MEM, FILTER] THENL
     [REWRITE_TAC [set_of_list, SUBSUMES, NOT_IN_EMPTY] THEN
      UNDISCH_TAC [[!c. c IN set_of_list (CONS cl cls) ==> clause c]] THEN
      REWRITE_TAC [set_of_list, IN_INSERT] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_TAC THEN ASM_CASES_TAC [[tautologous h]] THEN ASM_SIMP_TAC [] THENL
     [MP_TAC (← HolLight.SPECL [ [[cl:form->bool]], [[h:form->bool]],
                    [[ITLIST (incorporate cl) t cls]] ]
                   INCORPORATE) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC [(← HolLight.GSYM IN_SET_OF_LIST)], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [IN_SET_OF_LIST] THEN
      MATCH_MP_TAC SUBSUMES_TRANS THEN
      EXISTS_TAC [[set_of_list (ITLIST (incorporate cl) t cls) UNION {cl}]] THEN
      ASM_SIMP_TAC [SUBSUMES_UNION, SUBSUMES_REFL] THEN
      REWRITE_TAC [IN_UNION, NOT_IN_EMPTY, IN_INSERT, IN_ELIM_THM,
                  IN_SET_OF_LIST] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    MP_TAC (← HolLight.SPECL [ [[cl:form->bool]], [[h:form->bool]],
                  [[ITLIST (incorporate cl) t cls]] ]
                 INCORPORATE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [(← HolLight.GSYM IN_SET_OF_LIST)], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [IN_SET_OF_LIST] THEN
    MATCH_MP_TAC SUBSUMES_TRANS THEN
    EXISTS_TAC
      [[set_of_list(CONS h (ITLIST (incorporate cl) t cls)) UNION {cl}]] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, IN_UNION] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC [] THEN ASM_MESON_TAC [IN_SET_OF_LIST],
      HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [lemma4] THEN
      ASM_SIMP_TAC [SUBSUMES_UNION, SUBSUMES_REFL],
      REWRITE_TAC [set_of_list] THEN ONCE_REWRITE_TAC [lemma5] THEN
      HolLight.GEN_REWRITE_TAC HolLight.RAND_CONV [lemma1] THEN
      MATCH_MP_TAC SUBSUMES_UNION THEN REWRITE_TAC [SUBSUMES_REFL] THEN
      ASM_SIMP_TAC []])
  : ExceptT String IO thm).run
#eval GIVEN_INVARIANT

#eval phrase 55
unsafe def SUB_MONO_SUBSET : thm := keep "SUB_MONO_SUBSET" fun _ => (do
  prove ([[!init m n. m <= n ==> (Sub init m) SUBSET (Sub init n)]])
   (REPEAT GEN_TAC THEN SIMP_TAC [LE_EXISTS, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC [[d:num]] THEN DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN
    SPEC_TAC ([[d:num]], [[d:num]]) THEN INDUCT_TAC THEN
    REWRITE_TAC [ADD_CLAUSES, SUBSET_REFL] THEN
    REWRITE_TAC [Sub_DEF] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [SUBSET_TRANS, SUBSET, IN_INSERT])
  : ExceptT String IO thm).run
#eval SUB_MONO_SUBSET

#eval phrase 56
unsafe def SUB_MONO : thm := keep "SUB_MONO" fun _ => (do
  prove ([[!init m n. m <= n ==> (Sub init n) SUBSUMES (Sub init m)]])
   (MESON_TAC [SUBSUMES_SUBSET_REFL, SUB_MONO_SUBSET])
  : ExceptT String IO thm).run
#eval SUB_MONO

#eval phrase 57
unsafe def LENGTH_REPLACE : thm := keep "LENGTH_REPLACE" fun _ => (do
  prove ([[!cl current. LENGTH current <= LENGTH(replace cl current)]])
   (GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [replace] THEN
    REWRITE_TAC [LENGTH, LE_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [LENGTH, LE_SUC, LE_REFL])
  : ExceptT String IO thm).run
#eval LENGTH_REPLACE

#eval phrase 58
unsafe def LENGTH_INCORPORATE : thm := keep "LENGTH_INCORPORATE" fun _ => (do
  prove ([[!gcl cl current. LENGTH current <= LENGTH(incorporate gcl cl current)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [incorporate] THEN
    COND_CASES_TAC THEN REWRITE_TAC [LE_REFL, LENGTH_REPLACE])
  : ExceptT String IO thm).run
#eval LENGTH_INCORPORATE

#eval phrase 59
unsafe def LENGTH_UNUSED_CHANGE : thm := keep "LENGTH_UNUSED_CHANGE" fun _ => (do
  prove ([[!init m n.
        LENGTH(SND(given m init)) <= LENGTH (SND(given (m + n) init)) + n]])
   (HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[used:(form->bool)list]], [[unused:(form->bool)list]] ] THEN
    GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, LE_REFL] THEN
    REWRITE_TAC [given] THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[given (m + n) (used,unused)]]) PAIR)) THEN
    PURE_REWRITE_TAC [step] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN
    COND_CASES_TAC THEN REWRITE_TAC [SND] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (ARITH_RULE [[m <= n ==> m <= SUC n]]))] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC [[LENGTH (SND (given (m + n) (used,unused))) + n]] THEN
    ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC [[~(SND (given (m + n) (used,unused)) = [])]] THEN
    SPEC_TAC ([[SND (given (m + n) (used,unused))]], [[l:(form->bool)list]]) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [NOT_CONS_NIL, TL, LENGTH] THEN
    MATCH_MP_TAC (← ExceptT.mk (ARITH_RULE [[x <= y ==> SUC x + n <= SUC(y + n)]])) THEN
    SPEC_TAC ([[(resolvents (HD (CONS h t))
                (CONS (HD (CONS h t)) (FST (given (m + n) (used,unused)))))]],
             [[k:(form->bool)list]]) THEN
    REWRITE_TAC [HD] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [ITLIST, LE_REFL] THEN
    ASM_MESON_TAC [LENGTH_INCORPORATE, LE_TRANS])
  : ExceptT String IO thm).run
#eval LENGTH_UNUSED_CHANGE

#eval phrase 60
unsafe def LENGTH_UNUSED_ZERO : thm := keep "LENGTH_UNUSED_ZERO" fun _ => (do
  prove ([[!used unused m n.
        (SND (given m (used,unused)) = [])
        ==> (SND (given (m + n) (used,unused)) = [])]])
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    INDUCT_TAC THEN SIMP_TAC [ADD_CLAUSES] THEN
    REWRITE_TAC [given] THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[given (m + n) (used,unused)]]) PAIR)) THEN
    PURE_REWRITE_TAC [step] THEN ASM_SIMP_TAC [])
  : ExceptT String IO thm).run
#eval LENGTH_UNUSED_ZERO

#eval phrase 61
unsafe def REPLACE_SUBSUMES_SELF : thm := keep "REPLACE_SUBSUMES_SELF" fun _ => (do
  prove ([[!cl current n.
        n < LENGTH current
        ==> (EL n (replace cl current)) subsumes (EL n current)]])
   (GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [replace, LENGTH, (← liftExcept (Session.CONJUNCT1 LT))] THEN
    INDUCT_TAC THEN REWRITE_TAC [EL] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [HD, TL, EL, subsumes_REFL, LT_SUC])
  : ExceptT String IO thm).run
#eval REPLACE_SUBSUMES_SELF

#eval phrase 62
unsafe def INCORPORATE_SUBSUMES_SELF : thm := keep "INCORPORATE_SUBSUMES_SELF" fun _ => (do
  prove ([[!gcl cl current n.
        n < LENGTH current
        ==> (EL n (incorporate gcl cl current)) subsumes (EL n current)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [incorporate] THEN
    COND_CASES_TAC THEN REWRITE_TAC [subsumes_REFL, REPLACE_SUBSUMES_SELF])
  : ExceptT String IO thm).run
#eval INCORPORATE_SUBSUMES_SELF

#eval phrase 63
unsafe def REPLACE_CLAUSE : thm := keep "REPLACE_CLAUSE" fun _ => (do
  prove ([[!cl current.
        (!c. MEM c current ==> clause c) /\ clause cl
        ==> !c. MEM c (replace cl current) ==> clause c]])
   (GEN_TAC THEN LIST_INDUCT_TAC THEN SIMP_TAC [replace, MEM] THEN
    STRIP_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC [MEM] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval REPLACE_CLAUSE

#eval phrase 64
unsafe def INCORPORATE_CLAUSE : thm := keep "INCORPORATE_CLAUSE" fun _ => (do
  prove ([[(!c. MEM c current ==> clause c) /\ clause cl
   ==> !c. MEM c (incorporate gcl cl current) ==> clause c]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC [incorporate] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [REPLACE_CLAUSE])
  : ExceptT String IO thm).run
#eval INCORPORATE_CLAUSE

#eval phrase 65
unsafe def INCORPORATE_CLAUSE_EL : thm := keep "INCORPORATE_CLAUSE_EL" fun _ => (do
  prove ([[(!c. MEM c current ==> clause c) /\ clause cl /\ p < LENGTH current
   ==> clause (EL p (incorporate gcl cl current))]])
   (MESON_TAC [MEM_EL, INCORPORATE_CLAUSE, LENGTH_INCORPORATE,
              LTE_TRANS])
  : ExceptT String IO thm).run
#eval INCORPORATE_CLAUSE_EL

#eval phrase 66
unsafe def UNUSED_SUBSUMES_SELF : thm := keep "UNUSED_SUBSUMES_SELF" fun _ => (do
  prove ([[!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !k m n. n + k < LENGTH(SND(given m (used,unused)))
                    ==> (EL n (SND(given (m + k) (used,unused))))
                    subsumes (EL (n + k) (SND(given m (used,unused))))]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [ADD_CLAUSES, subsumes_REFL] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [ [[SUC m]], [[n:num]] ]) THEN
    REWRITE_TAC [ADD_CLAUSES] THEN ANTS_TAC THENL
     [MP_TAC (← HolLight.SPECL [ [[(used:(form->bool)list,unused:(form->bool)list)]],
                    [[m:num]], [[1]] ] LENGTH_UNUSED_CHANGE) THEN
      REWRITE_TAC [ADD1] THEN
      MATCH_MP_TAC (← ExceptT.mk (ARITH_RULE
       [[SUC x < lm ==> lm <= lm1 + 1 ==> x < lm1]])) THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC (← HolLight.ONCE_REWRITE_RULE [(← ExceptT.mk (TAUT
     [[a /\ b /\ c ==> d <=> a /\ c ==> b ==> d]]))] subsumes_TRANS) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN ([[(EL n (SND (given (SUC (m + k)) (used,unused)))) IN
                    Unused(used,unused) (SUC(m + k))]])
       (fun th => ASM_MESON_TAC [th, GIVEN_INVARIANT]) THEN
      REWRITE_TAC [Unused_DEF, IN_SET_OF_LIST] THEN
      MATCH_MP_TAC MEM_EL THEN
      MP_TAC (← HolLight.SPECL [ [[(used:(form->bool)list,unused:(form->bool)list)]],
                    [[m:num]], [[SUC k]] ] LENGTH_UNUSED_CHANGE) THEN
      UNDISCH_TAC [[SUC (n + k) < LENGTH (SND (given m (used,unused)))]] THEN
      REWRITE_TAC [ADD_CLAUSES] THEN ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [given] THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[given m (used,unused)]]) PAIR)) THEN
    PURE_REWRITE_TAC [step] THEN LET_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC [SND] THENL
     [UNDISCH_TAC [[SUC (n + k) < LENGTH (SND (given m (used,unused)))]] THEN
      ASM_REWRITE_TAC [LENGTH, LT], ALL_TAC] THEN
    UNDISCH_TAC [[SUC (n + k) < LENGTH (SND (given m (used,unused)))]] THEN
    SUBGOAL_THEN ([[!c. MEM c (SND (given m (used,unused))) ==> clause c]])
    MP_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM IN_SET_OF_LIST), (← HolLight.GSYM Unused_DEF)] THEN
      ASM_MESON_TAC [GIVEN_INVARIANT], ALL_TAC] THEN
    SUBGOAL_THEN ([[!c. MEM c new ==> clause c]]) MP_TAC THENL
     [Fol.EXPAND_TAC "new" THEN REWRITE_TAC [resolvents, set_of_list] THEN
      ABBREV_TAC [[gcl = HD (SND (given m (used,unused)))]] THEN
      REWRITE_TAC [(← HolLight.GSYM Used_DEF)] THEN
      SUBGOAL_THEN ([[!c. MEM c (list_of_set (allresolvents {gcl}
                            (gcl INSERT Used (used,unused) m))) <=>
                        c IN (allresolvents {gcl}
                             (gcl INSERT Used (used,unused) m))]])
       (fun th => REWRITE_TAC [th])
      THENL
       [MATCH_MP_TAC MEM_LIST_OF_SET THEN
        MATCH_MP_TAC ALLRESOLVENTS_FINITE THEN
        SIMP_TAC [FINITE_RULES, FINITE_SET_OF_LIST] THEN
        ASM_SIMP_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
        REWRITE_TAC [FINITE_INSERT] THEN
        REWRITE_TAC [Used_DEF, FINITE_SET_OF_LIST] THEN
        REWRITE_TAC [(← HolLight.GSYM Used_DEF)],
        MATCH_MP_TAC ALLRESOLVENTS_CLAUSE THEN
        ASM_SIMP_TAC [IN_INSERT, NOT_IN_EMPTY]] THEN
      SUBGOAL_THEN ([[clause gcl]])
        (fun th => ASM_MESON_TAC [th, GIVEN_INVARIANT]) THEN
      SUBGOAL_THEN ([[gcl IN Unused(used,unused) m]])
        (fun th => ASM_MESON_TAC [th, GIVEN_INVARIANT]) THEN
      REWRITE_TAC [Unused_DEF, IN_SET_OF_LIST] THEN
      Fol.EXPAND_TAC "gcl" THEN
      UNDISCH_TAC [[~(SND(given m (used,unused)) = [])]] THEN
      SPEC_TAC ([[SND(given m (used,unused))]], [[l:(form->bool)list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [MEM, HD], ALL_TAC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC [[~(SND (given m (used,unused)) = [])]] THEN
    SPEC_TAC ([[SND(given m (used,unused))]], [[l:(form->bool)list]]) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [NOT_CONS_NIL, EL, HD, TL] THEN
    REWRITE_TAC [LENGTH, LT_SUC] THEN
    UNDISCH_TAC [[!c. MEM c new ==> clause c]] THEN
    SPEC_TAC ([[n + k:num]], [[p:num]]) THEN
    SPEC_TAC ([[new:(form->bool)list]], [[new:(form->bool)list]]) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC [ITLIST, subsumes_REFL] THEN
    X_GEN_TAC [[p:num]] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[p:num]]) THEN
    ASM_REWRITE_TAC [] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [MEM], ALL_TAC] THEN
    MATCH_MP_TAC (← HolLight.ONCE_REWRITE_RULE [(← ExceptT.mk (TAUT
     [[a /\ b /\ c ==> d <=> a /\ b ==> c ==> d]]))] subsumes_TRANS) THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC INCORPORATE_SUBSUMES_SELF THEN
      UNDISCH_TAC [[p < LENGTH(t:(form->bool)list)]] THEN
      SPEC_TAC ([[t':(form->bool)list]], [[k:(form->bool)list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [ITLIST] THEN
      ASM_MESON_TAC [LENGTH_INCORPORATE, LTE_TRANS]] THEN
    MATCH_MP_TAC INCORPORATE_CLAUSE_EL THEN
    CONJ_TAC THENL
     [ALL_TAC,
      CONJ_TAC THENL [ASM_MESON_TAC [MEM], ALL_TAC] THEN
      SUBGOAL_THEN
       ([[!gcl current lis.
          LENGTH(current) <= LENGTH(ITLIST (incorporate gcl) lis current)]])
       (fun th => ASM_MESON_TAC [LTE_TRANS, th]) THEN
      GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
      REWRITE_TAC [ITLIST, LE_REFL] THEN
      ASM_MESON_TAC [LE_TRANS, LENGTH_INCORPORATE]] THEN
    SUBGOAL_THEN
     ([[!current gcl new.
          (!c. MEM c current ==> clause c) /\
          (!c. MEM c new ==> clause c)
          ==> !c. MEM c (ITLIST (incorporate gcl) new current)
                  ==> clause c]])
    MATCH_MP_TAC THENL [ALL_TAC, ASM_MESON_TAC [MEM]] THEN
    POP_ASSUM_LIST (HolCore.Lib.K ALL_TAC) THEN
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [ITLIST, MEM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [INCORPORATE_CLAUSE])
  : ExceptT String IO thm).run
#eval UNUSED_SUBSUMES_SELF

#eval phrase 67
unsafe def SUB_SUBSUMES_UNUSED : thm := keep "SUB_SUBSUMES_UNUSED" fun _ => (do
  let lemma ← prove ([[x INSERT s = {x} UNION s]]) (SET_TAC [])
  let ar1 ← ExceptT.mk (ARITH_RULE [[x <= n ==> x <= SUC n]])
  prove ([[(!c. MEM c used ==> clause c) /\
   (!c. MEM c unused ==> clause c)
   ==> !n. Sub(used,unused)
              (n + LENGTH(SND(given n (used,unused))))
           SUBSUMES (Sub (used,unused) n UNION Unused(used,unused) n)]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     ([[!m n. Sub(used,unused) (m + n) SUBSUMES
          Sub(used,unused) m UNION
          set_of_list(FIRSTN n (SND(given m (used,unused))))]])
    MP_TAC THENL
     [ALL_TAC, ASM_MESON_TAC [LE_REFL, FIRSTN_TRIVIAL, Unused_DEF]] THEN
    GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES] THENL
     [REWRITE_TAC [FIRSTN, set_of_list, UNION_EMPTY, SUBSUMES_REFL], ALL_TAC] THEN
    REWRITE_TAC [Sub_DEF] THEN COND_CASES_TAC THENL
     [SUBGOAL_THEN ([[FIRSTN (SUC n) (SND(given m (used,unused))) =
                    FIRSTN n (SND(given m (used,unused)))]])
       (fun th => ASM_REWRITE_TAC [th]) THEN
      SUBGOAL_THEN ([[LENGTH(SND (given m (used,unused))) <= n]])
       (fun th => MESON_TAC [th, FIRSTN_TRIVIAL, LE_REFL,
                            ar1]) THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC [[LENGTH(SND (given (m + n) (used,unused))) + n]] THEN
      ASM_REWRITE_TAC [LENGTH_UNUSED_CHANGE, LENGTH, ADD_CLAUSES, LE_REFL],
      ALL_TAC] THEN
    REWRITE_TAC [FIRSTN] THEN COND_CASES_TAC THENL
     [ASM_MESON_TAC [LENGTH_UNUSED_ZERO], ALL_TAC] THEN
    MATCH_MP_TAC SUBSUMES_TRANS THEN
    EXISTS_TAC
     [[HD(SND (given (m + n) (used,unused))) INSERT
      (Sub (used,unused) m UNION
       set_of_list (FIRSTN n (SND (given m (used,unused)))))]] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [IN_INSERT] THEN
      SUBGOAL_THEN
       ([[HD(SND(given (m + n) (used,unused))) IN Unused (used,unused) (m + n)]])
      MP_TAC THENL
       [ALL_TAC, ASM_MESON_TAC [GIVEN_INVARIANT]] THEN
      UNDISCH_TAC [[~(SND(given (m + n) (used,unused)) = [])]] THEN
      REWRITE_TAC [Unused_DEF, IN_SET_OF_LIST] THEN
      SPEC_TAC ([[SND(given(m + n) (used,unused))]], [[l:(form->bool)list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [MEM, HD], ALL_TAC] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC [lemma] THEN MATCH_MP_TAC SUBSUMES_UNION THEN
      ASM_REWRITE_TAC [SUBSUMES_REFL], ALL_TAC] THEN
    REWRITE_TAC [set_of_list] THEN ONCE_REWRITE_TAC [lemma] THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [(← ExceptT.mk (Session.AC UNION_ACI
     [[s UNION t UNION u = t UNION u UNION s]]))] THEN
    MATCH_MP_TAC SUBSUMES_UNION THEN ASM_REWRITE_TAC [SUBSUMES_REFL] THEN
    SUBGOAL_THEN
     ([[{(HD (SND (given m (used,unused))))} UNION
      set_of_list(FIRSTN n (TL (SND (given m (used,unused))))) =
      set_of_list(FIRSTN (SUC n) (SND (given m (used,unused))))]])
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC [FIRSTN] THEN
      UNDISCH_TAC [[~(SND (given m (used,unused)) = [])]] THEN
      REWRITE_TAC [set_of_list] THEN SET_TAC [], ALL_TAC] THEN
    ASM_CASES_TAC
     [[LENGTH(SND (given m (used,unused))) <= n]]
    THENL
     [ASM_SIMP_TAC [FIRSTN_SHORT] THEN
      MATCH_MP_TAC SUBSUMES_SUBSET THEN
      EXISTS_TAC [[set_of_list(FIRSTN n (SND (given m (used,unused))))]] THEN
      REWRITE_TAC [SUBSUMES_REFL] THEN SIMP_TAC [SUBSET, IN_UNION], ALL_TAC] THEN
    MATCH_MP_TAC SUBSUMES_TRANS THEN
    EXISTS_TAC
     [[set_of_list(FIRSTN n (SND (given m (used,unused)))) UNION
      {(EL n (SND (given m (used,unused))))}]] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [IN_UNION, IN_INSERT, NOT_IN_EMPTY] THEN
      REWRITE_TAC [(← HolLight.GSYM Unused_DEF)] THEN
      REWRITE_TAC [IN_SET_OF_LIST] THEN
      X_GEN_TAC [[c:form->bool]] THEN DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
       [DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP FIRSTN_SUBLIST) THEN
        REWRITE_TAC [(← HolLight.GSYM IN_SET_OF_LIST), (← HolLight.GSYM Unused_DEF)] THEN
        ASM_MESON_TAC [GIVEN_INVARIANT], ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN
       ([[(HD(SND (given (m + n) (used,unused)))) IN
        Unused(used,unused) (m + n)]])
       (fun th => ASM_MESON_TAC [th, GIVEN_INVARIANT]) THEN
      REWRITE_TAC [Unused_DEF, IN_SET_OF_LIST] THEN
      UNDISCH_TAC [[~(SND (given (m + n) (used,unused)) = [])]] THEN
      SPEC_TAC ([[SND (given (m + n) (used,unused))]], [[l:(form->bool)list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [MEM, HD], ALL_TAC] THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC SUBSUMES_SUBSET THEN
      EXISTS_TAC [[set_of_list (FIRSTN (SUC n) (SND (given m (used,unused))))]] THEN
      REWRITE_TAC [SUBSUMES_REFL] THEN
      MP_TAC (← HolLight.GEN ([[x:form->bool]])
       (← HolLight.ISPECL [ [[x:form->bool]], [[n:num]], [[SND (given m (used,unused))]] ]
              FIRSTN_SUC)) THEN
      REWRITE_TAC [(← HolLight.GSYM IN_SET_OF_LIST), SET_OF_LIST_APPEND, set_of_list] THEN
      REWRITE_TAC [SUBSET, IN_UNION, IN_INSERT, NOT_IN_EMPTY]] THEN
    MATCH_MP_TAC SUBSUMES_UNION THEN REWRITE_TAC [SUBSUMES_REFL] THEN
    REWRITE_TAC [SUBSUMES, IN_INSERT, NOT_IN_EMPTY] THEN
    SUBGOAL_THEN
     ([[HD(SND(given (m + n) (used,unused))) subsumes
      (EL n (SND (given m (used,unused))))]])
     (fun th => MESON_TAC [th]) THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM (← liftExcept (Session.CONJUNCT1 EL)))] THEN
    HolLight.GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.LAND_CONV) [(← ExceptT.mk (ARITH_RULE [[n = 0 + n]]))] THEN
    MP_TAC (← HolLight.SPECL [ [[used:(form->bool)list]], [[unused:(form->bool)list]] ]
          UNUSED_SUBSUMES_SELF) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC [[~(LENGTH (SND (given m (used,unused))) <= n)]] THEN
    ARITH_TAC)
  : ExceptT String IO thm).run
#eval SUB_SUBSUMES_UNUSED

#eval phrase 68
unsafe def «break» : thm := keep "break" fun _ => (do
  newRec num_RECURSION
    [[(break init 0 = LENGTH(SND(given 0 init))) /\
      (break init (SUC n) =
           break init n + LENGTH(SND(given (break init n) init)))]]
  : ExceptT String IO thm).run
#eval «break»

#eval phrase 69
unsafe def level : thm := keep "level" fun _ => new_definition
  [[level init n = Sub init (break init n)]]
#eval level

#eval phrase 70
unsafe def LEVEL_0 : thm := keep "LEVEL_0" fun _ => (do
  prove ([[!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> level(used,unused) 0 SUBSUMES set_of_list(unused)]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC oTIO HolLight.MATCH_MP SUB_SUBSUMES_UNUSED) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[0]]) THEN
    REWRITE_TAC [ADD_CLAUSES, Sub_DEF, UNION_EMPTY] THEN
    REWRITE_TAC [Unused_DEF, given, level, Sub_DEF, «break»])
  : ExceptT String IO thm).run
#eval LEVEL_0

#eval phrase 71
unsafe def LEVEL_STEP : thm := keep "LEVEL_STEP" fun _ => (do
  prove ([[!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !n. level(used,unused) (SUC n) SUBSUMES
                allntresolvents (level(used,unused) (n))
                                (set_of_list(used) UNION
                                 level(used,unused) (n))]])
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUBSUMES_TRANS THEN
    EXISTS_TAC [[Sub(used,unused) (break(used,unused) n) UNION
              Unused(used,unused) (break(used,unused) n)]] THEN
    REWRITE_TAC [level] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [GIVEN_INVARIANT],
      ALL_TAC,
      ASM_MESON_TAC [GIVEN_INVARIANT]] THEN
    REWRITE_TAC [«break»] THEN
    ASM_SIMP_TAC [SUB_SUBSUMES_UNUSED])
  : ExceptT String IO thm).run
#eval LEVEL_STEP

#eval phrase 72
unsafe def level_CLAUSE : thm := keep "level_CLAUSE" fun _ => (do
  prove ([[!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !n c. c IN (level(used,unused) n) ==> clause c]])
   (REWRITE_TAC [level] THEN MESON_TAC [GIVEN_INVARIANT])
  : ExceptT String IO thm).run
#eval level_CLAUSE

#eval phrase 73
unsafe def BREAK_MONO : thm := keep "BREAK_MONO" fun _ => (do
  prove ([[!init m n. m <= n ==> break init m <= break init n]])
   (SUBGOAL_THEN ([[!init m d. break init m <= break init (m + d)]])
     (fun th => MESON_TAC [th, LE_EXISTS]) THEN
    GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [ADD_CLAUSES, «break», LE_REFL] THEN
    ASM_MESON_TAC [LE_TRANS, LE_ADD])
  : ExceptT String IO thm).run
#eval BREAK_MONO

#eval phrase 74
unsafe def level_MONO_SUBSET : thm := keep "level_MONO_SUBSET" fun _ => (do
  prove ([[!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !m n. m <= n
                  ==> level(used,unused) m SUBSET level(used,unused) n]])
   (REWRITE_TAC [level] THEN MESON_TAC [SUB_MONO_SUBSET, BREAK_MONO])
  : ExceptT String IO thm).run
#eval level_MONO_SUBSET

#eval phrase 75
unsafe def level_MONO : thm := keep "level_MONO" fun _ => (do
  prove ([[!used unused.
        (!c. MEM c used ==> clause c) /\
        (!c. MEM c unused ==> clause c)
        ==> !m n. m <= n
                  ==> level(used,unused) n SUBSUMES level(used,unused) m]])
   (REWRITE_TAC [level] THEN MESON_TAC [SUB_MONO, BREAK_MONO])
  : ExceptT String IO thm).run
#eval level_MONO

#eval phrase 76
unsafe def IMAGE_CLAUSE_EQ : thm := keep "IMAGE_CLAUSE_EQ" fun _ => (do
  prove ([[clause p /\ (!q. qfree(q) ==> (f q = g q))
   ==> (IMAGE f p = IMAGE g p)]])
   (REWRITE_TAC [clause, EXTENSION, IN_IMAGE] THEN
    MESON_TAC [QFREE_LITERAL])
  : ExceptT String IO thm).run
#eval IMAGE_CLAUSE_EQ

#eval phrase 77
unsafe def FORMSUBST_TERMSUBST_EQ : thm := keep "FORMSUBST_TERMSUBST_EQ" fun _ => (do
  prove ([[(!p. qfree(p) ==> (formsubst i p = formsubst j p)) <=>
   (termsubst i = termsubst j)]])
   (REWRITE_TAC [FUN_EQ_THM, o_THM] THEN EQ_TAC THEN DISCH_TAC THENL
     [X_GEN_TAC [[t:term]] THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[Atom p [t] ]]) THEN
      REWRITE_TAC [qfree, formsubst, MAP, form_INJ, CONS_11],
      MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC [qfree] THEN
      SIMP_TAC [formsubst] THEN REWRITE_TAC [form_INJ, (← HolLight.GSYM MAP_o)] THEN
      GEN_TAC THEN MATCH_MP_TAC MAP_EQ THEN ASM_REWRITE_TAC [o_THM, ALL_T]])
  : ExceptT String IO thm).run
#eval FORMSUBST_TERMSUBST_EQ

#eval phrase 78
unsafe def ISARESOLVENT_SUBSUME_L : thm := keep "ISARESOLVENT_SUBSUME_L" fun _ => (do
  let lemma ← prove
   ([[a SUBSET a' /\ b SUBSET b' ==> (a UNION b) SUBSET (a' UNION b')]])
    (SET_TAC [])
  prove ([[!p p' q r.
        clause p /\ clause p' /\ clause q /\
        p' subsumes p /\ isaresolvent r (p,q)
        ==> p' subsumes r \/ ?r'. isaresolvent r' (p',q) /\ r' subsumes r]])
   (REPEAT STRIP_TAC THEN
    UNDISCH_TAC [[isaresolvent r (p,q)]] THEN
    HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [isaresolvent] THEN
    ABBREV_TAC [[q' = IMAGE (formsubst (rename q (FVS p))) q]] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[p1:form->bool]], [[q1':form->bool]] ] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    LET_TAC THEN DISCH_THEN (ASSUME_TAC oTIO HolLight.SYM) THEN
    ABBREV_TAC [[ri = rename q (FVS p)]] THEN
    UNDISCH_TAC [[p' subsumes p]] THEN REWRITE_TAC [subsumes] THEN
    DISCH_THEN (X_CHOOSE_TAC ([[j:num->term]])) THEN
    ASM_CASES_TAC [[(IMAGE (formsubst j) p') INTER p1 = {}]] THENL
     [DISJ1_TAC THEN EXISTS_TAC [[termsubst i o (j:num->term)]] THEN
      SUBGOAL_THEN
       ([[IMAGE (formsubst (termsubst i o j)) p' =
        IMAGE (formsubst i o formsubst j) p']])
      SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_IMAGE, o_THM] THEN
        ASM_MESON_TAC [FORMSUBST_FORMSUBST, clause, QFREE_LITERAL], ALL_TAC] THEN
      REWRITE_TAC [IMAGE_o] THEN
      Fol.EXPAND_TAC "r" THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC [[(p:form->bool) DIFF p1]] THEN
      CONJ_TAC THENL [ALL_TAC, SET_TAC []] THEN
      UNDISCH_TAC [[IMAGE (formsubst j) p' SUBSET p]] THEN
      UNDISCH_TAC [[IMAGE (formsubst j) p' INTER p1 = {}]] THEN
      REWRITE_TAC [SUBSET, EXTENSION, IN_DIFF, IN_INTER, NOT_IN_EMPTY] THEN
      MESON_TAC [], ALL_TAC] THEN
    DISJ2_TAC THEN
    ABBREV_TAC [[p1' = {x | x IN p' /\ (formsubst j x IN p1)}]] THEN
    SUBGOAL_THEN ([[(IMAGE (formsubst j) p1') SUBSET p1 /\ ~(p1' = {})]])
    STRIP_ASSUME_TAC THENL
     [Fol.EXPAND_TAC "p1'" THEN
      UNDISCH_TAC [[~(p1:form->bool = {})]] THEN
      UNDISCH_TAC [[IMAGE (formsubst j) p' SUBSET p]] THEN
      UNDISCH_TAC [[~(IMAGE (formsubst j) p' INTER p1 = {})]] THEN
      REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM, SUBSET,
                  IN_INTER, NOT_IN_EMPTY] THEN
      MESON_TAC [], ALL_TAC] THEN
    ABBREV_TAC [[si = rename q (FVS p')]] THEN
    ABBREV_TAC [[q'' = IMAGE (formsubst si) q]] THEN
    MP_TAC (← HolLight.SPECL [ [[q:form->bool]], [[FVS(p)]] ] rename) THEN
    ASM_SIMP_TAC [FVS_CLAUSE_FINITE] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC [«renaming»] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[ri':num->term]]) MP_TAC) THEN
    REWRITE_TAC [FUN_EQ_THM, I_DEF, o_THM] THEN STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [ [[q:form->bool]], [[FVS(p')]] ] rename) THEN
    ASM_SIMP_TAC [FVS_CLAUSE_FINITE] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC [«renaming»] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[si':num->term]]) MP_TAC) THEN
    REWRITE_TAC [FUN_EQ_THM, I_DEF, o_THM] THEN STRIP_TAC THEN
    ABBREV_TAC [[q1'' = IMAGE (formsubst si o formsubst ri') q1']] THEN
    SUBGOAL_THEN ([[(q1'':form->bool) SUBSET q'']]) ASSUME_TAC THENL
     [MAP_EVERY (fun s => Fol.EXPAND_TAC s) ["q''", "q1''"] THEN
      UNDISCH_TAC [[q1':form->bool SUBSET q']] THEN Fol.EXPAND_TAC "q'" THEN
      DISCH_THEN (MP_TAC o HolLight.ISPEC [[formsubst si o formsubst ri']] oTIO
                 HolLight.MATCH_MP IMAGE_SUBSET) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC [(← HolLight.GSYM IMAGE_o)] THEN
      MATCH_MP_TAC IMAGE_CLAUSE_EQ THEN ASM_REWRITE_TAC [] THEN
      SIMP_TAC [o_THM, FORMSUBST_FORMSUBST] THEN
      REWRITE_TAC [FORMSUBST_TERMSUBST_EQ] THEN
      REWRITE_TAC [FUN_EQ_THM, (← HolLight.GSYM TERMSUBST_TERMSUBST)] THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
    ABBREV_TAC [[i' = \x. if x IN FVS(q'')
                       then termsubst i (termsubst ri (si' x))
                       else termsubst i (j x)]] THEN
    SUBGOAL_THEN ([[Unifies i' (p1' UNION {~~p | p IN q1''})]]) ASSUME_TAC THENL
     [UNDISCH_THEN
       ([[(\x. if x IN FVS q''
              then termsubst i (termsubst ri (si' x))
              else termsubst i (j x)) =
         i']]) (SUBST_ALL_TAC oTIO HolLight.SYM) THEN
      MP_TAC (← HolLight.SPEC ([[p1 UNION {~~ p | p IN q1'}]]) MGU) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [FINITE_UNION] THEN
        SUBGOAL_THEN ([[{~~p | p IN q1'} = IMAGE (~~) q1']]) SUBST1_TAC THENL
         [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN MESON_TAC [],
          ALL_TAC] THEN
        CONJ_TAC THENL
         [ASM_MESON_TAC [FINITE_SUBSET, clause, IMAGE_FORMSUBST_CLAUSE,
                        FINITE_IMAGE],
          REWRITE_TAC [IN_UNION, IN_IMAGE] THEN
          REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [QFREE_NEGATE] THEN
          ASM_MESON_TAC [clause, SUBSET, QFREE_LITERAL,
                        IMAGE_FORMSUBST_CLAUSE]],
        ALL_TAC] THEN
      DISCH_THEN (MP_TAC o Session.CONJUNCT1) THEN ASM_REWRITE_TAC [UNIFIES] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC [[P:form]] THEN
      REWRITE_TAC [IN_UNION] THEN
      REWRITE_TAC [(← ExceptT.mk (TAUT [[(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)]]))] THEN
      REWRITE_TAC [FORALL_AND_THM] THEN
      MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a ==> a') /\ (b ==> b') ==> a /\ b ==> a' /\ b']])) THEN
      CONJ_TAC THEN DISCH_TAC THENL
       [X_GEN_TAC [[x:form]] THEN Fol.EXPAND_TAC "p1'" THEN
        REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC [[formsubst (termsubst i o j) x]] THEN CONJ_TAC THENL
         [ALL_TAC,
          SUBGOAL_THEN ([[qfree x]]) MP_TAC THENL
           [ASM_MESON_TAC [clause, QFREE_LITERAL], ALL_TAC] THEN
          SIMP_TAC [(← HolLight.GSYM FORMSUBST_FORMSUBST)] THEN ASM_SIMP_TAC []] THEN
        MATCH_MP_TAC FORMSUBST_VALUATION THEN
        X_GEN_TAC [[z:num]] THEN DISCH_TAC THEN REWRITE_TAC [] THEN
        SUBGOAL_THEN ([[~(z IN FVS q'')]])
          (fun th => REWRITE_TAC [th, o_THM]) THEN
        UNDISCH_TAC [[FVS q'' INTER FVS p' = {}]] THEN
        REWRITE_TAC [EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC [[z:num]]) THEN
        MATCH_MP_TAC (← ExceptT.mk (TAUT [[b ==> ~(a /\ b) ==> ~a]])) THEN
        REWRITE_TAC [FVS, IN_UNIONS, IN_ELIM_THM] THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      X_GEN_TAC [[x:form]] THEN REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC [[y:form]] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC SUBST_ALL_TAC) THEN
      Fol.EXPAND_TAC "q1''" THEN REWRITE_TAC [IN_IMAGE, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC [[u:form]] THEN
      DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN DISCH_TAC THEN
      REWRITE_TAC [FORMSUBST_NEGATE] THEN
      SUBGOAL_THEN ([[formsubst i (~~u) = P]]) (SUBST1_TAC oTIO HolLight.SYM) THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN
        ASM_MESON_TAC [], ALL_TAC] THEN
      REWRITE_TAC [FORMSUBST_NEGATE] THEN AP_TERM_TAC THEN
      REWRITE_TAC [o_THM] THEN
      SUBGOAL_THEN ([[qfree u]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [SUBSET, clause, IMAGE_FORMSUBST_CLAUSE, QFREE_LITERAL],
        ALL_TAC] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC [[formsubst (termsubst i o termsubst ri o si')
                            (formsubst si (formsubst ri' u))]] THEN
      CONJ_TAC THENL
       [ALL_TAC,
        ASM_SIMP_TAC [FORMSUBST_FORMSUBST] THEN
        UNDISCH_TAC [[qfree u]] THEN SPEC_TAC ([[u:form]], [[u:form]]) THEN
        ONCE_REWRITE_TAC [FORMSUBST_TERMSUBST_EQ] THEN
        REWRITE_TAC [o_ASSOC] THEN REWRITE_TAC [(← HolLight.GSYM TERMSUBST_TERMSUBST_o)] THEN
        REWRITE_TAC [TERMSUBST_TERMSUBST_o] THEN
        ASM_REWRITE_TAC [FUN_EQ_THM, o_THM]] THEN
      MATCH_MP_TAC FORMSUBST_VALUATION THEN X_GEN_TAC [[z:num]] THEN
      DISCH_TAC THEN REWRITE_TAC [o_THM] THEN
      SUBGOAL_THEN ([[z IN FVS q'']]) (fun th => REWRITE_TAC [th]) THEN
      SUBGOAL_THEN ([[(formsubst si (formsubst ri' u)) IN q'']]) MP_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [FVS, IN_UNIONS, IN_ELIM_THM] THEN ASM_MESON_TAC []] THEN
      Fol.EXPAND_TAC "q''" THEN REWRITE_TAC [IN_IMAGE] THEN
      EXISTS_TAC [[formsubst ri' u]] THEN REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[u:form IN q']]) MP_TAC THENL
       [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
      Fol.EXPAND_TAC "q'" THEN REWRITE_TAC [IN_IMAGE] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[x:form]]) STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[formsubst ri' (formsubst ri x) = formsubst V x]])
       (fun th => ASM_REWRITE_TAC [th, FORMSUBST_TRIV]) THEN
      SUBGOAL_THEN ([[qfree x]]) MP_TAC THENL
       [ASM_MESON_TAC [clause, QFREE_LITERAL], ALL_TAC] THEN
      SPEC_TAC ([[x:form]], [[x:form]]) THEN
      SIMP_TAC [FORMSUBST_FORMSUBST] THEN
      ONCE_REWRITE_TAC [FORMSUBST_TERMSUBST_EQ] THEN
      ASM_REWRITE_TAC [FUN_EQ_THM, (← HolLight.GSYM TERMSUBST_TERMSUBST), TERMSUBST_TRIV],
      ALL_TAC] THEN
    MP_TAC (← HolLight.SPEC ([[p1' UNION {~~p | p IN q1''}]]) MGU) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [CONJ_ASSOC] THEN
      CONJ_TAC THENL
       [ALL_TAC, EXISTS_TAC [[i':num->term]] THEN ASM_REWRITE_TAC []] THEN
      ASM_REWRITE_TAC [FINITE_UNION] THEN
      SUBGOAL_THEN ([[{~~p | p IN q1''} = IMAGE (~~) q1'']]) SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN MESON_TAC [],
        ALL_TAC] THEN
      CONJ_TAC THENL
       [CONJ_TAC THENL
         [ALL_TAC,
          ASM_MESON_TAC [FINITE_SUBSET, clause, IMAGE_FORMSUBST_CLAUSE,
                      IMAGE_o, FINITE_IMAGE]] THEN
        SUBGOAL_THEN ([[p1':form->bool SUBSET p']])
          (fun th =>
             ASM_MESON_TAC [th, FINITE_SUBSET, clause, QFREE_LITERAL]) THEN
        Fol.EXPAND_TAC "p1'" THEN SIMP_TAC [SUBSET, IN_ELIM_THM],
        ALL_TAC] THEN
      Fol.EXPAND_TAC "p1'" THEN REWRITE_TAC [IN_UNION, IN_IMAGE, IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [QFREE_NEGATE] THEN
      ASM_MESON_TAC [clause, SUBSET, QFREE_LITERAL,
                    IMAGE_FORMSUBST_CLAUSE],
      ALL_TAC] THEN
    ABBREV_TAC [[k = mgu (p1' UNION {~~p | p IN q1''})]] THEN STRIP_TAC THEN
    EXISTS_TAC [[IMAGE (formsubst k) ((p' DIFF p1') UNION (q'' DIFF q1''))]] THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC [isaresolvent] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN
      MAP_EVERY EXISTS_TAC [ [[p1':form->bool]], [[q1'':form->bool]] ] THEN
      ASM_REWRITE_TAC [] THEN CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN
      REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [Fol.EXPAND_TAC "p1'" THEN SIMP_TAC [IN_ELIM_THM, SUBSET],
        Fol.EXPAND_TAC "q1''" THEN UNDISCH_TAC [[~(q1':form->bool = {})]] THEN
        REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, IN_IMAGE] THEN MESON_TAC [],
        EXISTS_TAC [[i':num->term]] THEN ASM_REWRITE_TAC []],
      ALL_TAC] THEN
    Fol.EXPAND_TAC "r" THEN EXISTS_TAC [[i':num->term]] THEN
    REWRITE_TAC [(← HolLight.GSYM IMAGE_o)] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC [[IMAGE (formsubst i') (p' DIFF p1' UNION q'' DIFF q1'')]] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[i':num->term]]) THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[!x. x IN (p' DIFF p1' UNION q'' DIFF q1'') ==> qfree x]])
       (fun th => REWRITE_TAC [SUBSET, IN_IMAGE, o_THM] THEN MESON_TAC [th]) THEN
      REWRITE_TAC [IN_DIFF, IN_UNION] THEN
      ASM_MESON_TAC [IMAGE_FORMSUBST_CLAUSE, clause, QFREE_LITERAL], ALL_TAC] THEN
    REWRITE_TAC [IMAGE_UNION] THEN MATCH_MP_TAC lemma THEN CONJ_TAC THENL
     [SUBGOAL_THEN ([[IMAGE (formsubst i') (p' DIFF p1') =
                    IMAGE (formsubst (termsubst i o j)) (p' DIFF p1')]])
      SUBST1_TAC THENL
       [SUBGOAL_THEN
         ([[!x. x IN p' ==> (formsubst i' x = formsubst (termsubst i o j) x)]])
         (fun th => REWRITE_TAC [EXTENSION, IN_IMAGE, IN_DIFF] THEN
                    MESON_TAC [th]) THEN
        X_GEN_TAC [[x:form]] THEN
        DISCH_TAC THEN MATCH_MP_TAC FORMSUBST_VALUATION THEN
        X_GEN_TAC [[z:num]] THEN DISCH_TAC THEN Fol.EXPAND_TAC "i'" THEN
        SUBGOAL_THEN ([[~(z IN FVS q'')]]) (fun th => REWRITE_TAC [th, o_THM]) THEN
        UNDISCH_TAC [[FVS q'' INTER FVS p' = {}]] THEN
        REWRITE_TAC [EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC [[z:num]]) THEN
        MATCH_MP_TAC (← ExceptT.mk (TAUT [[b ==> ~(a /\ b) ==> ~a]])) THEN
        REWRITE_TAC [FVS, IN_UNIONS, IN_ELIM_THM] THEN ASM_MESON_TAC [],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[IMAGE (formsubst (termsubst i o j)) (p' DIFF p1') =
                    IMAGE (formsubst i o formsubst j) (p' DIFF p1')]])
      SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_IMAGE, IN_DIFF, o_THM] THEN
        ASM_MESON_TAC [FORMSUBST_FORMSUBST, clause, QFREE_LITERAL], ALL_TAC] THEN
      Fol.EXPAND_TAC "p1'" THEN UNDISCH_TAC [[IMAGE (formsubst j) p' SUBSET p]] THEN
      REWRITE_TAC [SUBSET, IN_IMAGE, IN_DIFF, IN_ELIM_THM, o_THM] THEN
      MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[IMAGE (formsubst i') (q'' DIFF q1'') =
      IMAGE (formsubst (termsubst i o termsubst ri o si')) (q'' DIFF q1'')]])
    SUBST1_TAC THENL
     [SUBGOAL_THEN
       ([[!x. x IN q''
            ==> (formsubst i' x = formsubst (termsubst i o termsubst ri o si') x)]])
       (fun th => REWRITE_TAC [EXTENSION, IN_IMAGE, IN_DIFF] THEN
                  MESON_TAC [th]) THEN
      X_GEN_TAC [[x:form]] THEN
      DISCH_TAC THEN MATCH_MP_TAC FORMSUBST_VALUATION THEN
      X_GEN_TAC [[z:num]] THEN DISCH_TAC THEN Fol.EXPAND_TAC "i'" THEN
      SUBGOAL_THEN ([[z IN FVS q'']]) (fun th => REWRITE_TAC [th, o_THM]) THEN
      REWRITE_TAC [FVS, IN_UNIONS, IN_ELIM_THM] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     ([[IMAGE (formsubst (termsubst i o termsubst ri o si')) (q'' DIFF q1'') =
      IMAGE (formsubst i o formsubst ri o formsubst si') (q'' DIFF q1'')]])
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE] THEN
      SUBGOAL_THEN
       ([[(!q. qfree q ==> (formsubst (termsubst i o termsubst ri o si') q =
                          (formsubst i o formsubst ri o formsubst si') q)) /\
        (!q. q IN (q'' DIFF q1'') ==> qfree q)]])
       (fun th => MESON_TAC [th]) THEN
      CONJ_TAC THENL
       [SIMP_TAC [o_THM, FORMSUBST_FORMSUBST] THEN
        ONCE_REWRITE_TAC [FORMSUBST_TERMSUBST_EQ] THEN
        REWRITE_TAC [o_ASSOC] THEN REWRITE_TAC [(← HolLight.GSYM TERMSUBST_TERMSUBST_o)] THEN
        REWRITE_TAC [TERMSUBST_TERMSUBST_o],
        ALL_TAC] THEN
      ASM_MESON_TAC [IN_DIFF, IMAGE_FORMSUBST_CLAUSE, clause, QFREE_LITERAL],
      ALL_TAC] THEN
    REWRITE_TAC [IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC [(← HolLight.GSYM IMAGE_o)] THEN
    MAP_EVERY (fun s => Fol.EXPAND_TAC s) ["q''", "q1''", "q'"] THEN
    REWRITE_TAC [SUBSET, IN_IMAGE, IN_DIFF, o_THM] THEN
    X_GEN_TAC [[u:form]] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[v:form]]) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
    ONCE_REWRITE_TAC [IMP_CONJ] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[w:form]])
     (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN ([[formsubst si' (formsubst si w) = formsubst V w]])
    SUBST1_TAC THENL
     [SUBGOAL_THEN ([[qfree w]]) MP_TAC THENL
       [ASM_MESON_TAC [clause, QFREE_LITERAL], ALL_TAC] THEN
      SPEC_TAC ([[w:form]], [[w:form]]) THEN
      SIMP_TAC [FORMSUBST_FORMSUBST] THEN
      ONCE_REWRITE_TAC [FORMSUBST_TERMSUBST_EQ] THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM TERMSUBST_TERMSUBST), FUN_EQ_THM, TERMSUBST_TRIV],
      ALL_TAC] THEN
    REWRITE_TAC [FORMSUBST_TRIV] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[b /\ (c ==> a) ==> ~a ==> b /\ ~c]])) THEN
    CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    DISCH_TAC THEN EXISTS_TAC [[formsubst ri w]] THEN ASM_REWRITE_TAC [] THEN
    AP_TERM_TAC THEN HolLight.GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM FORMSUBST_TRIV)] THEN
    SUBGOAL_THEN ([[qfree w]]) MP_TAC THENL
     [ASM_MESON_TAC [clause, QFREE_LITERAL], ALL_TAC] THEN
    SPEC_TAC ([[w:form]], [[w:form]]) THEN
    SIMP_TAC [FORMSUBST_FORMSUBST] THEN
    ONCE_REWRITE_TAC [FORMSUBST_TERMSUBST_EQ] THEN
    ASM_REWRITE_TAC [(← HolLight.GSYM TERMSUBST_TERMSUBST), FUN_EQ_THM] THEN
    REWRITE_TAC [TERMSUBST_TRIV])
  : ExceptT String IO thm).run
#eval ISARESOLVENT_SUBSUME_L

#eval phrase 79
unsafe def ISARESOLVENT_SUBSUME_R : thm := keep "ISARESOLVENT_SUBSUME_R" fun _ => (do
  prove ([[!p q q' r.
        clause p /\ clause q /\ clause q' /\
        q' subsumes q /\ isaresolvent r (p,q)
        ==> q' subsumes r \/ ?r'. isaresolvent r' (p,q') /\ r' subsumes r]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [ [[q:form->bool]], [[p:form->bool]], [[r:form->bool]] ]
                 ISARESOLVENT_SYM) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[r':form->bool]]) STRIP_ASSUME_TAC) THEN
    MP_TAC (← HolLight.SPECL [ [[q:form->bool]], [[q':form->bool]], [[p:form->bool]],
                  [[r':form->bool]] ] ISARESOLVENT_SUBSUME_L) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
     [DISJ1_TAC THEN MATCH_MP_TAC subsumes_TRANS THEN
      EXISTS_TAC [[r':form->bool]] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[r'':form->bool]]) STRIP_ASSUME_TAC) THEN
    DISJ2_TAC THEN
    MP_TAC (← HolLight.SPECL [ [[p:form->bool]], [[q':form->bool]], [[r'':form->bool]] ]
                 ISARESOLVENT_SYM) THEN
    ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [ISARESOLVENT_CLAUSE, subsumes_TRANS])
  : ExceptT String IO thm).run
#eval ISARESOLVENT_SUBSUME_R

#eval phrase 80
unsafe def ISARESOLVENT_SUBSUME : thm := keep "ISARESOLVENT_SUBSUME" fun _ => (do
  prove ([[!p p' q q' r.
        clause p /\ clause p' /\ clause q /\ clause q' /\
        p' subsumes p /\ q' subsumes q /\ isaresolvent r (p,q)
        ==> p' subsumes r \/ q' subsumes r \/
            ?r'. isaresolvent r' (p',q') /\ r' subsumes r]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [ [[p:form->bool]], [[q:form->bool]],
                  [[q':form->bool]], [[r:form->bool]] ] ISARESOLVENT_SUBSUME_R) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[r':form->bool]]) STRIP_ASSUME_TAC) THEN
    MP_TAC (← HolLight.SPECL [ [[p:form->bool]], [[p':form->bool]],
                  [[q':form->bool]], [[r':form->bool]] ] ISARESOLVENT_SUBSUME_L) THEN
    ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [subsumes_TRANS, ISARESOLVENT_CLAUSE])
  : ExceptT String IO thm).run
#eval ISARESOLVENT_SUBSUME

#eval phrase 81
unsafe def ALLRESOLVENTS_SUBSUME_L : thm := keep "ALLRESOLVENTS_SUBSUME_L" fun _ => (do
  prove ([[!s t u.
      (!c. c IN s ==> clause c) /\
      (!c. c IN t ==> clause c) /\
      (!c. c IN u ==> clause c) /\
      s SUBSUMES t
      ==> (s UNION (allresolvents s u)) SUBSUMES (allresolvents t u)]])
   (REWRITE_TAC [SUBSUMES, IN_UNION, allresolvents, IN_ELIM_THM] THEN
    MESON_TAC [ISARESOLVENT_SUBSUME_L, subsumes_REFL])
  : ExceptT String IO thm).run
#eval ALLRESOLVENTS_SUBSUME_L

#eval phrase 82
unsafe def ALLRESOLVENTS_SUBSUME_R : thm := keep "ALLRESOLVENTS_SUBSUME_R" fun _ => (do
  prove ([[!s t u.
      (!c. c IN s ==> clause c) /\
      (!c. c IN t ==> clause c) /\
      (!c. c IN u ==> clause c) /\
      t SUBSUMES u
      ==> (t UNION (allresolvents s t)) SUBSUMES (allresolvents s u)]])
   (REWRITE_TAC [SUBSUMES, IN_UNION, allresolvents, IN_ELIM_THM] THEN
    MESON_TAC [ISARESOLVENT_SUBSUME_R, subsumes_REFL])
  : ExceptT String IO thm).run
#eval ALLRESOLVENTS_SUBSUME_R

#eval phrase 83
unsafe def ALLRESOLVENTS_SUBSUME : thm := keep "ALLRESOLVENTS_SUBSUME" fun _ => (do
  prove ([[!s t s' t'.
      (!c. c IN s ==> clause c) /\
      (!c. c IN s' ==> clause c) /\
      (!c. c IN t ==> clause c) /\
      (!c. c IN t' ==> clause c) /\
      s SUBSUMES s' /\ t SUBSUMES t'
      ==> (s UNION t UNION (allresolvents s t)) SUBSUMES
          (allresolvents s' t')]])
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUBSUMES_TRANS THEN
    EXISTS_TAC [[s UNION (allresolvents s t')]] THEN
    ASM_SIMP_TAC [ALLRESOLVENTS_SUBSUME_L, ALLRESOLVENTS_SUBSUME_R,
                 SUBSUMES_UNION, SUBSUMES_REFL, IN_UNION] THEN
    ASM_MESON_TAC [ALLRESOLVENTS_CLAUSE])
  : ExceptT String IO thm).run
#eval ALLRESOLVENTS_SUBSUME

#eval phrase 84
unsafe def ISARESOLVENT_TAUTOLOGY_L : thm := keep "ISARESOLVENT_TAUTOLOGY_L" fun _ => (do
  let lemma ← prove
   ([[{~~p | p IN s} = IMAGE (~~) s]])
    (REWRITE_TAC [EXTENSION, IN_IMAGE, IN_ELIM_THM] THEN MESON_TAC [])
  prove ([[!p q r.
      clause p /\ clause q /\
      tautologous(p) /\ isaresolvent r (p,q)
      ==> tautologous(r) \/ q subsumes r]])
   (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [tautologous, isaresolvent] THEN
    DISCH_THEN (CONJUNCTS_THEN2
     (X_CHOOSE_THEN ([[x:form]]) STRIP_ASSUME_TAC) MP_TAC) THEN
    ABBREV_TAC [[q' = IMAGE (formsubst (rename q (FVS p))) q]] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV Session.let_CONV) THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [ [[p1:form->bool]], [[q1':form->bool]] ] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    LET_TAC THEN DISCH_THEN (ASSUME_TAC oTIO HolLight.SYM) THEN
    ASM_CASES_TAC [[x IN (p DIFF p1) /\ ~~x IN (p DIFF p1)]] THENL
     [DISJ1_TAC THEN EXISTS_TAC [[formsubst i x]] THEN
      Fol.EXPAND_TAC "r" THEN REWRITE_TAC [(← HolLight.GSYM FORMSUBST_NEGATE)] THEN
      REWRITE_TAC [IN_IMAGE, IN_DIFF, IN_UNION] THEN
      ASM_MESON_TAC [IN_DIFF], ALL_TAC] THEN
    ABBREV_TAC [[k = rename q (FVS p)]] THEN
    DISJ2_TAC THEN ASM_CASES_TAC [[x:form IN p1]] THENL
     [REWRITE_TAC [subsumes] THEN
      EXISTS_TAC [[termsubst i o (k:num->term)]] THEN
      MP_TAC (← HolLight.SPEC ([[p1 UNION {~~p | p IN q1'}]]) MGU) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [REWRITE_TAC [lemma, FINITE_UNION] THEN
          ASM_MESON_TAC [FINITE_IMAGE, FINITE_SUBSET, clause, SUBSET, IN_DIFF],
          REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN
          REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [QFREE_NEGATE] THEN
          ASM_MESON_TAC [QFREE_LITERAL, clause, SUBSET, IN_IMAGE,
                          IMAGE_FORMSUBST_CLAUSE]],
        ALL_TAC] THEN
      DISCH_THEN (MP_TAC o Session.CONJUNCT1) THEN
      REWRITE_TAC [Unifies_DEF, IN_UNION, IN_ELIM_THM] THEN
      DISCH_THEN (fun th => HolLight.tactic_of do
        let th2 ← ExceptT.mk (HolLight.SPECL [ [[x:form]], [[~~x]] ] th)
        pure (ASSUME_TAC th THEN MP_TAC th2)) THEN
      REWRITE_TAC [FORMSUBST_NEGATE, NEGATE_REFL, (ASSUME [[x:form IN p1]])] THEN
      REWRITE_TAC [DE_MORGAN_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN ([[!y. y IN q1' ==> (formsubst i (~~y) = formsubst i x)]])
      ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN
       ([[IMAGE(formsubst (termsubst i o k)) q =
        IMAGE (formsubst i o formsubst k) q]])
      SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_IMAGE, o_THM] THEN
        ASM_MESON_TAC [clause, FORMSUBST_FORMSUBST, QFREE_LITERAL],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [IMAGE_o] THEN
      SUBGOAL_THEN ([[!y. y IN q1' ==> (formsubst i y = formsubst i (~~x))]])
      MP_TAC THENL
       [REPEAT STRIP_TAC THEN
        UNDISCH_TAC [[!y. y IN q1' ==> (formsubst i (~~ y) = formsubst i x)]] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC [[y:form]]) THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (MP_TAC o HolLight.AP_TERM [[(~~)]]) THEN
        REWRITE_TAC [(← HolLight.GSYM FORMSUBST_NEGATE)] THEN
        ASM_MESON_TAC [NEGATE_NEGATE, clause, IMAGE_FORMSUBST_CLAUSE, SUBSET],
        ALL_TAC] THEN
      Fol.EXPAND_TAC "r" THEN
      REWRITE_TAC [SUBSET, IN_IMAGE, IN_DIFF, IN_UNION] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[~~x IN p1]]) ASSUME_TAC THENL
     [ASM_MESON_TAC [IN_DIFF], ALL_TAC] THEN
    REWRITE_TAC [subsumes] THEN
    EXISTS_TAC [[termsubst i o (k:num->term)]] THEN
    MP_TAC (← HolLight.SPEC ([[p1 UNION {~~p | p IN q1'}]]) MGU) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC [lemma, FINITE_UNION] THEN
        ASM_MESON_TAC [FINITE_IMAGE, FINITE_SUBSET, clause, SUBSET, IN_DIFF],
        REWRITE_TAC [IN_UNION, IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [QFREE_NEGATE] THEN
        ASM_MESON_TAC [QFREE_LITERAL, clause, SUBSET, IN_IMAGE,
                        IMAGE_FORMSUBST_CLAUSE]],
      ALL_TAC] THEN
    DISCH_THEN (MP_TAC o Session.CONJUNCT1) THEN
    REWRITE_TAC [Unifies_DEF, IN_UNION, IN_ELIM_THM] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
      let th2 ← ExceptT.mk (HolLight.SPECL [ [[~~x]], [[x:form]] ] th)
      pure (ASSUME_TAC th THEN MP_TAC th2)) THEN
    REWRITE_TAC [FORMSUBST_NEGATE, NEGATE_REFL, (ASSUME [[~~x IN p1]])] THEN
    REWRITE_TAC [DE_MORGAN_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[!y. y IN q1' ==> (formsubst i (~~y) = formsubst i (~~x))]])
    ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[IMAGE(formsubst (termsubst i o k)) q =
      IMAGE (formsubst i o formsubst k) q]])
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_IMAGE, o_THM] THEN
      ASM_MESON_TAC [clause, FORMSUBST_FORMSUBST, QFREE_LITERAL],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [IMAGE_o] THEN
    SUBGOAL_THEN ([[!y. y IN q1' ==> (formsubst i y = formsubst i x)]])
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      UNDISCH_TAC [[!y. y IN q1' ==> (formsubst i (~~y) = formsubst i (~~x))]] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[y:form]]) THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o HolLight.AP_TERM [[(~~)]]) THEN
      REWRITE_TAC [(← HolLight.GSYM FORMSUBST_NEGATE)] THEN
      SUBGOAL_THEN ([[literal x /\ literal y]])
        (fun th => MESON_TAC [NEGATE_NEGATE, th]) THEN
      ASM_MESON_TAC [clause, IMAGE_FORMSUBST_CLAUSE, SUBSET],
      ALL_TAC] THEN
    Fol.EXPAND_TAC "r" THEN
    REWRITE_TAC [SUBSET, IN_IMAGE, IN_DIFF, IN_UNION] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval ISARESOLVENT_TAUTOLOGY_L

#eval phrase 85
unsafe def TAUTOLOGOUS_SUBSUMES : thm := keep "TAUTOLOGOUS_SUBSUMES" fun _ => (do
  prove ([[!p q. p subsumes q /\ tautologous(p) ==> tautologous(q)]])
   (MESON_TAC [subsumes, tautologous, SUBSET, TAUTOLOGOUS_INSTANCE])
  : ExceptT String IO thm).run
#eval TAUTOLOGOUS_SUBSUMES

#eval phrase 86
unsafe def ISARESOLVENT_TAUTOLOGY_R : thm := keep "ISARESOLVENT_TAUTOLOGY_R" fun _ => (do
  prove ([[!p q r.
      clause p /\ clause q /\
      tautologous(p) /\ isaresolvent r (q,p)
      ==> tautologous(r) \/ q subsumes r]])
   (MESON_TAC [ISARESOLVENT_SYM, ISARESOLVENT_TAUTOLOGY_L, subsumes_TRANS,
              TAUTOLOGOUS_SUBSUMES])
  : ExceptT String IO thm).run
#eval ISARESOLVENT_TAUTOLOGY_R

#eval phrase 87
unsafe def REPLACE_FROMNEW : thm := keep "REPLACE_FROMNEW" fun _ => (do
  prove ([[!cl lis c. MEM c (replace cl lis) ==> MEM c lis \/ (c = cl)]])
   (GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [replace] THEN
    SIMP_TAC [MEM] THEN GEN_TAC THEN COND_CASES_TAC THEN
    SIMP_TAC [MEM] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval REPLACE_FROMNEW

#eval phrase 88
unsafe def INCORPORATE_FROMNEW : thm := keep "INCORPORATE_FROMNEW" fun _ => (do
  prove ([[!gcl cl lis c.
        MEM c (incorporate gcl cl lis) ==> MEM c lis \/ (c = cl)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [incorporate] THEN COND_CASES_TAC THEN
    MESON_TAC [REPLACE_FROMNEW])
  : ExceptT String IO thm).run
#eval INCORPORATE_FROMNEW

#eval phrase 89
unsafe def ITLIST_INCORPORATE_FROMNEW : thm := keep "ITLIST_INCORPORATE_FROMNEW" fun _ => (do
  prove ([[!gcl lis new c.
        MEM c (ITLIST (incorporate gcl) new lis)
        ==> MEM c new \/ MEM c lis]])
   (GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [ITLIST, MEM] THEN ASM_MESON_TAC [INCORPORATE_FROMNEW])
  : ExceptT String IO thm).run
#eval ITLIST_INCORPORATE_FROMNEW

#eval phrase 90
unsafe def UNUSED_FROMNEW : thm := keep "UNUSED_FROMNEW" fun _ => (do
  prove ([[!used unused c n.
        MEM c (SND(given n (used,unused)))
        ==> MEM c unused \/
            ?m. m < n /\
                MEM c (resolvents
                         (HD(SND(given m (used,unused))))
                         (CONS (HD(SND(given m (used,unused))))
                               (FST(given m (used,unused)))))]])
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC [given] THEN
    SUBST1_TAC (← HolLight.SYM (← HolLight.ISPEC ([[given n (used,unused)]]) PAIR)) THEN
    PURE_REWRITE_TAC [step] THEN
    COND_CASES_TAC THEN REWRITE_TAC [] THENL
     [ASM_MESON_TAC [(← ExceptT.mk (ARITH_RULE [[x < n ==> x < SUC n]]))], ALL_TAC] THEN
    LET_TAC THEN REWRITE_TAC [SND] THEN
    DISCH_THEN (MP_TAC oTIO HolLight.MATCH_MP ITLIST_INCORPORATE_FROMNEW) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THENL [ASM_MESON_TAC [LT], ALL_TAC] THEN
    SUBGOAL_THEN ([[MEM c (SND (given n (used,unused)))]])
     (fun th => FIRST_ASSUM (MP_TAC o HolCore.Lib.C HolLight.MATCH_MP th))
    THENL
     [UNDISCH_TAC [[MEM c (TL (SND (given n (used,unused))))]] THEN
      UNDISCH_TAC [[~(SND (given n (used,unused)) = [])]] THEN
      SPEC_TAC ([[SND (given n (used,unused))]], [[l:(form->bool)list]]) THEN
      LIST_INDUCT_TAC THEN SIMP_TAC [MEM, TL], ALL_TAC] THEN
    MESON_TAC [(← ExceptT.mk (ARITH_RULE [[x < n ==> x < SUC n]]))])
  : ExceptT String IO thm).run
#eval UNUSED_FROMNEW

#eval phrase 91
unsafe def SUB_FROMNEW : thm := keep "SUB_FROMNEW" fun _ => (do
  let _lemma ← prove
   ([[!l. ~(l = []) ==> MEM (HD l) l]])
    (LIST_INDUCT_TAC THEN REWRITE_TAC [MEM, HD])
  prove ([[!used unused c n.
        c IN Sub(used,unused) n
        ==> MEM c unused \/
            ?m. m < n /\
                MEM c (resolvents
                         (HD(SND(given m (used,unused))))
                         (CONS (HD(SND(given m (used,unused))))
                               (FST(given m (used,unused)))))]])
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [Sub_DEF, NOT_IN_EMPTY] THEN
    COND_CASES_TAC THENL
     [ASM_MESON_TAC [(← ExceptT.mk (ARITH_RULE [[x < n ==> x < SUC n]]))], ALL_TAC] THEN
    REWRITE_TAC [IN_INSERT] THEN STRIP_TAC THENL
     [ALL_TAC, ASM_MESON_TAC [(← ExceptT.mk (ARITH_RULE [[x < n ==> x < SUC n]]))]] THEN
    SUBGOAL_THEN ([[MEM c (SND(given n (used,unused)))]])
     (fun th => HolLight.tactic_of do
       let t ← HolLight.MATCH_MP UNUSED_FROMNEW th
       pure (MP_TAC t))
    THENL [ALL_TAC, MESON_TAC [(← ExceptT.mk (ARITH_RULE [[x < n ==> x < SUC n]]))]] THEN
    UNDISCH_TAC [[~(SND (given n (used,unused)) = [])]] THEN
    ASM_REWRITE_TAC [] THEN
    SPEC_TAC ([[SND (given n (used,unused))]], [[l:(form->bool)list]]) THEN
    LIST_INDUCT_TAC THEN SIMP_TAC [MEM, TL, HD])
  : ExceptT String IO thm).run
#eval SUB_FROMNEW

#eval phrase 92
unsafe def LEVEL_FROMNEW : thm := keep "LEVEL_FROMNEW" fun _ => (do
  prove ([[!used unused c n.
        c IN level(used,unused) n
        ==> MEM c unused \/
            ?m. MEM c (resolvents
                         (HD(SND(given m (used,unused))))
                         (CONS (HD(SND(given m (used,unused))))
                               (FST(given m (used,unused)))))]])
   (REWRITE_TAC [level] THEN MESON_TAC [SUB_FROMNEW])
  : ExceptT String IO thm).run
#eval LEVEL_FROMNEW

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.Given" do
  replay (
          HolLogicArith.Resolution.ensure)
  replay (
          FIRSTN)
  replay (
          FIRSTN_TRIVIAL)
  replay (
          FIRSTN_EMPTY)
  replay (
          FIRSTN_SUBLIST)
  replay (
          FIRSTN_SUC)
  replay (
          FIRSTN_SHORT)
  replay (
          tautologous)
  replay (
          parse_as_infix ("subsumes", (12, "right")))
  replay (
          subsumes)
  replay (
          subsumes_REFL)
  replay (
          subsumes_TRANS)
  replay (
          parse_as_infix ("SUBSUMES", (12, "right")))
  replay (
          SUBSUMES)
  replay (
          SUBSUMES_REFL)
  replay (
          SUBSUMES_UNION)
  replay (
          SUBSUMES_TRANS)
  replay (
          SUBSUMES_SUBSET)
  replay (
          SUBSUMES_CLAUSES)
  replay (
          SUBSUMES_SUBSET_REFL)
  replay (
          allresolvents)
  replay (
          allntresolvents)
  replay (
          TERMSUBST_TERMSUBST_o)
  replay (
          FORMSUBST_FORMSUBST)
  replay (
          ISARESOLVENT_SYM)
  replay (
          ALLRESOLVENTS_SYM)
  replay (
          ALLRESOLVENTS_UNION)
  replay (
          ALLRESOLVENTS_STEP)
  replay (
          resolvents)
  replay (
          CLAUSE_UNION)
  replay (
          CLAUSE_SUBSET)
  replay (
          CLAUSE_DIFF)
  replay (
          ISARESOLVENT_CLAUSE)
  replay (
          ALLRESOLVENTS_CLAUSE)
  replay (
          ISARESOLVENT_FINITE)
  replay (
          ALLRESOLVENTS_FINITE)
  replay (
          replace)
  replay (
          REPLACE)
  replay (
          incorporate)
  replay (
          INCORPORATE)
  replay (
          insert_def)
  replay (
          step)
  replay (
          STEP)
  replay (
          given)
  replay (
          Used_DEF)
  replay (
          Unused_DEF)
  replay (
          Sub_DEF)
  replay (
          TAUTOLOGOUS_INSTANCE)
  replay (
          NONTAUTOLOGOUS_SUBSUMES)
  replay (
          ALLNTRESOLVENTS_STEP)
  replay (
          ALLNTRESOLVENTS_UNION)
  replay (
          SET_OF_LIST_INSERT)
  replay (
          SET_OF_LIST_FILTER)
  replay (
          USED_SUB)
  replay (
          GIVEN_INVARIANT)
  replay (
          SUB_MONO_SUBSET)
  replay (
          SUB_MONO)
  replay (
          LENGTH_REPLACE)
  replay (
          LENGTH_INCORPORATE)
  replay (
          LENGTH_UNUSED_CHANGE)
  replay (
          LENGTH_UNUSED_ZERO)
  replay (
          REPLACE_SUBSUMES_SELF)
  replay (
          INCORPORATE_SUBSUMES_SELF)
  replay (
          REPLACE_CLAUSE)
  replay (
          INCORPORATE_CLAUSE)
  replay (
          INCORPORATE_CLAUSE_EL)
  replay (
          UNUSED_SUBSUMES_SELF)
  replay (
          SUB_SUBSUMES_UNUSED)
  replay (
          «break»)
  replay (
          level)
  replay (
          LEVEL_0)
  replay (
          LEVEL_STEP)
  replay (
          level_CLAUSE)
  replay (
          BREAK_MONO)
  replay (
          level_MONO_SUBSET)
  replay (
          level_MONO)
  replay (
          IMAGE_CLAUSE_EQ)
  replay (
          FORMSUBST_TERMSUBST_EQ)
  replay (
          ISARESOLVENT_SUBSUME_L)
  replay (
          ISARESOLVENT_SUBSUME_R)
  replay (
          ISARESOLVENT_SUBSUME)
  replay (
          ALLRESOLVENTS_SUBSUME_L)
  replay (
          ALLRESOLVENTS_SUBSUME_R)
  replay (
          ALLRESOLVENTS_SUBSUME)
  replay (
          ISARESOLVENT_TAUTOLOGY_L)
  replay (
          TAUTOLOGOUS_SUBSUMES)
  replay (
          ISARESOLVENT_TAUTOLOGY_R)
  replay (
          REPLACE_FROMNEW)
  replay (
          INCORPORATE_FROMNEW)
  replay (
          ITLIST_INCORPORATE_FROMNEW)
  replay (
          UNUSED_FROMNEW)
  replay (
          SUB_FROMNEW)
  replay (
          LEVEL_FROMNEW)
-- @@ENSURE END

end HolLogicArith.Given
