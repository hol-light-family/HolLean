/- File: HolExamples/MultiWf.lean
Translation of HOL Light's Examples/multiwf.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
namespace HolExamples.MultiWf

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- Run `new_inductive_definition`, panicking with HOL Light's message on
   failure (as the toplevel throws). -/
private unsafe def indDef (tm : term) : thm × thm × thm :=
  match unsafeIO (Session.new_inductive_definition tm) with
  | .ok (.ok t) => t
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)

/- ========================================================================= -/
/- Part 1: Background theories.                                              -/
/- ========================================================================= -/

#eval phrase 1
unsafe def EMPTY_IS_FINITE : thm := keep "EMPTY_IS_FINITE" fun _ => (do
  prove ([[!s. (s = EMPTY) ==> FINITE s]])
   (SIMP_TAC [FINITE_RULES])
  : ExceptT String IO thm).run
#eval EMPTY_IS_FINITE

#eval phrase 2
unsafe def SING_IS_FINITE : thm := keep "SING_IS_FINITE" fun _ => (do
  prove ([[!s a. (s = {a}) ==> FINITE s]])
   (SIMP_TAC [FINITE_INSERT, FINITE_RULES])
  : ExceptT String IO thm).run
#eval SING_IS_FINITE

#eval phrase 3
unsafe def UNION_NONZERO : thm := keep "UNION_NONZERO" fun _ => (do
  prove ([[{a | ~(f a + g a = 0)} = {a | ~(f a = 0)} UNION {a | ~(g a = 0)}]])
   (REWRITE_TAC [ADD_EQ_0, EXTENSION, IN_UNION, IN_ELIM_THM, DE_MORGAN_THM])
  : ExceptT String IO thm).run
#eval UNION_NONZERO

/- ------------------------------------------------------------------------- -/
/- Definition of type of finite multisets with a few basic operations.       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
#eval parse_as_infix ("mmember", (11, "right"))

#eval phrase 5
#eval parse_as_infix ("munion", (16, "right"))

#eval phrase 6
#eval parse_as_infix ("mdiff", (18, "left"))

#eval phrase 7
unsafe def multiset_tybij_th : thm := keep "multiset_tybij_th" fun _ => (do
  prove ([[?f. FINITE {a:A | ~(f a = 0)}]])
   (EXISTS_TAC [[\a:A. 0]] THEN
    SIMP_TAC [EMPTY_IS_FINITE, EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY])
  : ExceptT String IO thm).run
#eval multiset_tybij_th

#eval phrase 8
unsafe def multiset_tybij : thm := keep "multiset_tybij" fun _ =>
  Session.new_type_definition "multiset" "multiset" "multiplicity" multiset_tybij_th
#eval multiset_tybij

#eval phrase 9
unsafe def mempty : thm := keep "mempty" fun _ => new_definition
 [[mempty = multiset (\b. 0)]]
#eval mempty

#eval phrase 10
unsafe def mmember : thm := keep "mmember" fun _ => new_definition
 [[a mmember M <=> ~(multiplicity M a = 0)]]
#eval mmember

#eval phrase 11
unsafe def msing : thm := keep "msing" fun _ => new_definition
 [[msing a = multiset (\b. if b = a then 1 else 0)]]
#eval msing

#eval phrase 12
unsafe def munion : thm := keep "munion" fun _ => new_definition
 [[M munion N = multiset(\b. multiplicity M b + multiplicity N b)]]
#eval munion

#eval phrase 13
unsafe def mdiff : thm := keep "mdiff" fun _ => new_definition
 [[M mdiff N = multiset(\b. multiplicity M b - multiplicity N b)]]
#eval mdiff

/- ------------------------------------------------------------------------- -/
/- Extensionality for multisets.                                             -/
/- ------------------------------------------------------------------------- -/

#eval phrase 14
unsafe def MEXTENSION : thm := keep "MEXTENSION" fun _ => (do
  prove ([[(M = N) = !a. multiplicity M a = multiplicity N a]])
   (REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM FUN_EQ_THM))] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (Session.ETA_CONV t))) THEN
    MESON_TAC [multiset_tybij])
  : ExceptT String IO thm).run
#eval MEXTENSION

/- ------------------------------------------------------------------------- -/
/- Basic properties of multisets.                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 15
unsafe def MULTIPLICITY_MULTISET : thm := keep "MULTIPLICITY_MULTISET" fun _ => (do
  prove ([[FINITE {a | ~(f a = 0)} /\ (f a = y) ==> (multiplicity(multiset f) a = y)]])
   (SIMP_TAC [multiset_tybij])
  : ExceptT String IO thm).run
#eval MULTIPLICITY_MULTISET

#eval phrase 16
unsafe def MEMPTY : thm := keep "MEMPTY" fun _ => (do
  prove ([[multiplicity mempty a = 0]])
   (REWRITE_TAC [mempty] THEN MATCH_MP_TAC MULTIPLICITY_MULTISET THEN
    SIMP_TAC [EMPTY_IS_FINITE, EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY])
  : ExceptT String IO thm).run
#eval MEMPTY

#eval phrase 17
unsafe def MSING : thm := keep "MSING" fun _ => (do
  prove ([[multiplicity (msing (a:A)) b = if b = a then 1 else 0]])
   (REWRITE_TAC [msing] THEN MATCH_MP_TAC MULTIPLICITY_MULTISET THEN
    REWRITE_TAC [] THEN MATCH_MP_TAC SING_IS_FINITE THEN EXISTS_TAC [[a:A]] THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY] THEN
    GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [ARITH_EQ])
  : ExceptT String IO thm).run
#eval MSING

#eval phrase 18
unsafe def MUNION : thm := keep "MUNION" fun _ => (do
  prove ([[multiplicity (M munion N) a = multiplicity M a + multiplicity N a]])
   (REWRITE_TAC [munion] THEN MATCH_MP_TAC MULTIPLICITY_MULTISET THEN
    REWRITE_TAC [UNION_NONZERO, FINITE_UNION] THEN SIMP_TAC [multiset_tybij] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (Session.ETA_CONV t))) THEN REWRITE_TAC [multiset_tybij])
  : ExceptT String IO thm).run
#eval MUNION

#eval phrase 19
unsafe def MDIFF : thm := keep "MDIFF" fun _ => (do
  prove ([[multiplicity (M mdiff N) (a:A) = multiplicity M a - multiplicity N a]])
   (REWRITE_TAC [mdiff] THEN MATCH_MP_TAC MULTIPLICITY_MULTISET THEN
    REWRITE_TAC [] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC [[{a:A | ~(multiplicity M a = 0)}]] THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM, multiset_tybij] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (Session.ETA_CONV t))) THEN REWRITE_TAC [multiset_tybij] THEN
    ARITH_TAC)
  : ExceptT String IO thm).run
#eval MDIFF

/- ------------------------------------------------------------------------- -/
/- Some trivial properties of multisets that we use later.                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 20
unsafe def MUNION_MEMPTY : thm := keep "MUNION_MEMPTY" fun _ => (do
  prove ([[~(M munion (msing(a:A)) = mempty)]])
   (REWRITE_TAC [MEXTENSION, MEMPTY, MSING, MUNION] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[a:A]]) THEN
    REWRITE_TAC [ADD_EQ_0, ARITH_EQ])
  : ExceptT String IO thm).run
#eval MUNION_MEMPTY

#eval phrase 21
unsafe def MMEMBER_MUNION : thm := keep "MMEMBER_MUNION" fun _ => (do
  prove ([[x mmember (M munion N) <=> x mmember M \/ x mmember N]])
   (REWRITE_TAC [mmember, MUNION, ADD_EQ_0, DE_MORGAN_THM])
  : ExceptT String IO thm).run
#eval MMEMBER_MUNION

#eval phrase 22
unsafe def MMEMBER_MSING : thm := keep "MMEMBER_MSING" fun _ => (do
  prove ([[x mmember (msing a) <=> (x = a)]])
   (REWRITE_TAC [mmember, MSING] THEN COND_CASES_TAC THEN REWRITE_TAC [ARITH_EQ])
  : ExceptT String IO thm).run
#eval MMEMBER_MSING

#eval phrase 23
unsafe def MUNION_EMPTY : thm := keep "MUNION_EMPTY" fun _ => (do
  prove ([[M munion mempty = M]])
   (REWRITE_TAC [MEXTENSION, MUNION, MEMPTY, ADD_CLAUSES])
  : ExceptT String IO thm).run
#eval MUNION_EMPTY

#eval phrase 24
unsafe def MUNION_ASSOC : thm := keep "MUNION_ASSOC" fun _ => (do
  prove ([[M1 munion (M2 munion M3) = (M1 munion M2) munion M3]])
   (REWRITE_TAC [MEXTENSION, MUNION, ADD_ASSOC])
  : ExceptT String IO thm).run
#eval MUNION_ASSOC

#eval phrase 25
unsafe def MUNION_AC : thm := keep "MUNION_AC" fun _ => (do
  prove ([[(M1 munion M2 = M2 munion M1) /\
   ((M1 munion M2) munion M3 = M1 munion M2 munion M3) /\
   (M1 munion M2 munion M3 = M2 munion M1 munion M3)]])
   (REWRITE_TAC [MEXTENSION, MUNION, ADD_AC])
  : ExceptT String IO thm).run
#eval MUNION_AC

#eval phrase 26
unsafe def MUNION_11 : thm := keep "MUNION_11" fun _ => (do
  prove ([[(M1 munion N = M2 munion N) <=> (M1 = M2)]])
   (REWRITE_TAC [MEXTENSION, MUNION, EQ_ADD_RCANCEL])
  : ExceptT String IO thm).run
#eval MUNION_11

#eval phrase 27
unsafe def MUNION_INUNION : thm := keep "MUNION_INUNION" fun _ => (do
  prove ([[a mmember (M munion (msing b)) /\ ~(b = a) ==> a mmember M]])
   (REWRITE_TAC [mmember, MUNION, MSING, ADD_EQ_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [ARITH_EQ])
  : ExceptT String IO thm).run
#eval MUNION_INUNION

#eval phrase 28
unsafe def MMEMBER_MDIFF : thm := keep "MMEMBER_MDIFF" fun _ => (do
  prove ([[(a:A) mmember M ==> (M = (M mdiff (msing a)) munion (msing a))]])
   (REWRITE_TAC [mmember, MEXTENSION, MUNION, MDIFF, MSING] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC [[~(multiplicity M (a:A) = 0)]] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval MMEMBER_MDIFF

/- ------------------------------------------------------------------------- -/
/- Induction principle for multisets.                                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 29
unsafe def MULTISET_INDUCT_LEMMA1 : thm := keep "MULTISET_INDUCT_LEMMA1" fun _ => (do
  prove ([[(!M. ({a | ~(multiplicity M a = 0)} SUBSET s) ==> P M) /\
   (!a:A M. P M ==> P (M munion (msing a)))
   ==> !n M. (multiplicity M a = n) /\
             {a:A | ~(multiplicity M a = 0)} SUBSET (a INSERT s)
             ==> P M]])
   (STRIP_TAC THEN INDUCT_TAC THEN REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC [[{a:A | ~(multiplicity M a = 0)} SUBSET (a INSERT s)]] THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_INSERT] THEN ASM_MESON_TAC [],
      SUBGOAL_THEN ([[M = (M mdiff (msing(a:A))) munion (msing a)]]) SUBST1_TAC THENL
       [MATCH_MP_TAC MMEMBER_MDIFF THEN ASM_REWRITE_TAC [mmember, NOT_SUC],
        ALL_TAC] THEN
      MAP_EVERY (fun t => MATCH_MP_TAC (HolCore.Kernel.ASSUME t))
       [ [[!a:A M. P M ==> P (M munion msing a)]],
         [[!M. (multiplicity M a = n) /\
           {a:A | ~(multiplicity M a = 0)} SUBSET (a INSERT s)
           ==> P M]] ] THEN
      ASM_REWRITE_TAC [MDIFF, MSING, (← ExceptT.mk (ARITH_RULE [[SUC n - 1 = n]]))] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC [[{a:A | ~(multiplicity M a = 0)}]] THEN
      ASM_SIMP_TAC [SUBSET, IN_ELIM_THM, CONTRAPOS_THM, SUB_0]])
  : ExceptT String IO thm).run
#eval MULTISET_INDUCT_LEMMA1

#eval phrase 30
unsafe def MULTISET_INDUCT_LEMMA2 : thm := keep "MULTISET_INDUCT_LEMMA2" fun _ => (do
  prove ([[P mempty /\
   (!a:A M. P M ==> P (M munion (msing a)))
   ==> !s. FINITE s ==> !M. {a:A | ~(multiplicity M a = 0)} SUBSET s ==> P M]])
   (STRIP_TAC THEN MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC [SUBSET, IN_ELIM_THM, NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN ([[M:(A)multiset = mempty]]) (fun th => ASM_REWRITE_TAC [th]) THEN
      ASM_REWRITE_TAC [MEXTENSION, MEMPTY], X_GEN_TAC [[a:A]]] THEN
    REPEAT STRIP_TAC THEN MP_TAC MULTISET_INDUCT_LEMMA1 THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM EXISTS_REFL))])
  : ExceptT String IO thm).run
#eval MULTISET_INDUCT_LEMMA2

#eval phrase 31
unsafe def MULTISET_INDUCT : thm := keep "MULTISET_INDUCT" fun _ => (do
  prove ([[P mempty /\
   (!a:A M. P M ==> P (M munion (msing a)))
   ==> !M. P M]])
   (DISCH_THEN (MP_TAC o HolLight.MATCH_MP MULTISET_INDUCT_LEMMA2) THEN
    REWRITE_TAC [RIGHT_IMP_FORALL_THM] THEN
    REWRITE_TAC [IMP_IMP] THEN
    GEN_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC [[{a:A | ~(multiplicity M a = 0)}]] THEN
    REWRITE_TAC [SUBSET_REFL, multiset_tybij] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV (fun t => pure (Session.ETA_CONV t))) THEN REWRITE_TAC [multiset_tybij])
  : ExceptT String IO thm).run
#eval MULTISET_INDUCT

/- ========================================================================= -/
/- Part 2: Transcription of Tobias's paper.                                  -/
/- ========================================================================= -/

#eval phrase 32
#eval parse_as_infix ("<<", (12, "right"))

/- ------------------------------------------------------------------------- -/
/- Wellfounded part of a relation.                                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 33
unsafe def WFP_triple : thm × thm × thm := keep "WFP" fun _ =>
  indDef [[!x. (!y. y << x ==> WFP(<<) y) ==> WFP(<<) x]]
unsafe def WFP_RULES : thm := WFP_triple.1
unsafe def WFP_INDUCT : thm := WFP_triple.2.1
unsafe def WFP_CASES : thm := WFP_triple.2.2
#eval (do IO.println (← HolCore.Printer.string_of_thm WFP_RULES)
          IO.println (← HolCore.Printer.string_of_thm WFP_INDUCT)
          IO.println (← HolCore.Printer.string_of_thm WFP_CASES) : IO Unit)

/- ------------------------------------------------------------------------- -/
/- Wellfounded part induction.                                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 34
unsafe def WFP_PART_INDUCT : thm := keep "WFP_PART_INDUCT" fun _ => (do
  prove ([[!P. (!x. x IN WFP(<<) /\ (!y. y << x ==> P(y)) ==> P(x))
       ==> !x:A. x IN WFP(<<) ==> P(x)]])
   (GEN_TAC THEN REWRITE_TAC [IN] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (TAUT [[a ==> b <=> a ==> a /\ b]]))] THEN
    MATCH_MP_TAC WFP_INDUCT THEN ASM_MESON_TAC [WFP_RULES])
  : ExceptT String IO thm).run
#eval WFP_PART_INDUCT

/- ------------------------------------------------------------------------- -/
/- A relation is wellfounded iff WFP is the whole universe.                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 35
unsafe def WFP_WF : thm := keep "WFP_WF" fun _ => (do
  prove ([[WF(<<) <=> (WFP(<<) = UNIV:A->bool)]])
   (EQ_TAC THENL
     [REWRITE_TAC [WF_IND, EXTENSION, IN, UNIV] THEN MESON_TAC [WFP_RULES],
      DISCH_TAC THEN MP_TAC WFP_PART_INDUCT THEN
      ASM_REWRITE_TAC [IN, UNIV, WF_IND]])
  : ExceptT String IO thm).run
#eval WFP_WF

/- ------------------------------------------------------------------------- -/
/- This isn't needed for the result as such, but formalizes the last         -/
/- remarks in section 3 that the WFP is exactly those elements that cannot   -/
/- start infinite descending chains.                                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 36
unsafe def WFP_DCHAIN : thm := keep "WFP_DCHAIN" fun _ => (do
  prove ([[!(<<):A->A->bool.
        WFP(<<) = {a | !x. (!n. x(SUC n) << x n) ==> ~(x 0 = a)}]])
   (GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN REWRITE_TAC [IN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC WFP_INDUCT THEN X_GEN_TAC [[a:A]] THEN DISCH_TAC THEN
      X_GEN_TAC [[x:num->A]] THEN DISCH_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC [[(x:num->A) (SUC 0)]]) THEN
      REWRITE_TAC [NOT_IMP] THEN CONJ_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[(x:num->A) o SUC]]) THEN
      ASM_REWRITE_TAC [o_THM],
      X_GEN_TAC [[a:A]] THEN GEN_REWRITE_TAC HolCore.Lib.I [(← ExceptT.mk (HolLight.GSYM CONTRAPOS_THM))] THEN
      DISCH_TAC THEN MP_TAC (← ExceptT.mk (HolLight.ISPECL
       [ [[\(n:num) (x:A). ~WFP(<<) x]], [[\(n:num) x y. ((<<):A->A->bool) y x]],
        [[a:A]] ] DEPENDENT_CHOICE_FIXED)) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ALL_TAC, MESON_TAC []] THEN
      GEN_TAC THEN GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [WFP_CASES] THEN
      MESON_TAC []])
  : ExceptT String IO thm).run
#eval WFP_DCHAIN

/- ------------------------------------------------------------------------- -/
/- The multiset order.                                                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 37
unsafe def morder : thm := keep "morder" fun _ => new_definition
 [[morder(<<) N M <=> ?M0 a K. (M = M0 munion (msing a)) /\
                               (N = M0 munion K) /\
                               (!b. b mmember K ==> b << a)]]
#eval morder

/- ------------------------------------------------------------------------- -/
/- We separate off this part from the proof of LEMMA_2_1.                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 38
unsafe def LEMMA_2_0 : thm := keep "LEMMA_2_0" fun _ => (do
  prove ([[morder(<<) N (M0 munion (msing a))
   ==> (?M. morder(<<) M M0 /\ (N = M munion (msing a))) \/
       (?K. (N = M0 munion K) /\ (!b:A. b mmember K ==> b << a))]])
   (GEN_REWRITE_TAC HolLight.LAND_CONV [morder] THEN
    DISCH_THEN (EVERY_TCL [Session.X_CHOOSE_THEN [[M1:(A)multiset]],
      Session.X_CHOOSE_THEN [[b:A]], Session.X_CHOOSE_THEN [[K:(A)multiset]]]
      STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC [[b:A = a]] THENL
     [DISJ2_TAC THEN UNDISCH_THEN ([[b:A = a]]) SUBST_ALL_TAC THEN
      EXISTS_TAC [[K:(A)multiset]] THEN ASM_MESON_TAC [MUNION_11], DISJ1_TAC] THEN
    SUBGOAL_THEN ([[?M2. M1 = M2 munion (msing(a:A))]]) STRIP_ASSUME_TAC THENL
     [EXISTS_TAC [[M1 mdiff (msing(a:A))]] THEN
      MAP_EVERY MATCH_MP_TAC [MMEMBER_MDIFF, MUNION_INUNION] THEN
      UNDISCH_TAC [[M0 munion (msing a) = M1 munion (msing(b:A))]] THEN
      ASM_REWRITE_TAC [MEXTENSION, MUNION, MSING, mmember] THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[a:A]]) THEN ASM_REWRITE_TAC [] THEN
      ARITH_TAC, ALL_TAC] THEN
    EXISTS_TAC [[M2 munion K:(A)multiset]] THEN ASM_REWRITE_TAC [MUNION_AC] THEN
    REWRITE_TAC [morder] THEN
    MAP_EVERY EXISTS_TAC [ [[M2:(A)multiset]], [[b:A]], [[K:(A)multiset]] ] THEN
    UNDISCH_TAC [[M0 munion msing (a:A) = M1 munion msing b]] THEN
    ASM_REWRITE_TAC [MUNION_AC] THEN MESON_TAC [MUNION_AC, MUNION_11])
  : ExceptT String IO thm).run
#eval LEMMA_2_0

/- ------------------------------------------------------------------------- -/
/- The sequence of lemmas from Tobias's paper.                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 39
unsafe def LEMMA_2_1 : thm := keep "LEMMA_2_1" fun _ => (do
  prove ([[(!M b:A. b << a /\ M IN WFP(morder(<<))
            ==> (M munion (msing b)) IN WFP(morder(<<))) /\
   M0 IN WFP(morder(<<)) /\
   (!M. morder(<<) M M0 ==> (M munion (msing a)) IN WFP(morder(<<)))
   ==> (M0 munion (msing a)) IN WFP(morder(<<))]])
   (STRIP_TAC THEN REWRITE_TAC [IN] THEN MATCH_MP_TAC WFP_RULES THEN
    X_GEN_TAC [[N:(A)multiset]] THEN
    DISCH_THEN (DISJ_CASES_THEN MP_TAC o HolLight.MATCH_MP LEMMA_2_0) THENL
     [ASM_MESON_TAC [IN], REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN
    SPEC_TAC ([[N:(A)multiset]], [[N:(A)multiset]]) THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    MATCH_MP_TAC MULTISET_INDUCT THEN REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [MUNION_ASSOC, MMEMBER_MUNION, MMEMBER_MSING]) THEN
    ASM_MESON_TAC [IN, MUNION_EMPTY])
  : ExceptT String IO thm).run
#eval LEMMA_2_1

#eval phrase 40
unsafe def LEMMA_2_2 : thm := keep "LEMMA_2_2" fun _ => (do
  prove ([[(!M b. b << a /\ M IN WFP(morder(<<))
          ==> (M munion (msing b)) IN WFP(morder(<<)))
   ==> !M. M IN WFP(morder(<<)) ==> (M munion (msing a)) IN WFP(morder(<<))]])
   (STRIP_TAC THEN MATCH_MP_TAC WFP_PART_INDUCT THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LEMMA_2_1 THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval LEMMA_2_2

#eval phrase 41
unsafe def LEMMA_2_3 : thm := keep "LEMMA_2_3" fun _ => (do
  prove ([[WF(<<)
   ==> !a M. M IN WFP(morder(<<)) ==> (M munion (msing a)) IN WFP(morder(<<))]])
   (REWRITE_TAC [WF_IND] THEN DISCH_THEN MATCH_MP_TAC THEN MESON_TAC [LEMMA_2_2])
  : ExceptT String IO thm).run
#eval LEMMA_2_3

#eval phrase 42
unsafe def LEMMA_2_4 : thm := keep "LEMMA_2_4" fun _ => (do
  prove ([[WF(<<) ==> !M. M IN WFP(morder(<<))]])
   (DISCH_TAC THEN MATCH_MP_TAC MULTISET_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC [IN] THEN MATCH_MP_TAC WFP_RULES THEN
      REWRITE_TAC [morder, MUNION_MEMPTY],
      ASM_SIMP_TAC [LEMMA_2_3]])
  : ExceptT String IO thm).run
#eval LEMMA_2_4

/- ------------------------------------------------------------------------- -/
/- Hence the final result.                                                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 43
unsafe def MORDER_WF : thm := keep "MORDER_WF" fun _ => (do
  prove ([[WF(<<) ==> WF(morder(<<))]])
   (SIMP_TAC [WFP_WF, EXTENSION, IN_UNIV, LEMMA_2_4])
  : ExceptT String IO thm).run
#eval MORDER_WF

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolExamples.MultiWf" do
  replay (
          EMPTY_IS_FINITE)
  replay (
          SING_IS_FINITE)
  replay (
          UNION_NONZERO)
  replay (
          parse_as_infix ("mmember", (11, "right")))
  replay (
          parse_as_infix ("munion", (16, "right")))
  replay (
          parse_as_infix ("mdiff", (18, "left")))
  replay (
          multiset_tybij_th)
  replay (
          multiset_tybij)
  replay (
          mempty)
  replay (
          mmember)
  replay (
          msing)
  replay (
          munion)
  replay (
          mdiff)
  replay (
          MEXTENSION)
  replay (
          MULTIPLICITY_MULTISET)
  replay (
          MEMPTY)
  replay (
          MSING)
  replay (
          MUNION)
  replay (
          MDIFF)
  replay (
          MUNION_MEMPTY)
  replay (
          MMEMBER_MUNION)
  replay (
          MMEMBER_MSING)
  replay (
          MUNION_EMPTY)
  replay (
          MUNION_ASSOC)
  replay (
          MUNION_AC)
  replay (
          MUNION_11)
  replay (
          MUNION_INUNION)
  replay (
          MMEMBER_MDIFF)
  replay (
          MULTISET_INDUCT_LEMMA1)
  replay (
          MULTISET_INDUCT_LEMMA2)
  replay (
          MULTISET_INDUCT)
  replay (
          parse_as_infix ("<<", (12, "right")))
  replay (
          (do IO.println (← HolCore.Printer.string_of_thm WFP_RULES)
              IO.println (← HolCore.Printer.string_of_thm WFP_INDUCT)
              IO.println (← HolCore.Printer.string_of_thm WFP_CASES) : IO Unit))
  replay (
          WFP_PART_INDUCT)
  replay (
          WFP_WF)
  replay (
          WFP_DCHAIN)
  replay (
          morder)
  replay (
          LEMMA_2_0)
  replay (
          LEMMA_2_1)
  replay (
          LEMMA_2_2)
  replay (
          LEMMA_2_3)
  replay (
          LEMMA_2_4)
  replay (
          MORDER_WF)
-- @@ENSURE END

end HolExamples.MultiWf
