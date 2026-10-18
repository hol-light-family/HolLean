/- File: HolLogicArith/Fol.lean
Translation of HOL Light's Logic/fol.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Common
import HolExamples.Reduct
import HolExamples.MultiWf
open HolCore.Kernel Session HolLight.Syntax HolLogicArith
open scoped HolLight

namespace HolLogicArith.Fol

/- The list definitions and theorems used below are exposed by Session as
   fields of the `listDefs`/`listThms1` bundles; alias the ones we need. -/
private unsafe def MAP : thm := Session.listDefs.MAP
private unsafe def ALL : thm := Session.listDefs.ALL
private unsafe def MEM : thm := Session.listDefs.MEM
private unsafe def EX : thm := Session.listDefs.EX
private unsafe def APPEND : thm := Session.listDefs.APPEND
private unsafe def LENGTH : thm := Session.listDefs.LENGTH
private unsafe def MAP_EQ : thm := Session.listThms1.MAP_EQ
private unsafe def MAP_EQ_DEGEN : thm := Session.listThms1.MAP_EQ_DEGEN
private unsafe def MEM_MAP : thm := Session.listThms1.MEM_MAP
private unsafe def MAP_o : thm := Session.listThms1.MAP_o
private unsafe def ALL_MAP : thm := Session.listThms1.ALL_MAP
private unsafe def ALL_IMP : thm := Session.listThms1.ALL_IMP
private unsafe def ALL_MEM : thm := Session.listThms1.ALL_MEM
private unsafe def EX_MEM : thm := Session.listThms1.EX_MEM
private unsafe def LENGTH_MAP : thm := Session.listThms1.LENGTH_MAP
private unsafe def CONS_11 : thm := Session.listThms1.CONS_11
private unsafe def ALL_T : thm := Session.listThms1.ALL_T

-- What Logic/make.ml loads before fol.ml.
#eval SessionLibrary.Analysis.ensureAnalysis
#eval SessionLibrary.Wo.ensureWo
#eval SessionLibrary.RSTC.ensureRSTC
#eval HolExamples.Reduct.ensure
#eval HolExamples.MultiWf.ensure

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- Run `define_type`, panicking with HOL Light's message on failure (as the
   toplevel throws). -/
private unsafe def defType (s : String) : thm × thm :=
  match unsafeIO (Session.define_type s) with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! s!"define_type: {e}"
  | .error e => panic! s!"define_type IO: {e}"

/- `new_recursive_definition` lifted into `ExceptT String IO`. -/
private unsafe def newRec (ax : thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (Session.new_recursive_definition ax tm)

#eval phrase 1
-- let EXPAND_TAC s = FIRST_ASSUM(SUBST1_TAC o SYM o
--   check((=) s o fst o dest_var o rhs o concl)) THEN BETA_TAC;;
unsafe def EXPAND_TAC (s : String) : HolCore.Tactics.tactic :=
  FIRST_ASSUM (fun th => HolLight.tactic_of do
    let th' ← liftExcept (do
      let _ ← HolCore.Lib.check
        (fun t => s == t)
        (← (do let (nm, _) ← HolCore.Kernel.dest_var (← HolCore.Equal.rhs (concl th)); pure nm))
      HolCore.Equal.SYM th)
    pure (SUBST1_TAC th'))
  THEN BETA_TAC
#eval IO.println "<fun>"

#eval phrase 2
unsafe def LIST_UNION : thm := keep "LIST_UNION" fun _ => (do
  newRec Session.list_RECURSION
    [[(LIST_UNION [] = {}) /\
      (LIST_UNION (CONS h t) = h UNION (LIST_UNION t))]]
  : ExceptT String IO thm).run
#eval LIST_UNION

#eval phrase 3
unsafe def LIST_UNION_FINITE : thm := keep "LIST_UNION_FINITE" fun _ => (do
  prove ([[!l. ALL FINITE l ==> FINITE(LIST_UNION l)]])
   (LIST_INDUCT_TAC THEN REWRITE_TAC [LIST_UNION, FINITE_RULES] THEN
    REWRITE_TAC [FINITE_UNION, ALL] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval LIST_UNION_FINITE

#eval phrase 4
unsafe def IN_LIST_UNION : thm := keep "IN_LIST_UNION" fun _ => (do
  prove ([[!x l. x IN (LIST_UNION l) <=> EX (\s. x IN s) l]])
   (GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [LIST_UNION, EX, NOT_IN_EMPTY, IN_UNION])
  : ExceptT String IO thm).run
#eval IN_LIST_UNION

#eval phrase 5
unsafe def LIST_UNION_APPEND : thm := keep "LIST_UNION_APPEND" fun _ => (do
  prove ([[!l1 l2. LIST_UNION(APPEND l1 l2) = (LIST_UNION l1) UNION (LIST_UNION l2)]])
   (LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [LIST_UNION, APPEND, UNION_EMPTY, (← HolLight.GSYM UNION_ASSOC)])
  : ExceptT String IO thm).run
#eval LIST_UNION_APPEND

#eval phrase 6
unsafe def term_raw : thm × thm := keep "term_raw" fun _ =>
  defType "term = V num | Fn num (term list)"
unsafe def term_raw_INDUCT : thm := term_raw.1
unsafe def term_raw_RECURSION : thm := term_raw.2
#eval do IO.println term_raw_INDUCT; IO.println term_raw_RECURSION

#eval phrase 7
unsafe def term_INDUCT : thm := keep "term_INDUCT" fun _ => (do
  prove ([[!P. (!v. P(V v)) /\ (!s l. ALL P l ==> P(Fn s l)) ==> !t. P t]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[P:term->bool]], [[ALL(P:term->bool)]] ] term_raw_INDUCT)) THEN
    ASM_SIMP_TAC [ALL])
  : ExceptT String IO thm).run
#eval term_INDUCT

#eval phrase 8
unsafe def term_RECURSION : thm := keep "term_RECURSION" fun _ => (do
  prove ([[!f h. ?fn:term->Z.
        (!v. fn(V v) = f v) /\
        (!s l. fn(Fn s l) = h s l (MAP fn l))]])
   (REPEAT GEN_TAC THEN
    MP_TAC (← ExceptT.mk (HolLight.ISPECL [ [[f:num->Z]], [[h:num->(term)list->(Z)list->Z]],
                 [[[]:(Z)list]], [[\(x:term) (y:term list) (z:Z) (w:Z list).
                                CONS z w]] ] term_raw_RECURSION)) THEN
    REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[mf:(term)list->(Z)list]])
          (X_CHOOSE_THEN ([[fn:term ->Z]]) STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC [[fn:term ->Z]] THEN ASM_REWRITE_TAC [] THEN
    GEN_TAC THEN X_GEN_TAC [[l:term list]] THEN AP_TERM_TAC THEN
    SPEC_TAC ([[l:term list]], [[l:term list]]) THEN
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP])
  : ExceptT String IO thm).run
#eval term_RECURSION

#eval phrase 9
-- let new_nested_recursive_definition ax tm = ...
unsafe def new_nested_recursive_definition (ax : thm) (tm : term) :
    ExceptT String IO thm := do
  let expat ← liftExcept (HolCore.Equal.lhand (Prod.snd (HolCore.Basics.strip_forall (← liftExcept (HolCore.Lib.hd (HolCore.Basics.conjuncts tm))))))
  let (ev, allargs) := HolCore.Basics.strip_comb expat
  let pargs ← liftExcept (HolCore.Lib.butlast allargs)
  let tm' ← liftExcept (do HolCore.Bool.mk_exists ev (← HolCore.Bool.list_mk_forall pargs tm))
  let rawprover := Session.prove_recursive_functions_exist ax
  let eth ← prove tm'
    (HolLight.tactic_of do
      let skolem ← HolLight.GSYM Session.SKOLEM_THM
      pure (REWRITE_TAC [skolem] THEN
        REPEAT GEN_TAC THEN
        HolCore.Lib.W (fun g => HolLight.tactic_of do
            let (_, bod) ← liftExcept (HolCore.Basics.dest_exists (HolLight.snd g))
            let th ← ExceptT.mk (rawprover bod)
            pure (ACCEPT_TAC th))))
  let (evname, _) ← liftExcept (HolCore.Kernel.dest_var ev)
  ExceptT.mk (do
    match ← Session.new_specification [evname] eth with
    | .error e => pure (.error e)
    | .ok sth => (HolLight.SPECL pargs sth).run)
#eval IO.println "<fun>"

#eval phrase 10
unsafe def term_INJ : thm := keep "term_INJ" fun _ =>
  (ExceptT.mk (Session.prove_constructors_injective term_RECURSION) : ExceptT String IO thm).run
#eval term_INJ

#eval phrase 11
unsafe def term_DISTINCT : thm := keep "term_DISTINCT" fun _ =>
  (ExceptT.mk (Session.prove_constructors_distinct term_RECURSION) : ExceptT String IO thm).run
#eval term_DISTINCT

#eval phrase 12
unsafe def term_CASES : thm := keep "term_CASES" fun _ =>
  (ExceptT.mk (Session.prove_cases_thm term_INDUCT) : ExceptT String IO thm).run
#eval term_CASES

#eval phrase 13
#eval parse_as_infix ("-->", (13, "right"))

#eval phrase 14
unsafe def form_pair : thm × thm := keep "form_pair" fun _ =>
  defType "form = False
                    | Atom num (term list)
                    | --> form form
                    | !! num form"
unsafe def form_INDUCTION : thm := form_pair.1
unsafe def form_RECURSION : thm := form_pair.2
#eval do IO.println form_INDUCTION; IO.println form_RECURSION

#eval phrase 15
unsafe def form_INJ : thm := keep "form_INJ" fun _ =>
  (ExceptT.mk (Session.prove_constructors_injective form_RECURSION) : ExceptT String IO thm).run
#eval form_INJ

#eval phrase 16
unsafe def form_DISTINCT : thm := keep "form_DISTINCT" fun _ =>
  (ExceptT.mk (Session.prove_constructors_distinct form_RECURSION) : ExceptT String IO thm).run
#eval form_DISTINCT

#eval phrase 17
unsafe def form_CASES : thm := keep "form_CASES" fun _ =>
  (ExceptT.mk (Session.prove_cases_thm form_INDUCTION) : ExceptT String IO thm).run
#eval form_CASES

#eval phrase 18
#eval parse_as_infix ("&&", (16, "right"))

#eval phrase 19
#eval parse_as_infix ("||", (14, "right"))

#eval phrase 20
#eval parse_as_infix ("<->", (12, "right"))

#eval phrase 21
unsafe def Not_DEF : thm := keep "Not_DEF" fun _ => new_definition
  [[Not p = p --> False]]
#eval Not_DEF

#eval phrase 22
unsafe def True_DEF : thm := keep "True_DEF" fun _ => new_definition
  [[True = Not False]]
#eval True_DEF

#eval phrase 23
unsafe def Or_DEF : thm := keep "Or_DEF" fun _ => new_definition
  [[p || q = (p --> q) --> q]]
#eval Or_DEF

#eval phrase 24
unsafe def And_DEF : thm := keep "And_DEF" fun _ => new_definition
  [[p && q = Not (Not p || Not q)]]
#eval And_DEF

#eval phrase 25
unsafe def Iff_DEF : thm := keep "Iff_DEF" fun _ => new_definition
  [[(p <-> q) = (p --> q) && (q --> p)]]
#eval Iff_DEF

#eval phrase 26
unsafe def Exists_DEF : thm := keep "Exists_DEF" fun _ => new_definition
  [[?? x p = Not(!!x (Not p))]]
#eval Exists_DEF

#eval phrase 27
unsafe def functions_term : thm := keep "functions_term" fun _ => (do
  newRec term_RECURSION
    [[(!v. functions_term (V v) = {}) /\
      (!f l. functions_term (Fn f l) =
           (f,LENGTH l) INSERT (LIST_UNION (MAP functions_term l)))]]
  : ExceptT String IO thm).run
#eval functions_term

#eval phrase 28
unsafe def functions_form : thm := keep "functions_form" fun _ => (do
  newRec form_RECURSION
    [[(functions_form False = {}) /\
      (functions_form (Atom a l) = LIST_UNION (MAP functions_term l)) /\
      (functions_form (p --> q) = (functions_form p) UNION (functions_form q)) /\
      (functions_form (!! x p) = functions_form p)]]
  : ExceptT String IO thm).run
#eval functions_form

#eval phrase 29
unsafe def predicates_form : thm := keep "predicates_form" fun _ => (do
  newRec form_RECURSION
    [[(predicates_form False = {}) /\
      (predicates_form (Atom a l) = {(a,LENGTH l)}) /\
      (predicates_form (p --> q) =
           (predicates_form p) UNION (predicates_form q)) /\
      (predicates_form (!! x p) = predicates_form p)]]
  : ExceptT String IO thm).run
#eval predicates_form

#eval phrase 30
unsafe def functions : thm := keep "functions" fun _ => new_definition
  [[functions fms = UNIONS {functions_form f | f IN fms}]]
#eval functions

#eval phrase 31
unsafe def predicates : thm := keep "predicates" fun _ => new_definition
  [[predicates fms = UNIONS {predicates_form f | f IN fms}]]
#eval predicates

#eval phrase 32
unsafe def language : thm := keep "language" fun _ => new_definition
  [[language fms = functions fms, predicates fms]]
#eval language

#eval phrase 33
unsafe def FUNCTIONS_SING : thm := keep "FUNCTIONS_SING" fun _ => (do
  prove ([[functions {p} = functions_form p]])
   (REWRITE_TAC [EXTENSION, IN_INSERT, NOT_IN_EMPTY,
                functions, IN_ELIM_THM, IN_UNIONS] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval FUNCTIONS_SING

#eval phrase 34
unsafe def LANGUAGE_1 : thm := keep "LANGUAGE_1" fun _ => (do
  prove ([[language {p} = functions_form p,predicates_form p]])
   (REWRITE_TAC [language, functions, predicates, PAIR_EQ] THEN
    CONJ_TAC THEN ONCE_REWRITE_TAC [EXTENSION] THEN
    REWRITE_TAC [IN_UNIONS, IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval LANGUAGE_1

#eval phrase 35
unsafe def Dom_DEF : thm := keep "Dom_DEF" fun _ => new_definition
  [[Dom (D:A->bool,Funs:num->(A list)->A,Preds:num->(A list)->bool) = D]]
#eval Dom_DEF

#eval phrase 36
unsafe def Fun_DEF : thm := keep "Fun_DEF" fun _ => new_definition
  [[Fun (D:A->bool,Funs:num->(A list)->A,Preds:num->(A list)->bool) = Funs]]
#eval Fun_DEF

#eval phrase 37
unsafe def Pred_DEF : thm := keep "Pred_DEF" fun _ => new_definition
  [[Pred (D:A->bool,Funs:num->(A list)->A,Preds:num->(A list)->bool) = Preds]]
#eval Pred_DEF

#eval phrase 38
unsafe def MODEL_EQ : thm := keep "MODEL_EQ" fun _ => (do
  prove ([[(M = M') <=> (Dom M = Dom M') /\ (Fun M = Fun M') /\ (Pred M = Pred M')]])
   (HolLight.tactic_of do
     let detrip ← prove ([[p = FST(p),FST(SND p),SND(SND p)]]) (REWRITE_TAC [])
     pure
      (ONCE_REWRITE_TAC [detrip] THEN PURE_REWRITE_TAC [PAIR_EQ, Dom_DEF, Fun_DEF, Pred_DEF] THEN
       REWRITE_TAC []))
  : ExceptT String IO thm).run
#eval MODEL_EQ

#eval phrase 39
unsafe def MODEL_DECOMP : thm := keep "MODEL_DECOMP" fun _ => (do
  prove ([[M = Dom M,Fun M,Pred M]])
   (REWRITE_TAC [MODEL_EQ] THEN REWRITE_TAC [Dom_DEF, Fun_DEF, Pred_DEF])
  : ExceptT String IO thm).run
#eval MODEL_DECOMP

#eval phrase 40
unsafe def FVT : thm := keep "FVT" fun _ => (do
  newRec term_RECURSION
    [[(!x. FVT (V x) = {x}) /\
      (!f l. FVT (Fn f l) = LIST_UNION (MAP FVT l))]]
  : ExceptT String IO thm).run
#eval FVT

#eval phrase 41
unsafe def FV : thm := keep "FV" fun _ => (do
  newRec form_RECURSION
    [[(FV False = {}) /\
      (!a l. FV (Atom a l) = LIST_UNION (MAP FVT l)) /\
      (!p q. FV (p --> q) = FV p UNION FV q) /\
      (!x p. FV (!! x p) = FV p DELETE x)]]
  : ExceptT String IO thm).run
#eval FV

#eval phrase 42
unsafe def BV : thm := keep "BV" fun _ => (do
  newRec form_RECURSION
    [[(BV False = {}) /\
      (!a l. BV (Atom a l) = {}) /\
      (!p q. BV (p --> q) = BV p UNION BV q) /\
      (!x p. BV (!! x p) = x INSERT BV p)]]
  : ExceptT String IO thm).run
#eval BV

#eval phrase 43
unsafe def FVT_FINITE : thm := keep "FVT_FINITE" fun _ => (do
  prove ([[!t. FINITE(FVT t)]])
   (MATCH_MP_TAC term_INDUCT THEN
    REWRITE_TAC [FVT, FINITE_RULES, FINITE_INSERT] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LIST_UNION_FINITE THEN
    ASM_REWRITE_TAC [ALL_MAP, o_DEF])
  : ExceptT String IO thm).run
#eval FVT_FINITE

#eval phrase 44
unsafe def FV_FINITE : thm := keep "FV_FINITE" fun _ => (do
  prove ([[!p. FINITE(FV p)]])
   (MATCH_MP_TAC form_INDUCTION THEN
    ASM_REWRITE_TAC [FV, FINITE_RULES, FINITE_UNION, FINITE_DELETE] THEN
    GEN_TAC THEN MATCH_MP_TAC LIST_UNION_FINITE THEN
    REWRITE_TAC [ALL_MAP, FVT_FINITE, o_DEF, ALL_T])
  : ExceptT String IO thm).run
#eval FV_FINITE

#eval phrase 45
unsafe def BV_FINITE : thm := keep "BV_FINITE" fun _ => (do
  prove ([[!p. FINITE(BV p)]])
   (MATCH_MP_TAC form_INDUCTION THEN
    ASM_REWRITE_TAC [BV, FINITE_RULES, FINITE_UNION, FINITE_INSERT])
  : ExceptT String IO thm).run
#eval BV_FINITE

#eval phrase 46
unsafe def FV_EXISTS : thm := keep "FV_EXISTS" fun _ => (do
  prove ([[FV(??x p) = FV(p) DELETE x]])
   (REWRITE_TAC [Exists_DEF, Not_DEF, FV] THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval FV_EXISTS

#eval phrase 47
unsafe def valmod : thm := keep "valmod" fun _ => new_definition
  [[valmod (x,a) v = \y. if y = x then a else v y]]
#eval valmod

#eval phrase 48
unsafe def VALMOD_CLAUSES : thm := keep "VALMOD_CLAUSES" fun _ => (do
  prove ([[(!v a k. valmod (k,a) v k = a) /\
   (!v a k x. ~(x = k) ==> (valmod (k,a) v x = v x))]])
   (REWRITE_TAC [valmod] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval VALMOD_CLAUSES

#eval phrase 49
unsafe def VALMOD_TRIV : thm := keep "VALMOD_TRIV" fun _ => (do
  prove ([[!v x. valmod (x,v x) v = v]])
   (REWRITE_TAC [valmod, FUN_EQ_THM] THEN
    REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval VALMOD_TRIV

#eval phrase 50
unsafe def VALMOD_VALMOD : thm := keep "VALMOD_VALMOD" fun _ => (do
  prove ([[!v a x b. valmod (x,a) (valmod (x,b) v) = valmod (x,a) v]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [valmod] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []))
  : ExceptT String IO thm).run
#eval VALMOD_VALMOD

#eval phrase 51
unsafe def valuation : thm := keep "valuation" fun _ => new_definition
  [[valuation(M) v <=> !x:num. v(x) IN Dom(M)]]
#eval valuation

#eval phrase 52
unsafe def VALUATION_VALMOD : thm := keep "VALUATION_VALMOD" fun _ => (do
  prove ([[!M a v. valuation(M) v /\ a IN Dom(M) ==> valuation(M) (valmod (x,a) v)]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [valuation, valmod] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval VALUATION_VALMOD

#eval phrase 53
unsafe def VALUATION_IS_VALMOD : thm := keep "VALUATION_IS_VALMOD" fun _ => (do
  prove ([[!v x. valmod(x,v x) v = v]])
   (REWRITE_TAC [valmod, FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval VALUATION_IS_VALMOD

#eval phrase 54
#eval parse_as_infix ("satisfies", (10, "right"))

#eval phrase 55
unsafe def termval : thm := keep "termval" fun _ => (do
  new_nested_recursive_definition term_RECURSION
    [[(!x. termval M v (V x) = v(x)) /\
      (!f l. termval M v (Fn f l) = Fun(M) f (MAP (termval M v) l))]]
  : ExceptT String IO thm).run
#eval termval

#eval phrase 56
unsafe def holds : thm := keep "holds" fun _ => (do
  newRec form_RECURSION
    [[(holds M v False <=> F) /\
      (!a l. holds M v (Atom a l) <=> Pred(M) a (MAP (termval M v) l)) /\
      (!p q. holds M v (p --> q) <=> holds M v p ==> holds M v q) /\
      (!x p. holds M v (!! x p) <=>
                   !a. a IN Dom(M) ==> holds M (valmod (x,a) v) p)]]
  : ExceptT String IO thm).run
#eval holds

#eval phrase 57
unsafe def hold : thm := keep "hold" fun _ => new_definition
  [[hold M v fms <=> !p. p IN fms ==> holds M v p]]
#eval hold

#eval phrase 58
unsafe def satisfies : thm := keep "satisfies" fun _ => new_definition
  [[M satisfies fms <=> !v p. valuation(M) v /\ p IN fms ==> holds M v p]]
#eval satisfies

#eval phrase 59
unsafe def SATISFIES_1 : thm := keep "SATISFIES_1" fun _ => (do
  prove ([[M satisfies {p} <=> !v. valuation(M) v ==> holds M v p]])
   (REWRITE_TAC [satisfies, IN_INSERT, NOT_IN_EMPTY] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval SATISFIES_1

#eval phrase 60
unsafe def HOLDS : thm := keep "HOLDS" fun _ => (do
  prove ([[(holds M v False <=> F) /\
   (holds M v True <=> T) /\
   (!a l. holds M v (Atom a l) <=> Pred(M) a (MAP (termval M v) l)) /\
   (!p. holds M v (Not p) <=> ~(holds M v p)) /\
   (!p q. holds M v (p || q) <=> holds M v p \/ holds M v q) /\
   (!p q. holds M v (p && q) <=> holds M v p /\ holds M v q) /\
   (!p q. holds M v (p --> q) <=> holds M v p ==> holds M v q) /\
   (!p q. holds M v (p <-> q) <=> (holds M v p = holds M v q)) /\
   (!x p. holds M v (!! x p) <=>
                !a. a IN Dom(M) ==> holds M (valmod (x,a) v) p) /\
   (!x p. holds M v (?? x p) <=>
                ?a. a IN Dom(M) /\ holds M (valmod (x,a) v) p)]])
   (REWRITE_TAC [Not_DEF, True_DEF, Or_DEF, And_DEF, Iff_DEF, Exists_DEF, holds] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval HOLDS

#eval phrase 61
unsafe def TERMVAL_VALUATION : thm := keep "TERMVAL_VALUATION" fun _ => (do
  prove ([[!M t (v:num->A) v'.
        (!x. x IN (FVT t) ==> (v'(x) = v(x)))
             ==> (termval M v' t = termval M v t)]])
   (HolLight.tactic_of do
     let lemma ← prove
      ([[!l t x. x IN FVT t /\ MEM t l
                ==>  x IN LIST_UNION (MAP FVT l)]])
      (LIST_INDUCT_TAC THEN REWRITE_TAC [MAP, LIST_UNION, IN_UNION, MEM] THEN
       ASM_MESON_TAC [])
     let exv ← HolCore.Parser.parse_term r"\t. !(v:num->A) v'.
                (!x. x IN FVT t ==> (v' x = v x))
                ==> (termval M v' t :A = termval M v t)"
     pure
      (GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
       REWRITE_TAC [FVT, termval] THEN CONJ_TAC THENL
        [REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN MESON_TAC [],
         GEN_TAC THEN LIST_INDUCT_TAC THEN
         REWRITE_TAC [ALL, LIST_UNION, MAP, IN_UNION] THEN
         REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [CONS_11] THEN
         CONJ_TAC THENL
          [FIRST_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
           FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
           MATCH_MP_TAC MAP_EQ THEN MATCH_MP_TAC ALL_IMP THEN
           EXISTS_TAC exv THEN
           ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [lemma]]]))
  : ExceptT String IO thm).run
#eval TERMVAL_VALUATION

#eval phrase 62
unsafe def HOLDS_VALUATION : thm := keep "HOLDS_VALUATION" fun _ => (do
  prove ([[!M p (v:num->A) v'.
      (!x. x IN (FV p) ==> (v'(x) = v(x)))
             ==> (holds M v' p <=> holds M v p)]])
   (GEN_TAC THEN MATCH_MP_TAC form_INDUCTION THEN
    REWRITE_TAC [FV, HOLDS, IN_UNION, IN_DELETE] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN X_GEN_TAC [[l:term list]] THEN
      REPEAT STRIP_TAC THEN AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN
      SPEC_TAC ([[l:term list]], [[l:term list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [MAP, LIST_UNION, IN_UNION] THEN
      ASM_MESON_TAC [TERMVAL_VALUATION],
      MESON_TAC [],
      X_GEN_TAC [[p:num]] THEN
      REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      X_GEN_TAC [[x:num]] THEN ASM_CASES_TAC [[x:num = p]] THEN
      ASM_REWRITE_TAC [valmod] THEN ASM_MESON_TAC []])
  : ExceptT String IO thm).run
#eval HOLDS_VALUATION

#eval phrase 63
unsafe def satisfiable : thm := keep "satisfiable" fun _ => new_definition
  [[satisfiable (U:A->bool) fms <=>
   ?M:(A->bool)#(num->A list->A)#(num->A list->bool).
        ~(Dom M = {}) /\ M satisfies fms]]
#eval satisfiable

#eval phrase 64
unsafe def valid : thm := keep "valid" fun _ => new_definition
  [[valid (U:A->bool) fms <=>
   !M:(A->bool)#(num->A list->A)#(num->A list->bool).
        M satisfies fms]]
#eval valid

#eval phrase 65
unsafe def entails : thm := keep "entails" fun _ => new_definition
  [[entails (U:A->bool) A p <=>
   !(M:(A->bool)#(num->A list->A)#(num->A list->bool)) v.
        hold M v A ==> holds M v p]]
#eval entails

#eval phrase 66
unsafe def equivalent : thm := keep "equivalent" fun _ => new_definition
  [[equivalent (U:A->bool) p q <=>
   !(M:(A->bool)#(num->A list->A)#(num->A list->bool)) v.
        holds M v p <=> holds M v q]]
#eval equivalent

#eval phrase 67
unsafe def interpretation : thm := keep "interpretation" fun _ => new_definition
  [[interpretation (fns:(num#num)->bool,preds:(num#num)->bool) M <=>
     !f l. (f,LENGTH l) IN fns /\ ALL (\x. x IN Dom(M)) l
           ==> (Fun(M) f l) IN Dom(M)]]
#eval interpretation

#eval phrase 68
unsafe def INTERPRETATION_TERMVAL : thm := keep "INTERPRETATION_TERMVAL" fun _ => (do
  prove ([[!any:num#num->bool M v t.
        interpretation (functions_term t,any) M /\
        valuation(M) v
        ==> termval M v t IN Dom(M)]])
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [interpretation] THEN
    MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC [termval] THEN CONJ_TAC THENL
     [REWRITE_TAC [valuation] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [],
      REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [LENGTH_MAP, functions_term, IN_INSERT] THEN
      REWRITE_TAC [ALL_MAP] THEN REWRITE_TAC [o_DEF] THEN
      MATCH_MP_TAC ALL_IMP THEN
      FIRST_ASSUM (EXISTS_TAC o HolCore.Equal.lhand o concl) THEN
      ASM_REWRITE_TAC [] THEN GEN_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC) THEN
      REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [functions_term] THEN
      REWRITE_TAC [IN_INSERT] THEN DISJ2_TAC THEN
      UNDISCH_TAC [[MEM (x:term) l]] THEN
      SPEC_TAC ([[l:term list]], [[l:term list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [MEM] THEN
      REWRITE_TAC [LIST_UNION, MAP, IN_UNION] THEN ASM_MESON_TAC []])
  : ExceptT String IO thm).run
#eval INTERPRETATION_TERMVAL

#eval phrase 69
unsafe def INTERPRETATION_SUBLANGUAGE : thm := keep "INTERPRETATION_SUBLANGUAGE" fun _ => (do
  prove ([[!M funs1 funs2 preds1 preds2.
        funs2 SUBSET funs1
        ==> interpretation (funs1,preds1) M
            ==> interpretation (funs2,preds2) M]])
   (GEN_TAC THEN REWRITE_TAC [interpretation, SUBSET] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval INTERPRETATION_SUBLANGUAGE

#eval phrase 70
unsafe def termsubst : thm := keep "termsubst" fun _ => (do
  new_nested_recursive_definition term_RECURSION
    [[(!x. termsubst v (V x) = v(x)) /\
      (!f l. termsubst v (Fn f l) = Fn f (MAP (termsubst v) l))]]
  : ExceptT String IO thm).run
#eval termsubst

#eval phrase 71
unsafe def TERMSUBST_TERMVAL : thm := keep "TERMSUBST_TERMVAL" fun _ => (do
  prove ([[!M. (Fun(M) = Fn) ==> !v t. termsubst v t = termval M v t]])
   (GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
    ASM_REWRITE_TAC [termsubst, termval] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval TERMSUBST_TERMVAL

#eval phrase 72
unsafe def TERMVAL_TRIV : thm := keep "TERMVAL_TRIV" fun _ => (do
  prove ([[!M. (Fun(M) = Fn) ==> !t. termval M V t = t]])
   (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC term_INDUCT THEN
    ASM_REWRITE_TAC [termval] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ_DEGEN THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval TERMVAL_TRIV

#eval phrase 73
unsafe def TERMVAL_TERMSUBST : thm := keep "TERMVAL_TERMSUBST" fun _ => (do
  prove ([[!M v i t. termval M v (termsubst i t) = termval M (termval M v o i) t]])
   (GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC [termval, termsubst, o_THM] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [(← HolLight.GSYM MAP_o)] THEN
    MATCH_MP_TAC MAP_EQ THEN ASM_REWRITE_TAC [o_THM])
  : ExceptT String IO thm).run
#eval TERMVAL_TERMSUBST

#eval phrase 74
unsafe def TERMSUBST_TERMSUBST : thm := keep "TERMSUBST_TERMSUBST" fun _ => (do
  prove ([[!i j t. termsubst j (termsubst i t) = termsubst (termsubst j o i) t]])
   (GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
    REWRITE_TAC [termsubst, o_THM] THEN REWRITE_TAC [(← HolLight.GSYM MAP_o)] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MAP_EQ THEN ASM_REWRITE_TAC [o_THM])
  : ExceptT String IO thm).run
#eval TERMSUBST_TERMSUBST

#eval phrase 75
unsafe def TERMSUBST_TRIV : thm := keep "TERMSUBST_TRIV" fun _ => (do
  prove ([[!t. termsubst V t = t]])
   (MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC [termsubst] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MAP_EQ_DEGEN THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval TERMSUBST_TRIV

#eval phrase 76
unsafe def TERMSUBST_VALUATION : thm := keep "TERMSUBST_VALUATION" fun _ => (do
  prove ([[!t v v'. (!x. x IN (FVT t) ==> (v'(x) = v(x)))
            ==> (termsubst v' t = termsubst v t)]])
   (HolLight.tactic_of do
     let th0 ← ExceptT.mk (HolLight.ISPEC ([[Dom(a,Fn,b),Fn,Pred(a,Fn,b)]]) TERMSUBST_TERMVAL)
     pure
      (MP_TAC th0 THEN
       REWRITE_TAC [Fun_DEF] THEN DISCH_THEN (fun th => REWRITE_TAC [th]) THEN
       REWRITE_TAC [TERMVAL_VALUATION]))
  : ExceptT String IO thm).run
#eval TERMSUBST_VALUATION

#eval phrase 77
unsafe def TERMSUBST_FVT : thm := keep "TERMSUBST_FVT" fun _ => (do
  prove ([[!t i. FVT(termsubst i t) = {x | ?y. y IN FVT(t) /\ x IN FVT(i y)}]])
   (HolLight.tactic_of do
     let lemma1 ← prove
      ([[{x | ?y. y IN (s UNION t) /\ P x y} =
         {x | ?y. y IN s /\ P x y} UNION {x | ?y. y IN t /\ P x y}]])
      (REWRITE_TAC [EXTENSION, IN_UNION, IN_ELIM_THM] THEN MESON_TAC [])
     pure
      (MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC [FVT, termsubst] THEN
       CONJ_TAC THENL
        [REWRITE_TAC [IN_INSERT, IN_ELIM_THM, NOT_IN_EMPTY, EXTENSION] THEN
         MESON_TAC [],
         LIST_INDUCT_TAC THEN REWRITE_TAC [MAP, LIST_UNION] THENL
          [REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, SUBSET, IN_ELIM_THM], ALL_TAC] THEN
         REWRITE_TAC [ALL] THEN STRIP_TAC THEN X_GEN_TAC [[i:num->term]] THEN
         REWRITE_TAC [lemma1] THEN BINOP_TAC THEN ASM_REWRITE_TAC [] THEN
         SPEC_TAC ([[i:num->term]], [[i:num->term]]) THEN
         FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []]))
  : ExceptT String IO thm).run
#eval TERMSUBST_FVT

#eval phrase 78
unsafe def MAX_SYM : thm := keep "MAX_SYM" fun _ => (do
  prove ([[!x y. MAX x y = MAX y x]])
   (ARITH_TAC)
  : ExceptT String IO thm).run
#eval MAX_SYM

#eval phrase 79
unsafe def MAX_ASSOC : thm := keep "MAX_ASSOC" fun _ => (do
  prove ([[!x y z. MAX x (MAX y z) = MAX (MAX x y) z]])
   (ARITH_TAC)
  : ExceptT String IO thm).run
#eval MAX_ASSOC

#eval phrase 80
unsafe def SETMAX : thm := keep "SETMAX" fun _ => new_definition
  [[SETMAX s = ITSET MAX s 0]]
#eval SETMAX

#eval phrase 81
unsafe def VARIANT : thm := keep "VARIANT" fun _ => new_definition
  [[VARIANT s = SETMAX s + 1]]
#eval VARIANT

#eval phrase 82
unsafe def SETMAX_LEMMA : thm := keep "SETMAX_LEMMA" fun _ => (do
  prove ([[(SETMAX {} = 0) /\
   (!x s. FINITE s ==>
           (SETMAX (x INSERT s) = if x IN s then SETMAX s
                                  else MAX x (SETMAX s)))]])
   (REWRITE_TAC [SETMAX] THEN MATCH_MP_TAC FINITE_RECURSION THEN
    REWRITE_TAC [MAX] THEN REPEAT GEN_TAC THEN
    MAP_EVERY ASM_CASES_TAC
     [ [[x:num <= s]], [[y:num <= s]], [[x:num <= y]], [[y <= x]] ] THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [LE_CASES, LE_TRANS, LE_ANTISYM])
  : ExceptT String IO thm).run
#eval SETMAX_LEMMA

#eval phrase 83
unsafe def SETMAX_MEMBER : thm := keep "SETMAX_MEMBER" fun _ => (do
  prove ([[!s. FINITE s ==> !x. x IN s ==> x <= SETMAX s]])
   (MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC [NOT_IN_EMPTY, IN_INSERT] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC [SETMAX_LEMMA] THEN
    ASM_REWRITE_TAC [MAX] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [LE_REFL] THEN
    ASM_MESON_TAC [LE_CASES, LE_TRANS])
  : ExceptT String IO thm).run
#eval SETMAX_MEMBER

#eval phrase 84
unsafe def SETMAX_THM : thm := keep "SETMAX_THM" fun _ => (do
  prove ([[(SETMAX {} = 0) /\
   (!x s. FINITE s ==>
           (SETMAX (x INSERT s) = MAX x (SETMAX s)))]])
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [SETMAX_LEMMA] THEN
    COND_CASES_TAC THEN REWRITE_TAC [MAX] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC [SETMAX_MEMBER])
  : ExceptT String IO thm).run
#eval SETMAX_THM

#eval phrase 85
unsafe def SETMAX_UNION : thm := keep "SETMAX_UNION" fun _ => (do
  prove ([[!s t. FINITE(s UNION t)
         ==> (SETMAX(s UNION t) = MAX (SETMAX s) (SETMAX t))]])
   (HolLight.tactic_of do
     let lemma ← prove ([[(x INSERT s) UNION t = x INSERT (s UNION t)]]) (SET_TAC [])
     pure
      (SUBGOAL_THEN ([[!t. FINITE(t) ==> !s. FINITE(s) ==>
                          (SETMAX(s UNION t) = MAX (SETMAX s) (SETMAX t))]])
        (fun th => MESON_TAC [th, FINITE_UNION]) THEN
       GEN_TAC THEN DISCH_TAC THEN
       MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
       REWRITE_TAC [UNION_EMPTY, SETMAX_THM] THEN CONJ_TAC THENL
        [REWRITE_TAC [MAX, LE_0], ALL_TAC] THEN
       REPEAT STRIP_TAC THEN REWRITE_TAC [lemma] THEN
       ASM_SIMP_TAC [SETMAX_THM, FINITE_UNION] THEN
       REWRITE_TAC [MAX_ASSOC]))
  : ExceptT String IO thm).run
#eval SETMAX_UNION

#eval phrase 86
unsafe def VARIANT_FINITE : thm := keep "VARIANT_FINITE" fun _ => (do
  prove ([[!s:num->bool. FINITE(s) ==> ~(VARIANT(s) IN s)]])
   (HolLight.tactic_of do
     let ar ← ExceptT.mk (ARITH_RULE [[~(x + 1 <= x)]])
     pure
      (REWRITE_TAC [VARIANT] THEN
       MESON_TAC [SETMAX_MEMBER, ar]))
  : ExceptT String IO thm).run
#eval VARIANT_FINITE

#eval phrase 87
unsafe def VARIANT_THM : thm := keep "VARIANT_THM" fun _ => (do
  prove ([[!p. ~(VARIANT(FV p) IN FV(p))]])
   (GEN_TAC THEN MATCH_MP_TAC VARIANT_FINITE THEN REWRITE_TAC [FV_FINITE])
  : ExceptT String IO thm).run
#eval VARIANT_THM

#eval phrase 88
unsafe def formsubst : thm := keep "formsubst" fun _ => (do
  newRec form_RECURSION
    [[(formsubst v False = False) /\
      (formsubst v (Atom p l) = Atom p (MAP (termsubst v) l)) /\
      (formsubst v (q --> r) = (formsubst v q --> formsubst v r)) /\
      (formsubst v (!!x q) =
           let v' = valmod (x,V x) v in
           let z = if ?y. y IN FV(!!x q) /\ x IN FVT(v'(y))
                   then VARIANT(FV(formsubst v' q)) else x in
           !!z (formsubst (valmod (x,V(z)) v) q))]]
  : ExceptT String IO thm).run
#eval formsubst

#eval phrase 89
unsafe def FORMSUBST_TRIV : thm := keep "FORMSUBST_TRIV" fun _ => (do
  prove ([[!p. formsubst V p = p]])
   (MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC [formsubst] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ_DEGEN THEN
      REWRITE_TAC [TERMSUBST_TRIV, ALL_T],
      REWRITE_TAC [VALMOD_TRIV, LET_DEF, LET_END_DEF] THEN
      REWRITE_TAC [FVT, IN_INSERT, NOT_IN_EMPTY, FV, IN_DELETE] THEN
      REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC), EQ_SYM_EQ, (← ExceptT.mk (TAUT [[~(~p /\ p)]]))] THEN
      ASM_REWRITE_TAC [VALMOD_TRIV]])
  : ExceptT String IO thm).run
#eval FORMSUBST_TRIV

#eval phrase 90
unsafe def FORMSUBST_VALUATION : thm := keep "FORMSUBST_VALUATION" fun _ => (do
  prove ([[!p v v'. (!x. x IN (FV p) ==> (v'(x) = v(x)))
            ==> (formsubst v' p = formsubst v p)]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)]])
     pure
      (MATCH_MP_TAC form_INDUCTION THEN
       REWRITE_TAC [FV, formsubst, IN_UNION, IN_DELETE] THEN
       REPEAT CONJ_TAC THENL
        [GEN_TAC THEN X_GEN_TAC [[l:term list]] THEN
         REPEAT STRIP_TAC THEN AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN
         SPEC_TAC ([[l:term list]], [[l:term list]]) THEN
         LIST_INDUCT_TAC THEN REWRITE_TAC [MAP, LIST_UNION, IN_UNION] THEN
         ASM_MESON_TAC [TERMSUBST_VALUATION],
         MESON_TAC [],
         X_GEN_TAC [[p:num]] THEN REPEAT STRIP_TAC THEN
         REWRITE_TAC [LET_DEF, LET_END_DEF] THEN
         SUBGOAL_THEN
          ([[(?y. (y IN FV a1 /\ ~(y = p)) /\ p IN FVT (valmod (p,V p) v' y)) <=>
           (?y. (y IN FV a1 /\ ~(y = p)) /\ p IN FVT (valmod (p,V p) v y))]])
         SUBST1_TAC THENL
          [AP_TERM_TAC THEN ABS_TAC THEN
           MATCH_MP_TAC taut1 THEN
           DISCH_THEN (ANTE_RES_THEN ASSUME_TAC) THEN
           REWRITE_TAC [valmod] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [],
           ALL_TAC] THEN
         COND_CASES_TAC THEN ASM_REWRITE_TAC [VALMOD_VALMOD] THENL
          [BINOP_TAC THENL
            [AP_TERM_TAC THEN AP_TERM_TAC THEN
             FIRST_ASSUM MATCH_MP_TAC THEN
             GEN_TAC THEN REWRITE_TAC [valmod] THEN
             COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [],
             FIRST_ASSUM MATCH_MP_TAC THEN
             X_GEN_TAC [[x:num]] THEN DISCH_TAC THEN
             REWRITE_TAC [valmod] THEN
             COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
              [ALL_TAC, ASM_MESON_TAC []] THEN
             AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
             FIRST_ASSUM MATCH_MP_TAC THEN
             X_GEN_TAC [[y:num]] THEN REWRITE_TAC [] THEN
             COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
             ASM_MESON_TAC []],
           AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
           GEN_TAC THEN REWRITE_TAC [valmod] THEN
           COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
           ASM_MESON_TAC []]]))
  : ExceptT String IO thm).run
#eval FORMSUBST_VALUATION

#eval phrase 91
unsafe def FORMSUBST_FV : thm := keep "FORMSUBST_FV" fun _ => (do
  prove ([[!p i. FV(formsubst i p) = {x | ?y. y IN FV(p) /\ x IN FVT(i y)}]])
   (HolLight.tactic_of do
     let _lemma1 ← prove
      ([[{x | ?y. y IN (s UNION t) /\ P x y} =
         {x | ?y. y IN s /\ P x y} UNION {x | ?y. y IN t /\ P x y}]])
      (REWRITE_TAC [EXTENSION, IN_UNION, IN_ELIM_THM] THEN MESON_TAC [])
     pure
      (MATCH_MP_TAC form_INDUCTION THEN
       REWRITE_TAC [formsubst, FV] THEN REPEAT CONJ_TAC THENL
        [REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, IN_ELIM_THM],
         REWRITE_TAC [(← HolLight.GSYM MAP_o), o_DEF, TERMSUBST_FVT] THEN
         LIST_INDUCT_TAC THEN REWRITE_TAC [LIST_UNION, MAP] THEN
         ASM_REWRITE_TAC [] THEN
         REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY, IN_UNION] THEN
         MESON_TAC [],
         REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
         REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY, IN_UNION] THEN
         MESON_TAC [],
         REPEAT STRIP_TAC THEN REWRITE_TAC [LET_DEF, LET_END_DEF] THEN
         COND_CASES_TAC THEN REWRITE_TAC [FV, VALMOD_VALMOD] THENL
          [MP_TAC (← ExceptT.mk (HolLight.SPEC ([[formsubst (valmod (a0,V a0) i) a1]]) VARIANT_THM)) THEN
           ABBREV_TAC [[a0' = VARIANT (FV (formsubst (valmod (a0,V a0) i) a1))]],
           ALL_TAC] THEN
         ASM_REWRITE_TAC [] THEN
         REWRITE_TAC [EXTENSION, IN_DELETE, IN_ELIM_THM] THEN
         REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
         REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
         FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [NOT_EXISTS_THM]) THEN
         DISCH_THEN (MP_TAC o HolLight.SPEC [[y:num]]) THEN
         REWRITE_TAC [valmod] THEN COND_CASES_TAC THEN
         ASM_REWRITE_TAC [FVT, IN_INSERT, NOT_IN_EMPTY, IN_DELETE] THEN
         MESON_TAC []]))
  : ExceptT String IO thm).run
#eval FORMSUBST_FV

#eval phrase 92
unsafe def HOLDS_FORMSUBST : thm := keep "HOLDS_FORMSUBST" fun _ => (do
  prove ([[!p i v. holds M (v:num->A) (formsubst i p) <=>
           holds M (termval M v o i) p]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[(a ==> (b <=> c)) ==> (a ==> b <=> a ==> c)]])
     pure
      (MATCH_MP_TAC form_INDUCTION THEN
       ASM_REWRITE_TAC [formsubst, holds] THEN
       REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
        [AP_TERM_TAC THEN REWRITE_TAC [(← HolLight.GSYM MAP_o)] THEN MATCH_MP_TAC MAP_EQ THEN
         REWRITE_TAC [o_THM, TERMVAL_TERMSUBST, ALL_T], ALL_TAC] THEN
       REWRITE_TAC [LET_DEF, LET_END_DEF, HOLDS] THEN
       AP_TERM_TAC THEN ABS_TAC THEN
       MATCH_MP_TAC taut1 THEN
       DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [VALMOD_VALMOD] THEN
       MATCH_MP_TAC HOLDS_VALUATION THEN
       X_GEN_TAC [[x:num]] THEN DISCH_TAC THEN
       REWRITE_TAC [o_THM, valmod] THEN
       (COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [(← HolLight.GSYM valmod)] THENL
        [REWRITE_TAC [termval, valmod], ALL_TAC]) THEN
       MATCH_MP_TAC TERMVAL_VALUATION THEN
       X_GEN_TAC [[y:num]] THEN DISCH_TAC THEN
       ONCE_REWRITE_TAC [valmod] THEN ASM_REWRITE_TAC [] THEN
       COND_CASES_TAC THEN REWRITE_TAC [] THENL
        [FIRST_X_ASSUM (ASSUME_TAC o HolLight.SYM) THEN
         SUBGOAL_THEN ([[~(y IN FV(formsubst (valmod (a0,V a0) i) a1))]])
         MP_TAC THENL [EXPAND_TAC "y" THEN REWRITE_TAC [VARIANT_THM], ALL_TAC] THEN
         REWRITE_TAC [FORMSUBST_FV] THEN REWRITE_TAC [IN_ELIM_THM] THEN
         REWRITE_TAC [NOT_EXISTS_THM] THEN
         DISCH_THEN (MP_TAC o HolLight.SPEC [[x:num]]) THEN
         ASM_REWRITE_TAC [] THEN
         REWRITE_TAC [valmod] THEN COND_CASES_TAC THEN
         ASM_REWRITE_TAC [FVT, IN_INSERT, NOT_IN_EMPTY] THEN ASM_MESON_TAC [],
         FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [NOT_EXISTS_THM]) THEN
         DISCH_THEN (MP_TAC o HolLight.SPEC [[x:num]]) THEN
         ASM_REWRITE_TAC [FV, IN_DELETE] THEN
         REWRITE_TAC [valmod] THEN COND_CASES_TAC THEN
         ASM_REWRITE_TAC [FVT, IN_INSERT, NOT_IN_EMPTY] THEN
         ASM_MESON_TAC []]))
  : ExceptT String IO thm).run
#eval HOLDS_FORMSUBST

#eval phrase 93
unsafe def HOLDS_FORMSUBST1 : thm := keep "HOLDS_FORMSUBST1" fun _ => (do
  prove ([[!x t p v. holds M (v:num->A) (formsubst (valmod (x,t) V) p) <=>
             holds M (valmod (x,termval M v t) v) p]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [HOLDS_FORMSUBST] THEN
    MATCH_MP_TAC HOLDS_VALUATION THEN
    X_GEN_TAC [[y:num]] THEN DISCH_TAC THEN
    REWRITE_TAC [valmod, o_THM] THEN
    COND_CASES_TAC THEN REWRITE_TAC [termval])
  : ExceptT String IO thm).run
#eval HOLDS_FORMSUBST1

#eval phrase 94
unsafe def HOLDS_RENAME : thm := keep "HOLDS_RENAME" fun _ => (do
  prove ([[!x y p v. holds M (v:num->A) (formsubst (valmod (x,V y) V) p) <=>
             holds M (valmod (x,v(y)) v) p]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [HOLDS_FORMSUBST1] THEN
    MATCH_MP_TAC HOLDS_VALUATION THEN REWRITE_TAC [termval])
  : ExceptT String IO thm).run
#eval HOLDS_RENAME

#eval phrase 95
unsafe def HOLDS_ALPHA_FORALL : thm := keep "HOLDS_ALPHA_FORALL" fun _ => (do
  prove ([[!x y p v. ~(y IN FV(!!x p))
             ==> (holds M v (!!y (formsubst (valmod (x,V y) V) p)) <=>
                  holds M (v:num->A) (!!x p))]])
   (REWRITE_TAC [FV, IN_DELETE] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [HOLDS, HOLDS_FORMSUBST] THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC HOLDS_VALUATION THEN
    GEN_TAC THEN REWRITE_TAC [valmod, termval, o_THM] THEN
    COND_CASES_TAC THEN REWRITE_TAC [valmod, termval] THEN
    COND_CASES_TAC THEN REWRITE_TAC [] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval HOLDS_ALPHA_FORALL

#eval phrase 96
unsafe def HOLDS_ALPHA_EXISTS : thm := keep "HOLDS_ALPHA_EXISTS" fun _ => (do
  prove ([[!x y p v. ~(y IN FV(??x p))
              ==> (holds M v (??y (formsubst (valmod (x,V y) V) p)) <=>
                   holds M (v:num->A) (??x p))]])
   (REWRITE_TAC [FV, Exists_DEF, Not_DEF, IN_DELETE, UNION_EMPTY] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [HOLDS, HOLDS_FORMSUBST] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC HOLDS_VALUATION THEN
    GEN_TAC THEN REWRITE_TAC [valmod, termval, o_THM] THEN
    COND_CASES_TAC THEN REWRITE_TAC [valmod, termval] THEN
    COND_CASES_TAC THEN REWRITE_TAC [] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval HOLDS_ALPHA_EXISTS

#eval phrase 97
unsafe def FORMSUBST_RENAME : thm := keep "FORMSUBST_RENAME" fun _ => (do
  prove ([[!p x y. FV(formsubst (valmod (x,V y) V) p) DELETE y =
           (FV(p) DELETE x) DELETE y]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [FORMSUBST_FV] THEN
    REWRITE_TAC [EXTENSION, IN_DELETE, IN_ELIM_THM] THEN
    GEN_TAC THEN REWRITE_TAC [valmod] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV COND_ELIM_CONV) THEN
    REWRITE_TAC [FVT, IN_INSERT, NOT_IN_EMPTY] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval FORMSUBST_RENAME

#eval phrase 98
unsafe def TERMSUBST_FUNCTIONS_TERM : thm := keep "TERMSUBST_FUNCTIONS_TERM" fun _ => (do
  prove ([[!t i. functions_term(termsubst i t) =
         functions_term t UNION
         {x | ?y. y IN FVT(t) /\ x IN functions_term(i y)}]])
   (HolLight.tactic_of do
     let lemma1 ← prove
      ([[{x | ?y. y IN (s UNION t) /\ P x y} =
         {x | ?y. y IN s /\ P x y} UNION {x | ?y. y IN t /\ P x y}]])
      (REWRITE_TAC [EXTENSION, IN_UNION, IN_ELIM_THM] THEN MESON_TAC [])
     let lemma2 ← prove
      ([[(s = a UNION c) /\ (t = b UNION d)
         ==> (s UNION t = (a UNION b) UNION (c UNION d))]])
      (SET_TAC [])
     pure
      (MATCH_MP_TAC term_INDUCT THEN
       REWRITE_TAC [functions_term, termsubst, FVT] THEN CONJ_TAC THENL
        [REWRITE_TAC [IN_INSERT, IN_UNION, IN_ELIM_THM, NOT_IN_EMPTY, EXTENSION] THEN
         MESON_TAC [], ALL_TAC] THEN
       GEN_TAC THEN SUBGOAL_THEN
        ([[!l.
          ALL
          (\t. !i. functions_term (termsubst i t) =
                   functions_term t UNION
                   {x | ?y. y IN FVT t /\ x IN functions_term (i y)}) l
          ==> (!i. LIST_UNION (MAP functions_term (MAP (termsubst i) l)) =
                   LIST_UNION (MAP functions_term l) UNION
                   {x | ?y. y IN LIST_UNION (MAP FVT l) /\
                            x IN functions_term (i y)})]])
       ASSUME_TAC THENL
        [ALL_TAC,
         GEN_TAC THEN DISCH_THEN (ANTE_RES_THEN (fun th => REWRITE_TAC [th])) THEN
         REWRITE_TAC [EXTENSION, IN_INSERT, IN_UNION, LENGTH_MAP, DISJ_ACI]] THEN
       LIST_INDUCT_TAC THEN REWRITE_TAC [MAP, LIST_UNION] THENL
          [REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, IN_INSERT, SUBSET,
                       IN_ELIM_THM, IN_UNION],
           ALL_TAC] THEN
       REWRITE_TAC [ALL] THEN STRIP_TAC THEN X_GEN_TAC [[i:num->term]] THEN
       REWRITE_TAC [lemma1, LENGTH, LENGTH_MAP] THEN
       MATCH_MP_TAC lemma2 THEN ASM_REWRITE_TAC [] THEN
       RULE_ASSUM_TAC (HolLight.REWRITE_RULE [LENGTH_MAP]) THEN
       SPEC_TAC ([[i:num->term]], [[i:num->term]]) THEN
       FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []))
  : ExceptT String IO thm).run
#eval TERMSUBST_FUNCTIONS_TERM

#eval phrase 99
unsafe def FORMSUBST_FUNCTIONS_FORM : thm := keep "FORMSUBST_FUNCTIONS_FORM" fun _ => (do
  prove ([[!p i. functions_form(formsubst i p) =
         functions_form p UNION
         {x | ?y. y IN FV(p) /\ x IN functions_term(i y)}]])
   (HolLight.tactic_of do
     let lemma1 ← prove
      ([[{x | ?y. y IN (s UNION t) /\ P x y} =
         {x | ?y. y IN s /\ P x y} UNION {x | ?y. y IN t /\ P x y}]])
      (REWRITE_TAC [EXTENSION, IN_UNION, IN_ELIM_THM] THEN MESON_TAC [])
     let lemma2 ← prove
      ([[(a UNION b) UNION (c UNION d) = (a UNION c) UNION (b UNION d)]])
      (REWRITE_TAC [EXTENSION, IN_UNION, DISJ_ACI])
     pure
      (MATCH_MP_TAC form_INDUCTION THEN
       REWRITE_TAC [formsubst, functions_form, FV] THEN REPEAT CONJ_TAC THENL
        [REPEAT STRIP_TAC THEN
         REWRITE_TAC [EXTENSION, IN_UNION, NOT_IN_EMPTY, IN_ELIM_THM],
         LIST_INDUCT_TAC THEN REWRITE_TAC [MAP, LIST_UNION] THENL
          [REWRITE_TAC [NOT_IN_EMPTY, EXTENSION, IN_UNION, IN_ELIM_THM],
           ALL_TAC] THEN
         X_GEN_TAC [[i:num->term]] THEN REWRITE_TAC [lemma1] THEN
         ONCE_REWRITE_TAC [lemma2] THEN
         BINOP_TAC THEN ASM_REWRITE_TAC [TERMSUBST_FUNCTIONS_TERM],
         REWRITE_TAC [lemma1] THEN REPEAT STRIP_TAC THEN
         ONCE_REWRITE_TAC [lemma2] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
       REWRITE_TAC [functions_form, LET_DEF, LET_END_DEF, VALMOD_VALMOD] THEN
       REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [valmod] THEN
       CONV_TAC (HolLight.DEPTH_CONV COND_ELIM_CONV) THEN
       REWRITE_TAC [functions_term, NOT_IN_EMPTY, IN_INSERT, IN_DELETE] THEN
       REWRITE_TAC [FVT, IN_INSERT, NOT_IN_EMPTY] THEN
       REWRITE_TAC [EXTENSION, IN_UNION, IN_ELIM_THM] THEN
       GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
       ASM_CASES_TAC [[y:num = a0]] THEN ASM_REWRITE_TAC [] THEN
       ASM_MESON_TAC []))
  : ExceptT String IO thm).run
#eval FORMSUBST_FUNCTIONS_FORM

#eval phrase 100
unsafe def FORMSUBST_FUNCTIONS_FORM_1 : thm := keep "FORMSUBST_FUNCTIONS_FORM_1" fun _ => (do
  prove ([[!x t p. x IN FV(p)
           ==> (functions_form(formsubst (valmod (x,t) V) p) =
                functions_form p UNION functions_term t)]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [FORMSUBST_FUNCTIONS_FORM] THEN
    REWRITE_TAC [valmod] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV COND_ELIM_CONV) THEN
    REWRITE_TAC [functions_term, NOT_IN_EMPTY] THEN
    AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval FORMSUBST_FUNCTIONS_FORM_1

#eval phrase 101
unsafe def FORMSUBST_PREDICATES : thm := keep "FORMSUBST_PREDICATES" fun _ => (do
  prove ([[!p i. predicates_form(formsubst i p) = predicates_form p]])
   (MATCH_MP_TAC form_INDUCTION THEN
    REWRITE_TAC [predicates_form, formsubst, LET_DEF, LET_END_DEF] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [LENGTH_MAP])
  : ExceptT String IO thm).run
#eval FORMSUBST_PREDICATES

#eval phrase 102
unsafe def FORMSUBST_LANGUAGE_RENAME : thm := keep "FORMSUBST_LANGUAGE_RENAME" fun _ => (do
  prove ([[language {(formsubst (valmod (x,V y) V) p)} = language {p}]])
   (REWRITE_TAC [LANGUAGE_1, FORMSUBST_PREDICATES, FORMSUBST_FUNCTIONS_FORM] THEN
    REWRITE_TAC [PAIR_EQ] THEN
    REWRITE_TAC [EXTENSION, IN_UNION, IN_ELIM_THM] THEN
    REWRITE_TAC [valmod] THEN CONV_TAC (HolLight.ONCE_DEPTH_CONV COND_ELIM_CONV) THEN
    REWRITE_TAC [functions_term, NOT_IN_EMPTY] THEN
    REWRITE_TAC [(← ExceptT.mk (TAUT [[~p /\ p <=> F]]))])
  : ExceptT String IO thm).run
#eval FORMSUBST_LANGUAGE_RENAME

#eval phrase 103
unsafe def TERMVAL_FUNCTIONS : thm := keep "TERMVAL_FUNCTIONS" fun _ => (do
  prove ([[!M t. (!f zs. (f,LENGTH zs) IN functions_term t
                 ==> (Fun(M) f zs = Fun(M') f zs))
         ==> !v:num->A. termval M v t = termval M' v t]])
   (GEN_TAC THEN MATCH_MP_TAC term_INDUCT THEN
    REWRITE_TAC [termval, functions_term] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[MAP (termval M (v:num->A)) l =
                 MAP (termval M' v) l]])
    SUBST1_TAC THENL
     [MATCH_MP_TAC MAP_EQ THEN
      MATCH_MP_TAC ALL_IMP THEN
      FIRST_ASSUM (EXISTS_TAC o HolCore.Equal.lhand o concl) THEN
      ASM_REWRITE_TAC [] THEN
      GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN (fun th => SPEC_TAC ([[v:num->A]], [[v:num->A]]) THEN
                           MATCH_MP_TAC th) THEN
      REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC [IN_INSERT] THEN DISJ2_TAC THEN
      UNDISCH_TAC [[MEM (x:term) l]] THEN
      SPEC_TAC ([[l:term list]], [[l:term list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [MEM] THEN
      REWRITE_TAC [LIST_UNION, MAP, IN_UNION] THEN ASM_MESON_TAC [],
      FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [IN_INSERT] THEN
      REWRITE_TAC [LENGTH_MAP]])
  : ExceptT String IO thm).run
#eval TERMVAL_FUNCTIONS

#eval phrase 104
unsafe def HOLDS_FUNCTIONS : thm := keep "HOLDS_FUNCTIONS" fun _ => (do
  prove ([[!M M' p. (Dom(M) = Dom(M')) /\
            (!P zs. Pred(M) P zs = Pred(M') P zs) /\
            (!f zs. (f,LENGTH zs) IN functions_form p
                    ==> (Fun(M) f zs = Fun(M') f zs))
            ==> !v:num->A. holds M v p <=> holds M' v p]])
   (GEN_TAC THEN GEN_TAC THEN
    REWRITE_TAC [IMP_CONJ] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC [holds] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
     [AP_TERM_TAC THEN
      UNDISCH_TAC [[!f zs.
           f,LENGTH zs IN functions_form (Atom a0 a1)
           ==> (Fun M f zs :A = Fun M' f zs)]] THEN
      REWRITE_TAC [functions_form] THEN
      SPEC_TAC ([[a1:term list]], [[a1:term list]]) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC [LIST_UNION, MAP, NOT_IN_EMPTY] THEN
      REWRITE_TAC [IN_UNION, CONS_11] THEN REPEAT STRIP_TAC THENL
       [SPEC_TAC ([[v:num->A]], [[v:num->A]]) THEN MATCH_MP_TAC TERMVAL_FUNCTIONS THEN
        REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [],
        FIRST_ASSUM MATCH_MP_TAC THEN
        REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []],
      BINOP_TAC THEN SPEC_TAC ([[v:num->A]], [[v:num->A]]) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [functions_form, IN_UNION],
      AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
      SPEC_TAC ([[valmod (a0,a) (v:num->A)]], [[v:num->A]]) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [functions_form]])
  : ExceptT String IO thm).run
#eval HOLDS_FUNCTIONS

#eval phrase 105
unsafe def HOLDS_PREDICATES : thm := keep "HOLDS_PREDICATES" fun _ => (do
  prove ([[!M M' p. (Dom(M) = Dom(M')) /\
            (!f zs. Fun(M) f zs = Fun(M') f zs) /\
            (!P zs. (P,LENGTH zs) IN predicates_form p
                    ==> (Pred(M) P zs = Pred(M') P zs))
            ==> !v:num->A. holds M v p <=> holds M' v p]])
   (GEN_TAC THEN GEN_TAC THEN
    REWRITE_TAC [IMP_CONJ] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC [holds] THEN
    REWRITE_TAC [predicates_form, IN_INSERT, NOT_IN_EMPTY, IN_UNION] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
     [SUBGOAL_THEN
       ([[MAP (termval M' (v:num->A)) a1 = MAP (termval M (v:num->A)) a1]])
      SUBST1_TAC THENL
       [MATCH_MP_TAC MAP_EQ THEN
        SUBGOAL_THEN ([[!x. termval M' (v:num->A) x = termval M (v:num->A) x]])
         (fun th => REWRITE_TAC [th, ALL_T]) THEN
        GEN_TAC THEN SPEC_TAC ([[v:num->A]], [[v:num->A]]) THEN
        MATCH_MP_TAC TERMVAL_FUNCTIONS THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [LENGTH_MAP],
      ASM_MESON_TAC [],
      AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
      SPEC_TAC ([[valmod (a0,a) (v:num->A)]], [[v:num->A]]) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []])
  : ExceptT String IO thm).run
#eval HOLDS_PREDICATES

#eval phrase 106
unsafe def HOLDS_UCLOSE : thm := keep "HOLDS_UCLOSE" fun _ => (do
  prove ([[!M x p. (!v:num->A. valuation(M) v ==> holds M v (!!x p)) <=>
           (Dom M = EMPTY) \/ !v. valuation(M) v ==> holds M v p]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [holds] THEN
    ASM_CASES_TAC [[Dom(M):A->bool = EMPTY]] THEN
    ASM_REWRITE_TAC [NOT_IN_EMPTY] THEN
    ASM_MESON_TAC [VALUATION_IS_VALMOD, VALUATION_VALMOD, valuation])
  : ExceptT String IO thm).run
#eval HOLDS_UCLOSE

#eval phrase 107
unsafe def MODEL_DUPLICATE : thm := keep "MODEL_DUPLICATE" fun _ => (do
  prove ([[!M fns preds D.
        interpretation(fns,preds) M /\
        (Dom(M) SUBSET D) /\
        ~(Dom(M):A->bool = {})
        ==> ?M'. interpretation(fns,preds) M' /\
                 (Dom(M') = D) /\
                 !s. functions s SUBSET fns /\
                     predicates s SUBSET preds
                     ==> (M' satisfies s <=> M satisfies s)]])
   (REPEAT STRIP_TAC THEN
    ABBREV_TAC [[i = \x. if x IN Dom(M) then x else @z:A. z IN Dom(M)]] THEN
    ABBREV_TAC [[M' = (D:A->bool,
                   (\f args. Fun(M) f (MAP (i:A->A) args)),
                   (\P args. Pred(M) P (MAP i args)))]] THEN
    HolCore.Lib.W (fun g => HolLight.tactic_of do
        let (var, _) ← liftExcept (HolCore.Basics.dest_exists (HolLight.snd g))
        pure (EXISTS_TAC var)) THEN
    SUBGOAL_THEN ([[!x. (i:A->A) x IN Dom(M)]]) ASSUME_TAC THENL
     [X_GEN_TAC [[x:A]] THEN EXPAND_TAC "i" THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC (fun t => pure (SELECT_CONV t)) THEN
      UNDISCH_TAC [[~(Dom(M) = ({}:A->bool))]] THEN
      REWRITE_TAC [EXTENSION, NOT_IN_EMPTY, NOT_FORALL_THM], ALL_TAC] THEN
    MATCH_MP_TAC (← ExceptT.mk (TAUT [[b /\ (b ==> a /\ c) ==> a /\ b /\ c]])) THEN
    CONJ_TAC THENL [EXPAND_TAC "M'" THEN REWRITE_TAC [Dom_DEF], ALL_TAC] THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [interpretation]) THEN
      ASM_REWRITE_TAC [interpretation] THEN
      EXPAND_TAC "M'" THEN REWRITE_TAC [Fun_DEF] THEN
      REPEAT STRIP_TAC THEN FIRST_ASSUM (MATCH_MP_TAC o HolLight.REWRITE_RULE [SUBSET]) THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [LENGTH_MAP] THEN
      UNDISCH_TAC [[ALL (\x:A. x IN D) l]] THEN
      REWRITE_TAC [ALL_MAP] THEN MATCH_MP_TAC MONO_ALL THEN
      ASM_REWRITE_TAC [o_THM], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[!t. functions_term t SUBSET fns
        ==> !v:num->A. (i:A->A) (termval M' v t) = termval M (i o v) t]])
    ASSUME_TAC THENL
     [MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC [termval, o_THM] THEN
      EXPAND_TAC "M'" THEN REWRITE_TAC [Fun_DEF] THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [(← HolLight.GSYM MAP_o)] THEN
      MAP_EVERY X_GEN_TAC [ [[P:num]], [[args:term list]] ] THEN
      REWRITE_TAC [functions_term, SUBSET, IN_LIST_UNION, IN_INSERT] THEN
      REWRITE_TAC [(← HolLight.GSYM EX_MEM), (← HolLight.GSYM ALL_MEM)] THEN DISCH_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[(P:num,LENGTH(args:term list)) IN fns]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [], ALL_TAC] THEN
      SUBGOAL_THEN ([[!t. MEM t args ==> functions_term t SUBSET fns]])
      ASSUME_TAC THENL
       [REWRITE_TAC [SUBSET] THEN ASM_MESON_TAC [MEM_MAP], ALL_TAC] THEN
      SUBGOAL_THEN
       ([[!t. MEM t args
          ==> !v:num->A. (i:A->A) (termval M' v t) = termval M (i o v) t]])
      ASSUME_TAC THENL
       [ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
      X_GEN_TAC [[v:num->A]] THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC [[Fun M P (MAP ((i:A->A) o termval M' (v:num->A)) args)]] THEN
      CONJ_TAC THENL
       [FIRST_ASSUM (fun th => HolLight.tactic_of do
          let sth ← liftExcept (HolCore.Equal.SYM th)
          pure (HolLight.GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RATOR_CONV) [sth])) THEN
        SUBGOAL_THEN ([[Fun M P (MAP ((i:A->A) o termval M' (v:num->A)) args) IN
                    Dom(M)]])
          (fun th => REWRITE_TAC [th]) THEN
        FIRST_ASSUM (MATCH_MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [interpretation]) THEN
        ASM_REWRITE_TAC [LENGTH_MAP] THEN REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN
        REWRITE_TAC [MEM_MAP, o_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC MAP_EQ THEN
      REWRITE_TAC [(← HolLight.GSYM ALL_MEM), o_THM] THEN ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN
     ([[!p. functions_form p SUBSET fns
        ==> !v:num->A. holds M' v p <=> holds M ((i:A->A) o v) p]])
    ASSUME_TAC THENL
     [MATCH_MP_TAC form_INDUCTION THEN REWRITE_TAC [holds, functions_form] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC [SUBSET, IN_LIST_UNION, (← HolLight.GSYM EX_MEM), MEM_MAP] THEN
        REPEAT STRIP_TAC THEN EXPAND_TAC "M'" THEN REWRITE_TAC [Pred_DEF] THEN
        ASM_REWRITE_TAC [] THEN AP_TERM_TAC THEN REWRITE_TAC [(← HolLight.GSYM MAP_o)] THEN
        MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC [(← HolLight.GSYM ALL_MEM)] THEN
        REWRITE_TAC [o_THM] THEN ASM_MESON_TAC [SUBSET],
        REWRITE_TAC [SUBSET, IN_UNION] THEN MESON_TAC [],
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [ [[x:num]], [[p:form]] ] THEN
      DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC [[v:num->A]] THEN
      SUBGOAL_THEN
       ([[!a. i o valmod (x,a) (v:num->A) = valmod (x,i(a)) ((i:A->A) o v)]])
       (fun th => REWRITE_TAC [th])
      THENL
       [REWRITE_TAC [FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
        REWRITE_TAC [valmod] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [o_THM],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[!x:A. x IN Dom(M) ==> (i x = x)]]) MP_TAC THENL
       [EXPAND_TAC "i" THEN SIMP_TAC [], ALL_TAC] THEN
      ASM_MESON_TAC [SUBSET], ALL_TAC] THEN
    X_GEN_TAC [[s:form->bool]] THEN STRIP_TAC THEN REWRITE_TAC [satisfies] THEN
    REWRITE_TAC [valuation] THEN EXPAND_TAC "M'" THEN REWRITE_TAC [Dom_DEF] THEN
    ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN AP_TERM_TAC THEN
    HolLight.GEN_REWRITE_TAC HolCore.Lib.I [FUN_EQ_THM] THEN X_GEN_TAC [[p:form]] THEN
    ASM_CASES_TAC [[p:form IN s]] THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[functions_form p SUBSET fns]]) ASSUME_TAC THENL
     [UNDISCH_TAC [[functions s SUBSET fns]] THEN
      REWRITE_TAC [functions, SUBSET, IN_UNIONS, IN_ELIM_THM] THEN
      ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC [[v:num->A]] THENL
     [DISCH_TAC THEN SUBGOAL_THEN ([[v:num->A = i o v]]) SUBST1_TAC THENL
       [EXPAND_TAC "i" THEN REWRITE_TAC [FUN_EQ_THM, o_THM] THEN
        ASM_REWRITE_TAC [], ALL_TAC] THEN ASM_MESON_TAC [SUBSET],
      DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [o_THM]])
  : ExceptT String IO thm).run
#eval MODEL_DUPLICATE

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.Fol" do
  replay (
          SessionLibrary.Analysis.ensureAnalysis)
  replay (
          SessionLibrary.Wo.ensureWo)
  replay (
          SessionLibrary.RSTC.ensureRSTC)
  replay (
          HolExamples.Reduct.ensure)
  replay (
          HolExamples.MultiWf.ensure)
  replay (
          IO.println "<fun>")
  replay (
          LIST_UNION)
  replay (
          LIST_UNION_FINITE)
  replay (
          IN_LIST_UNION)
  replay (
          LIST_UNION_APPEND)
  replay (
          do IO.println term_raw_INDUCT; IO.println term_raw_RECURSION)
  replay (
          term_INDUCT)
  replay (
          term_RECURSION)
  replay (
          IO.println "<fun>")
  replay (
          term_INJ)
  replay (
          term_DISTINCT)
  replay (
          term_CASES)
  replay (
          parse_as_infix ("-->", (13, "right")))
  replay (
          do IO.println form_INDUCTION; IO.println form_RECURSION)
  replay (
          form_INJ)
  replay (
          form_DISTINCT)
  replay (
          form_CASES)
  replay (
          parse_as_infix ("&&", (16, "right")))
  replay (
          parse_as_infix ("||", (14, "right")))
  replay (
          parse_as_infix ("<->", (12, "right")))
  replay (
          Not_DEF)
  replay (
          True_DEF)
  replay (
          Or_DEF)
  replay (
          And_DEF)
  replay (
          Iff_DEF)
  replay (
          Exists_DEF)
  replay (
          functions_term)
  replay (
          functions_form)
  replay (
          predicates_form)
  replay (
          functions)
  replay (
          predicates)
  replay (
          language)
  replay (
          FUNCTIONS_SING)
  replay (
          LANGUAGE_1)
  replay (
          Dom_DEF)
  replay (
          Fun_DEF)
  replay (
          Pred_DEF)
  replay (
          MODEL_EQ)
  replay (
          MODEL_DECOMP)
  replay (
          FVT)
  replay (
          FV)
  replay (
          BV)
  replay (
          FVT_FINITE)
  replay (
          FV_FINITE)
  replay (
          BV_FINITE)
  replay (
          FV_EXISTS)
  replay (
          valmod)
  replay (
          VALMOD_CLAUSES)
  replay (
          VALMOD_TRIV)
  replay (
          VALMOD_VALMOD)
  replay (
          valuation)
  replay (
          VALUATION_VALMOD)
  replay (
          VALUATION_IS_VALMOD)
  replay (
          parse_as_infix ("satisfies", (10, "right")))
  replay (
          termval)
  replay (
          holds)
  replay (
          hold)
  replay (
          satisfies)
  replay (
          SATISFIES_1)
  replay (
          HOLDS)
  replay (
          TERMVAL_VALUATION)
  replay (
          HOLDS_VALUATION)
  replay (
          satisfiable)
  replay (
          valid)
  replay (
          entails)
  replay (
          equivalent)
  replay (
          interpretation)
  replay (
          INTERPRETATION_TERMVAL)
  replay (
          INTERPRETATION_SUBLANGUAGE)
  replay (
          termsubst)
  replay (
          TERMSUBST_TERMVAL)
  replay (
          TERMVAL_TRIV)
  replay (
          TERMVAL_TERMSUBST)
  replay (
          TERMSUBST_TERMSUBST)
  replay (
          TERMSUBST_TRIV)
  replay (
          TERMSUBST_VALUATION)
  replay (
          TERMSUBST_FVT)
  replay (
          MAX_SYM)
  replay (
          MAX_ASSOC)
  replay (
          SETMAX)
  replay (
          VARIANT)
  replay (
          SETMAX_LEMMA)
  replay (
          SETMAX_MEMBER)
  replay (
          SETMAX_THM)
  replay (
          SETMAX_UNION)
  replay (
          VARIANT_FINITE)
  replay (
          VARIANT_THM)
  replay (
          formsubst)
  replay (
          FORMSUBST_TRIV)
  replay (
          FORMSUBST_VALUATION)
  replay (
          FORMSUBST_FV)
  replay (
          HOLDS_FORMSUBST)
  replay (
          HOLDS_FORMSUBST1)
  replay (
          HOLDS_RENAME)
  replay (
          HOLDS_ALPHA_FORALL)
  replay (
          HOLDS_ALPHA_EXISTS)
  replay (
          FORMSUBST_RENAME)
  replay (
          TERMSUBST_FUNCTIONS_TERM)
  replay (
          FORMSUBST_FUNCTIONS_FORM)
  replay (
          FORMSUBST_FUNCTIONS_FORM_1)
  replay (
          FORMSUBST_PREDICATES)
  replay (
          FORMSUBST_LANGUAGE_RENAME)
  replay (
          TERMVAL_FUNCTIONS)
  replay (
          HOLDS_FUNCTIONS)
  replay (
          HOLDS_PREDICATES)
  replay (
          HOLDS_UCLOSE)
  replay (
          MODEL_DUPLICATE)
-- @@ENSURE END

end HolLogicArith.Fol
