/- File: HolLogicArith/ArithFol.lean
Translation of HOL Light's Arithmetic/fol.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolLogicArith.Common
open HolCore.Kernel Session HolLight.Syntax HolLogicArith
open scoped HolLight

namespace HolLogicArith.ArithFol

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

/- `new_inductive_definition` run eagerly, panicking with HOL Light's message
   on failure (as the toplevel throws); returns the (rules, induct, cases)
   triple directly, as the OCaml `let a,b,c = new_inductive_definition ...`. -/
private unsafe def defInductive (tm : term) : thm × thm × thm :=
  match unsafeIO (Session.new_inductive_definition tm) with
  | .ok (.ok trip) => trip
  | .ok (.error e) => panic! s!"new_inductive_definition: {e}"
  | .error e => panic! s!"new_inductive_definition IO: {e}"

-- What Arithmetic/make.ml loads before fol.ml.
#eval Session.prioritize_num
#eval SessionLibrary.RSTC.ensureRSTC
#eval SessionLibrary.Prime.ensurePrime

#eval phrase 1
#eval Session.prioritize_num

#eval phrase 2
#eval parse_as_infix ("++", (20, "right"))

#eval phrase 3
#eval parse_as_infix ("**", (22, "right"))

#eval phrase 4
unsafe def term_pair : thm × thm := keep "term_pair" fun _ =>
  defType "term = Z
        | V num
        | Suc term
        | ++ term term
        | ** term term"
unsafe def term_INDUCT : thm := term_pair.1
unsafe def term_RECURSION : thm := term_pair.2
#eval do IO.println term_INDUCT; IO.println term_RECURSION

#eval phrase 5
unsafe def term_CASES : thm := keep "term_CASES" fun _ =>
  (ExceptT.mk (Session.prove_cases_thm term_INDUCT) : ExceptT String IO thm).run
#eval term_CASES

#eval phrase 6
unsafe def term_DISTINCT : thm := keep "term_DISTINCT" fun _ =>
  (liftExcept (Session.distinctness "term") : ExceptT String IO thm).run
#eval term_DISTINCT

#eval phrase 7
unsafe def term_INJ : thm := keep "term_INJ" fun _ =>
  (liftExcept (Session.injectivity "term") : ExceptT String IO thm).run
#eval term_INJ

#eval phrase 8
#eval parse_as_infix ("===", (18, "right"))

#eval phrase 9
#eval parse_as_infix ("<<", (18, "right"))

#eval phrase 10
#eval parse_as_infix ("<<=", (18, "right"))

#eval phrase 11
#eval parse_as_infix ("&&", (16, "right"))

#eval phrase 12
#eval parse_as_infix ("||", (15, "right"))

#eval phrase 13
#eval parse_as_infix ("-->", (14, "right"))

#eval phrase 14
#eval parse_as_infix ("<->", (13, "right"))

#eval phrase 15
unsafe def form_pair : thm × thm := keep "form_pair" fun _ =>
  defType "form = False
        | True
        | === term term
        | << term term
        | <<= term term
        | Not form
        | && form form
        | || form form
        | --> form form
        | <-> form form
        | !! num form
        | ?? num form"
unsafe def form_INDUCT : thm := form_pair.1
unsafe def form_RECURSION : thm := form_pair.2
#eval do IO.println form_INDUCT; IO.println form_RECURSION

#eval phrase 16
unsafe def form_CASES : thm := keep "form_CASES" fun _ =>
  (ExceptT.mk (Session.prove_cases_thm form_INDUCT) : ExceptT String IO thm).run
#eval form_CASES

#eval phrase 17
unsafe def form_DISTINCT : thm := keep "form_DISTINCT" fun _ =>
  (liftExcept (Session.distinctness "form") : ExceptT String IO thm).run
#eval form_DISTINCT

#eval phrase 18
unsafe def form_INJ : thm := keep "form_INJ" fun _ =>
  (liftExcept (Session.injectivity "form") : ExceptT String IO thm).run
#eval form_INJ

#eval phrase 19
#eval parse_as_infix ("|->", (22, "right"))

#eval phrase 20
unsafe def valmod : thm := keep "valmod" fun _ => new_definition
  [[(x |-> a) (v:A->B) = \y. if y = x then a else v(y)]]
#eval valmod

#eval phrase 21
unsafe def termval : thm := keep "termval" fun _ => (do
  newRec term_RECURSION
    [[(termval v Z = 0) /\
      (termval v (V n) = v(n)) /\
      (termval v (Suc t) = SUC (termval v t)) /\
      (termval v (s ++ t) = termval v s + termval v t) /\
      (termval v (s ** t) = termval v s * termval v t)]]
  : ExceptT String IO thm).run
#eval termval

#eval phrase 22
unsafe def holds : thm := keep "holds" fun _ => (do
  newRec form_RECURSION
    [[(holds v False <=> F) /\
      (holds v True <=> T) /\
      (holds v (s === t) <=> (termval v s = termval v t)) /\
      (holds v (s << t) <=> (termval v s < termval v t)) /\
      (holds v (s <<= t) <=> (termval v s <= termval v t)) /\
      (holds v (Not p) <=> ~(holds v p)) /\
      (holds v (p && q) <=> holds v p /\ holds v q) /\
      (holds v (p || q) <=> holds v p \/ holds v q) /\
      (holds v (p --> q) <=> holds v p ==> holds v q) /\
      (holds v (p <-> q) <=> (holds v p <=> holds v q)) /\
      (holds v (!! x p) <=> !a. holds ((x|->a) v) p) /\
      (holds v (?? x p) <=> ?a. holds ((x|->a) v) p)]]
  : ExceptT String IO thm).run
#eval holds

#eval phrase 23
unsafe def arithtrue : thm := keep "arithtrue" fun _ => new_definition
  [[arithtrue p <=> !v. holds v p]]
#eval arithtrue

#eval phrase 24
unsafe def VALMOD : thm := keep "VALMOD" fun _ => (do
  prove ([[!v x y a. ((x |-> y) v) a = if a = x then y else v(a)]])
   (REWRITE_TAC [valmod])
  : ExceptT String IO thm).run
#eval VALMOD

#eval phrase 25
unsafe def VALMOD_BASIC : thm := keep "VALMOD_BASIC" fun _ => (do
  prove ([[!v x y. (x |-> y) v x = y]])
   (REWRITE_TAC [valmod])
  : ExceptT String IO thm).run
#eval VALMOD_BASIC

#eval phrase 26
unsafe def VALMOD_VALMOD_BASIC : thm := keep "VALMOD_VALMOD_BASIC" fun _ => (do
  prove ([[!v a b x. (x |-> a) ((x |-> b) v) = (x |-> a) v]])
   (REWRITE_TAC [valmod, FUN_EQ_THM] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval VALMOD_VALMOD_BASIC

#eval phrase 27
unsafe def VALMOD_REPEAT : thm := keep "VALMOD_REPEAT" fun _ => (do
  prove ([[!v x. (x |-> v(x)) v = v]])
   (REWRITE_TAC [valmod, FUN_EQ_THM] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval VALMOD_REPEAT

#eval phrase 28
unsafe def FORALL_VALMOD : thm := keep "FORALL_VALMOD" fun _ => (do
  prove ([[!x. (!v a. P((x |-> a) v)) <=> (!v. P v)]])
   (MESON_TAC [VALMOD_REPEAT])
  : ExceptT String IO thm).run
#eval FORALL_VALMOD

#eval phrase 29
unsafe def VALMOD_SWAP : thm := keep "VALMOD_SWAP" fun _ => (do
  prove ([[!v x y a b.
     ~(x = y) ==> ((x |-> a) ((y |-> b) v) = (y |-> b) ((x |-> a) v))]])
   (REWRITE_TAC [valmod, FUN_EQ_THM] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval VALMOD_SWAP

#eval phrase 30
unsafe def VALMOD_TRIVIAL : thm := keep "VALMOD_TRIVIAL" fun _ => (do
  prove ([[!v x. v x = t ==> (x |-> t) v = v]])
   (REWRITE_TAC [valmod, FUN_EQ_THM] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval VALMOD_TRIVIAL

#eval phrase 31
#eval parse_as_infix ("|=>", (22, "right"))

#eval phrase 32
unsafe def assign : thm := keep "assign" fun _ => new_definition
  [[(x |=> a) = (x |-> a) V]]
#eval assign

#eval phrase 33
unsafe def ASSIGN : thm := keep "ASSIGN" fun _ => (do
  prove ([[!x y a. (x |=> a) y = if y = x then a else V(y)]])
   (REWRITE_TAC [assign, valmod])
  : ExceptT String IO thm).run
#eval ASSIGN

#eval phrase 34
unsafe def ASSIGN_TRIV : thm := keep "ASSIGN_TRIV" fun _ => (do
  prove ([[!x. (x |=> V x) = V]])
   (REWRITE_TAC [VALMOD_REPEAT, assign])
  : ExceptT String IO thm).run
#eval ASSIGN_TRIV

#eval phrase 35
unsafe def FVT : thm := keep "FVT" fun _ => (do
  newRec term_RECURSION
    [[(FVT Z = {}) /\
      (FVT (V n) = {n}) /\
      (FVT (Suc t) = FVT t) /\
      (FVT (s ++ t) = (FVT s) UNION (FVT t)) /\
      (FVT (s ** t) = (FVT s) UNION (FVT t))]]
  : ExceptT String IO thm).run
#eval FVT

#eval phrase 36
unsafe def FV : thm := keep "FV" fun _ => (do
  newRec form_RECURSION
    [[(FV False = {}) /\
      (FV True = {}) /\
      (FV (s === t) = (FVT s) UNION (FVT t)) /\
      (FV (s << t) = (FVT s) UNION (FVT t)) /\
      (FV (s <<= t) = (FVT s) UNION (FVT t)) /\
      (FV (Not p) = FV p) /\
      (FV (p && q) = (FV p) UNION (FV q)) /\
      (FV (p || q) = (FV p) UNION (FV q)) /\
      (FV (p --> q) = (FV p) UNION (FV q)) /\
      (FV (p <-> q) = (FV p) UNION (FV q)) /\
      (FV (!!x p) = (FV p) DELETE x) /\
      (FV (??x p) = (FV p) DELETE x)]]
  : ExceptT String IO thm).run
#eval FV

#eval phrase 37
unsafe def FVT_FINITE : thm := keep "FVT_FINITE" fun _ => (do
  prove ([[!t. FINITE(FVT t)]])
   (MATCH_MP_TAC term_INDUCT THEN
    SIMP_TAC [FVT, FINITE_RULES, FINITE_INSERT, FINITE_UNION])
  : ExceptT String IO thm).run
#eval FVT_FINITE

#eval phrase 38
unsafe def FV_FINITE : thm := keep "FV_FINITE" fun _ => (do
  prove ([[!p. FINITE(FV p)]])
   (MATCH_MP_TAC form_INDUCT THEN
    SIMP_TAC [FV, FVT_FINITE, FINITE_RULES, FINITE_DELETE, FINITE_UNION])
  : ExceptT String IO thm).run
#eval FV_FINITE

#eval phrase 39
unsafe def axiom_triple : thm × thm × thm := keep "axiom_triple" fun _ =>
  defInductive
    [[(!p q. axiom(p --> (q --> p))) /\
      (!p q r. axiom((p --> q --> r) --> (p --> q) --> (p --> r))) /\
      (!p. axiom(((p --> False) --> False) --> p)) /\
      (!x p q. axiom((!!x (p --> q)) --> (!!x p) --> (!!x q))) /\
      (!x p. ~(x IN FV p) ==> axiom(p --> !!x p)) /\
      (!x t. ~(x IN FVT t) ==> axiom(??x (V x === t))) /\
      (!t. axiom(t === t)) /\
      (!s t. axiom((s === t) --> (Suc s === Suc t))) /\
      (!s t u v. axiom(s === t --> u === v --> s ++ u === t ++ v)) /\
      (!s t u v. axiom(s === t --> u === v --> s ** u === t ** v)) /\
      (!s t u v. axiom(s === t --> u === v --> s === u --> t === v)) /\
      (!s t u v. axiom(s === t --> u === v --> s << u --> t << v)) /\
      (!s t u v. axiom(s === t --> u === v --> s <<= u --> t <<= v)) /\
      (!p q. axiom((p <-> q) --> p --> q)) /\
      (!p q. axiom((p <-> q) --> q --> p)) /\
      (!p q. axiom((p --> q) --> (q --> p) --> (p <-> q))) /\
      axiom(True <-> (False --> False)) /\
      (!p. axiom(Not p <-> (p --> False))) /\
      (!p q. axiom((p && q) <-> (p --> q --> False) --> False)) /\
      (!p q. axiom((p || q) <-> Not(Not p && Not q))) /\
      (!x p. axiom((??x p) <-> Not(!!x (Not p))))]]
unsafe def axiom_RULES : thm := axiom_triple.1
unsafe def axiom_INDUCT : thm := axiom_triple.2.1
unsafe def axiom_CASES : thm := axiom_triple.2.2
#eval do IO.println axiom_RULES; IO.println axiom_INDUCT; IO.println axiom_CASES

#eval phrase 40
#eval parse_as_infix ("|--", (11, "right"))

#eval phrase 41
unsafe def proves_triple : thm × thm × thm := keep "proves_triple" fun _ =>
  defInductive
    [[(!p. axiom p \/ p IN A ==> A |-- p) /\
      (!p q. A |-- (p --> q) /\ A |-- p ==> A |-- q) /\
      (!p x. A |-- p ==> A |-- (!!x p))]]
unsafe def proves_RULES : thm := proves_triple.1
unsafe def proves_INDUCT : thm := proves_triple.2.1
unsafe def proves_CASES : thm := proves_triple.2.2
#eval do IO.println proves_RULES; IO.println proves_INDUCT; IO.println proves_CASES

#eval phrase 42
unsafe def TERMVAL_VALUATION : thm := keep "TERMVAL_VALUATION" fun _ => (do
  prove ([[!t v v'. (!x. x IN FVT(t) ==> (v'(x) = v(x)))
            ==> (termval v' t = termval v t)]])
   (MATCH_MP_TAC term_INDUCT THEN
    REWRITE_TAC [termval, FVT, IN_INSERT, IN_UNION, NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval TERMVAL_VALUATION

#eval phrase 43
unsafe def HOLDS_VALUATION : thm := keep "HOLDS_VALUATION" fun _ => (do
  prove ([[!p v v'.
      (!x. x IN (FV p) ==> (v'(x) = v(x)))
      ==> (holds v' p <=> holds v p)]])
   (MATCH_MP_TAC form_INDUCT THEN
    REWRITE_TAC [FV, holds, IN_UNION, IN_DELETE] THEN
    SIMP_TAC [TERMVAL_VALUATION] THEN
    REWRITE_TAC [valmod] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC [])
  : ExceptT String IO thm).run
#eval HOLDS_VALUATION

#eval phrase 44
unsafe def TERMVAL_VALMOD_OTHER : thm := keep "TERMVAL_VALMOD_OTHER" fun _ => (do
  prove ([[!v x a t. ~(x IN FVT t) ==> (termval ((x |-> a) v) t = termval v t)]])
   (MESON_TAC [TERMVAL_VALUATION, VALMOD])
  : ExceptT String IO thm).run
#eval TERMVAL_VALMOD_OTHER

#eval phrase 45
unsafe def HOLDS_VALMOD_OTHER : thm := keep "HOLDS_VALMOD_OTHER" fun _ => (do
  prove ([[!v x a p. ~(x IN FV p) ==> (holds ((x |-> a) v) p <=> holds v p)]])
   (MESON_TAC [HOLDS_VALUATION, VALMOD])
  : ExceptT String IO thm).run
#eval HOLDS_VALMOD_OTHER

#eval phrase 46
unsafe def AXIOMS_TRUE : thm := keep "AXIOMS_TRUE" fun _ => (do
  prove ([[!p. axiom p ==> arithtrue p]])
   (MATCH_MP_TAC axiom_INDUCT THEN
    REWRITE_TAC [arithtrue] THEN REPEAT STRIP_TAC THEN REWRITE_TAC [holds] THENL
     [CONV_TAC TAUT,
      CONV_TAC TAUT,
      SIMP_TAC [],
      REWRITE_TAC [RIGHT_IMP_FORALL_THM] THEN REPEAT GEN_TAC THEN
      MATCH_MP_TAC EQ_IMP THEN
      MATCH_MP_TAC HOLDS_VALUATION THEN
      REWRITE_TAC [valmod] THEN GEN_TAC THEN COND_CASES_TAC THEN
      ASM_MESON_TAC [],
      EXISTS_TAC [[termval v t]] THEN
      REWRITE_TAC [termval, valmod] THEN
      MATCH_MP_TAC TERMVAL_VALUATION THEN
      GEN_TAC THEN REWRITE_TAC [] THEN
      COND_CASES_TAC THEN ASM_MESON_TAC [],
      SIMP_TAC [termval],
      SIMP_TAC [termval],
      SIMP_TAC [termval],
      SIMP_TAC [termval],
      SIMP_TAC [termval],
      SIMP_TAC [termval],
      SIMP_TAC [termval],
      SIMP_TAC [termval],
      CONV_TAC TAUT,
      CONV_TAC TAUT,
      CONV_TAC TAUT,
      MESON_TAC []])
  : ExceptT String IO thm).run
#eval AXIOMS_TRUE

#eval phrase 47
unsafe def THEOREMS_TRUE : thm := keep "THEOREMS_TRUE" fun _ => (do
  prove ([[!A p. (!q. q IN A ==> arithtrue q) /\ A |-- p ==> arithtrue p]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[a \/ b ==> c <=> (a ==> c) /\ (b ==> c)]])
     pure
      (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
       DISCH_TAC THEN MATCH_MP_TAC proves_INDUCT THEN
       ASM_SIMP_TAC [taut1] THEN
       REWRITE_TAC [IN, AXIOMS_TRUE] THEN
       SIMP_TAC [holds, arithtrue]))
  : ExceptT String IO thm).run
#eval THEOREMS_TRUE

#eval phrase 48
unsafe def MAX_SYM : thm := keep "MAX_SYM" fun _ => (do
  prove ([[!x y. MAX x y = MAX y x]])
   (ARITH_TAC)
  : ExceptT String IO thm).run
#eval MAX_SYM

#eval phrase 49
unsafe def MAX_ASSOC : thm := keep "MAX_ASSOC" fun _ => (do
  prove ([[!x y z. MAX x (MAX y z) = MAX (MAX x y) z]])
   (ARITH_TAC)
  : ExceptT String IO thm).run
#eval MAX_ASSOC

#eval phrase 50
unsafe def SETMAX : thm := keep "SETMAX" fun _ => new_definition
  [[SETMAX s = ITSET MAX s 0]]
#eval SETMAX

#eval phrase 51
unsafe def VARIANT : thm := keep "VARIANT" fun _ => new_definition
  [[VARIANT s = SETMAX s + 1]]
#eval VARIANT

#eval phrase 52
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

#eval phrase 53
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

#eval phrase 54
unsafe def SETMAX_THM : thm := keep "SETMAX_THM" fun _ => (do
  prove ([[(SETMAX {} = 0) /\
   (!x s. FINITE s ==>
           (SETMAX (x INSERT s) = MAX x (SETMAX s)))]])
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [SETMAX_LEMMA] THEN
    COND_CASES_TAC THEN REWRITE_TAC [MAX] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC [SETMAX_MEMBER])
  : ExceptT String IO thm).run
#eval SETMAX_THM

#eval phrase 55
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

#eval phrase 56
unsafe def VARIANT_FINITE : thm := keep "VARIANT_FINITE" fun _ => (do
  prove ([[!s:num->bool. FINITE(s) ==> ~(VARIANT(s) IN s)]])
   (HolLight.tactic_of do
     let ar ← ExceptT.mk (ARITH_RULE [[~(x + 1 <= x)]])
     pure
      (REWRITE_TAC [VARIANT] THEN
       MESON_TAC [SETMAX_MEMBER, ar]))
  : ExceptT String IO thm).run
#eval VARIANT_FINITE

#eval phrase 57
unsafe def VARIANT_THM : thm := keep "VARIANT_THM" fun _ => (do
  prove ([[!p. ~(VARIANT(FV p) IN FV(p))]])
   (GEN_TAC THEN MATCH_MP_TAC VARIANT_FINITE THEN REWRITE_TAC [FV_FINITE])
  : ExceptT String IO thm).run
#eval VARIANT_THM

#eval phrase 58
unsafe def NOT_IN_VARIANT : thm := keep "NOT_IN_VARIANT" fun _ => (do
  prove ([[!s t. FINITE s /\ t SUBSET s ==> ~(VARIANT(s) IN t)]])
   (MESON_TAC [SUBSET, VARIANT_FINITE])
  : ExceptT String IO thm).run
#eval NOT_IN_VARIANT

#eval phrase 59
unsafe def termsubst : thm := keep "termsubst" fun _ => (do
  newRec term_RECURSION
    [[(termsubst v Z = Z) /\
      (!x. termsubst v (V x) = v(x)) /\
      (!t. termsubst v (Suc t) = Suc(termsubst v t)) /\
      (!s t. termsubst v (s ++ t) = termsubst v s ++ termsubst v t) /\
      (!s t. termsubst v (s ** t) = termsubst v s ** termsubst v t)]]
  : ExceptT String IO thm).run
#eval termsubst

#eval phrase 60
unsafe def TERMVAL_TERMSUBST : thm := keep "TERMVAL_TERMSUBST" fun _ => (do
  prove ([[!v i t. termval v (termsubst i t) = termval (termval v o i) t]])
   (GEN_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC term_INDUCT THEN SIMP_TAC [termval, termsubst, o_THM])
  : ExceptT String IO thm).run
#eval TERMVAL_TERMSUBST

#eval phrase 61
unsafe def TERMSUBST_TERMSUBST : thm := keep "TERMSUBST_TERMSUBST" fun _ => (do
  prove ([[!i j t. termsubst j (termsubst i t) = termsubst (termsubst j o i) t]])
   (GEN_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC term_INDUCT THEN SIMP_TAC [termval, termsubst, o_THM])
  : ExceptT String IO thm).run
#eval TERMSUBST_TERMSUBST

#eval phrase 62
unsafe def TERMSUBST_TRIV : thm := keep "TERMSUBST_TRIV" fun _ => (do
  prove ([[!t. termsubst V t = t]])
   (MATCH_MP_TAC term_INDUCT THEN SIMP_TAC [termsubst])
  : ExceptT String IO thm).run
#eval TERMSUBST_TRIV

#eval phrase 63
unsafe def TERMSUBST_EQ : thm := keep "TERMSUBST_EQ" fun _ => (do
  prove ([[!t v v'. (!x. x IN (FVT t) ==> (v'(x) = v(x)))
            ==> (termsubst v' t = termsubst v t)]])
   (MATCH_MP_TAC term_INDUCT THEN
    SIMP_TAC [termsubst, FVT, IN_SING, IN_UNION] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval TERMSUBST_EQ

#eval phrase 64
unsafe def TERMSUBST_FVT : thm := keep "TERMSUBST_FVT" fun _ => (do
  prove ([[!t i. FVT(termsubst i t) = {x | ?y. y IN FVT(t) /\ x IN FVT(i y)}]])
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    MATCH_MP_TAC term_INDUCT THEN REWRITE_TAC [FVT, termsubst] THEN
    REWRITE_TAC [IN_UNION, IN_SING, NOT_IN_EMPTY] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval TERMSUBST_FVT

#eval phrase 65
unsafe def TERMSUBST_ASSIGN : thm := keep "TERMSUBST_ASSIGN" fun _ => (do
  prove ([[!x s t. ~(x IN FVT t) ==> (termsubst (x |=> s) t = t)]])
   (HolLight.tactic_of do
     let gsym ← HolLight.GSYM TERMSUBST_TRIV
     pure
      (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC HolLight.RAND_CONV [gsym] THEN
       MATCH_MP_TAC TERMSUBST_EQ THEN
       REWRITE_TAC [ASSIGN] THEN ASM_MESON_TAC []))
  : ExceptT String IO thm).run
#eval TERMSUBST_ASSIGN

#eval phrase 66
unsafe def TERMSUBST_TRIVIAL : thm := keep "TERMSUBST_TRIVIAL" fun _ => (do
  prove ([[!v t. (!x. x IN FVT t ==> v x = V x) ==> termsubst v t = t]])
   (MESON_TAC [TERMSUBST_EQ, TERMSUBST_TRIV])
  : ExceptT String IO thm).run
#eval TERMSUBST_TRIVIAL

#eval phrase 67
unsafe def formsubst : thm := keep "formsubst" fun _ => (do
  newRec form_RECURSION
    [[(formsubst v False = False) /\
      (formsubst v True = True) /\
      (formsubst v (s === t) = termsubst v s === termsubst v t) /\
      (formsubst v (s << t) = termsubst v s << termsubst v t) /\
      (formsubst v (s <<= t) = termsubst v s <<= termsubst v t) /\
      (formsubst v (Not p) = Not(formsubst v p)) /\
      (formsubst v (p && q) = formsubst v p && formsubst v q) /\
      (formsubst v (p || q) = formsubst v p || formsubst v q) /\
      (formsubst v (p --> q) = formsubst v p --> formsubst v q) /\
      (formsubst v (p <-> q) = formsubst v p <-> formsubst v q) /\
      (formsubst v (!!x q) =
           let z = if ?y. y IN FV(!!x q) /\ x IN FVT(v(y))
                   then VARIANT(FV(formsubst ((x |-> V x) v) q)) else x in
           !!z (formsubst ((x |-> V(z)) v) q)) /\
      (formsubst v (??x q) =
           let z = if ?y. y IN FV(??x q) /\ x IN FVT(v(y))
                   then VARIANT(FV(formsubst ((x |-> V x) v) q)) else x in
           ??z (formsubst ((x |-> V(z)) v) q))]]
  : ExceptT String IO thm).run
#eval formsubst

#eval phrase 68
unsafe def FORMSUBST_PROPERTIES : thm := keep "FORMSUBST_PROPERTIES" fun _ => (do
  prove ([[!p. (!i. FV(formsubst i p) = {x | ?y. y IN FV(p) /\ x IN FVT(i y)}) /\
       (!i v. holds v (formsubst i p) = holds (termval v o i) p)]])
   (REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    MATCH_MP_TAC form_INDUCT THEN
    REWRITE_TAC [FV, holds, formsubst, TERMSUBST_FVT, IN_ELIM_THM, NOT_IN_EMPTY,
                IN_UNION, TERMVAL_TERMSUBST] THEN
    REPEAT (CONJ_TAC THENL [MESON_TAC [], ALL_TAC]) THEN CONJ_TAC THEN
    (MAP_EVERY X_GEN_TAC [ [[x:num]], [[p:form]] ] THEN STRIP_TAC THEN
     REWRITE_TAC [AND_FORALL_THM] THEN X_GEN_TAC [[i:num->term]] THEN
     LET_TAC THEN CONV_TAC (HolLight.TOP_DEPTH_CONV Session.let_CONV) THEN
     SUBGOAL_THEN ([[~(?y. y IN (FV(p) DELETE x) /\ z IN FVT(i y))]])
     ASSUME_TAC THENL
      [EXPAND_TAC "z" THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
       MP_TAC (← ExceptT.mk (HolLight.SPEC ([[formsubst ((x |-> V x) i) p]]) VARIANT_THM)) THEN
       ASM_REWRITE_TAC [valmod, IN_DELETE, CONTRAPOS_THM] THEN
       MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [],
       ALL_TAC] THEN
     CONJ_TAC THEN GEN_TAC THEN ASM_REWRITE_TAC [FV, IN_DELETE, holds] THENL
      [REWRITE_TAC [LEFT_AND_EXISTS_THM, valmod] THEN AP_TERM_TAC THEN
       ABS_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC [FVT, IN_SING, IN_DELETE],
       AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC HOLDS_VALUATION THEN
       GEN_TAC THEN REWRITE_TAC [valmod, o_DEF] THEN COND_CASES_TAC THEN
       ASM_REWRITE_TAC [termval] THEN DISCH_TAC THEN
       MATCH_MP_TAC TERMVAL_VALUATION THEN GEN_TAC THEN
       REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_MESON_TAC [IN_DELETE]]))
  : ExceptT String IO thm).run
#eval FORMSUBST_PROPERTIES

#eval phrase 69
unsafe def FORMSUBST_FV : thm := keep "FORMSUBST_FV" fun _ => (do
  prove ([[!p i. FV(formsubst i p) = {x | ?y. y IN FV(p) /\ x IN FVT(i y)}]])
   (REWRITE_TAC [FORMSUBST_PROPERTIES])
  : ExceptT String IO thm).run
#eval FORMSUBST_FV

#eval phrase 70
unsafe def HOLDS_FORMSUBST : thm := keep "HOLDS_FORMSUBST" fun _ => (do
  prove ([[!p i v. holds v (formsubst i p) <=> holds (termval v o i) p]])
   (REWRITE_TAC [FORMSUBST_PROPERTIES])
  : ExceptT String IO thm).run
#eval HOLDS_FORMSUBST

#eval phrase 71
unsafe def FORMSUBST_EQ : thm := keep "FORMSUBST_EQ" fun _ => (do
  prove ([[!p i j. (!x. x IN FV(p) ==> (i(x) = j(x)))
           ==> (formsubst i p = formsubst j p)]])
   (HolLight.tactic_of do
     let taut1 ← ExceptT.mk (TAUT [[a /\ (a ==> b) ==> a /\ b]])
     pure
      (MATCH_MP_TAC form_INDUCT THEN
       REWRITE_TAC [FV, formsubst, IN_UNION, IN_DELETE] THEN
       SIMP_TAC [] THEN REWRITE_TAC [CONJ_ASSOC] THEN
       GEN_REWRITE_TAC HolCore.Lib.I [(← HolLight.GSYM CONJ_ASSOC)] THEN CONJ_TAC THENL
        [MESON_TAC [TERMSUBST_EQ], ALL_TAC] THEN
       CONJ_TAC THEN MAP_EVERY X_GEN_TAC [ [[x:num]], [[p:form]] ] THEN
       (DISCH_TAC THEN MAP_EVERY X_GEN_TAC [ [[i:num->term]], [[j:num->term]] ] THEN
        DISCH_TAC THEN REWRITE_TAC [LET_DEF, LET_END_DEF, form_INJ] THEN
        MATCH_MP_TAC taut1 THEN SIMP_TAC [] THEN
        CONJ_TAC THENL
         [ALL_TAC,
          DISCH_THEN (HolCore.Lib.K ALL_TAC) THEN FIRST_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC [valmod] THEN ASM_SIMP_TAC []] THEN
        AP_THM_TAC THEN BINOP_TAC THENL
         [ASM_MESON_TAC [],
          AP_TERM_TAC THEN AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC [valmod] THEN ASM_MESON_TAC []])))
  : ExceptT String IO thm).run
#eval FORMSUBST_EQ

#eval phrase 72
unsafe def FORMSUBST_TRIV : thm := keep "FORMSUBST_TRIV" fun _ => (do
  prove ([[!p. formsubst V p = p]])
   (MATCH_MP_TAC form_INDUCT THEN
    SIMP_TAC [formsubst, TERMSUBST_TRIV] THEN
    REWRITE_TAC [FVT, IN_SING, FV, IN_DELETE] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [LET_DEF, LET_END_DEF, VALMOD_REPEAT] THEN
    ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval FORMSUBST_TRIV

#eval phrase 73
unsafe def FORMSUBST_TRIVIAL : thm := keep "FORMSUBST_TRIVIAL" fun _ => (do
  prove ([[!v p. (!x. x IN FV(p) ==> v x = V x) ==> formsubst v p = p]])
   (MESON_TAC [FORMSUBST_EQ, FORMSUBST_TRIV])
  : ExceptT String IO thm).run
#eval FORMSUBST_TRIVIAL

#eval phrase 74
unsafe def safe_for : thm := keep "safe_for" fun _ => new_definition
  [[safe_for x v <=> !y. x IN FVT(v y) ==> y = x]]
#eval safe_for

#eval phrase 75
unsafe def SAFE_FOR_V : thm := keep "SAFE_FOR_V" fun _ => (do
  prove ([[!x. safe_for x V]])
   (SIMP_TAC [safe_for, FVT, IN_SING])
  : ExceptT String IO thm).run
#eval SAFE_FOR_V

#eval phrase 76
unsafe def SAFE_FOR_VALMOD : thm := keep "SAFE_FOR_VALMOD" fun _ => (do
  prove ([[!v x y t. safe_for x v /\ (x IN FVT t ==> y = x)
             ==> safe_for x ((y |-> t) v)]])
   (REWRITE_TAC [safe_for, VALMOD] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval SAFE_FOR_VALMOD

#eval phrase 77
unsafe def SAFE_FOR_ASSIGN : thm := keep "SAFE_FOR_ASSIGN" fun _ => (do
  prove ([[!x y t. safe_for x (y |=> t) <=> x IN FVT t ==> y = x]])
   (REWRITE_TAC [safe_for, ASSIGN] THEN MESON_TAC [FVT, IN_SING])
  : ExceptT String IO thm).run
#eval SAFE_FOR_ASSIGN

#eval phrase 78
unsafe def FORMSUBST_SAFE_FOR : thm := keep "FORMSUBST_SAFE_FOR" fun _ => (do
  prove ([[(!v x p. safe_for x v
            ==> formsubst v (!! x p) = !!x (formsubst ((x |-> V x) v) p)) /\
   (!v x p. safe_for x v
            ==> formsubst v (?? x p) = ??x (formsubst ((x |-> V x) v) p))]])
   (REWRITE_TAC [safe_for, formsubst, LET_DEF, LET_END_DEF, FV] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC [] THEN ASM SET_TAC [])
  : ExceptT String IO thm).run
#eval FORMSUBST_SAFE_FOR

#eval phrase 79
unsafe def qsubst : thm := keep "qsubst" fun _ => new_definition
  [[qsubst (x,t) p = ??x (V x === t && p)]]
#eval qsubst

#eval phrase 80
unsafe def FV_QSUBST : thm := keep "FV_QSUBST" fun _ => (do
  prove ([[!x n p. FV(qsubst (x,t) p) = (FV(p) UNION FVT(t)) DELETE x]])
   (REWRITE_TAC [qsubst, FV, FVT] THEN SET_TAC [])
  : ExceptT String IO thm).run
#eval FV_QSUBST

#eval phrase 81
unsafe def HOLDS_QSUBST : thm := keep "HOLDS_QSUBST" fun _ => (do
  prove ([[!v t p v. ~(x IN FVT(t))
             ==> (holds v (qsubst (x,t) p) <=>
                  holds ((x |-> termval v t) v) p)]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[!v z. termval ((x |-> z) v) t = termval v t]]) ASSUME_TAC THENL
     [REWRITE_TAC [valmod] THEN ASM_MESON_TAC [TERMVAL_VALUATION],
      ASM_REWRITE_TAC [holds, qsubst, termval, VALMOD_BASIC, UNWIND_THM2]])
  : ExceptT String IO thm).run
#eval HOLDS_QSUBST

#eval phrase 82
unsafe def numeral : thm := keep "numeral" fun _ => (do
  newRec Session.num_RECURSION
    [[(numeral 0 = Z) /\
      (!n. numeral (SUC n) = Suc(numeral n))]]
  : ExceptT String IO thm).run
#eval numeral

#eval phrase 83
unsafe def TERMVAL_NUMERAL : thm := keep "TERMVAL_NUMERAL" fun _ => (do
  prove ([[!v n. termval v (numeral n) = n]])
   (GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [termval, numeral])
  : ExceptT String IO thm).run
#eval TERMVAL_NUMERAL

#eval phrase 84
unsafe def FVT_NUMERAL : thm := keep "FVT_NUMERAL" fun _ => (do
  prove ([[!n. FVT(numeral n) = {}]])
   (INDUCT_TAC THEN ASM_REWRITE_TAC [FVT, numeral])
  : ExceptT String IO thm).run
#eval FVT_NUMERAL

#eval phrase 85
unsafe def closed : thm := keep "closed" fun _ => new_definition
  [[closed p <=> (FV p = {})]]
#eval closed

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py from the `#eval`s above. -/
unsafe def ensure : IO Unit := once "HolLogicArith.ArithFol" do
  replay (
          Session.prioritize_num)
  replay (
          SessionLibrary.RSTC.ensureRSTC)
  replay (
          SessionLibrary.Prime.ensurePrime)
  replay (
          Session.prioritize_num)
  replay (
          parse_as_infix ("++", (20, "right")))
  replay (
          parse_as_infix ("**", (22, "right")))
  replay (
          do IO.println term_INDUCT; IO.println term_RECURSION)
  replay (
          term_CASES)
  replay (
          term_DISTINCT)
  replay (
          term_INJ)
  replay (
          parse_as_infix ("===", (18, "right")))
  replay (
          parse_as_infix ("<<", (18, "right")))
  replay (
          parse_as_infix ("<<=", (18, "right")))
  replay (
          parse_as_infix ("&&", (16, "right")))
  replay (
          parse_as_infix ("||", (15, "right")))
  replay (
          parse_as_infix ("-->", (14, "right")))
  replay (
          parse_as_infix ("<->", (13, "right")))
  replay (
          do IO.println form_INDUCT; IO.println form_RECURSION)
  replay (
          form_CASES)
  replay (
          form_DISTINCT)
  replay (
          form_INJ)
  replay (
          parse_as_infix ("|->", (22, "right")))
  replay (
          valmod)
  replay (
          termval)
  replay (
          holds)
  replay (
          arithtrue)
  replay (
          VALMOD)
  replay (
          VALMOD_BASIC)
  replay (
          VALMOD_VALMOD_BASIC)
  replay (
          VALMOD_REPEAT)
  replay (
          FORALL_VALMOD)
  replay (
          VALMOD_SWAP)
  replay (
          VALMOD_TRIVIAL)
  replay (
          parse_as_infix ("|=>", (22, "right")))
  replay (
          assign)
  replay (
          ASSIGN)
  replay (
          ASSIGN_TRIV)
  replay (
          FVT)
  replay (
          FV)
  replay (
          FVT_FINITE)
  replay (
          FV_FINITE)
  replay (
          do IO.println axiom_RULES; IO.println axiom_INDUCT; IO.println axiom_CASES)
  replay (
          parse_as_infix ("|--", (11, "right")))
  replay (
          do IO.println proves_RULES; IO.println proves_INDUCT; IO.println proves_CASES)
  replay (
          TERMVAL_VALUATION)
  replay (
          HOLDS_VALUATION)
  replay (
          TERMVAL_VALMOD_OTHER)
  replay (
          HOLDS_VALMOD_OTHER)
  replay (
          AXIOMS_TRUE)
  replay (
          THEOREMS_TRUE)
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
          NOT_IN_VARIANT)
  replay (
          termsubst)
  replay (
          TERMVAL_TERMSUBST)
  replay (
          TERMSUBST_TERMSUBST)
  replay (
          TERMSUBST_TRIV)
  replay (
          TERMSUBST_EQ)
  replay (
          TERMSUBST_FVT)
  replay (
          TERMSUBST_ASSIGN)
  replay (
          TERMSUBST_TRIVIAL)
  replay (
          formsubst)
  replay (
          FORMSUBST_PROPERTIES)
  replay (
          FORMSUBST_FV)
  replay (
          HOLDS_FORMSUBST)
  replay (
          FORMSUBST_EQ)
  replay (
          FORMSUBST_TRIV)
  replay (
          FORMSUBST_TRIVIAL)
  replay (
          safe_for)
  replay (
          SAFE_FOR_V)
  replay (
          SAFE_FOR_VALMOD)
  replay (
          SAFE_FOR_ASSIGN)
  replay (
          FORMSUBST_SAFE_FOR)
  replay (
          qsubst)
  replay (
          FV_QSUBST)
  replay (
          HOLDS_QSUBST)
  replay (
          numeral)
  replay (
          TERMVAL_NUMERAL)
  replay (
          FVT_NUMERAL)
  replay (
          closed)
-- @@ENSURE END

end HolLogicArith.ArithFol
