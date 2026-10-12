/- File: HolTest/ListsIndTypesCheck.lean
Self-checking tests for ind_types.ml and lists.ml: theorem statements checked
against the OCaml source, and documented examples from hol-light/Help.
Lean4 translation by Chris Walton 2026 -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- LAYER FORCING.  The list constants (LENGTH, CONS, APPEND, HD, TL, ...)  -/
/- are declared lazily by `setupListDefs`.  A term parsed BEFORE that      -/
/- runs sees `LENGTH`/`APPEND` etc. as FREE VARIABLES, making every        -/
/- stmtOK/ruleOK below meaningless.  Reading one list theorem here forces  -/
/- the whole layer (constants declared) before anything parses.  Each      -/
/- stmtOK below additionally passes an already-evaluated `Session.*` thm,  -/
/- which re-forces the layer in the same #eval.                            -/
/- ---------------------------------------------------------------------- -/

#eval Session.listDefs.LENGTH

/- ====================================================================== -/
/- 1. lists.ml definition STATEMENTS (verbatim from lists.ml 28-143).     -/
/-    stmtOK checks alpha-equivalence to the parsed OCaml statement and    -/
/-    does not depend on printing.                                         -/
/- ====================================================================== -/

-- LAST (lists.ml 82-83): single clause, no leading quantifier.
#eval (do
  let th := listDefs.LAST
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "LAST def (lists.ml 82)" th
    "LAST (CONS (h:A) t) = if t = [] then h else LAST t")

-- BUTLAST (lists.ml 85-86): two clauses.
#eval (do
  let th := listDefs.BUTLAST
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "BUTLAST def (lists.ml 85)" th
    "(BUTLAST [] = []) /\\ (BUTLAST (CONS (h:A) t) = if t = [] then [] else CONS h (BUTLAST t))")

-- NULL (lists.ml 90-91).
#eval (do
  let th := listDefs.NULL
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "NULL def (lists.ml 90)" th
    "(NULL [] = T) /\\ (NULL (CONS (h:A) t) = F)")

-- ITLIST (lists.ml 101-102).
#eval (do
  let th := listDefs.ITLIST
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "ITLIST def (lists.ml 101)" th
    "(ITLIST (f:A->B->B) [] b = b) /\\ (ITLIST f (CONS h t) b = f h (ITLIST f t b))")

-- ASSOC (lists.ml 118-119): single clause.
#eval (do
  let th := listDefs.ASSOC
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "ASSOC def (lists.ml 118)" th
    "ASSOC a (CONS (h:A#B) t) = if FST h = a then SND h else ASSOC a t")

-- ALLPAIRS (lists.ml 135-136).
#eval (do
  let th := listDefs.ALLPAIRS
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "ALLPAIRS def (lists.ml 135)" th
    "(ALLPAIRS (f:A->B->bool) [] l <=> T) /\\ (ALLPAIRS f (CONS h t) l <=> ALL (f h) l /\\ ALLPAIRS f t l)")

-- REPLICATE (lists.ml 88, num_RECURSION).
#eval (do
  let th := listDefs.REPLICATE
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "REPLICATE def (lists.ml 88)" th
    "(REPLICATE 0 (x:A) = []) /\\ (REPLICATE (SUC n) x = CONS x (REPLICATE n x))")

-- FILTER (lists.ml 115-116).
#eval (do
  let th := listDefs.FILTER
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "FILTER def (lists.ml 115)" th
    "(FILTER (P:A->bool) [] = []) /\\ (FILTER P (CONS h t) = if P h then CONS h (FILTER P t) else FILTER P t)")

/- ====================================================================== -/
/- 2. lists.ml THEOREM statements, spread early/middle/late.              -/
/-    Many of these have THENL/o-heavy proofs, so a wrong proof would not  -/
/-    yield the theorem, and a statement typo is what stmtOK catches.      -/
/- ====================================================================== -/

-- NOT_CONS_NIL (lists.ml 148-150): proof = REWRITE_TAC[distinctness "list"].
#eval (do
  let th := listThms1.NOT_CONS_NIL
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "NOT_CONS_NIL (lists.ml 148)" th
    "!(h:A) t. ~(CONS h t = [])")

-- APPEND_NIL (lists.ml 157-159): LIST_INDUCT_TAC THEN ASM_REWRITE_TAC.
#eval (do
  let th := listThms1.APPEND_NIL
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "APPEND_NIL (lists.ml 157)" th
    "!l:A list. APPEND l [] = l")

-- REVERSE_REVERSE (lists.ml 170-172).
#eval (do
  let th := listThms1.REVERSE_REVERSE
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "REVERSE_REVERSE (lists.ml 170)" th
    "!l:A list. REVERSE(REVERSE l) = l")

-- CONS_11 (lists.ml 178-180): REWRITE_TAC[injectivity "list"].
#eval (do
  let th := listThms1.CONS_11
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "CONS_11 (lists.ml 178)" th
    "!(h1:A) h2 t1 t2. (CONS h1 t1 = CONS h2 t2) <=> (h1 = h2) /\\ (t1 = t2)")

-- LENGTH_APPEND (lists.ml 198-200).
#eval (do
  let th := listThms1.LENGTH_APPEND
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "LENGTH_APPEND (lists.ml 198)" th
    "!(l:A list) m. LENGTH(APPEND l m) = LENGTH l + LENGTH m")

-- MAP_APPEND (lists.ml 202-204).
#eval (do
  let th := listThms1.MAP_APPEND
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "MAP_APPEND (lists.ml 202)" th
    "!f:A->B. !l1 l2. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)")

-- LENGTH_MAP (lists.ml 206-208).
#eval (do
  let th := listThms1.LENGTH_MAP
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "LENGTH_MAP (lists.ml 206)" th
    "!l. !f:A->B. LENGTH (MAP f l) = LENGTH l")

-- MAP_o (lists.ml 225-228): uses o_THM rewrite.
#eval (do
  let th := listThms1.MAP_o
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "MAP_o (lists.ml 225)" th
    "!f:A->B. !g:B->C. !l. MAP (g o f) l = MAP g (MAP f l)")

-- ALL_MEM (lists.ml 314-317): ASM_MESON-finished.
#eval (do
  let th := listThms1.ALL_MEM
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "ALL_MEM (lists.ml 314)" th
    "!P (l:A list). (!x. MEM x l ==> P x) <=> ALL P l")

-- MEM_APPEND (lists.ml 343-345): DISJ_ACI rewrite.
#eval (do
  let th := listThms1.MEM_APPEND
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "MEM_APPEND (lists.ml 343)" th
    "!(x:A) l1 l2. MEM x (APPEND l1 l2) <=> MEM x l1 \\/ MEM x l2")

-- MEM_MAP (lists.ml 347-350): MESON-finished, existential RHS.
#eval (do
  let th := listThms1.MEM_MAP
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "MEM_MAP (lists.ml 347)" th
    "!(f:A->B) y l. MEM y (MAP f l) <=> ?x. MEM x l /\\ (y = f x)")

-- MEM_ASSOC (lists.ml 399-402): COND_CASES_TAC + ASM_MESON[PAIR;FST].
#eval (do
  let th := listThms1.MEM_ASSOC
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "MEM_ASSOC (lists.ml 399)" th
    "!(l:(A#B)list) x. MEM (x,ASSOC x l) l <=> MEM x (MAP FST l)")

-- LENGTH_TL (lists.ml 550-552): ~(l=[]) ==> ... uses num arith (-,1).
#eval (do
  let th := listThms2.LENGTH_TL
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "LENGTH_TL (lists.ml 550)" th
    "!l:A list. ~(l = []) ==> LENGTH(TL l) = LENGTH l - 1")

-- EL_APPEND (lists.ml 563-567): conditional RHS, INDUCT-heavy proof.
#eval (do
  let th := listThms2.EL_APPEND
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "EL_APPEND (lists.ml 563)" th
    "!k l m:A list. EL k (APPEND l m) = if k < LENGTH l then EL k l else EL (k - LENGTH l) m")

-- LAST_EL (lists.ml 580-583): ASM_SIMP with EL_CONS/LENGTH_EQ_NIL.
#eval (do
  let th := listThms2.LAST_EL
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "LAST_EL (lists.ml 580)" th
    "!l:A list. ~(l = []) ==> LAST l = EL (LENGTH l - 1) l")

-- EL_MAP (lists.ml 594-596).
#eval (do
  let th := listThms2.EL_MAP
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "EL_MAP (lists.ml 594)" th
    "!(f:A->B) n l. n < LENGTH l ==> EL n (MAP f l) = f(EL n l)")

-- PAIRWISE_APPEND (lists.ml 628-631): MATCH_MP_TAC list_INDUCT proof.
#eval (do
  let th := listThms2.PAIRWISE_APPEND
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "PAIRWISE_APPEND (lists.ml 628)" th
    "!R:A->A->bool l m. PAIRWISE R (APPEND l m) <=> PAIRWISE R l /\\ PAIRWISE R m /\\ (!x y. MEM x l /\\ MEM y m ==> R x y)")

-- PAIRWISE_MAP (lists.ml 636-639): lambda on RHS (o_DEF rewrite).
#eval (do
  let th := listThms2.PAIRWISE_MAP
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "PAIRWISE_MAP (lists.ml 636)" th
    "!R f:A->B l. PAIRWISE R (MAP f l) <=> PAIRWISE (\\x y. R (f x) (f y)) l")

-- LIST_OF_SEQ (lists.ml 689-692): two-clause conjunction, o-composition.
#eval (do
  let th := listThms2.LIST_OF_SEQ
  let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
  stmtOK "LIST_OF_SEQ (lists.ml 689)" th
    "(!(f:num->A). list_of_seq f 0 = []) /\\ (!(f:num->A) n. list_of_seq f (SUC n) = CONS (f 0) (list_of_seq (f o SUC) n))")

/- ====================================================================== -/
/- 3. lists.ml Help examples: LENGTH_CONV / EL_CONV / REVERSE_CONV /       -/
/-    LIST_OF_SEQ_CONV, transcribed VERBATIM from the .hlp EXAMPLE blocks. -/
/-    A conversion's `expected` is the full equation shown after `|-`.     -/
/- ====================================================================== -/

-- Help/LENGTH_CONV.hlp
#eval (do
  let _ ← (IO.mkRef (concl listDefs.LENGTH) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "LENGTH [1;2;3;4;5]" with
  | .error e => IO.println s!"LENGTH_CONV.hlp (1) -> MISMATCH parse ERR {e}"
  | .ok tm => ruleOK "LENGTH_CONV.hlp (1)" (Session.LENGTH_CONV tm)
                "LENGTH [1; 2; 3; 4; 5] = 5")
#eval (do
  let _ ← (IO.mkRef (concl listDefs.LENGTH) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "LENGTH [a;one;c]" with
  | .error e => IO.println s!"LENGTH_CONV.hlp (2) -> MISMATCH parse ERR {e}"
  | .ok tm => ruleOK "LENGTH_CONV.hlp (2)" (Session.LENGTH_CONV tm)
                "LENGTH [a; one; c] = 3")

-- Help/EL_CONV.hlp
#eval (do
  let _ ← (IO.mkRef (concl listDefs.EL) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "EL 4 [1;2;3;4;5]" with
  | .error e => IO.println s!"EL_CONV.hlp (1) -> MISMATCH parse ERR {e}"
  | .ok tm => ruleOK "EL_CONV.hlp (1)" (Session.EL_CONV tm)
                "EL 4 [1; 2; 3; 4; 5] = 5")
#eval (do
  let _ ← (IO.mkRef (concl listDefs.EL) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "EL 0 [a;one;c]" with
  | .error e => IO.println s!"EL_CONV.hlp (2) -> MISMATCH parse ERR {e}"
  | .ok tm => ruleOK "EL_CONV.hlp (2)" (Session.EL_CONV tm)
                "EL 0 [a; one; c] = a")

-- Help/REVERSE_CONV.hlp
#eval (do
  let _ ← (IO.mkRef (concl listDefs.REVERSE) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "REVERSE [1;2;3]" with
  | .error e => IO.println s!"REVERSE_CONV.hlp (1) -> MISMATCH parse ERR {e}"
  | .ok tm => ruleOK "REVERSE_CONV.hlp (1)" (Session.REVERSE_CONV tm)
                "REVERSE [1; 2; 3] = [3; 2; 1]")
#eval (do
  let _ ← (IO.mkRef (concl listDefs.REVERSE) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "REVERSE [one;two;three]" with
  | .error e => IO.println s!"REVERSE_CONV.hlp (2) -> MISMATCH parse ERR {e}"
  | .ok tm => ruleOK "REVERSE_CONV.hlp (2)" (Session.REVERSE_CONV tm)
                "REVERSE [one; two; three] = [three; two; one]")

-- Help/LIST_OF_SEQ_CONV.hlp: non-lambda case (bflag=false) ...
#eval (do
  let _ ← (IO.mkRef (concl listDefs.list_of_seq) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "list_of_seq (f:num->A) 3" with
  | .error e => IO.println s!"LIST_OF_SEQ_CONV.hlp (nonlambda) -> MISMATCH parse ERR {e}"
  | .ok tm => ruleOK "LIST_OF_SEQ_CONV.hlp (nonlambda)" (Session.LIST_OF_SEQ_CONV tm)
                "list_of_seq (f:num->A) 3 = [f 0; f 1; f 2]")
-- ... and lambda case (bflag=true, beta-fixup path).
#eval (do
  let _ ← (IO.mkRef (concl listDefs.list_of_seq) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "list_of_seq (\\n. f n > 0) 3" with
  | .error e => IO.println s!"LIST_OF_SEQ_CONV.hlp (lambda) -> MISMATCH parse ERR {e}"
  | .ok tm => ruleOK "LIST_OF_SEQ_CONV.hlp (lambda)" (Session.LIST_OF_SEQ_CONV tm)
                "list_of_seq (\\n. f n > 0) 3 = [f 0 > 0; f 1 > 0; f 2 > 0]")

/- ====================================================================== -/
/- 4. lists.ml term constructors: mk_cons / mk_list / dest_string.        -/
/-    Documented in Help/mk_cons.hlp, mk_list.hlp, dest_string.hlp.        -/
/-    These return terms/strings, so they are checked directly (printing   -/
/-    of a list literal has no quantifiers/T/F).                           -/
/- ====================================================================== -/

-- Help/mk_cons.hlp: mk_cons `1` `l:num list` = `CONS 1 l`
#eval (do
  let _ ← (IO.mkRef (concl listDefs.APPEND) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "1", ← HolCore.Parser.parse_term "l:num list" with
  | .ok h, .ok t =>
    match ← Session.mk_cons h t with
    | .error e => IO.println s!"mk_cons.hlp (1) -> MISMATCH ERR {e}"
    | .ok r =>
      let got := (← HolCore.Printer.string_of_term r)
      if got == "CONS 1 l" then IO.println "mk_cons.hlp (1) -> OK"
      else IO.println s!"mk_cons.hlp (1) -> MISMATCH got={got}"
  | _, _ => IO.println "mk_cons.hlp (1) -> MISMATCH parse ERR")

-- Help/mk_cons.hlp: mk_cons `1` `[2;3;4]` = `[1; 2; 3; 4]`
#eval (do
  let _ ← (IO.mkRef (concl listDefs.APPEND) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "1", ← HolCore.Parser.parse_term "[2;3;4]" with
  | .ok h, .ok t =>
    match ← Session.mk_cons h t with
    | .error e => IO.println s!"mk_cons.hlp (2) -> MISMATCH ERR {e}"
    | .ok r =>
      let got := (← HolCore.Printer.string_of_term r)
      if got == "[1; 2; 3; 4]" then IO.println "mk_cons.hlp (2) -> OK"
      else IO.println s!"mk_cons.hlp (2) -> MISMATCH got={got}"
  | _, _ => IO.println "mk_cons.hlp (2) -> MISMATCH parse ERR")

-- Help/mk_list.hlp: mk_list([`1`;`2`],`:num`) = `[1; 2]`
#eval (do
  let _ ← (IO.mkRef (concl listDefs.APPEND) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_type "num" with
  | .error e => IO.println s!"mk_list.hlp (1) -> MISMATCH type parse ERR {e}"
  | .ok numTy =>
    match ← HolCore.Parser.parse_term "1", ← HolCore.Parser.parse_term "2" with
    | .ok t1, .ok t2 =>
      match ← Session.mk_list [t1, t2] numTy with
      | .error e => IO.println s!"mk_list.hlp (1) -> MISMATCH ERR {e}"
      | .ok r =>
        let got := (← HolCore.Printer.string_of_term r)
        if got == "[1; 2]" then IO.println "mk_list.hlp (1) -> OK"
        else IO.println s!"mk_list.hlp (1) -> MISMATCH got={got}"
    | _, _ => IO.println "mk_list.hlp (1) -> MISMATCH parse ERR")

-- Help/mk_list.hlp: mk_list([],`:num`) = `[]`
#eval (do
  let _ ← (IO.mkRef (concl listDefs.APPEND) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_type "num" with
  | .error e => IO.println s!"mk_list.hlp (2) -> MISMATCH type parse ERR {e}"
  | .ok numTy =>
    match ← Session.mk_list [] numTy with
    | .error e => IO.println s!"mk_list.hlp (2) -> MISMATCH ERR {e}"
    | .ok r =>
      let got := (← HolCore.Printer.string_of_term r)
      if got == "[]" then IO.println "mk_list.hlp (2) -> OK"
      else IO.println s!"mk_list.hlp (2) -> MISMATCH got={got}")

-- Help/dest_string.hlp: dest_string `"HOL"` = "HOL"
#eval (do
  let _ ← (IO.mkRef (concl listDefs.APPEND) : IO (IO.Ref term))
  match ← Session.mk_string "HOL" with
  | .error e => IO.println s!"dest_string.hlp -> MISMATCH mk_string ERR {e}"
  | .ok t =>
    match Session.dest_string t with
    | .error e => IO.println s!"dest_string.hlp -> MISMATCH ERR {e}"
    | .ok s =>
      if s == "HOL" then IO.println "dest_string.hlp -> OK"
      else IO.println s!"dest_string.hlp -> MISMATCH got={s}")

/- ====================================================================== -/
/- 5. ind_types.ml: option/sum derived theorems and the store lookups.    -/
/-    distinctness / injectivity are pure (Except), wrapped with `pure`;   -/
/-    cases / option_DISTINCT / option_INJ are IO (Except thm).            -/
/-    Statements taken from Help/*.hlp and ind_types.ml 1049-1055.         -/
/- ====================================================================== -/

-- Help/distinctness.hlp: distinctness "list"
#eval (do
  let _ ← (IO.mkRef (concl listDefs.APPEND) : IO (IO.Ref term))
  ruleOK "distinctness \"list\" (.hlp)" (pure (Session.distinctness "list"))
    "!a0' a1'. ~([] = CONS a0' a1')")

-- Help/injectivity.hlp: injectivity "list"
#eval (do
  let _ ← (IO.mkRef (concl listDefs.APPEND) : IO (IO.Ref term))
  ruleOK "injectivity \"list\" (.hlp)" (pure (Session.injectivity "list"))
    "!a0 a1 a0' a1'. CONS a0 a1 = CONS a0' a1' <=> a0 = a0' /\\ a1 = a1'")

-- Help/cases.hlp: cases "list"
#eval (do
  let _ ← (IO.mkRef (concl listDefs.APPEND) : IO (IO.Ref term))
  ruleOK "cases \"list\" (.hlp)" (Session.cases "list")
    "!x. x = [] \\/ (?a0 a1. x = CONS a0 a1)")

-- ind_types.ml 1049-1051: option_DISTINCT.
#eval (do
  let _ ← (IO.mkRef (concl listDefs.APPEND) : IO (IO.Ref term))
  ruleOK "option_DISTINCT (ind_types.ml 1049)" Session.option_DISTINCT
    "!a:A. ~(SOME a = NONE)")

-- ind_types.ml 1053-1055: option_INJ.
#eval (do
  let _ ← (IO.mkRef (concl listDefs.APPEND) : IO (IO.Ref term))
  ruleOK "option_INJ (ind_types.ml 1053)" Session.option_INJ
    "!a b:A. SOME a = SOME b <=> a = b")

-- distinctness/injectivity/cases on the primitive num type (Help examples).
#eval (do
  let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
  ruleOK "distinctness \"num\" (.hlp)" (pure (Session.distinctness "num"))
    "!n'. ~(0 = SUC n')")
#eval (do
  let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
  ruleOK "injectivity \"num\" (.hlp)" (pure (Session.injectivity "num"))
    "!n n'. SUC n = SUC n' <=> n = n'")
#eval (do
  let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
  ruleOK "cases \"num\" (.hlp)" (Session.cases "num")
    "!m. m = 0 \\/ (?n. m = SUC n)")

/- ====================================================================== -/
/- 6. Negative / failure cases (failsOK).                                 -/
/- ====================================================================== -/

-- distinctness on a nonexistent type must fail (store lookup miss).
#eval (do
  let _ ← (IO.mkRef (concl listDefs.APPEND) : IO (IO.Ref term))
  failsOK "distinctness bogus-type fails" (pure (Session.distinctness "nosuchtype")))

-- LENGTH_CONV on a non-LENGTH term must fail.
#eval (do
  let _ ← (IO.mkRef (concl listDefs.LENGTH) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "REVERSE [1;2;3]" with
  | .error e => IO.println s!"LENGTH_CONV wrong-head fails -> MISMATCH parse ERR {e}"
  | .ok tm => failsOK "LENGTH_CONV wrong-head fails" (Session.LENGTH_CONV tm))
