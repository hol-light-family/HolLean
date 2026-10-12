/- File: HolTest/SetsCheck.lean
Self-checking tests for sets.ml: theorem statements checked against the
OCaml source, and documented examples from hol-light/Help.
Lean4 translation by Chris Walton 2026 -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ---------------------------------------------------------------------- -/
/- (1) Core membership / extensionality (sets.ml 45-308).                 -/
/- Each stmtOK forces its own theorem's layer via the `th` argument.      -/
/- ---------------------------------------------------------------------- -/

#eval (do let th := Session.EXTENSION
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "EXTENSION (sets.ml 45)" th
            "!s t. (s = t) <=> !x:A. x IN s <=> x IN t")

#eval (do let th := Session.NOT_IN_EMPTY
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "NOT_IN_EMPTY (sets.ml 174)" th "!x:A. ~(x IN EMPTY)")

#eval (do let th := Session.IN_UNION
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "IN_UNION (sets.ml 182)" th
            "!s t (x:A). x IN (s UNION t) <=> x IN s \\/ x IN t")

#eval (do let th := Session.IN_INSERT
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "IN_INSERT (sets.ml 202)" th
            "!x:A. !y s. x IN (y INSERT s) <=> (x = y) \\/ x IN s")

#eval (do let th := Session.IN_INTER
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "IN_INTER (sets.ml)" th
            "!s t (x:A). x IN (s INTER t) <=> x IN s /\\ x IN t")

#eval (do let th := Session.IN_DIFF
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "IN_DIFF (sets.ml)" th
            "!s t (x:A). x IN (s DIFF t) <=> x IN s /\\ ~(x IN t)")

/- ---------------------------------------------------------------------- -/
/- (2) Inclusion / operators (sets.ml 383-665). SET_TAC-proved lemmas.    -/
/- ---------------------------------------------------------------------- -/

#eval (do let th := Session.SUBSET_TRANS
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "SUBSET_TRANS (sets.ml 383)" th
            "!(s:A->bool) t u. s SUBSET t /\\ t SUBSET u ==> s SUBSET u")

#eval (do let th := Session.SUBSET_REFL
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "SUBSET_REFL (sets.ml 387)" th "!s:A->bool. s SUBSET s")

#eval (do let th := Session.SUBSET_ANTISYM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "SUBSET_ANTISYM (sets.ml 391)" th
            "!(s:A->bool) t. s SUBSET t /\\ t SUBSET s ==> s = t")

#eval (do let th := Session.UNION_ASSOC
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "UNION_ASSOC (sets.ml 463)" th
            "!(s:A->bool) t u. (s UNION t) UNION u = s UNION (t UNION u)")

#eval (do let th := Session.UNION_COMM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "UNION_COMM (sets.ml 471)" th
            "!(s:A->bool) t. s UNION t = t UNION s")

#eval (do let th := Session.SUBSET_UNION
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "SUBSET_UNION (sets.ml 475)" th
            ("(!s:A->bool. !t. s SUBSET (s UNION t)) /\\ "
             ++ "(!s:A->bool. !t. s SUBSET (t UNION s))"))

#eval (do let th := Session.INTER_COMM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "INTER_COMM (sets.ml 553)" th
            "!(s:A->bool) t. s INTER t = t INTER s")

#eval (do let th := Session.FORALL_SUBSET_UNION
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "FORALL_SUBSET_UNION (sets.ml 508)" th
            ("!t u:A->bool. (!s. s SUBSET t UNION u ==> P s) <=> "
             ++ "(!t' u'. t' SUBSET t /\\ u' SUBSET u ==> P(t' UNION u'))"))

#eval (do let th := Session.INSERT_COMM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "INSERT_COMM (sets.ml 691)" th
            "!x:A. !y s. x INSERT (y INSERT s) = y INSERT (x INSERT s)")

/- ---------------------------------------------------------------------- -/
/- (3) Misc structured proofs (sets.ml 1160-1272).                        -/
/- ---------------------------------------------------------------------- -/

#eval (do let th := Session.INTER_INTERS
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "INTER_INTERS (sets.ml 1160)" th
            ("(!f s:A->bool. s INTER INTERS f = "
             ++ "if f = {} then s else INTERS {s INTER t | t IN f}) /\\ "
             ++ "(!f s:A->bool. INTERS f INTER s = "
             ++ "if f = {} then s else INTERS {t INTER s | t IN f})"))

#eval (do let th := Session.IMAGE_INTERS_SATURATED_GEN
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "IMAGE_INTERS_SATURATED_GEN (sets.ml 1207)" th
            ("!f:A->B g s u. ~(g = {}) /\\ (!t. t IN g ==> t SUBSET u) /\\ "
             ++ "(!t. t IN g DELETE s ==> "
             ++ "{x | x IN u /\\ f(x) IN IMAGE f t} SUBSET t) "
             ++ "==> IMAGE f (INTERS g) = INTERS (IMAGE (IMAGE f) g)"))

#eval (do let th := Session.FINITE_INDUCT_STRONG
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "FINITE_INDUCT_STRONG (sets.ml 1259)" th
            ("!P:(A->bool)->bool. P {} /\\ "
             ++ "(!x s. P s /\\ ~(x IN s) /\\ FINITE s ==> P(x INSERT s)) "
             ++ "==> !s. FINITE s ==> P s"))

/- ---------------------------------------------------------------------- -/
/- (4) Finite / cardinality (sets.ml 1390-2270).                          -/
/- ---------------------------------------------------------------------- -/

#eval (do let th := Session.FINITE_SUBSET
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "FINITE_SUBSET (sets.ml 1390)" th
            "!(s:A->bool) t. FINITE t /\\ s SUBSET t ==> FINITE s")

#eval (do let th := Session.FINITE_UNION
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "FINITE_UNION (sets.ml 1422)" th
            "!(s:A->bool) t. FINITE(s UNION t) <=> FINITE(s) /\\ FINITE(t)")

#eval (do let th := Session.FINITE_INSERT
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "FINITE_INSERT (sets.ml 1433)" th
            "!(s:A->bool) x. FINITE (x INSERT s) <=> FINITE s")

#eval (do let th := Session.CARD_UNION
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "CARD_UNION (sets.ml 2003)" th
            ("!(s:A->bool) t. FINITE(s) /\\ FINITE(t) /\\ (s INTER t = EMPTY) "
             ++ "==> (CARD (s UNION t) = CARD s + CARD t)"))

#eval (do let th := Session.CARD_SUBSET
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "CARD_SUBSET (sets.ml 2268)" th
            "!(a:A->bool) b. a SUBSET b /\\ FINITE(b) ==> CARD(a) <= CARD(b)")

/- ---------------------------------------------------------------------- -/
/- (5) HAS_SIZE machinery (sets.ml 2156-2270).                            -/
/- ---------------------------------------------------------------------- -/

#eval (do let th := Session.HAS_SIZE_UNIONS
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "HAS_SIZE_UNIONS (sets.ml 2156)" th
            ("!s t:A->B->bool m n. s HAS_SIZE m /\\ "
             ++ "(!x. x IN s ==> t(x) HAS_SIZE n) /\\ "
             ++ "(!x y. x IN s /\\ y IN s /\\ ~(x = y) ==> DISJOINT (t x) (t y)) "
             ++ "==> UNIONS {t(x) | x IN s} HAS_SIZE (m * n)"))

#eval (do let th := Session.CARD_LE_1
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "CARD_LE_1 (sets.ml 2603)" th
            "!s:A->bool. FINITE s /\\ CARD s <= 1 <=> ?a. s SUBSET {a}")

#eval (do let th := Session.INVOLUTION_EVEN_NOFIXPOINTS
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "INVOLUTION_EVEN_NOFIXPOINTS (sets.ml 2613)" th
            ("!f (s:A->bool). FINITE s /\\ "
             ++ "(!x. x IN s ==> f x IN s /\\ ~(f x = x) /\\ f(f x) = x) "
             ++ "==> EVEN(CARD s)"))

/- ---------------------------------------------------------------------- -/
/- (6) ITSET recursor (sets.ml 1943-1980).                                -/
/- ---------------------------------------------------------------------- -/

#eval (do let th := Session.FINITE_RECURSION
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "FINITE_RECURSION (sets.ml 1943)" th
            ("!(f:A->B->B) b. "
             ++ "(!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s))) "
             ++ "==> (ITSET f {} b = b) /\\ "
             ++ "!x s. FINITE s ==> (ITSET f (x INSERT s) b = "
             ++ "if x IN s then ITSET f s b else f x (ITSET f s b))"))

#eval (do let th := Session.ITSET_EQ
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "ITSET_EQ (sets.ml 1974)" th
            ("!s (f:A->B->B) g b. FINITE(s) /\\ (!x. x IN s ==> (f x = g x)) /\\ "
             ++ "(!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s))) /\\ "
             ++ "(!x y s. ~(x = y) ==> (g x (g y s) = g y (g x s))) "
             ++ "==> (ITSET f s b = ITSET g s b)"))

/- ---------------------------------------------------------------------- -/
/- (7) CROSS / product cardinality (sets.ml 2734-2772).                   -/
/- ---------------------------------------------------------------------- -/

#eval (do let th := Session.CROSS
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "CROSS def (sets.ml 2734)" th
            "!(s:A->bool) (t:B->bool). s CROSS t = {x,y | x IN s /\\ y IN t}")

#eval (do let th := Session.CROSS_SING
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "CROSS_SING (sets.ml 2763)" th
            "!x:A y:B. {x} CROSS {y} = {(x,y)}")

#eval (do let th := Session.CROSS_UNIV
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "CROSS_UNIV (sets.ml 2767)" th "(:A) CROSS (:B) = (:A#B)")

#eval (do let th := Session.CARD_CROSS
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "CARD_CROSS (sets.ml 2750)" th
            ("!(s:A->bool) (t:B->bool). FINITE s /\\ FINITE t "
             ++ "==> CARD(s CROSS t) = CARD s * CARD t"))

/- ---------------------------------------------------------------------- -/
/- (8) Funspace / bool cardinality (sets.ml 3328-3413).                   -/
/- ---------------------------------------------------------------------- -/

#eval (do let th := Session.HAS_SIZE_BOOL
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "HAS_SIZE_BOOL (sets.ml 3403)" th "(:bool) HAS_SIZE 2")

#eval (do let th := Session.CARD_BOOL
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "CARD_BOOL (sets.ml 3410)" th "CARD(:bool) = 2")

/- ---------------------------------------------------------------------- -/
/- (9) Infinity (sets.ml 3612-3691).                                      -/
/- ---------------------------------------------------------------------- -/

#eval (do let th := Session.num_INFINITE
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "num_INFINITE (sets.ml 3612)" th "INFINITE(:num)")

#eval (do let th := Session.string_INFINITE
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "string_INFINITE (sets.ml 3620)" th "INFINITE(:string)")

#eval (do let th := Session.real_INFINITE
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "real_INFINITE (sets.ml 3689)" th "INFINITE(:real)")

/- ---------------------------------------------------------------------- -/
/- (10) set_of_list / list_of_set / pairwise (sets.ml 3790-3897).         -/
/- ---------------------------------------------------------------------- -/

#eval (do let th := Session.set_of_list
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "set_of_list def (sets.ml 3790)" th
            ("(set_of_list ([]:A list) = {}) /\\ "
             ++ "(set_of_list (CONS (h:A) t) = h INSERT (set_of_list t))"))

#eval (do let th := Session.IN_SET_OF_LIST
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "IN_SET_OF_LIST (sets.ml 3832)" th
            "!x l:A list. x IN (set_of_list l) <=> MEM x l")

#eval (do let th := Session.SET_OF_LIST_APPEND
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "SET_OF_LIST_APPEND (sets.ml 3838)" th
            ("!l1 l2:A list. set_of_list(APPEND l1 l2) = "
             ++ "set_of_list(l1) UNION set_of_list(l2)"))

#eval (do let th := Session.LIST_OF_SET_SING
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "LIST_OF_SET_SING (sets.ml 3858)" th
            "!a:A. list_of_set {a} = [a]")

#eval (do let th := Session.pairwise
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "pairwise def (sets.ml 3894)" th
            ("!(s:A->bool) r. pairwise r s <=> "
             ++ "!x y. x IN s /\\ y IN s /\\ ~(x = y) ==> r x y"))

/- ---------------------------------------------------------------------- -/
/- (11) Cardinal comparisons / countability (sets.ml 4665-4696).          -/
/- ---------------------------------------------------------------------- -/

#eval (do let th := Session.le_c
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "le_c def (sets.ml 4665)" th
            ("!(t:B->bool) (s:A->bool). s <=_c t <=> ?f:A->B. (!x. x IN s ==> f(x) IN t) /\\ "
             ++ "(!x y. x IN s /\\ y IN s /\\ f(x) = f(y) ==> x = y)"))

#eval (do let th := Session.LE_C
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "LE_C (sets.ml 4684)" th
            "!s t. s <=_c t <=> ?g:A->B. !x. x IN s ==> ?y. y IN t /\\ g y = x")

#eval (do let th := Session.GE_C
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "GE_C (sets.ml 4690)" th
            "!s t. s >=_c t <=> ?f:A->B. !y. y IN t ==> ?x. x IN s /\\ (y = f x)")

#eval (do let th := Session.COUNTABLE
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "COUNTABLE def (sets.ml 4694)" th
            "!t:A->bool. COUNTABLE t <=> (:num) >=_c t")

/- ---------------------------------------------------------------------- -/
/- (12) Supremum / infimum (sets.ml 4801-4963).                           -/
/- ---------------------------------------------------------------------- -/

#eval (do let th := Session.SUP_SING
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "SUP_SING (sets.ml 4801)" th "!a. sup {a} = a")

#eval (do let th := Session.SUP_UNION
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "SUP_UNION (sets.ml 4826)" th
            ("!s t. ~(s = {}) /\\ ~(t = {}) /\\ "
             ++ "(?b. !x. x IN s ==> x <= b) /\\ (?c. !x. x IN t ==> x <= c) "
             ++ "==> sup(s UNION t) = max (sup s) (sup t)"))

#eval (do let th := Session.INF_SING
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "INF_SING (sets.ml 4961)" th "!a. inf {a} = a")

/- ---------------------------------------------------------------------- -/
/- (13) HAS_SIZE_CONV examples (Help/HAS_SIZE_CONV.hlp).                   -/
/- A conversion: `expected` is the full equation from the .hlp after |-.   -/
/- ---------------------------------------------------------------------- -/

#eval (do
  let _ ← (IO.mkRef (concl Session.CARD_CLAUSES) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "(s:A->bool) HAS_SIZE 1" with
  | .error e => IO.println s!"HAS_SIZE_CONV.hlp 1 -> MISMATCH parse ERR {e}"
  | .ok tm =>
    ruleOK "HAS_SIZE_CONV.hlp (s HAS_SIZE 1)"
      (Session.HAS_SIZE_CONV tm)
      "s HAS_SIZE 1 <=> (?a. s = {a})")

#eval (do
  let _ ← (IO.mkRef (concl Session.CARD_CLAUSES) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "(t:A->bool) HAS_SIZE 3" with
  | .error e => IO.println s!"HAS_SIZE_CONV.hlp 3 -> MISMATCH parse ERR {e}"
  | .ok tm =>
    ruleOK "HAS_SIZE_CONV.hlp (t HAS_SIZE 3)"
      (Session.HAS_SIZE_CONV tm)
      ("t HAS_SIZE 3 <=> (?a a' a''. ~(a' = a'') /\\ ~(a = a') /\\ "
       ++ "~(a = a'') /\\ t = {a, a', a''})"))

/- HAS_SIZE_CONV must reject a non-`HAS_SIZE` term. -/
#eval (do
  let _ ← (IO.mkRef (concl Session.CARD_CLAUSES) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "T" with
  | .error e => IO.println s!"HAS_SIZE_CONV reject -> MISMATCH parse ERR {e}"
  | .ok tm => failsOK "HAS_SIZE_CONV reject (wrong form)" (Session.HAS_SIZE_CONV tm))

/- ---------------------------------------------------------------------- -/
/- (14) SET_RULE examples (Help/SET_RULE.hlp).  {{..}} in .hlp = {..}.     -/
/- ---------------------------------------------------------------------- -/

#eval (do
  let _ ← (IO.mkRef (concl Session.IN_UNION) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term
    "{x | ~(x IN s <=> x IN t)} = (s DIFF t) UNION (t DIFF s)" with
  | .error e => IO.println s!"SET_RULE.hlp #1 -> MISMATCH parse ERR {e}"
  | .ok tm =>
    ruleOK "SET_RULE.hlp #1" (Session.SET_RULE tm)
      "{x | ~(x IN s <=> x IN t)} = (s DIFF t) UNION (t DIFF s)")

#eval (do
  let _ ← (IO.mkRef (concl Session.IN_UNION) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term
    "UNIONS {t y | y IN x INSERT s} = t x UNION UNIONS {t y | y IN s}" with
  | .error e => IO.println s!"SET_RULE.hlp #2 -> MISMATCH parse ERR {e}"
  | .ok tm =>
    ruleOK "SET_RULE.hlp #2" (Session.SET_RULE tm)
      "UNIONS {t y | y IN x INSERT s} = t x UNION UNIONS {t y | y IN s}")

/- ---------------------------------------------------------------------- -/
/- (15) SET_RULE / SET_TAC Pelletier-style set goals.                     -/
/- ---------------------------------------------------------------------- -/

/- The documented SET_TAC.hlp goal, solved through SET_RULE. -/
#eval (do
  let _ ← (IO.mkRef (concl Session.IN_UNION) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term
    "!s. (UNIONS s = {}) <=> !t. t IN s ==> t = {}" with
  | .error e => IO.println s!"SET_TAC.hlp goal -> MISMATCH parse ERR {e}"
  | .ok tm =>
    ruleOK "SET_TAC.hlp goal (UNIONS empty)" (Session.SET_RULE tm)
      "!s. (UNIONS s = {}) <=> !t. t IN s ==> t = {}")

/- De Morgan / distributive laws – provable by SET_RULE. -/
#eval (do
  let _ ← (IO.mkRef (concl Session.IN_UNION) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term
    "!s t u:A->bool. s INTER (t UNION u) = (s INTER t) UNION (s INTER u)" with
  | .error e => IO.println s!"SET_RULE distrib -> MISMATCH parse ERR {e}"
  | .ok tm =>
    ruleOK "SET_RULE distrib (INTER over UNION)" (Session.SET_RULE tm)
      "!s t u:A->bool. s INTER (t UNION u) = (s INTER t) UNION (s INTER u)")

#eval (do
  let _ ← (IO.mkRef (concl Session.IN_UNION) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term
    "!s t:A->bool. (s SUBSET t) <=> (s UNION t = t)" with
  | .error e => IO.println s!"SET_RULE subset<=>union -> MISMATCH parse ERR {e}"
  | .ok tm =>
    ruleOK "SET_RULE (SUBSET <=> UNION)" (Session.SET_RULE tm)
      "!s t:A->bool. (s SUBSET t) <=> (s UNION t = t)")

#eval (do
  let _ ← (IO.mkRef (concl Session.IN_UNION) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term
    "!s t:A->bool. (s DIFF t = {}) <=> (s SUBSET t)" with
  | .error e => IO.println s!"SET_RULE diff-empty -> MISMATCH parse ERR {e}"
  | .ok tm =>
    ruleOK "SET_RULE (DIFF empty <=> SUBSET)" (Session.SET_RULE tm)
      "!s t:A->bool. (s DIFF t = {}) <=> (s SUBSET t)")

/- An UNPROVABLE (non-valid) set goal: SET_RULE must FAIL, not "prove" it. -/
#eval (do
  let _ ← (IO.mkRef (concl Session.IN_UNION) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term
    "!s t:A->bool. s UNION t = s INTER t" with
  | .error e => IO.println s!"SET_RULE bogus -> MISMATCH parse ERR {e}"
  | .ok tm =>
    failsOK "SET_RULE bogus (UNION = INTER, invalid)" (Session.SET_RULE tm))

/- ---------------------------------------------------------------------- -/
/- Statements checked against real HOL Light (tools/dbdiff).               -/
/- ---------------------------------------------------------------------- -/
/- After pair.ml, `new_definition` is pair.ml's, whose `GEN_ALL` quantifies
   in `frees` order: `GE` is `!n m`, not the drule.ml primitive's `!m n`.
   The three theorems below leave `n` / `s` free, exactly as stated in
   sets.ml. -/
#eval (do let th := Session.GE
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "GE def order (pair.ml new_definition)" th "!n m. m >= n <=> n <= m")
#eval (do let th := Session.IMAGE
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "IMAGE def order (pair.ml new_definition)" th
            "!s (f:A->B). IMAGE f s = {y | ?x. x IN s /\\ y = f x}")
#eval (do let th := Session.BIJECTIONS_HAS_SIZE
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "BIJECTIONS_HAS_SIZE, n free (sets.ml 4600)" th
            ("!s t (f:A->B) g. (!x. x IN s ==> f(x) IN t /\\ g(f x) = x) /\\ "
             ++ "(!y. y IN t ==> g(y) IN s /\\ f(g y) = y) /\\ s HAS_SIZE n ==> t HAS_SIZE n"))
#eval (do let th := Session.REAL_SUP_LE
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "REAL_SUP_LE, s free (sets.ml 4755)" th
            "!b. ~(s = {}) /\\ (!x. x IN s ==> x <= b) ==> sup s <= b")
#eval (do let th := Session.REAL_LE_INF
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "REAL_LE_INF, s free (sets.ml 4915)" th
            "!b. ~(s = {}) /\\ (!x. x IN s ==> b <= x) ==> b <= inf s")

/- CROSS_EMPTY (sets.ml 2759) gives its `{}`s no type, so they get invented
   type variables; stating them as `{}:B->bool` and `{}:A->bool` made a
   different theorem that prints the same.  Found by tools/dbdiff/scompare.py. -/
#eval (do let th := Session.CROSS_EMPTY
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          let tvs := (HolCore.Kernel.type_vars_in_term (concl th)).map dest_vartype
          IO.println (if tvs.any (fun v => match v with | .ok n => n.startsWith "?" | _ => false)
                      then "CROSS_EMPTY has invented type variables (sets.ml 2759) -> OK"
                      else s!"CROSS_EMPTY has invented type variables (sets.ml 2759) -> MISMATCH {tvs.length} vars, none invented"))
