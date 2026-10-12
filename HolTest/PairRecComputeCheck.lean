/- File: HolTest/PairRecComputeCheck.lean
Self-checking tests for pair.ml, recursion.ml, compute.ml, grobner.ml: theorem
statements checked against the OCaml source, and documented examples from
hol-light/Help.
Lean4 translation by Chris Walton 2026 -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ====================================================================== -/
/- pair.ml : theory of pairing.  Statements are checked with `stmtOK`      -/
/- against the VERBATIM OCaml `prove(`...`)` bodies.  The pair layer is     -/
/- forced first (reading a pair theorem in the SAME #eval as the parse),    -/
/- so `,`/`FST`/`SND`/`#` parse as the real constants and `aconv` sees the  -/
/- same generic type variables the polymorphic statements carry.           -/
/- ====================================================================== -/

-- PAIR_EQ (pair.ml 76): !(x:A) (y:B) a b. (x,y = a,b) <=> (x = a) /\ (y = b)
#eval (do let th := Session.PAIR_EQ
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "PAIR_EQ (pair.ml 76)" th
            "!(x:A) (y:B) a b. (x,y = a,b) <=> (x = a) /\\ (y = b)")

-- PAIR_SURJECTIVE (pair.ml 87): !p:A#B. ?x y. p = x,y
#eval (do let th := Session.PAIR_SURJECTIVE
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "PAIR_SURJECTIVE (pair.ml 87)" th "!p:A#B. ?x y. p = x,y")

-- FST (pair.ml 97): !(x:A) (y:B). FST(x,y) = x
#eval (do let th := Session.FST
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "FST (pair.ml 97)" th "!(x:A) (y:B). FST(x,y) = x")

-- SND (pair.ml 104): !(x:A) (y:B). SND(x,y) = y
#eval (do let th := Session.SND
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "SND (pair.ml 104)" th "!(x:A) (y:B). SND(x,y) = y")

-- PAIR (pair.ml 111): !x:A#B. FST x,SND x = x
#eval (do let th := Session.PAIR
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "PAIR (pair.ml 111)" th "!x:A#B. FST x,SND x = x")

-- pair_INDUCT (pair.ml 118): !P:A#B->bool. (!x y. P (x,y)) ==> !p. P p
#eval (do let th := Session.pair_INDUCT
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "pair_INDUCT (pair.ml 118)" th
            "!P:A#B->bool. (!x y. P (x,y)) ==> !p. P p")

-- pair_RECURSION (pair.ml 124): !PAIR'. ?fn:A#B->C. !a0 a1. fn (a0,a1) = PAIR' a0 a1
#eval (do let th := Session.pair_RECURSION
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "pair_RECURSION (pair.ml 124)" th
            "!PAIR'. ?fn:A#B->C. !a0 a1. fn (a0,a1) = PAIR' a0 a1")

-- FORALL_PAIR_THM (pair.ml 234): !P:A#B->bool. (!p. P p) <=> (!p1 p2. P(p1,p2))
#eval (do let th := Session.FORALL_PAIR_THM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "FORALL_PAIR_THM (pair.ml 234)" th
            "!P:A#B->bool. (!p. P p) <=> (!p1 p2. P(p1,p2))")

-- EXISTS_PAIR_THM (pair.ml 238): !P:A#B->bool. (?p. P p) <=> ?p1 p2. P(p1,p2)
#eval (do let th := Session.EXISTS_PAIR_THM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "EXISTS_PAIR_THM (pair.ml 238)" th
            "!P:A#B->bool. (?p. P p) <=> ?p1 p2. P(p1,p2)")

-- LAMBDA_PAIR_THM (pair.ml 242): !t:A#B->C. (\p. t p) = (\(x,y). t(x,y))
#eval (do let th := Session.LAMBDA_PAIR_THM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "LAMBDA_PAIR_THM (pair.ml 242)" th
            "!t:A#B->C. (\\p. t p) = (\\(x,y). t(x,y))")

-- LAMBDA_PAIR (pair.ml 246): !f:A->B->C. (\(x,y). f x y) = (\p. f (FST p) (SND p))
#eval (do let th := Session.LAMBDA_PAIR
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "LAMBDA_PAIR (pair.ml 246)" th
            "!f:A->B->C. (\\(x,y). f x y) = (\\p. f (FST p) (SND p))")

-- LAMBDA_TRIPLE_THM (pair.ml 250): !f:A#B#C->D. (\t. f t) = (\(x,y,z). f(x,y,z))
#eval (do let th := Session.LAMBDA_TRIPLE_THM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "LAMBDA_TRIPLE_THM (pair.ml 250)" th
            "!f:A#B#C->D. (\\t. f t) = (\\(x,y,z). f(x,y,z))")

-- PAIRED_ETA_THM (pair.ml 259): the three-clause conjunction, verbatim.
#eval (do let th := Session.PAIRED_ETA_THM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "PAIRED_ETA_THM (pair.ml 259)" th
            "(!f:A#B->C. (\\(x,y). f (x,y)) = f) /\\ (!f:A#B#C->D. (\\(x,y,z). f (x,y,z)) = f) /\\ (!f:A#B#C#D->E. (\\(w,x,y,z). f (w,x,y,z)) = f)")

-- FORALL_UNCURRY (pair.ml 266): !P. (!f:A->B->C. P f) <=> (!f. P (\a b. f(a,b)))
#eval (do let th := Session.FORALL_UNCURRY
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "FORALL_UNCURRY (pair.ml 266)" th
            "!P. (!f:A->B->C. P f) <=> (!f. P (\\a b. f(a,b)))")

-- EXISTS_UNCURRY (pair.ml 273): !P. (?f:A->B->C. P f) <=> (?f. P (\a b. f(a,b)))
#eval (do let th := Session.EXISTS_UNCURRY
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "EXISTS_UNCURRY (pair.ml 273)" th
            "!P. (?f:A->B->C. P f) <=> (?f. P (\\a b. f(a,b)))")

-- EXISTS_CURRY (pair.ml 278): !P:(A#B->C)->bool. (?f. P f) <=> (?f. P (\(a,b). f a b))
#eval (do let th := Session.EXISTS_CURRY
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "EXISTS_CURRY (pair.ml 278)" th
            "!P:(A#B->C)->bool. (?f. P f) <=> (?f. P (\\(a,b). f a b))")

-- FORALL_CURRY (pair.ml 282): !P:(A#B->C)->bool. (!f. P f) <=> (!f. P (\(a,b). f a b))
#eval (do let th := Session.FORALL_CURRY
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "FORALL_CURRY (pair.ml 282)" th
            "!P:(A#B->C)->bool. (!f. P f) <=> (!f. P (\\(a,b). f a b))")

-- FORALL_UNPAIR_THM (pair.ml 286): !P:A->B->bool. (!x y. P x y) <=> !z. P (FST z) (SND z)
#eval (do let th := Session.FORALL_UNPAIR_THM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "FORALL_UNPAIR_THM (pair.ml 286)" th
            "!P:A->B->bool. (!x y. P x y) <=> !z. P (FST z) (SND z)")

-- EXISTS_UNPAIR_THM (pair.ml 290): !P:A->B->bool. (?x y. P x y) <=> ?z. P (FST z) (SND z)
#eval (do let th := Session.EXISTS_UNPAIR_THM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "EXISTS_UNPAIR_THM (pair.ml 290)" th
            "!P:A->B->bool. (?x y. P x y) <=> ?z. P (FST z) (SND z)")

-- FORALL_PAIR_FUN_THM (pair.ml 294): !P. (!f:A->B#C. P f) <=> (!g h. P(\a. g a,h a))
#eval (do let th := Session.FORALL_PAIR_FUN_THM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "FORALL_PAIR_FUN_THM (pair.ml 294)" th
            "!P. (!f:A->B#C. P f) <=> (!g h. P(\\a. g a,h a))")

-- EXISTS_PAIR_FUN_THM (pair.ml 300): !P. (?f:A->B#C. P f) <=> (?g h. P(\a. g a,h a))
#eval (do let th := Session.EXISTS_PAIR_FUN_THM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "EXISTS_PAIR_FUN_THM (pair.ml 300)" th
            "!P. (?f:A->B#C. P f) <=> (?g h. P(\\a. g a,h a))")

-- FORALL_UNPAIR_FUN_THM (pair.ml 304): !P:(A->B)->(A->C)->bool. (!f g. P f g) <=> (!h. P (FST o h) (SND o h))
#eval (do let th := Session.FORALL_UNPAIR_FUN_THM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "FORALL_UNPAIR_FUN_THM (pair.ml 304)" th
            "!P:(A->B)->(A->C)->bool. (!f g. P f g) <=> (!h. P (FST o h) (SND o h))")

-- EXISTS_SWAP_FUN_THM (pair.ml 312): !P:(A->B->C)->bool. (?f. P f) <=> (?f. P (\a b. f b a))
#eval (do let th := Session.EXISTS_SWAP_FUN_THM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "EXISTS_SWAP_FUN_THM (pair.ml 312)" th
            "!P:(A->B->C)->bool. (?f. P f) <=> (?f. P (\\a b. f b a))")

-- FORALL_PAIRED_THM (pair.ml 325): !P:A->B->bool. (!(x,y). P x y) <=> (!x y. P x y)
#eval (do let th := Session.FORALL_PAIRED_THM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "FORALL_PAIRED_THM (pair.ml 325)" th
            "!P:A->B->bool. (!(x,y). P x y) <=> (!x y. P x y)")

-- EXISTS_PAIRED_THM (pair.ml 330): !P:A->B->bool. (?(x,y). P x y) <=> (?x y. P x y)
#eval (do let th := Session.EXISTS_PAIRED_THM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "EXISTS_PAIRED_THM (pair.ml 330)" th
            "!P:A->B->bool. (?(x,y). P x y) <=> (?x y. P x y)")

-- FORALL_TRIPLED_THM (pair.ml 339): !P:A->B->C->bool. (!(x,y,z). P x y z) <=> (!x y z. P x y z)
#eval (do let th := Session.FORALL_TRIPLED_THM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "FORALL_TRIPLED_THM (pair.ml 339)" th
            "!P:A->B->C->bool. (!(x,y,z). P x y z) <=> (!x y z. P x y z)")

-- EXISTS_TRIPLED_THM (pair.ml 344): !P:A->B->C->bool. (?(x,y,z). P x y z) <=> (?x y z. P x y z)
#eval (do let th := Session.EXISTS_TRIPLED_THM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "EXISTS_TRIPLED_THM (pair.ml 344)" th
            "!P:A->B->C->bool. (?(x,y,z). P x y z) <=> (?x y z. P x y z)")

-- CHOICE_UNPAIR_THM (pair.ml 353): !P. (@(x:A,y:B). P x y) = (@p. P (FST p) (SND p))
#eval (do let th := Session.CHOICE_UNPAIR_THM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "CHOICE_UNPAIR_THM (pair.ml 353)" th
            "!P. (@(x:A,y:B). P x y) = (@p. P (FST p) (SND p))")

-- CHOICE_PAIRED_THM (pair.ml 357): !P Q. (?x:A y:B. P x y) /\ (!x y. P x y ==> Q(x,y)) ==> Q (@(x,y). P x y)
#eval (do let th := Session.CHOICE_PAIRED_THM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "CHOICE_PAIRED_THM (pair.ml 357)" th
            "!P Q. (?x:A y:B. P x y) /\\ (!x y. P x y ==> Q(x,y)) ==> Q (@(x,y). P x y)")

/- ---------------------------------------------------------------------- -/
/- pair.ml definitions (statements verbatim from `new_definition`).        -/
/- ---------------------------------------------------------------------- -/

-- CURRY_DEF (pair.ml 209): CURRY(f:A#B->C) x y = f(x,y)  (fully generalized)
#eval (do let th := Session.CURRY_DEF
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "CURRY_DEF (pair.ml 209)" th
            "!f x y. CURRY(f:A#B->C) x y = f(x,y)")

-- UNCURRY_DEF (pair.ml 212): !f x y. UNCURRY(f:A->B->C)(x,y) = f x y
#eval (do let th := Session.UNCURRY_DEF
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "UNCURRY_DEF (pair.ml 212)" th
            "!f x y. UNCURRY(f:A->B->C)(x,y) = f x y")

-- PASSOC_DEF (pair.ml 215): !f x y z. PASSOC (f:(A#B)#C->D) (x,y,z) = f ((x,y),z)
#eval (do let th := Session.PASSOC_DEF
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "PASSOC_DEF (pair.ml 215)" th
            "!f x y z. PASSOC (f:(A#B)#C->D) (x,y,z) = f ((x,y),z)")

/- ---------------------------------------------------------------------- -/
/- pair.ml syntax operations: is_pair / dest_pair / mk_pair.               -/
/- ---------------------------------------------------------------------- -/

#eval (do let _ ← (IO.mkRef (concl Session.PAIR_EQ) : IO (IO.Ref term))
          let ab := [[ ((a:A),(b:B)) ]]
          if Session.is_pair ab then IO.println "is_pair (pair.ml 130) -> OK"
          else IO.println "is_pair (pair.ml 130) -> MISMATCH (returned false)")

#eval (do let _ ← (IO.mkRef (concl Session.PAIR_EQ) : IO (IO.Ref term))
          if Session.is_pair [[ (c:A) ]] then
            IO.println "is_pair non-pair -> MISMATCH (returned true)"
          else IO.println "is_pair non-pair -> OK")

#eval (do let _ ← (IO.mkRef (concl Session.PAIR_EQ) : IO (IO.Ref term))
          match Session.dest_pair [[ ((a:A),(b:B)) ]] with
          | .ok (l, r) =>
            let ls := (← HolCore.Printer.string_of_term l).replace " " ""
            let rs := (← HolCore.Printer.string_of_term r).replace " " ""
            if ls == "a" && rs == "b" then IO.println "dest_pair (pair.ml 132) -> OK"
            else IO.println s!"dest_pair (pair.ml 132) -> MISMATCH ({ls},{rs})"
          | .error e => IO.println s!"dest_pair (pair.ml 132) -> MISMATCH err {e}")

/- ---------------------------------------------------------------------- -/
/- pair.ml GEN_BETA_CONV / let_CONV / SUBLET_CONV.  Examples transcribed    -/
/- VERBATIM from the .hlp EXAMPLE sections (result after `|-`).  Numerals    -/
/- require the arithmetic layer, so force it (reading ADD_SYM) first.        -/
/- ---------------------------------------------------------------------- -/

-- GEN_BETA_CONV.hlp: (\x. x + 1) 2 = 2 + 1  (simple redex)
#eval (do let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
          ruleOK "GEN_BETA_CONV.hlp simple"
            (Session.GEN_BETA_CONV [[ (\x. x + 1) 2 ]])
            "(\\x. x + 1) 2 = 2 + 1")

-- GEN_BETA_CONV.hlp: (\(x,y,z). x + y + z) (1,2,3) = 1 + 2 + 3  (tupled redex)
#eval (do let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
          ruleOK "GEN_BETA_CONV.hlp tupled"
            (Session.GEN_BETA_CONV [[ (\(x,y,z). x + y + z) (1,2,3) ]])
            "(\\(x,y,z). x + y + z) (1,2,3) = 1 + 2 + 3")

-- GEN_BETA_CONV.hlp: mismatch (\(x,y,z). x+y+z) (1,x) FAILS.
#eval (do let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
          failsOK "GEN_BETA_CONV.hlp mismatch"
            (Session.GEN_BETA_CONV [[ (\(x,y,z). x + y + z) (1,x) ]]))

-- let_CONV.hlp: let x = 1 in x+y  =>  |- (let x = 1 in x + y) = 1 + y
#eval (do let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
          ruleOK "let_CONV.hlp single"
            (Session.let_CONV [[ let x = 1 in x + y ]])
            "(let x = 1 in x + y) = 1 + y")

-- let_CONV.hlp: let (x,y) = (1,2) in x+y  =>  |- (let x,y = 1,2 in x + y) = 1 + 2
#eval (do let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
          ruleOK "let_CONV.hlp tupled"
            (Session.let_CONV [[ let (x,y) = (1,2) in x + y ]])
            "(let x,y = 1,2 in x + y) = 1 + 2")

-- let_CONV.hlp: let x = 1 and y = 2 in x + y + z  =>  |- ... = 1 + 2 + z
#eval (do let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
          ruleOK "let_CONV.hlp simultaneous"
            (Session.let_CONV [[ let x = 1 and y = 2 in x + y + z ]])
            "(let x = 1 and y = 2 in x + y + z) = 1 + 2 + z")

-- let_CONV must FAIL on a non-let term.
#eval (do let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
          failsOK "let_CONV non-let" (Session.let_CONV [[ x + y ]]))

-- SUBLET_CONV.hlp: SUBLET_CONV NUM_ADD_CONV `let x = 5 + 2 and y = 8 + 17 and
-- z = 3 + 7 in x + y + z` reduces the RHSs (leaving the let-body untouched).
#eval (do let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
          ruleOK "SUBLET_CONV.hlp"
            (Session.SUBLET_CONV Session.NUM_ADD_CONV
               [[ let x = 5 + 2 and y = 8 + 17 and z = 3 + 7 in x + y + z ]])
            "(let x = 5 + 2 and y = 8 + 17 and z = 3 + 7 in x + y + z) = (let x = 7 and y = 25 and z = 10 in x + y + z)")

/- ---------------------------------------------------------------------- -/
/- pair.ml LET_TAC: proves a let-equivalence goal.                          -/
/- ---------------------------------------------------------------------- -/

#eval (do
  ruleOK "LET_TAC (pair.ml 379)"
    (Session.prove ([[ (let x = a in (f:A->bool) x) <=> f a ]])
       (THEN Session.LET_TAC (Session.ASM_REWRITE_TAC [])))
    "(let x = a in (f:A->bool) x) <=> f a")

/- ====================================================================== -/
/- recursion.ml : primitive-recursive definition.  Acceptance yields the   -/
/- exact defining theorem (ruleOK against the clause conjunction), and      -/
/- ill-formed inputs are rejected (failsOK).  Fresh constant names (NRC_*)  -/
/- avoid clashing with the constants declared by other test modules that    -/
/- are compiled together.  num_RECURSION forces the `num` layer.            -/
/- ====================================================================== -/

-- Acceptance: PRE-style recursion.  new_recursive_definition returns
-- |- NRC_PRE 0 = 0 /\ (!n. NRC_PRE (SUC n) = n).
#eval (do
  let _ ← (IO.mkRef (concl Session.num_RECURSION) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "(NRC_PRE 0 = 0) /\\ (!n. NRC_PRE (SUC n) = n)" with
  | .error e => IO.println s!"NRC_PRE parse ERR -> MISMATCH {e}"
  | .ok tm =>
    ruleOK "new_recursive_definition PRE (recursion.ml)"
      (Session.new_recursive_definition Session.num_RECURSION tm)
      "NRC_PRE 0 = 0 /\\ (!n. NRC_PRE (SUC n) = n)")

-- Benign redefinition: defining the same clauses again returns the same thm.
#eval (do
  let _ ← (IO.mkRef (concl Session.num_RECURSION) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "(NRC_PRE 0 = 0) /\\ (!n. NRC_PRE (SUC n) = n)" with
  | .error e => IO.println s!"NRC_PRE redef parse ERR -> MISMATCH {e}"
  | .ok tm =>
    ruleOK "new_recursive_definition PRE benign redef"
      (Session.new_recursive_definition Session.num_RECURSION tm)
      "NRC_PRE 0 = 0 /\\ (!n. NRC_PRE (SUC n) = n)")

-- Acceptance with the recursion argument NOT first (exercises `reshuffle`):
-- NRC_ADDY m 0 = m /\ NRC_ADDY m (SUC n) = SUC (NRC_ADDY m n).
#eval (do
  let _ ← (IO.mkRef (concl Session.num_RECURSION) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term
            "(!m. NRC_ADDY m 0 = m) /\\ (!m n. NRC_ADDY m (SUC n) = SUC (NRC_ADDY m n))" with
  | .error e => IO.println s!"NRC_ADDY parse ERR -> MISMATCH {e}"
  | .ok tm =>
    ruleOK "new_recursive_definition ADDY (arg not first)"
      (Session.new_recursive_definition Session.num_RECURSION tm)
      "(!m. NRC_ADDY m 0 = m) /\\ (!m n. NRC_ADDY m (SUC n) = SUC (NRC_ADDY m n))")

-- The defined function actually computes: NRC_PRE2 (SUC (SUC 0)) = SUC 0.
#eval (do
  let _ ← (IO.mkRef (concl Session.num_RECURSION) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "(NRC_PRE2 0 = 0) /\\ (!n. NRC_PRE2 (SUC n) = n)" with
  | .error e => IO.println s!"NRC_PRE2 parse ERR -> MISMATCH {e}"
  | .ok tm =>
    match ← Session.new_recursive_definition Session.num_RECURSION tm with
    | .error e => IO.println s!"NRC_PRE2 def -> MISMATCH err {e}"
    | .ok dth =>
      match ← HolCore.Parser.parse_term "NRC_PRE2 (SUC (SUC 0)) = SUC 0" with
      | .error e => IO.println s!"NRC_PRE2 goal parse ERR -> MISMATCH {e}"
      | .ok goal =>
        ruleOK "new_recursive_definition PRE2 computes"
          (Session.prove goal (Session.REWRITE_TAC [dth]))
          "NRC_PRE2 (SUC (SUC 0)) = SUC 0")

-- prove_recursive_functions_exist: existence form (?fn. ...).
#eval (do
  let _ ← (IO.mkRef (concl Session.num_RECURSION) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "(fnE 0 = 0) /\\ (!n. fnE (SUC n) = SUC (fnE n))" with
  | .error e => IO.println s!"prove_recursive_functions_exist parse ERR -> MISMATCH {e}"
  | .ok tm =>
    ruleOK "prove_recursive_functions_exist (recursion.ml)"
      (Session.prove_recursive_functions_exist Session.num_RECURSION tm)
      "?fnE. fnE 0 = 0 /\\ (!n. fnE (SUC n) = SUC (fnE n))")

-- Rejection: two functions defined at once against num_RECURSION must FAIL.
#eval (do
  let _ ← (IO.mkRef (concl Session.num_RECURSION) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term
            "(NRC_P9 0 = 0) /\\ (!n. NRC_P9 (SUC n) = n) /\\ (NRC_Q9 0 = 0) /\\ (!n. NRC_Q9 (SUC n) = SUC n)" with
  | .error e => IO.println s!"two-fn parse ERR -> MISMATCH {e}"
  | .ok tm =>
    failsOK "new_recursive_definition two functions (must reject)"
      (Session.new_recursive_definition Session.num_RECURSION tm))

/- ====================================================================== -/
/- compute.ml : call-by-value reduction.  `the_compset = bool_compset()`,   -/
/- so `EVAL_CONV`/`CBV_CONV` reduce the BOOLEAN operators (and COND/LET).    -/
/- Each equation `t = t'` is checked with `ruleOK` (printing-independent).   -/
/- ====================================================================== -/

-- EVAL_CONV on the boolean clauses: T /\ F reduces to F, etc.
#eval ruleOK "EVAL_CONV T/\\F" (Session.EVAL_CONV [[ T /\ F ]]) "(T /\\ F) <=> F"
#eval ruleOK "EVAL_CONV T\\/F" (Session.EVAL_CONV [[ T \/ F ]]) "(T \\/ F) <=> T"
#eval ruleOK "EVAL_CONV ~F" (Session.EVAL_CONV [[ ~F ]]) "~F <=> T"
#eval ruleOK "EVAL_CONV T==>F" (Session.EVAL_CONV [[ T ==> F ]]) "(T ==> F) <=> F"
#eval ruleOK "EVAL_CONV nested" (Session.EVAL_CONV [[ (T /\ T) /\ (F \/ T) ]])
  "(T /\\ T) /\\ (F \\/ T) <=> T"
#eval ruleOK "EVAL_CONV beta" (Session.EVAL_CONV [[ (\x. x /\ T) T ]])
  "(\\x. x /\\ T) T <=> T"

-- EVAL_CONV on COND (skip-argument reduction registered by bool_compset).
#eval ruleOK "EVAL_CONV cond-T" (Session.EVAL_CONV [[ if T then (a:A) else b ]])
  "(if T then (a:A) else b) = a"
#eval ruleOK "EVAL_CONV cond-F" (Session.EVAL_CONV [[ if F then (a:A) else b ]])
  "(if F then (a:A) else b) = b"

-- EVAL_CONV on LET.  `the_compset = bool_compset()` (compute.ml 786), whose
-- rules are `LET_DEF` and the boolean clauses (754-758) - NOT `LET_END_DEF`
-- (that, via let_CONV, is only in `basic_compset`).  So the `let` unfolds and
-- the body reduces, but the result stays wrapped in `LET_END`.
#eval ruleOK "EVAL_CONV let (bool_compset: LET_DEF, no LET_END_DEF)"
  (Session.EVAL_CONV [[ let x = T in x /\ F ]]) "(let x = T in x /\\ F) <=> LET_END F"

-- WEAK_CBV_CONV against the explicit bool compset: reduces (\x. x/\T) T.
#eval (do
  let cs ← Session.the_compset
  ruleOK "WEAK_CBV_CONV beta" (Session.WEAK_CBV_CONV cs [[ (\x. x /\ T) T ]])
    "(\\x. x /\\ T) T <=> T")

-- CBV_CONV against the explicit bool compset (full normalization).
#eval (do
  let cs ← Session.the_compset
  ruleOK "CBV_CONV nested" (Session.CBV_CONV cs [[ (T \/ F) /\ (T ==> T) ]])
    "(T \\/ F) /\\ (T ==> T) <=> T")

-- EVAL_RULE = CONV_RULE EVAL_CONV (compute.ml 795) evaluates the WHOLE
-- conclusion: `REFL t` states `t <=> t`, which the boolean clauses reduce to T.
#eval ruleOK "EVAL_RULE (REFL t) evaluates the whole conclusion"
  (Session.EVAL_RULE (REFL [[ (T /\ T) \/ F ]])) "T"

-- EVAL_TAC proves a true boolean goal outright.
#eval ruleOK "EVAL_TAC" (Session.prove ([[ (T /\ T) \/ F ]]) Session.EVAL_TAC)
  "(T /\\ T) \\/ F"

-- lazyfy_thm returns a usable rewrite (an equation/conjunction of equations).
#eval (do
  match ← Session.lazyfy_thm Session.AND_CLAUSES with
  | .error e => IO.println s!"lazyfy_thm AND_CLAUSES -> MISMATCH err {e}"
  | .ok th =>
    if (hyp th).isEmpty then IO.println "lazyfy_thm AND_CLAUSES -> OK"
    else IO.println "lazyfy_thm AND_CLAUSES -> MISMATCH (has hypotheses)")

-- RESTR_EVAL_CONV stops at `\/`: the disjunction survives (NOT reduced to T),
-- yet the conjunctions inside are reduced, so the result differs from `... <=> T`.
#eval (do
  match ← Session.RESTR_EVAL_CONV [([[ (\/) ]])] [[ (T /\ T) /\ (F \/ T) ]] with
  | .error e => IO.println s!"RESTR_EVAL_CONV stop-or -> MISMATCH err {e}"
  | .ok th =>
    let rhsStr := (← HolCore.Printer.string_of_thm th)
    if (rhsStr.splitOn "\\/").length ≥ 2 then IO.println "RESTR_EVAL_CONV stop-or -> OK"
    else IO.println s!"RESTR_EVAL_CONV stop-or -> MISMATCH (disjunction gone) {rhsStr}")

-- The stopper flag is restored afterwards: a plain EVAL_CONV reduces fully.
#eval ruleOK "EVAL_CONV after RESTR (flag restored)"
  (Session.EVAL_CONV [[ (T /\ T) /\ (F \/ T) ]])
  "(T /\\ T) /\\ (F \\/ T) <=> T"

/- ====================================================================== -/
/- grobner.ml : NUM_RING documented examples (Help/NUM_RING.hlp).           -/
/- The arithmetic layer must be forced before EXP/`+`/`*` parse as          -/
/- constants; NUM_RING itself forces it, but force explicitly to be safe.   -/
/- ====================================================================== -/

-- NUM_RING.hlp: proves (x + y) EXP 2 = x EXP 2 ==> y = 0 \/ y + 2 * x = 0
#eval (do
  let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "(x + y) EXP 2 = x EXP 2 ==> y = 0 \\/ y + 2 * x = 0" with
  | .error e => IO.println s!"NUM_RING.hlp thm parse ERR -> MISMATCH {e}"
  | .ok tm =>
    ruleOK "NUM_RING.hlp theorem" (Session.NUM_RING tm)
      "(x + y) EXP 2 = x EXP 2 ==> y = 0 \\/ y + 2 * x = 0")

-- NUM_RING.hlp: the companion NON-theorem must FAIL ("find").
#eval (do
  let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "(x + y) EXP 2 = x EXP 2 ==> y = 0 \\/ x = 0" with
  | .error e => IO.println s!"NUM_RING.hlp nonthm parse ERR -> MISMATCH {e}"
  | .ok tm =>
    failsOK "NUM_RING.hlp non-theorem (must fail)" (Session.NUM_RING tm))

-- A textbook integral-domain identity NUM_RING proves (binomial square).
#eval (do
  let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term
            "(a + b) * (a + b) = a EXP 2 + 2 * a * b + b EXP 2" with
  | .error e => IO.println s!"NUM_RING binom parse ERR -> MISMATCH {e}"
  | .ok tm =>
    ruleOK "NUM_RING binomial square" (Session.NUM_RING tm)
      "(a + b) * (a + b) = a EXP 2 + 2 * a * b + b EXP 2")

-- Integral-domain cancellation: (a + c = b + c) <=> (a = b).
#eval (do
  let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "(a + c = b + c) <=> (a = b)" with
  | .error e => IO.println s!"NUM_RING cancel parse ERR -> MISMATCH {e}"
  | .ok tm =>
    ruleOK "NUM_RING cancellation" (Session.NUM_RING tm)
      "(a + c = b + c) <=> (a = b)")

-- A clearly false num equation NUM_RING must NOT prove.
#eval (do
  let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "a + b = a * b" with
  | .error e => IO.println s!"NUM_RING false parse ERR -> MISMATCH {e}"
  | .ok tm =>
    failsOK "NUM_RING false identity (must fail)" (Session.NUM_RING tm))
