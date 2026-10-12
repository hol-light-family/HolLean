/- File: HolTest/NumsArithWfCheck.lean
Self-checking tests for nums.ml, arith.ml, wf.ml: theorem statements checked
against the OCaml source, and documented examples from hol-light/Help.
Lean4 translation by Chris Walton 2026 -/

import HolTest.CommonTest

open HolCore.Parser HolCore.Bool HolCore.Kernel HolCore.Equal Session
     HolCore.Basics HolCore.Lib HolTest.CommonTest

/- ====================================================================== -/
/- nums.ml : theorem statements (verbatim OCaml).                          -/
/- Each stmtOK evaluates the theorem itself, which forces the num layer    -/
/- (the `let th := ...; force; stmtOK` idiom from the brief).              -/
/- ====================================================================== -/

-- NOT_SUC (nums.ml 75), rewritten by `_0 = 0` at nums.ml 138 so `_0` prints 0.
#eval (do let th := Session.NOT_SUC
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "NOT_SUC (nums.ml 75)" th "!n. ~(SUC n = 0)")

-- SUC_INJ (nums.ml 80)
#eval (do let th := Session.SUC_INJ
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "SUC_INJ (nums.ml 80)" th "!m n. SUC m = SUC n <=> m = n")

-- num_INDUCTION (nums.ml 96, rewritten _0=0)
#eval (do let th := Session.num_INDUCTION
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "num_INDUCTION (nums.ml 96)" th
            "!P. P(0) /\\ (!n. P(n) ==> P(SUC n)) ==> !n. P n")

-- num_Axiom (nums.ml 116, rewritten _0=0)
#eval (do let th := Session.num_Axiom
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "num_Axiom (nums.ml 116)" th
            "!(e:A) f. ?!fn. (fn 0 = e) /\\ (!n. fn (SUC n) = f (fn n) n)")

-- num_CASES (nums.ml 177)
#eval (do let th := Session.num_CASES
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "num_CASES (nums.ml 177)" th "!m. (m = 0) \\/ (?n. m = SUC n)")

/- ---- nums.ml Help examples: numeral syntax functions ---- -/

-- mk_small_numeral.hlp : mk_small_numeral 12 -> `12`
#eval (do
  let _ ← (IO.mkRef (concl Session.NOT_SUC) : IO (IO.Ref term))
  match Session.mk_small_numeral 12 with
  | .error e => IO.println s!"mk_small_numeral.hlp -> MISMATCH err {e}"
  | .ok t =>
    let s ← HolCore.Printer.string_of_term t
    IO.println (if s == "12" then "mk_small_numeral.hlp -> OK"
                else s!"mk_small_numeral.hlp -> MISMATCH got {s} expected 12"))

-- mk_small_numeral.hlp : "Fails if the argument is negative."
#eval (do
  match Session.mk_small_numeral (-3) with
  | .error _ => IO.println "mk_small_numeral negative -> OK (correctly rejected)"
  | .ok _ => IO.println "mk_small_numeral negative -> MISMATCH accepted negative")

-- dest_small_numeral.hlp : dest_small_numeral `12` -> 12
#eval (do
  let _ ← (IO.mkRef (concl Session.NOT_SUC) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "12" with
  | .error e => IO.println s!"dest_small_numeral.hlp -> MISMATCH parse {e}"
  | .ok t =>
    match Session.dest_small_numeral t with
    | .ok m => IO.println (if m == 12 then "dest_small_numeral.hlp -> OK"
                           else s!"dest_small_numeral.hlp -> MISMATCH got {m} expected 12")
    | .error e => IO.println s!"dest_small_numeral.hlp -> MISMATCH err {e}")

-- dest_small_numeral: fails on a non-numeral (SUC 0)
#eval (do
  let _ ← (IO.mkRef (concl Session.NOT_SUC) : IO (IO.Ref term))
  match Session.dest_small_numeral ([[ SUC 0 ]]) with
  | .error _ => IO.println "dest_small_numeral (SUC 0) -> OK (correctly rejected)"
  | .ok m => IO.println s!"dest_small_numeral (SUC 0) -> MISMATCH accepted got {m}")

-- is_numeral.hlp : true on a canonical numeral, false on SUC 0
#eval (do
  let _ ← (IO.mkRef (concl Session.NOT_SUC) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "12" with
  | .error e => IO.println s!"is_numeral.hlp (12) -> MISMATCH parse {e}"
  | .ok t => IO.println (if Session.is_numeral t then "is_numeral.hlp (12) -> OK"
                         else "is_numeral.hlp (12) -> MISMATCH got false expected true"))
#eval (do
  let _ ← (IO.mkRef (concl Session.NOT_SUC) : IO (IO.Ref term))
  IO.println (if Session.is_numeral ([[ SUC 0 ]]) == false
              then "is_numeral (SUC 0) -> OK"
              else "is_numeral (SUC 0) -> MISMATCH got true expected false"))

-- mk_numeral round-trip across the 2^24 chunk boundary (value-level assertion).
#eval (do
  let _ ← (IO.mkRef (concl Session.NOT_SUC) : IO (IO.Ref term))
  for n in [(0:Int), 1, 255, 16777215, 16777216, 16777217] do
    match Session.mk_numeral (Rat.ofInt n) with
    | .error e => IO.println s!"mk_numeral round-trip {n} -> MISMATCH err {e}"
    | .ok t =>
      match Session.dest_small_numeral t with
      | .ok m => IO.println (if m == n then s!"mk_numeral round-trip {n} -> OK"
                             else s!"mk_numeral round-trip {n} -> MISMATCH got {m}")
      | .error e => IO.println s!"mk_numeral round-trip {n} -> MISMATCH dest {e}")

/- ---- nums.ml : new_specification failure messages (verbatim OCaml) ---- -/

-- "Assumptions not allowed in theorem" (nums.ml 283)
#eval (do
  match ASSUME ([[ ?x. x = 0 ]]) with
  | .error e => IO.println s!"new_spec assumptions -> MISMATCH setup {e}"
  | .ok ath =>
    failsOK "new_spec assumptions (nums.ml 283)"
      (Session.new_specification ["Z"] ath)
      "new_specification: Assumptions not allowed in theorem")

-- "Free variables in predicate:" (nums.ml 285) - REFL `y:num` has free `y`
#eval failsOK "new_spec free-vars (nums.ml 285)"
  (Session.new_specification ["Z"] (REFL ([[ y:num ]])))
  "new_specification: Free variables in predicate:"

-- "Unsuitable number of constant names" (nums.ml 289): too many / none
#eval (do
  match ← Session.prove ([[ ?x. x = 0 ]]) (Session.MESON_TAC []) with
  | .error e => IO.println s!"new_spec too-many -> MISMATCH setup {e}"
  | .ok exth =>
    failsOK "new_spec too-many (nums.ml 289)"
      (Session.new_specification ["A", "B"] exth)
      "new_specification: Unsuitable number of constant names")
#eval (do
  match ← Session.prove ([[ ?x. x = 0 ]]) (Session.MESON_TAC []) with
  | .error e => IO.println s!"new_spec no-names -> MISMATCH setup {e}"
  | .ok exth =>
    failsOK "new_spec no-names (nums.ml 289)"
      (Session.new_specification [] exth)
      "new_specification: Unsuitable number of constant names")

-- "Constant names not distinct" (nums.ml 291): needs a 2-existential theorem.
#eval (do
  match ← Session.prove ([[ ?x y. x = 0 /\ y = 0 ]]) (Session.MESON_TAC []) with
  | .error e => IO.println s!"new_spec dup-names -> MISMATCH setup {e}"
  | .ok th2 =>
    failsOK "new_spec dup-names (nums.ml 291)"
      (Session.new_specification ["A", "A"] th2)
      "new_specification: Constant names not distinct")

/- ====================================================================== -/
/- arith.ml : theorem statements spread across the bundles Ar1..Ar9.       -/
/- ====================================================================== -/

-- Ar1 (add / bit clauses)
#eval (do let th := Session.ADD_SYM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "ADD_SYM (arith.ml 67)" th "!m n. m + n = n + m")
#eval (do let th := Session.ADD_ASSOC
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "ADD_ASSOC (arith.ml 71)" th "!m n p. m + (n + p) = (m + n) + p")
#eval (do let th := Session.ADD_EQ_0
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "ADD_EQ_0 (arith.ml 81)" th "!m n. (m + n = 0) <=> (m = 0) /\\ (n = 0)")
#eval (do let th := Session.ADD1
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "ADD1 (arith.ml 137)" th "!m. SUC m = m + 1")

-- Ar2 (mult / exp)
#eval (do let th := Session.MULT_SYM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "MULT_SYM (arith.ml 166)" th "!m n. m * n = n * m")
#eval (do let th := Session.MULT_CLAUSES
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "MULT_CLAUSES (arith.ml 157)" th
            "(!n. 0 * n = 0) /\\ (!m. m * 0 = 0) /\\ (!n. 1 * n = n) /\\ (!m. m * 1 = m) /\\ (!m n. (SUC m) * n = (m * n) + n) /\\ (!m n. m * (SUC n) = m + (m * n))")
#eval (do let th := Session.MULT_2
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "MULT_2 (arith.ml 203)" th "!n. 2 * n = n + n")
#eval (do let th := Session.EXP_ADD
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "EXP_ADD (arith.ml 236)" th "!m n p. m EXP (n + p) = (m EXP n) * (m EXP p)")
#eval (do let th := Session.EXP_2
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "EXP_2 (arith.ml 249)" th "!n. n EXP 2 = n * n")

-- Ar3 (order theory)
#eval (do let th := Session.LE_REFL
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "LE_REFL (arith.ml 334)" th "!n. n <= n")
#eval (do let th := Session.LT_REFL
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "LT_REFL (arith.ml 338)" th "!n. ~(n < n)")
#eval (do let th := Session.LE_ANTISYM
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "LE_ANTISYM (arith.ml 350)" th "!m n. (m <= n /\\ n <= m) <=> (m = n)")
#eval (do let th := Session.LE_TRANS
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "LE_TRANS (arith.ml 372)" th "!m n p. m <= n /\\ n <= p ==> m <= p")

-- Ar4 (additive order / WF)
#eval (do let th := Session.LE_ADD
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "LE_ADD (arith.ml 509)" th "!m n. m <= m + n")
#eval (do let th := Session.num_WF
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "num_WF (arith.ml 657)" th "!P. (!n. (!m. m < n ==> P m) ==> P n) ==> !n. P n")
#eval (do let th := Session.num_WOP
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "num_WOP (arith.ml 662)" th
            "!P. (?n. P n) <=> (?n. P(n) /\\ !m. m < n ==> ~P(m))")

-- Ar5 (parity / subtraction / factorial)
#eval (do let th := Session.EVEN_OR_ODD
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "EVEN_OR_ODD (arith.ml 732)" th "!n. EVEN n \\/ ODD n")
#eval (do let th := Session.EVEN_ADD
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "EVEN_ADD (arith.ml 741)" th "!m n. EVEN(m + n) <=> (EVEN m <=> EVEN n)")
#eval (do let th := Session.SUB_REFL
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "SUB_REFL (arith.ml 857)" th "!n. n - n = 0")
#eval (do let th := Session.ADD_SUB
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "ADD_SUB (arith.ml 861)" th "!m n. (m + n) - n = m")

-- Ar7 (division / modulus)
#eval (do let th := Session.DIVISION
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "DIVISION (arith.ml 1094)" th
            "!m n. ~(n = 0) ==> (m = m DIV n * n + m MOD n) /\\ m MOD n < n")
#eval (do let th := Session.MOD_LT
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "MOD_LT (arith.ml 1183)" th "!m n. m < n ==> m MOD n = m")
#eval (do let th := Session.MOD_REFL
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "MOD_REFL (arith.ml 1398)" th "!n. n MOD n = 0")

-- Ar9 (minimal / dependent choice)
#eval (do let th := Session.minimal
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "minimal (arith.ml 1772)" th
            "!P:num->bool. (minimal) P = @n. P n /\\ !m. m < n ==> ~(P m)")
#eval (do let th := Session.MINIMAL
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "MINIMAL (arith.ml 1775)" th
            "!P. (?n. P n) <=> P((minimal) P) /\\ (!m. m < (minimal) P ==> ~(P m))")

/- ---- arith.ml Help examples: conversions and rules ---- -/

-- NUM_CANCEL_CONV.hlp
#eval (do
  let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term
            "(a + b + x * y + SUC c) + d = SUC c + d + y * z" with
  | .error e => IO.println s!"NUM_CANCEL_CONV.hlp -> MISMATCH parse {e}"
  | .ok tm =>
    ruleOK "NUM_CANCEL_CONV.hlp" (Session.NUM_CANCEL_CONV tm)
      "(a + b + x * y + SUC c) + d = SUC c + d + y * z <=> x * y + b + a = y * z")

-- MOD_DOWN_CONV.hlp
#eval (do
  let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "(x MOD n + (y MOD n * 3) EXP 2) MOD n" with
  | .error e => IO.println s!"MOD_DOWN_CONV.hlp -> MISMATCH parse {e}"
  | .ok tm =>
    ruleOK "MOD_DOWN_CONV.hlp" (Session.MOD_DOWN_CONV tm)
      "(x MOD n + (y MOD n * 3) EXP 2) MOD n = (x + (y * 3) EXP 2) MOD n")

-- BITS_ELIM_CONV.hlp
#eval (do
  let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
  match ← Session.BITS_ELIM_CONV with
  | .error e => IO.println s!"BITS_ELIM_CONV.hlp -> MISMATCH build {e}"
  | .ok conv =>
    match ← HolCore.Parser.parse_term "BIT0(BIT1(BIT1 _0)) = 6" with
    | .error e => IO.println s!"BITS_ELIM_CONV.hlp -> MISMATCH parse {e}"
    | .ok tm =>
      ruleOK "BITS_ELIM_CONV.hlp" (pure (conv tm))
        "BIT0 (BIT1 (BIT1 _0)) = 6 <=> 2 * (2 * (2 * 0 + 1) + 1) = 6")

-- LE_IMP.hlp shape: LE_IMP applied to LE_ADD (|- !m n. m <= m + n) chains it.
--   LE_ADD : |- !m n. m <= m + n ; LE_IMP introduces a fresh upper bound.
#eval (do
  let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
  ruleOK "LE_IMP LE_ADD (LE_IMP.hlp)" (Session.LE_IMP Session.LE_ADD)
    "!n m p. m + n <= p ==> m <= p")

/- ---- arith.ml : minimal binder actually parses (Ar9 forced first) ---- -/
#eval (do
  let _ ← (IO.mkRef (concl Session.MINIMAL) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "minimal n. 3 < n" with
  | .ok _ => IO.println "minimal binder parse -> OK"
  | .error e => IO.println s!"minimal binder parse -> MISMATCH {e}")

/- ---- arith.ml : decision-procedure-flavoured proofs from the layer ---- -/
#eval (do
  let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "!m n. m + n = 0 ==> m = 0" with
  | .error e => IO.println s!"ADD_EQ_0 proof -> MISMATCH parse {e}"
  | .ok g => ruleOK "ADD_EQ_0 proof" (Session.prove g (Session.MESON_TAC [Session.ADD_EQ_0]))
               "!m n. m + n = 0 ==> m = 0")
#eval (do
  let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "!n. EVEN n \\/ ODD n" with
  | .error e => IO.println s!"EVEN_OR_ODD proof -> MISMATCH parse {e}"
  | .ok g => ruleOK "EVEN_OR_ODD proof" (Session.prove g (Session.MESON_TAC [Session.EVEN_OR_ODD]))
               "!n. EVEN n \\/ ODD n")
#eval (do
  let _ ← (IO.mkRef (concl Session.ADD_SYM) : IO (IO.Ref term))
  match ← HolCore.Parser.parse_term "!n. n MOD n = 0" with
  | .error e => IO.println s!"MOD_REFL proof -> MISMATCH parse {e}"
  | .ok g => ruleOK "MOD_REFL proof" (Session.prove g (Session.MESON_TAC [Session.MOD_REFL]))
               "!n. n MOD n = 0")

/- ====================================================================== -/
/- wf.ml : theorem statements (verbatim OCaml) and applications.           -/
/- ====================================================================== -/

-- WF (wf.ml 18, new_definition)
#eval (do let th := Session.WF
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "WF (wf.ml 18)" th
            "!(<<). WF(<<) <=> !P:A->bool. (?x. P(x)) ==> (?x. P(x) /\\ !y. y << x ==> ~P(y))")
-- WF_EQ (wf.ml 25)
#eval (do let th := Session.WF_EQ
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "WF_EQ (wf.ml 25)" th
            "WF(<<) <=> !P:A->bool. (?x. P(x)) <=> (?x. P(x) /\\ !y. y << x ==> ~P(y))")
-- WF_IND (wf.ml 33)
#eval (do let th := Session.WF_IND
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "WF_IND (wf.ml 33)" th
            "WF(<<) <=> !P:A->bool. (!x. (!y. y << x ==> P(y)) ==> P(x)) ==> !x. P(x)")
-- WF_DCHAIN (wf.ml 42)
#eval (do let th := Session.WF_DCHAIN
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "WF_DCHAIN (wf.ml 42)" th
            "WF(<<) <=> ~(?s:num->A. !n. s(SUC n) << s(n))")
-- WF_SUBSET (wf.ml 188)
#eval (do let th := Session.WF_SUBSET
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "WF_SUBSET (wf.ml 188)" th
            "!(<<) (<<<). (!(x:A) y. x << y ==> x <<< y) /\\ WF(<<<) ==> WF(<<)")
-- WF_MEASURE_GEN (wf.ml 200)
#eval (do let th := Session.WF_MEASURE_GEN
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "WF_MEASURE_GEN (wf.ml 200)" th "!(<<) (m:A->B). WF(<<) ==> WF(\\x x'. m x << m x')")
-- WF_LEX (wf.ml 226)
#eval (do let th := Session.WF_LEX
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "WF_LEX (wf.ml 226)" th
            "!R:A->A->bool S:B->B->bool. WF(R) /\\ WF(S) ==> WF(\\(r1,s1) (r2,s2). R r1 r2 \\/ (r1 = r2) /\\ S s1 s2)")
-- WF_num (wf.ml 244)
#eval (do let th := Session.WF_num
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "WF_num (wf.ml 244)" th "WF(<)")
-- MEASURE (wf.ml 257, new_definition)
#eval (do let th := Session.MEASURE
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "MEASURE (wf.ml 257)" th "!m:A->num. MEASURE m = \\x y. m(x) < m(y)")
-- WF_MEASURE (wf.ml 260)
#eval (do let th := Session.WF_MEASURE
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "WF_MEASURE (wf.ml 260)" th "!m:A->num. WF(MEASURE m)")
-- WF_REFL (wf.ml 281)
#eval (do let th := Session.WF_REFL
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "WF_REFL (wf.ml 281)" th "!x:A. WF(<<) ==> ~(x << x)")
-- WF_FALSE (wf.ml 289)
#eval (do let th := Session.WF_FALSE
          let _ ← (IO.mkRef (concl th) : IO (IO.Ref term))
          stmtOK "WF_FALSE (wf.ml 289)" th "WF(\\x y:A. F)")

/- ---- wf.ml : WF_INDUCT_TAC used to prove real goals ---- -/

-- WF induction proving commutativity of + on the measure m+n.
#eval (do
  match ← HolCore.Parser.parse_term "!m n. m + n = n + m" with
  | .error e => IO.println s!"WF_INDUCT_TAC comm -> MISMATCH goal {e}"
  | .ok g =>
    match ← HolCore.Parser.parse_term "m + n:num" with
    | .error e => IO.println s!"WF_INDUCT_TAC comm -> MISMATCH meas {e}"
    | .ok meas =>
      ruleOK "WF_INDUCT_TAC comm"
        (Session.prove g
          (THEN Session.GEN_TAC (THEN Session.GEN_TAC
            (THEN (Session.WF_INDUCT_TAC meas)
              (Session.ASM_MESON_TAC [Session.ADD_SYM])))))
        "!m n. m + n = n + m")

-- WF induction with a single-variable measure n.
#eval (do
  match ← HolCore.Parser.parse_term "!n. n = 0 \\/ 0 < n" with
  | .error e => IO.println s!"WF_INDUCT_TAC single -> MISMATCH goal {e}"
  | .ok g =>
    match ← HolCore.Parser.parse_term "n:num" with
    | .error e => IO.println s!"WF_INDUCT_TAC single -> MISMATCH meas {e}"
    | .ok meas =>
      ruleOK "WF_INDUCT_TAC single"
        (Session.prove g
          (THEN Session.GEN_TAC
            (THEN (Session.WF_INDUCT_TAC meas)
              (Session.MESON_TAC [Session.num_CASES, Session.LT_0]))))
        "!n. n = 0 \\/ 0 < n")

/- ---- wf.ml : WF theorems applied as tools ---- -/

-- WF_MEASURE applied: MEASURE of any num-valued function is wellfounded.
#eval (do
  match ← HolCore.Parser.parse_term "WF(MEASURE (\\n:num. n))" with
  | .error e => IO.println s!"WF_MEASURE applied -> MISMATCH parse {e}"
  | .ok g =>
    ruleOK "WF_MEASURE applied" (Session.prove g (Session.MESON_TAC [Session.WF_MEASURE]))
      "WF(MEASURE (\\n:num. n))")

-- WF_SUBSET applied: a sub-relation of `<` is wellfounded.
#eval (do
  match ← HolCore.Parser.parse_term "WF(\\m n:num. m < n /\\ m < 5)" with
  | .error e => IO.println s!"WF_SUBSET applied -> MISMATCH parse {e}"
  | .ok g =>
    ruleOK "WF_SUBSET applied"
      (Session.prove g (Session.MESON_TAC [Session.WF_SUBSET, Session.WF_num]))
      "WF(\\m n:num. m < n /\\ m < 5)")
