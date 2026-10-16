/- File: HolTutorial/SemanticsOfProgrammingLanguagesShallow.lean
Translation of HOL Light's
Tutorial/Semantics_of_programming_languages_shallow.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolTutorial.Common
open HolCore.Kernel Session HolLight.Syntax HolTutorial
namespace HolTutorial.SemanticsOfProgrammingLanguagesShallow

/-- Run an `IO (Except String α)` once, caching under `name` (OCaml's `let`
    evaluates its right-hand side once).  Used for the `let X,Y,Z = e`
    bindings whose result is a tuple, for which there is no `thm` coercion. -/
unsafe def keepIO {α : Type} [Inhabited α] (name : String) (f : Unit → IO (Except String α)) : α :=
  keep name fun _ =>
    match unsafeIO (f ()) with
    | .ok (.ok v) => v
    | .ok (.error e) => panic! s!"keepIO {name}: {e}"
    | .error e => panic! s!"keepIO {name}: {e}"

#eval phrase 1
-- let assign = new_definition `Assign (f:S->S) (q:S->bool) = q o f`;;
unsafe def assign : thm := keep "assign" fun _ => new_definition
  [[Assign (f:S->S) (q:S->bool) = q o f]]
#eval assign

#eval phrase 2
-- parse_as_infix(";;",(18,"right"));;
#eval (parse_as_infix (";;", (18, "right")) : IO Unit)

#eval phrase 3
-- let sequence = new_definition
--  `(c1:(S->bool)->(S->bool)) ;; (c2:(S->bool)->(S->bool)) = c1 o c2`;;
unsafe def sequence : thm := keep "sequence" fun _ => new_definition
  [[(c1:(S->bool)->(S->bool)) ;; (c2:(S->bool)->(S->bool)) = c1 o c2]]
#eval sequence

#eval phrase 4
-- let if_def = new_definition
--  `If e (c:(S->bool)->(S->bool)) q = {s | if e s then c q s else q s}`;;
unsafe def if_def : thm := keep "if_def" fun _ => new_definition
  [[If e (c:(S->bool)->(S->bool)) q = {s | if e s then c q s else q s}]]
#eval if_def

#eval phrase 5
-- let ite_def = new_definition
--  `Ite e (c1:(S->bool)->(S->bool)) c2 q = {s | if e s then c1 q s else c2 q s}`;;
unsafe def ite_def : thm := keep "ite_def" fun _ => new_definition
  [[Ite e (c1:(S->bool)->(S->bool)) c2 q =
    {s | if e s then c1 q s else c2 q s}]]
#eval ite_def

#eval phrase 6
-- let while_RULES,while_INDUCT,while_CASES = new_inductive_definition
--          `!q s. If e (c ;; while e c) q s ==> while e c q s`;;
unsafe def while_defs : thm × thm × thm :=
  keepIO "while_defs" fun _ => new_inductive_definition
  [[!q s. If e (c ;; while e c) q s ==> while e c q s]]
unsafe def while_RULES : thm := while_defs.1
unsafe def while_INDUCT : thm := while_defs.2.1
unsafe def while_CASES : thm := while_defs.2.2
#eval do IO.println (repr while_RULES); IO.println (repr while_INDUCT); IO.println (repr while_CASES)

#eval phrase 7
-- let while_def = new_definition
--  `While e c q = {s | !w. (!s:S. (if e(s) then c w s else q s) ==> w s) ==> w s}`;;
unsafe def while_def : thm := keep "while_def" fun _ => new_definition
  [[While e c q =
    {s | !w. (!s:S. (if e(s) then c w s else q s) ==> w s) ==> w s}]]
#eval while_def

#eval phrase 8
-- let monotonic = new_definition `monotonic c <=> !q q'. q SUBSET q' ==> (c q) SUBSET (c q')`;;
unsafe def monotonic : thm := keep "monotonic" fun _ => new_definition
  [[monotonic c <=> !q q'. q SUBSET q' ==> (c q) SUBSET (c q')]]
#eval monotonic

#eval phrase 9
-- let MONOTONIC_ASSIGN = prove (`monotonic (Assign f)`, ...);;
unsafe def MONOTONIC_ASSIGN : thm := keep "MONOTONIC_ASSIGN" fun _ => prove
 ([[monotonic (Assign f)]])
  (SIMP_TAC [monotonic, assign, SUBSET, o_THM, IN])
#eval MONOTONIC_ASSIGN

#eval phrase 10
-- let MONOTONIC_IF = prove (`monotonic c ==> monotonic (If e c)`, ...);;
unsafe def MONOTONIC_IF : thm := keep "MONOTONIC_IF" fun _ => prove
 ([[monotonic c ==> monotonic (If e c)]])
  (REWRITE_TAC [monotonic, if_def] THEN SET_TAC [])
#eval MONOTONIC_IF

#eval phrase 11
-- let MONOTONIC_ITE = prove (`monotonic c1 /\ monotonic c2 ==> monotonic (Ite e c1 c2)`, ...);;
unsafe def MONOTONIC_ITE : thm := keep "MONOTONIC_ITE" fun _ => prove
 ([[monotonic c1 /\ monotonic c2 ==> monotonic (Ite e c1 c2)]])
  (REWRITE_TAC [monotonic, ite_def] THEN SET_TAC [])
#eval MONOTONIC_ITE

#eval phrase 12
-- let MONOTONIC_SEQ = prove (`monotonic c1 /\ monotonic c2 ==> monotonic (c1 ;; c2)`, ...);;
unsafe def MONOTONIC_SEQ : thm := keep "MONOTONIC_SEQ" fun _ => prove
 ([[monotonic c1 /\ monotonic c2 ==> monotonic (c1 ;; c2)]])
  (REWRITE_TAC [monotonic, sequence, o_THM] THEN SET_TAC [])
#eval MONOTONIC_SEQ

#eval phrase 13
-- let MONOTONIC_WHILE = prove (`monotonic c ==> monotonic(While e c)`, ...);;
unsafe def MONOTONIC_WHILE : thm := keep "MONOTONIC_WHILE" fun _ => prove
 ([[monotonic c ==> monotonic(While e c)]])
  (REWRITE_TAC [monotonic, while_def] THEN SET_TAC [])
#eval MONOTONIC_WHILE

#eval phrase 14
-- let WHILE_THM = prove (`!e c q:S->bool. ...`, ...);;
unsafe def WHILE_THM : thm := keep "WHILE_THM" fun _ => prove
 ([[!e c q:S->bool.
    monotonic c
    ==> (!s. If e (c ;; While e c) q s ==> While e c q s) /\
        (!w'. (!s. If e (c ;; (\q. w')) q s ==> w' s)
              ==> (!a. While e c q a ==> w' a)) /\
        (!s. While e c q s <=> If e (c ;; While e c) q s)]])
  (REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (GEN_ALL (DISCH_ALL
    (derive_nonschematic_inductive_relations
      ([[!s:S. (if e s then c w s else q s) ==> w s]]) : thm))) THEN
  REWRITE_TAC [if_def, sequence, o_THM, IN_ELIM_THM, IMP_IMP] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC [FUN_EQ_THM, while_def, IN_ELIM_THM] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC [monotonic] THEN SET_TAC [])
#eval WHILE_THM

#eval phrase 15
-- let WHILE_FIX = prove (`!e c. monotonic c ==> (While e c = If e (c ;; While e c))`, ...);;
unsafe def WHILE_FIX : thm := keep "WHILE_FIX" fun _ => prove
 ([[!e c. monotonic c ==> (While e c = If e (c ;; While e c))]])
  (REWRITE_TAC [FUN_EQ_THM] THEN MESON_TAC [WHILE_THM])
#eval WHILE_FIX

#eval phrase 16
-- let correct = new_definition `correct p c q <=> p SUBSET (c q)`;;
unsafe def correct : thm := keep "correct" fun _ => new_definition
  [[correct p c q <=> p SUBSET (c q)]]
#eval correct

#eval phrase 17
-- let CORRECT_PRESTRENGTH = prove (`!p p' c q. ...`, ...);;
unsafe def CORRECT_PRESTRENGTH : thm := keep "CORRECT_PRESTRENGTH" fun _ => prove
 ([[!p p' c q. p SUBSET p' /\ correct p' c q ==> correct p c q]])
  (REWRITE_TAC [correct, SUBSET_TRANS])
#eval CORRECT_PRESTRENGTH

#eval phrase 18
-- let CORRECT_POSTWEAK = prove (`!p c q q'. monotonic c /\ ...`, ...);;
unsafe def CORRECT_POSTWEAK : thm := keep "CORRECT_POSTWEAK" fun _ => prove
 ([[!p c q q'. monotonic c /\ correct p c q' /\ q' SUBSET q ==> correct p c q]])
  (REWRITE_TAC [correct, monotonic] THEN SET_TAC [])
#eval CORRECT_POSTWEAK

#eval phrase 19
-- let CORRECT_ASSIGN = prove (`!p f q. (p SUBSET (q o f)) ==> correct p (Assign f) q`, ...);;
unsafe def CORRECT_ASSIGN : thm := keep "CORRECT_ASSIGN" fun _ => prove
 ([[!p f q. (p SUBSET (q o f)) ==> correct p (Assign f) q]])
  (REWRITE_TAC [correct, assign])
#eval CORRECT_ASSIGN

#eval phrase 20
-- let CORRECT_SEQ = prove (`!p q r c1 c2. monotonic c1 /\ ...`, ...);;
unsafe def CORRECT_SEQ : thm := keep "CORRECT_SEQ" fun _ => prove
 ([[!p q r c1 c2.
        monotonic c1 /\ correct p c1 r /\ correct r c2 q
        ==> correct p (c1 ;; c2) q]])
  (REWRITE_TAC [correct, sequence, monotonic, o_THM] THEN SET_TAC [])
#eval CORRECT_SEQ

#eval phrase 21
-- let CORRECT_ITE = prove (`!p e c1 c2 q. ...`, ...);;
unsafe def CORRECT_ITE : thm := keep "CORRECT_ITE" fun _ => prove
 ([[!p e c1 c2 q.
       correct (p INTER e) c1 q /\ correct (p INTER (UNIV DIFF e)) c2 q
       ==> correct p (Ite e c1 c2) q]])
  (REWRITE_TAC [correct, ite_def] THEN SET_TAC [])
#eval CORRECT_ITE

#eval phrase 22
-- let CORRECT_IF = prove (`!p e c q. ...`, ...);;
unsafe def CORRECT_IF : thm := keep "CORRECT_IF" fun _ => prove
 ([[!p e c q.
       correct (p INTER e) c q /\ p INTER (UNIV DIFF e) SUBSET q
       ==> correct p (If e c) q]])
  (REWRITE_TAC [correct, if_def] THEN SET_TAC [])
#eval CORRECT_IF

#eval phrase 23
-- let CORRECT_WHILE = prove (`!(<<) p c q e invariant. ...`, ...);;
unsafe def CORRECT_WHILE : thm := keep "CORRECT_WHILE" fun _ => prove
 ([[!(<<) p c q e invariant.
      monotonic c /\
      WF(<<) /\
      p SUBSET invariant /\
      (UNIV DIFF e) INTER invariant SUBSET q /\
      (!X:S. correct (invariant INTER e INTER (\s. X = s)) c
                     (invariant INTER (\s. s << X)))
      ==> correct p (While e c) q]])
  (REWRITE_TAC [correct, SUBSET, IN_INTER, IN_UNIV, IN_DIFF, IN] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN ([[!s:S. invariant s ==> While e c q s]]) MP_TAC THENL
   [ALL_TAC, ASM_MESON_TAC []] THEN
  FIRST_ASSUM (fun th => HolLight.tactic_of do pure (MATCH_MP_TAC (← REWRITE_RULE [WF_IND] th))) THEN
  X_GEN_TAC ([[s:S]]) THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM (fun th => HolLight.tactic_of do pure (ONCE_REWRITE_TAC [← MATCH_MP WHILE_FIX th])) THEN
  REWRITE_TAC [if_def, sequence, o_THM, IN_ELIM_THM] THEN
  COND_CASES_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
  FIRST_X_ASSUM (fun th => HolLight.tactic_of do pure (MP_TAC (← SPECL [ [[s:S]], [[s:S]] ] th))) THEN ASM_REWRITE_TAC [] THEN
  FIRST_X_ASSUM (fun th => HolLight.tactic_of do pure (MP_TAC (← GEN_REWRITE_RULE HolCore.Lib.I [monotonic] th))) THEN
  REWRITE_TAC [SUBSET, IN, RIGHT_IMP_FORALL_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC [INTER, IN_ELIM_THM, IN])
#eval CORRECT_WHILE

#eval phrase 24
-- let assert_def = new_definition `assert (p:S->bool) (q:S->bool) = q`;;
unsafe def assert_def : thm := keep "assert_def" fun _ => new_definition
  [[assert (p:S->bool) (q:S->bool) = q]]
#eval assert_def

#eval phrase 25
-- let variant_def = new_definition `variant ((<<):S->S->bool) (q:S->bool) = q`;;
unsafe def variant_def : thm := keep "variant_def" fun _ => new_definition
  [[variant ((<<):S->S->bool) (q:S->bool) = q]]
#eval variant_def

#eval phrase 26
-- let CORRECT_SEQ_VC = prove (`!p q r c1 c2. ...`, ...);;
unsafe def CORRECT_SEQ_VC : thm := keep "CORRECT_SEQ_VC" fun _ => prove
 ([[!p q r c1 c2.
        monotonic c1 /\ correct p c1 r /\ correct r c2 q
        ==> correct p (c1 ;; assert r ;; c2) q]])
  (REWRITE_TAC [correct, sequence, monotonic, assert_def, o_THM] THEN SET_TAC [])
#eval CORRECT_SEQ_VC

#eval phrase 27
-- let CORRECT_WHILE_VC = prove (`!(<<) p c q e invariant. ...`, ...);;
unsafe def CORRECT_WHILE_VC : thm := keep "CORRECT_WHILE_VC" fun _ => prove
 ([[!(<<) p c q e invariant.
      monotonic c /\
      WF(<<) /\
      p SUBSET invariant /\
      (UNIV DIFF e) INTER invariant SUBSET q /\
      (!X:S. correct (invariant INTER e INTER (\s. X = s)) c
                     (invariant INTER (\s. s << X)))
      ==> correct p (While e (assert invariant ;; variant(<<) ;; c)) q]])
  (REPEAT STRIP_TAC THEN
  REWRITE_TAC [sequence, variant_def, assert_def, o_DEF, ETA_AX] THEN
  ASM_MESON_TAC [CORRECT_WHILE])
#eval CORRECT_WHILE_VC

#eval phrase 28
-- let MONOTONIC_ASSERT = prove (`monotonic (assert p)`, ...);;
unsafe def MONOTONIC_ASSERT : thm := keep "MONOTONIC_ASSERT" fun _ => prove
 ([[monotonic (assert p)]])
  (REWRITE_TAC [assert_def, monotonic])
#eval MONOTONIC_ASSERT

#eval phrase 29
-- let MONOTONIC_VARIANT = prove (`monotonic (variant p)`, ...);;
unsafe def MONOTONIC_VARIANT : thm := keep "MONOTONIC_VARIANT" fun _ => prove
 ([[monotonic (variant p)]])
  (REWRITE_TAC [variant_def, monotonic])
#eval MONOTONIC_VARIANT

#eval phrase 30
-- let MONO_TAC = REPEAT(...) THEN MAP_FIRST MATCH_ACCEPT_TAC [...];;
unsafe def MONO_TAC :=
  REPEAT (MATCH_MP_TAC MONOTONIC_WHILE ORELSE
         (MAP_FIRST MATCH_MP_TAC
           [MONOTONIC_SEQ, MONOTONIC_IF, MONOTONIC_ITE] THEN CONJ_TAC)) THEN
  MAP_FIRST MATCH_ACCEPT_TAC
   [MONOTONIC_ASSIGN, MONOTONIC_ASSERT, MONOTONIC_VARIANT]
#eval (IO.println "<fun>" : IO Unit)

#eval phrase 31
-- let VC_TAC = FIRST [ ... ];;
unsafe def VC_TAC :=
  FIRST
   [MATCH_MP_TAC CORRECT_SEQ_VC THEN CONJ_TAC THENL [MONO_TAC, CONJ_TAC],
    MATCH_MP_TAC CORRECT_ITE THEN CONJ_TAC,
    MATCH_MP_TAC CORRECT_IF THEN CONJ_TAC,
    MATCH_MP_TAC CORRECT_WHILE_VC THEN REPEAT CONJ_TAC THENL
     [MONO_TAC, TRY (MATCH_ACCEPT_TAC WF_MEASURE), ALL_TAC, ALL_TAC,
      REWRITE_TAC [FORALL_PAIR_THM, MEASURE] THEN REPEAT GEN_TAC],
    MATCH_MP_TAC CORRECT_ASSIGN]
#eval (IO.println "<fun>" : IO Unit)

#eval phrase 32
-- needs "Library/prime.ml";;
#eval SessionLibrary.Prime.ensurePrime

#eval phrase 33
-- (* x = m, y = n; ... *)
-- g `correct (\(m,n,x,y). T) ( ... ) (\(m,n,x,y). gcd(m,n) = x)`;;
#eval g ([[correct
    (\(m,n,x,y). T)
    (Assign (\(m,n,x,y). m,n,m,n) ;;         // x,y := m,n
     assert (\(m,n,x,y). x = m /\ y = n) ;;
     While (\(m,n,x,y). ~(x = 0 \/ y = 0))
      (assert (\(m,n,x,y). gcd(x,y) = gcd(m,n)) ;;
       variant(MEASURE(\(m,n,x,y). x + y)) ;;
       Ite (\(m,n,x,y). x < y)
           (Assign (\(m,n,x,y). m,n,x,y - x))
           (Assign (\(m,n,x,y). m,n,x - y,y))) ;;
     assert (\(m,n,x,y). (x = 0 \/ y = 0) /\ gcd(x,y) = gcd(m,n)) ;;
     If (\(m,n,x,y). x = 0) (Assign (\(m,n,x,y). (m,n,y,y))))
  (\(m,n,x,y). gcd(m,n) = x)]])

#eval phrase 34
-- e(REPEAT VC_TAC);;
#eval e (REPEAT VC_TAC)

#eval phrase 35
-- b();;
#eval b

#eval phrase 36
-- e(REPEAT VC_TAC THEN ... );;
#eval e (REPEAT VC_TAC THEN REWRITE_TAC [SUBSET, FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [ [[m:num]], [[n:num]], [[x:num]], [[y:num]] ] THEN
  REWRITE_TAC [IN, INTER, UNIV, DIFF, o_DEF, IN_ELIM_THM, PAIR_EQ] THEN
  CONV_TAC (HolLight.TOP_DEPTH_CONV GEN_BETA_CONV) THEN SIMP_TAC [])

#eval phrase 37
-- e(SIMP_TAC[GCD_SUB; LT_IMP_LE]);;
#eval e (SIMP_TAC [SessionLibrary.Prime.GCD_SUB, LT_IMP_LE])

#eval phrase 38
-- e ARITH_TAC;;
#eval e ARITH_TAC

#eval phrase 39
-- e(SIMP_TAC[GCD_SUB; NOT_LT] THEN ARITH_TAC);;
#eval e (SIMP_TAC [SessionLibrary.Prime.GCD_SUB, NOT_LT] THEN ARITH_TAC)

#eval phrase 40
-- e(MESON_TAC[GCD_0]);;
#eval e (MESON_TAC [SessionLibrary.Prime.GCD_0])

#eval phrase 41
-- e(MESON_TAC[GCD_0; GCD_SYM]);;
#eval e (MESON_TAC [SessionLibrary.Prime.GCD_0, SessionLibrary.Prime.GCD_SYM])

#eval phrase 42
-- parse_as_infix("refines",(12,"right"));;
#eval (parse_as_infix ("refines", (12, "right")) : IO Unit)

#eval phrase 43
-- let refines = new_definition `c2 refines c1 <=> !q. c1(q) SUBSET c2(q)`;;
unsafe def refines : thm := keep "refines" fun _ => new_definition
  [[c2 refines c1 <=> !q. c1(q) SUBSET c2(q)]]
#eval refines

#eval phrase 44
-- let REFINES_REFL = prove (`!c. c refines c`, ...);;
unsafe def REFINES_REFL : thm := keep "REFINES_REFL" fun _ => prove
 ([[!c. c refines c]])
  (REWRITE_TAC [refines, SUBSET_REFL])
#eval REFINES_REFL

#eval phrase 45
-- let REFINES_TRANS = prove (`!c1 c2 c3. ...`, ...);;
unsafe def REFINES_TRANS : thm := keep "REFINES_TRANS" fun _ => prove
 ([[!c1 c2 c3. c3 refines c2 /\ c2 refines c1 ==> c3 refines c1]])
  (REWRITE_TAC [refines] THEN MESON_TAC [SUBSET_TRANS])
#eval REFINES_TRANS

#eval phrase 46
-- let REFINES_CORRECT = prove (`correct p c1 q /\ c2 refines c1 ==> correct p c2 q`, ...);;
unsafe def REFINES_CORRECT : thm := keep "REFINES_CORRECT" fun _ => prove
 ([[correct p c1 q /\ c2 refines c1 ==> correct p c2 q]])
  (REWRITE_TAC [correct, refines] THEN MESON_TAC [SUBSET_TRANS])
#eval REFINES_CORRECT

#eval phrase 47
-- let REFINES_WHILE = prove (`c' refines c ==> While e c' refines While e c`, ...);;
unsafe def REFINES_WHILE : thm := keep "REFINES_WHILE" fun _ => prove
 ([[c' refines c ==> While e c' refines While e c]])
  (REWRITE_TAC [refines, while_def, SUBSET, IN_ELIM_THM, IN] THEN MESON_TAC [])
#eval REFINES_WHILE

#eval phrase 48
-- let specification = new_definition `specification(p,q) r = if q SUBSET r then p else {}`;;
unsafe def specification : thm := keep "specification" fun _ => new_definition
  [[specification(p,q) r = if q SUBSET r then p else {}]]
#eval specification

#eval phrase 49
-- let REFINES_SPECIFICATION = prove (`c refines specification(p,q) ==> correct p c q`, ...);;
unsafe def REFINES_SPECIFICATION : thm := keep "REFINES_SPECIFICATION" fun _ => prove
 ([[c refines specification(p,q) ==> correct p c q]])
  (REWRITE_TAC [specification, correct, refines] THEN
  MESON_TAC [SUBSET_REFL, SUBSET_EMPTY])
#eval REFINES_SPECIFICATION

end HolTutorial.SemanticsOfProgrammingLanguagesShallow
