/- File: HolExamples/McCarthy.lean
Translation of HOL Light's Examples/mccarthy.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
namespace HolExamples.McCarthy

/- Helpers: the session's IO-valued rules lifted into `ExceptT String IO`, so
   the term-building functions and tactic scripts read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ec {α : Type} (x : Except String α) : ExceptT String IO α := ExceptT.mk (pure x)

/-****************************************************************************
*
*  mp.ml
*
*  An HOL mechanization of the compiler correctness proof of McCarthy and
*  Painter from 1967.
*
*  From a HOL-4 original by Robert Bauer and Ray Toal
*
*  HOL Light proof by John Harrison, 21st April 2004
*
*****************************************************************************-/

-- ------------------------------------------------------------------------- --
-- Define a type of strings, not already there in HOL Light.                 --
-- We don't use any particular properties of the type in the proof below.    --
-- ------------------------------------------------------------------------- --

#eval phrase 1
unsafe def string_INDUCT_string_RECURSION : thm × thm := keep "string_types" fun _ =>
  match unsafeIO (define_type "string = String (int list)") with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
unsafe def string_INDUCT : thm := string_INDUCT_string_RECURSION.1
unsafe def string_RECURSION : thm := string_INDUCT_string_RECURSION.2
#eval (do IO.println (← HolCore.Printer.string_of_thm string_INDUCT)
          IO.println (← HolCore.Printer.string_of_thm string_RECURSION) : IO Unit)

-- ------------------------------------------------------------------------- --
-- The definitions from Robert's file.                                       --
-- ------------------------------------------------------------------------- --

/-
 *  The source language
 *  -------------------
 *
 *  Syntax:
 *
 *  The language contains only expressions of three kinds: (1) simple
 *  numeric literals, (2) simple variables, and (3) plus expressions.
 -/

#eval phrase 2
unsafe def exp_INDUCT_exp_RECURSION : thm × thm := keep "exp_types" fun _ =>
  match unsafeIO (define_type
    "exp = Lit num
         | Var string
         | Plus exp exp") with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
unsafe def exp_INDUCT : thm := exp_INDUCT_exp_RECURSION.1
unsafe def exp_RECURSION : thm := exp_INDUCT_exp_RECURSION.2
#eval (do IO.println (← HolCore.Printer.string_of_thm exp_INDUCT)
          IO.println (← HolCore.Printer.string_of_thm exp_RECURSION) : IO Unit)

/-
 *  Semantics:
 *
 *  Expressions evaluated in a state produce a result.  There are no
 *  side effects.  A state is simply a mapping from variables to
 *  values.  The semantic function is called E.
 -/

#eval phrase 3
unsafe def E_DEF : thm := keep "E_DEF" fun _ => (do
  ExceptT.mk (new_recursive_definition exp_RECURSION
   [[(E (Lit n) s = n)
  /\  (E (Var v) s = s v)
  /\  (E (Plus e1 e2) s = E e1 s + E e2 s)]])
  : ExceptT String IO thm).run
#eval E_DEF

/-
 *  The object language
 *  -------------------
 *
 *  Syntax:
 *
 *  The target machine has a single accumulator (Acc) and an infinite
 *  set of numbered registers (Reg 0, Reg 1, Reg 2, and so on).  The
 *  accumulator and registers together are called cells.  There are four
 *  instructions: LI (load immediate into accumulator), LOAD (load the
 *  contents of a numbered register into the accumulator), STO (store
 *  the accumulator value into a numbered register) and ADD (add the
 *  contents of a numbered register into the accumulator).
 -/

#eval phrase 4
unsafe def cell_INDUCT_cell_RECURSION : thm × thm := keep "cell_types" fun _ =>
  match unsafeIO (define_type
    "cell = Acc
          | Reg num") with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
unsafe def cell_INDUCT : thm := cell_INDUCT_cell_RECURSION.1
unsafe def cell_RECURSION : thm := cell_INDUCT_cell_RECURSION.2
#eval (do IO.println (← HolCore.Printer.string_of_thm cell_INDUCT)
          IO.println (← HolCore.Printer.string_of_thm cell_RECURSION) : IO Unit)

#eval phrase 5
unsafe def inst_INDUCT_inst_RECURSION : thm × thm := keep "inst_types" fun _ =>
  match unsafeIO (define_type
    "inst = LI num
          | LOAD num
          | STO num
          | ADD num") with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
unsafe def inst_INDUCT : thm := inst_INDUCT_inst_RECURSION.1
unsafe def inst_RECURSION : thm := inst_INDUCT_inst_RECURSION.2
#eval (do IO.println (← HolCore.Printer.string_of_thm inst_INDUCT)
          IO.println (← HolCore.Printer.string_of_thm inst_RECURSION) : IO Unit)

/-
 *  update x z s is the state that is just like s except that x now
 *  maps to z.  This definition applies to any kind of state.
 -/

#eval phrase 6
unsafe def update_def : thm := keep "update_def" fun _ => (do
  ExceptT.mk (new_definition [[update x z s y = if (y = x) then z else s y]])
  : ExceptT String IO thm).run
#eval update_def

/-
 *  Semantics:
 *
 *  First, the semantics of the execution of a single instruction.
 *  The semantic function is called S.  Executing an instruction in
 *  a machine state produces a new machine state.  Here a machine
 *  state is a mapping from cells to values.
 -/

#eval phrase 7
unsafe def S_DEF : thm := keep "S_DEF" fun _ => (do
  ExceptT.mk (new_recursive_definition inst_RECURSION
   [[(S (LI n) s = update Acc n s)
  /\  (S (LOAD r) s = update Acc (s (Reg r)) s)
  /\  (S (STO r) s = update (Reg r) (s Acc) s)
  /\  (S (ADD r) s = update Acc (s (Reg r) + s Acc) s)]])
  : ExceptT String IO thm).run
#eval S_DEF

/-
 *  Next we give the semantics of a list of instructions with the
 *  semantic function S'.  The execution of an intruction list
 *  in an initial state is given by executing the first instruction
 *  in the list in the initial state, which produce a new state s1,
 *  and taking the execution of the rest of the list in s1.
 -/

#eval phrase 8
unsafe def S'_DEF : thm := keep "S'_DEF" fun _ => (do
  ExceptT.mk (new_recursive_definition list_RECURSION
   [[(S' [] s = s)
  /\  (S' (CONS inst rest) s = S' rest (S inst s))]])
  : ExceptT String IO thm).run
#eval S'_DEF

/-
 *  The compiler
 *  ------------
 *
 *  Each source language expression is compiled into a list of
 *  instructions.  The compilation is done using a symbol table
 *  which maps source language indentifiers into target machine
 *  register numbers, and a parameter r which tells the next
 *  available free register.
 -/

#eval phrase 9
unsafe def C_DEF : thm := keep "C_DEF" fun _ => (do
  ExceptT.mk (new_recursive_definition exp_RECURSION
   [[(C (Lit n) map r = [LI n])
  /\  (C (Var v) map r = [LOAD (map v)])
  /\  (C (Plus e1 e2) map r =
           APPEND
               (APPEND (C e1 map r) [STO r])
               (APPEND (C e2 map (r + 1)) [ADD r]))]])
  : ExceptT String IO thm).run
#eval C_DEF

-- ------------------------------------------------------------------------- --
-- My key lemmas; UPDATE_DIFFERENT and S'_APPEND are the same as Robert's.   --
-- ------------------------------------------------------------------------- --

#eval phrase 10
unsafe def cellth : thm := keep "cellth" fun _ => (do
  ec (Session.CONJ (← ec (distinctness "cell")) (← ec (injectivity "cell")))
  : ExceptT String IO thm).run
#eval cellth

#eval phrase 11
unsafe def S'_APPEND : thm := keep "S'_APPEND" fun _ => (do
  prove ([[!p1 p2 s. S' (APPEND p1 p2) s = S' p2 (S' p1 s)]])
   (LIST_INDUCT_TAC THEN ASM_SIMP_TAC [S'_DEF, listDefs.APPEND])
  : ExceptT String IO thm).run
#eval S'_APPEND

#eval phrase 12
unsafe def UPDATE_DIFFERENT : thm := keep "UPDATE_DIFFERENT" fun _ => (do
  prove ([[!x y z s. ~(x = y) ==> (update x z s y = s y)]])
   (SIMP_TAC [update_def])
  : ExceptT String IO thm).run
#eval UPDATE_DIFFERENT

#eval phrase 13
unsafe def UPDATE_SAME : thm := keep "UPDATE_SAME" fun _ => (do
  prove ([[!x z s. update x z s x = z]])
   (SIMP_TAC [update_def])
  : ExceptT String IO thm).run
#eval UPDATE_SAME

/-
 *  The Correctness Condition
 *  -------------------------
 *
 *  The correctness condition is this:
 *
 *  For every expression e, symbol table map, source state s,
 *      target state s', register number r:
 *
 *  If all source variables map to registers LESS THAN r,
 *  and if the value of every variable v in s is exactly
 *  the same as the value in s' of the register to which
 *  v is mapped by map, THEN
 *
 *  When e is compiled with map and first free register r,
 *  and then executed in the state s', in the resulting
 *  machine state S'(C e map r):
 *
 *  the accumulator will contain E e s and every register
 *  with number x less than r will have the same value as
 *  it does in s'.
 *
 *  The Proof
 *  ---------
 *
 *  The proof can be done by induction and careful application of SIMP_TAC[]
 *  using the lemmas isolated above.
 *
 *  The only "hack" is to throw in GSYM SKOLEM_THM and EXISTS_REFL to dispose
 *  of state existence subgoals of the form `?s. !v. s v = t[v]`, which
 *  otherwise would not be proven automatically by the simplifier.
 -/

#eval phrase 14
unsafe def CORRECTNESS_THEOREM : thm := keep "CORRECTNESS_THEOREM" fun _ => (do
  prove ([[!e map s s' r.
      (!v. map v < r) ==>
      (!v. s v = s' (Reg (map v))) ==>
          (S' (C e map r) s' Acc = E e s) /\
          (!x. (x < r) ==> (S' (C e map r) s' (Reg x) = s' (Reg x)))]])
   (MATCH_MP_TAC exp_INDUCT THEN
    REWRITE_TAC [E_DEF, S_DEF, S'_DEF, update_def, C_DEF, S'_APPEND] THEN
    SIMP_TAC [(← ExceptT.mk (ARITH_RULE [[(x < y ==> x < y + 1 /\ ~(x = y)) /\ x < x + 1]])),
              cellth, UPDATE_SAME, UPDATE_DIFFERENT,
              (← ExceptT.mk (HolLight.GSYM SKOLEM_THM)), EXISTS_REFL])
  : ExceptT String IO thm).run
#eval CORRECTNESS_THEOREM

end HolExamples.McCarthy
