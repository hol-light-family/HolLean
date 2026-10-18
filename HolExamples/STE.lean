/- File: HolExamples/STE.lean
Translation of HOL Light's Examples/ste.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
open scoped HolLight
namespace HolExamples.STE

private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

-- ========================================================================= --
-- Abstract version of symbolic trajectory evaluation.                       --
--                                                                           --
-- Based on the paper "Symbolic Trajectory Evaluation in a Nutshell"         --
-- by Tom Melham & Ashish Darbari, 2002 (still unpublished?)                 --
-- ========================================================================= --

#eval phrase 1
#eval (parse_as_infix ("&&", (16, "right")) : IO Unit)

#eval phrase 2
#eval (parse_as_infix ("<<=", (14, "right")) : IO Unit)

#eval phrase 3
#eval (parse_as_infix (">->", (13, "right")) : IO Unit)

#eval phrase 4
#eval (parse_as_infix (">~~>", (6, "right")) : IO Unit)

-- ------------------------------------------------------------------------- --
-- Some type of nodes that we don't really care much about.                  --
-- ------------------------------------------------------------------------- --

#eval phrase 5
unsafe def node_INDUCT_node_RECURSION : thm × thm := keep "node_types" fun _ =>
  match unsafeIO (define_type
    "node = Node num") with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
unsafe def node_INDUCT : thm := node_INDUCT_node_RECURSION.1
unsafe def node_RECURSION : thm := node_INDUCT_node_RECURSION.2
#eval (do IO.println (← HolCore.Printer.string_of_thm node_INDUCT)
          IO.println (← HolCore.Printer.string_of_thm node_RECURSION) : IO Unit)

-- ------------------------------------------------------------------------- --
-- Also "abstract" propositional formulas (i.e. we never unfold "eval").     --
-- ------------------------------------------------------------------------- --

#eval phrase 6
unsafe def propform_INDUCT_propform_RECURSION : thm × thm := keep "propform_types" fun _ =>
  match unsafeIO (define_type
    "propform = Propform (num->bool)->bool") with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
unsafe def propform_INDUCT : thm := propform_INDUCT_propform_RECURSION.1
unsafe def propform_RECURSION : thm := propform_INDUCT_propform_RECURSION.2
#eval (do IO.println (← HolCore.Printer.string_of_thm propform_INDUCT)
          IO.println (← HolCore.Printer.string_of_thm propform_RECURSION) : IO Unit)

#eval phrase 7
unsafe def eval : thm := keep "eval" fun _ => (do
  ExceptT.mk (new_recursive_definition propform_RECURSION
   [[eval (Propform p) v = p v]])
  : ExceptT String IO thm).run
#eval eval

-- ------------------------------------------------------------------------- --
-- Quaternary lattice.                                                       --
-- ------------------------------------------------------------------------- --

#eval phrase 8
unsafe def quat_INDUCT_quat_RECURSION : thm × thm := keep "quat_types" fun _ =>
  match unsafeIO (define_type
    "quat = X | ZERO | ONE | TOP") with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
unsafe def quat_INDUCT : thm := quat_INDUCT_quat_RECURSION.1
unsafe def quat_RECURSION : thm := quat_INDUCT_quat_RECURSION.2
#eval (do IO.println (← HolCore.Printer.string_of_thm quat_INDUCT)
          IO.println (← HolCore.Printer.string_of_thm quat_RECURSION) : IO Unit)

#eval phrase 9
unsafe def quat_DISTINCT : thm := keep "quat_DISTINCT" fun _ => (do
  ExceptT.mk (Session.prove_constructors_distinct quat_RECURSION)
  : ExceptT String IO thm).run
#eval quat_DISTINCT

-- ------------------------------------------------------------------------- --
-- Basic lattice operations.                                                 --
-- ------------------------------------------------------------------------- --

#eval phrase 10
unsafe def qle : thm := keep "qle" fun _ => new_definition
  [[x <<= y <=> x = X \/ y = TOP \/ x = y]]
#eval qle

#eval phrase 11
unsafe def qjoin : thm := keep "qjoin" fun _ => new_definition
  [[x && y = if x <<= y then y else if y <<= x then x else TOP]]
#eval qjoin

-- ------------------------------------------------------------------------- --
-- Trivial lemmas about the quaternary lattice.                              --
-- ------------------------------------------------------------------------- --

#eval phrase 12
unsafe def QLE_REFL : thm := keep "QLE_REFL" fun _ => (do
  prove ([[!x. x <<= x]])
   (REWRITE_TAC [qle])
  : ExceptT String IO thm).run
#eval QLE_REFL

#eval phrase 13
unsafe def QLE_TRANS : thm := keep "QLE_TRANS" fun _ => (do
  prove ([[!x y z. x <<= y /\ y <<= z ==> x <<= z]])
   (REPEAT (MATCH_MP_TAC quat_INDUCT THEN REPEAT CONJ_TAC) THEN
    REWRITE_TAC [qle, quat_DISTINCT])
  : ExceptT String IO thm).run
#eval QLE_TRANS

#eval phrase 14
unsafe def QLE_LJOIN : thm := keep "QLE_LJOIN" fun _ => (do
  prove ([[!x y z. x && y <<= z <=> x <<= z /\ y <<= z]])
   (REPEAT (MATCH_MP_TAC quat_INDUCT THEN REPEAT CONJ_TAC) THEN
    REWRITE_TAC [qjoin, qle, quat_DISTINCT])
  : ExceptT String IO thm).run
#eval QLE_LJOIN

#eval phrase 15
unsafe def QLE_RJOIN : thm := keep "QLE_RJOIN" fun _ => (do
  prove ([[!x y. x <<= x && y /\ y <<= x && y]])
   (REPEAT (MATCH_MP_TAC quat_INDUCT THEN REPEAT CONJ_TAC) THEN
    REWRITE_TAC [qjoin, qle, quat_DISTINCT])
  : ExceptT String IO thm).run
#eval QLE_RJOIN

-- ------------------------------------------------------------------------- --
-- Choice expressions.                                                       --
-- ------------------------------------------------------------------------- --

#eval phrase 16
unsafe def choice : thm := keep "choice" fun _ => new_definition
  [[b >-> x = if b then x else X]]
#eval choice

#eval phrase 17
unsafe def QLE_CHOICE : thm := keep "QLE_CHOICE" fun _ => (do
  prove ([[(b >-> x) <<= y <=> b ==> x <<= y]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [choice] THEN
    COND_CASES_TAC THEN REWRITE_TAC [] THEN REWRITE_TAC [qle])
  : ExceptT String IO thm).run
#eval QLE_CHOICE

-- ------------------------------------------------------------------------- --
-- Basic type of trajectory formulas.                                        --
-- ------------------------------------------------------------------------- --

#eval phrase 18
unsafe def trajform_INDUCT_trajform_RECURSION : thm × thm := keep "trajform_types" fun _ =>
  match unsafeIO (define_type
    "trajform = Is_0 node
              | Is_1 node
              | Andj trajform trajform
              | When trajform propform
              | Next trajform") with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
unsafe def trajform_INDUCT : thm := trajform_INDUCT_trajform_RECURSION.1
unsafe def trajform_RECURSION : thm := trajform_INDUCT_trajform_RECURSION.2
#eval (do IO.println (← HolCore.Printer.string_of_thm trajform_INDUCT)
          IO.println (← HolCore.Printer.string_of_thm trajform_RECURSION) : IO Unit)

-- ------------------------------------------------------------------------- --
-- Semantics.                                                                --
-- ------------------------------------------------------------------------- --

#eval phrase 19
unsafe def tholds : thm := keep "tholds" fun _ => (do
  ExceptT.mk (new_recursive_definition trajform_RECURSION
   [[(tholds (Is_0 nd) seq v <=> ZERO <<= seq 0 nd v) /\
     (tholds (Is_1 nd) seq v <=> ONE <<= seq 0 nd v) /\
     (tholds (Andj tf1 tf2) seq v <=> tholds tf1 seq v /\ tholds tf2 seq v) /\
     (tholds (When tf1 p) seq v <=> eval p v ==> tholds tf1 seq v) /\
     (tholds (Next(tf1)) seq v <=> tholds tf1 (\t. seq(t + 1)) v)]])
  : ExceptT String IO thm).run
#eval tholds

-- ------------------------------------------------------------------------- --
-- Defining sequence.                                                        --
-- ------------------------------------------------------------------------- --

#eval phrase 20
unsafe def defseq : thm := keep "defseq" fun _ => (do
  ExceptT.mk (new_recursive_definition trajform_RECURSION
   [[(defseq (Is_0 n) t nd v = ((n = nd) /\ (t = 0)) >-> ZERO) /\
     (defseq (Is_1 n) t nd v = ((n = nd) /\ (t = 0)) >-> ONE) /\
     (defseq (Andj tf1 tf2) t nd v = defseq tf1 t nd v && defseq tf2 t nd v) /\
     (defseq (When tf1 p) t nd v =  eval p v >-> defseq tf1 t nd v) /\
     (defseq (Next(tf1)) t nd v = ~(t = 0) >-> defseq tf1 (t - 1) nd v)]])
  : ExceptT String IO thm).run
#eval defseq

-- ------------------------------------------------------------------------- --
-- Proof of the key property.                                                --
-- ------------------------------------------------------------------------- --

#eval phrase 21
unsafe def DEFSEQ_MINIMAL : thm := keep "DEFSEQ_MINIMAL" fun _ => (do
  let cases_lemma ← prove
   ([[(!t. P t) <=> P 0 /\ !t. P(SUC t)]]) (MESON_TAC [num_CASES])
  prove ([[!tf seq v. tholds tf seq v <=> !t nd. defseq tf t nd v <<= seq t nd v]])
   (MATCH_MP_TAC trajform_INDUCT THEN REWRITE_TAC [defseq, tholds] THEN
    REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC [QLE_CHOICE] THEN MESON_TAC [],
      REPEAT GEN_TAC THEN REWRITE_TAC [QLE_CHOICE] THEN MESON_TAC [],
      SIMP_TAC [QLE_LJOIN, FORALL_AND_THM],
      REWRITE_TAC [QLE_CHOICE] THEN MESON_TAC [],
      REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [cases_lemma] THEN
      ASM_REWRITE_TAC [QLE_CHOICE, NOT_SUC, ADD1, ADD_SUB]])
  : ExceptT String IO thm).run
#eval DEFSEQ_MINIMAL

-- ------------------------------------------------------------------------- --
-- Notion of a trajectory w.r.t. a next-state function.                      --
-- ------------------------------------------------------------------------- --

#eval phrase 22
unsafe def trajectory : thm := keep "trajectory" fun _ => new_definition
  [[trajectory next seq v <=> !t nd. next(seq t) nd v <<= seq (t + 1) nd v]]
#eval trajectory

-- ------------------------------------------------------------------------- --
-- Defining trajectory of a formula.                                         --
-- ------------------------------------------------------------------------- --

#eval phrase 23
unsafe def deftraj : thm := keep "deftraj" fun _ => (do
  ExceptT.mk (new_recursive_definition num_RECURSION
   [[(deftraj step tf 0 nd v = defseq tf 0 nd v) /\
     (deftraj step tf (SUC t) nd v =
          defseq tf (SUC t) nd v && step(deftraj step tf t) nd v)]])
  : ExceptT String IO thm).run
#eval deftraj

-- ------------------------------------------------------------------------- --
-- Obviously this is at least as strong as the defining sequence.            --
-- ------------------------------------------------------------------------- --

#eval phrase 24
unsafe def DEFTRAJ_DEFSEQ : thm := keep "DEFTRAJ_DEFSEQ" fun _ => (do
  prove ([[!tf t nd v. defseq tf t nd v <<= deftraj step tf t nd v]])
   (GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [deftraj, QLE_REFL, QLE_RJOIN])
  : ExceptT String IO thm).run
#eval DEFTRAJ_DEFSEQ

-- ------------------------------------------------------------------------- --
-- ...and it is indeed a trajectory.                                         --
-- ------------------------------------------------------------------------- --

#eval phrase 25
unsafe def TRAJECTORY_DEFTRAJ : thm := keep "TRAJECTORY_DEFTRAJ" fun _ => (do
  prove ([[!step tf v. trajectory step (deftraj step tf) v]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [trajectory] THEN
    REWRITE_TAC [(← HolLight.GSYM ADD1), deftraj, QLE_RJOIN])
  : ExceptT String IO thm).run
#eval TRAJECTORY_DEFTRAJ

-- ------------------------------------------------------------------------- --
-- Monotonicity of next-state function.                                      --
-- ------------------------------------------------------------------------- --

#eval phrase 26
unsafe def monotonic : thm := keep "monotonic" fun _ => new_definition
  [[monotonic next v <=>
   !s1 s2. (!nd. s1 nd v <<= s2 nd v) ==> !nd. next s1 nd v <<= next s2 nd v]]
#eval monotonic

-- ------------------------------------------------------------------------- --
-- Minimality property of defining trajectory (needs monotonicity).          --
-- ------------------------------------------------------------------------- --

#eval phrase 27
unsafe def DEFTRAJ_MINIMAL : thm := keep "DEFTRAJ_MINIMAL" fun _ => (do
  prove ([[!step v.
      monotonic step v
      ==> !tf seq. trajectory step seq v
                   ==> (tholds tf seq v <=>
                        !t nd. deftraj step tf t nd v <<= seq t nd v)]])
   (REWRITE_TAC [monotonic, trajectory, RIGHT_IMP_FORALL_THM] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ALL_TAC, MESON_TAC [DEFSEQ_MINIMAL, DEFTRAJ_DEFSEQ, QLE_TRANS]] THEN
    DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC [deftraj, QLE_LJOIN] THEN
    ASM_MESON_TAC [DEFSEQ_MINIMAL, QLE_TRANS, ADD1])
  : ExceptT String IO thm).run
#eval DEFTRAJ_MINIMAL

-- ------------------------------------------------------------------------- --
-- Basic semantic notion in STE.                                             --
-- ------------------------------------------------------------------------- --

#eval phrase 28
unsafe def ste : thm := keep "ste" fun _ => new_definition
  [[(A >~~> C) ckt v <=>
      !seq. trajectory ckt seq v /\ tholds A seq v ==> tholds C seq v]]
#eval ste

-- ------------------------------------------------------------------------- --
-- The "fundamental theorem of STE".                                         --
-- ------------------------------------------------------------------------- --

#eval phrase 29
unsafe def STE_THM : thm := keep "STE_THM" fun _ => (do
  prove ([[monotonic ckt v
   ==> ((A >~~> C) ckt v <=> !t nd. defseq C t nd v <<= deftraj ckt A t nd v)]])
   (MESON_TAC [ste, DEFTRAJ_MINIMAL, DEFSEQ_MINIMAL, DEFTRAJ_DEFSEQ,
            TRAJECTORY_DEFTRAJ, QLE_TRANS])
  : ExceptT String IO thm).run
#eval STE_THM

end HolExamples.STE
