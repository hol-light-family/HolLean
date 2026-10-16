/- File: HolTutorial/InductiveDatatypes.lean
Translation of HOL Light's Tutorial/Inductive_datatypes.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/

import HolTutorial.Common

open HolCore.Kernel Session HolLight.Syntax HolTutorial

namespace HolTutorial.InductiveDatatypes

/- The session's IO-valued rules/constructors lifted into `ExceptT String IO`,
   so the OCaml term-building functions and tactic scripts read as they do in
   OCaml. -/
private unsafe def mk_const' (s : String) : ExceptT String IO term :=
  ExceptT.mk (HolCore.Kernel.mk_const s [])
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ec {α : Type} (x : Except String α) : ExceptT String IO α := ExceptT.mk (pure x)

#eval phrase 1
unsafe def line_INDUCT_line_RECURSION : thm × thm := keep "line_types" fun _ =>
  match unsafeIO (define_type
    "line = Line_1 | Line_2 | Line_3 | Line_4 |
            Line_5 | Line_6 | Line_7") with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
unsafe def line_INDUCT : thm := line_INDUCT_line_RECURSION.1
unsafe def line_RECURSION : thm := line_INDUCT_line_RECURSION.2
#eval (do IO.println (← HolCore.Printer.string_of_thm line_INDUCT)
          IO.println (← HolCore.Printer.string_of_thm line_RECURSION) : IO Unit)

#eval phrase 2
unsafe def point_INDUCT_point_RECURSION : thm × thm := keep "point_types" fun _ =>
  match unsafeIO (define_type
    "point = Point_1 | Point_2 | Point_3 | Point_4 |
             Point_5 | Point_6 | Point_7") with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
unsafe def point_INDUCT : thm := point_INDUCT_point_RECURSION.1
unsafe def point_RECURSION : thm := point_INDUCT_point_RECURSION.2
#eval (do IO.println (← HolCore.Printer.string_of_thm point_INDUCT)
          IO.println (← HolCore.Printer.string_of_thm point_RECURSION) : IO Unit)

#eval phrase 3
unsafe def fano_incidence : List (Int × Int) :=
  [(1,1), (1,2), (1,3), (2,1), (2,4), (2,5), (3,1), (3,6), (3,7), (4,2), (4,4),
   (4,6), (5,2), (5,5), (5,7), (6,3), (6,4), (6,7), (7,3), (7,5), (7,6)]
-- OCaml prints the `(int * int) list` as `[(1, 1); (1, 2); ...]`.
#eval IO.println ("[" ++ String.intercalate "; "
  (fano_incidence.map (fun (i, j) => s!"({i}, {j})")) ++ "]")

#eval phrase 4
-- let fano_point i = mk_const("Point_"^string_of_int i,[]);;
unsafe def fano_point (i : Int) : ExceptT String IO term := mk_const' s!"Point_{i}"
#eval IO.println "<fun>"

#eval phrase 5
-- let fano_line i = mk_const("Line_"^string_of_int i,[]);;
unsafe def fano_line (i : Int) : ExceptT String IO term := mk_const' s!"Line_{i}"
#eval IO.println "<fun>"

#eval phrase 6
-- let p = `p:point` and l = `l:line`;;
unsafe def p : term := [[p:point]]
unsafe def l : term := [[l:line]]
#eval (do IO.println s!"`{← HolCore.Printer.string_of_term p}`"
          IO.println s!"`{← HolCore.Printer.string_of_term l}`" : IO Unit)

#eval phrase 7
-- let fano_clause (i,j) = mk_conj(mk_eq(p,fano_point i),mk_eq(l,fano_line j));;
unsafe def fano_clause : Int × Int → ExceptT String IO term := fun (i, j) => do
  ec (HolCore.Bool.mk_conj
    (safe_mk_eq p (← fano_point i)) (safe_mk_eq l (← fano_line j)))
#eval IO.println "<fun>"

#eval phrase 8
#eval parse_as_infix ("ON", (11, "right"))

#eval phrase 9
-- let ON = new_definition (mk_eq(`((ON):point->line->bool) p l`, list_mk_disj(map fano_clause fano_incidence)));;
unsafe def ON : thm := keep "ON" fun _ => (do
  let clauses ← fano_incidence.mapM fano_clause
  let rhs ← ec (HolCore.Bool.list_mk_disj clauses)
  let defn := safe_mk_eq (← HolLight.q r"((ON):point->line->bool) p l") rhs
  ExceptT.mk (new_definition defn)
  : ExceptT String IO thm).run
#eval ON

#eval phrase 10
-- let ON_CLAUSES = prove(list_mk_conj(allpairs (fun i j -> ...) (1--7) (1--7)), ...)
unsafe def ON_CLAUSES : thm := keep "ON_CLAUSES" fun _ => (do
  let mkcl : Int → Int → ExceptT String IO term := fun i j => do
    let onConst ← HolLight.q r"(ON)"
    let app1 ← ec (HolCore.Kernel.mk_comb onConst (← fano_point i))
    let onij ← ec (HolCore.Kernel.mk_comb app1 (← fano_line j))
    let rhs ← if HolCore.Lib.mem (i, j) fano_incidence then HolLight.q r"T" else HolLight.q r"F"
    pure (safe_mk_eq onij rhs)
  let cls ← (HolCore.Lib.allpairs (fun i j => mkcl i j) (HolCore.Lib.upto 1 7) (HolCore.Lib.upto 1 7)).mapM id
  let goal ← ec (HolCore.Bool.list_mk_conj cls)
  prove goal
    (REWRITE_TAC [ON, (← ec (distinctness "line")), (← ec (distinctness "point"))])
  : ExceptT String IO thm).run
#eval ON_CLAUSES

#eval phrase 11
unsafe def FORALL_POINT : thm := keep "FORALL_POINT" fun _ => (do
  prove ([[(!p. P p) <=> P Point_1 /\ P Point_2 /\ P Point_3 /\ P Point_4 /\
                 P Point_5 /\ P Point_6 /\ P Point_7]])
   (EQ_TAC THENL [SIMP_TAC [], REWRITE_TAC [point_INDUCT]])
  : ExceptT String IO thm).run
#eval FORALL_POINT

#eval phrase 12
unsafe def FORALL_LINE : thm := keep "FORALL_LINE" fun _ => (do
  prove ([[(!p. P p) <=> P Line_1 /\ P Line_2 /\ P Line_3 /\ P Line_4 /\
                 P Line_5 /\ P Line_6 /\ P Line_7]])
   (EQ_TAC THENL [SIMP_TAC [], REWRITE_TAC [line_INDUCT]])
  : ExceptT String IO thm).run
#eval FORALL_LINE

#eval phrase 13
unsafe def EXISTS_POINT : thm := keep "EXISTS_POINT" fun _ => (do
  prove ([[(?p. P p) <=> P Point_1 \/ P Point_2 \/ P Point_3 \/ P Point_4 \/
                 P Point_5 \/ P Point_6 \/ P Point_7]])
   (MATCH_MP_TAC (← ExceptT.mk (TAUT [[(~p <=> ~q) ==> (p <=> q)]])) THEN
    REWRITE_TAC [DE_MORGAN_THM, NOT_EXISTS_THM, FORALL_POINT])
  : ExceptT String IO thm).run
#eval EXISTS_POINT

#eval phrase 14
unsafe def EXISTS_LINE : thm := keep "EXISTS_LINE" fun _ => (do
  prove ([[(?p. P p) <=> P Line_1 \/ P Line_2 \/ P Line_3 \/ P Line_4 \/
                 P Line_5 \/ P Line_6 \/ P Line_7]])
   (MATCH_MP_TAC (← ExceptT.mk (TAUT [[(~p <=> ~q) ==> (p <=> q)]])) THEN
    REWRITE_TAC [DE_MORGAN_THM, NOT_EXISTS_THM, FORALL_LINE])
  : ExceptT String IO thm).run
#eval EXISTS_LINE

#eval phrase 15
-- let FANO_TAC = ... ;;
unsafe def FANO_TAC : HolCore.Tactics.tactic :=
  let brs := match unsafeIO basic_rewrites with | .ok l => l | .error _ => []
  let dpt := fun (ty : String) => match distinctness ty with | .ok t => t | .error e => panic! e
  GEN_REWRITE_TAC HolLight.DEPTH_CONV
   [FORALL_POINT, EXISTS_LINE, EXISTS_POINT, FORALL_LINE] THEN
  GEN_REWRITE_TAC HolLight.DEPTH_CONV
   (brs ++ [ON_CLAUSES, dpt "point", dpt "line"])
#eval IO.println "<fun>"

#eval phrase 16
-- let FANO_RULE tm = prove(tm,FANO_TAC);;
unsafe def FANO_RULE (tm : term) : ExceptT String IO thm := prove tm FANO_TAC
#eval IO.println "<fun>"

#eval phrase 17
unsafe def AXIOM_1 : thm := keep "AXIOM_1" fun _ => (FANO_RULE
  [[!p p'. ~(p = p') ==> ?l. p ON l /\ p' ON l /\
                          !l'. p ON l' /\ p' ON l' ==> l' = l]]).run
#eval AXIOM_1

#eval phrase 18
unsafe def AXIOM_2 : thm := keep "AXIOM_2" fun _ => (FANO_RULE
  [[!l l'. ?p. p ON l /\ p ON l']]).run
#eval AXIOM_2

#eval phrase 19
unsafe def AXIOM_3 : thm := keep "AXIOM_3" fun _ => (FANO_RULE
  [[?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
             ~(?l. p ON l /\ p' ON l /\ p'' ON l)]]).run
#eval AXIOM_3

#eval phrase 20
unsafe def AXIOM_4 : thm := keep "AXIOM_4" fun _ => (FANO_RULE
  [[!l. ?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
                  p ON l /\ p' ON l /\ p'' ON l]]).run
#eval AXIOM_4

end HolTutorial.InductiveDatatypes
