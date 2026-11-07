/- File: Hol100/Konigsberg.lean
Translation of HOL Light's 100/konigsberg.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
namespace Hol100.Konigsberg

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
/-- Run an `IO (Except String α)` once, caching under `name` (OCaml's `let`
    evaluates its right-hand side once), for the `let X,Y,Z = e` bindings
    whose result is a tuple. -/
private def keepIO {α : Type} [Inhabited α] (name : String) (f : Unit → IO (Except String α)) : α :=
  keep name fun _ =>
    match runIO (f ()) with
    | .ok (.ok v) => v
    | .ok (.error e) => panic! s!"keepIO {name}: {e}"
    | .error e => panic! s!"keepIO {name}: {e}"
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- Impossibility of Eulerian path for bridges of Koenigsberg.                -/
/- ========================================================================= -/

#eval phrase 1
def edges : thm := keep "edges" fun _ => new_definition
 [[edges(E:E->bool,V:V->bool,Ter:E->V->bool) = E]]
#eval edges

#eval phrase 2
def vertices : thm := keep "vertices" fun _ => new_definition
 [[vertices(E:E->bool,V:V->bool,Ter:E->V->bool) = V]]
#eval vertices

#eval phrase 3
def termini : thm := keep "termini" fun _ => new_definition
 [[termini(E:E->bool,V:V->bool,Ter:E->V->bool) = Ter]]
#eval termini

/- ------------------------------------------------------------------------- -/
/- Definition of an undirected graph.                                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def graph : thm := keep "graph" fun _ => new_definition
 [[graph G <=>
        !e. e IN edges(G)
            ==> ?a b. a IN vertices(G) /\ b IN vertices(G) /\
                      termini G e = {a,b}]]
#eval graph

#eval phrase 5
def TERMINI_IN_VERTICES : thm := keep "TERMINI_IN_VERTICES" fun _ => (do
  prove ([[!G e v. graph G /\ e IN edges(G) /\ v IN termini G e ==> v IN vertices G]])
   (REWRITE_TAC [graph, EXTENSION, IN_INSERT, NOT_IN_EMPTY] THEN
    MESON_TAC [])
  : ExceptT String IO thm).run
#eval TERMINI_IN_VERTICES

/- ------------------------------------------------------------------------- -/
/- Connection in a graph.                                                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 6
def connects : thm := keep "connects" fun _ => new_definition
 [[connects G e (a,b) <=> termini G e = {a,b}]]
#eval connects

/- ------------------------------------------------------------------------- -/
/- Delete an edge in a graph.                                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 7
def delete_edge : thm := keep "delete_edge" fun _ => new_definition
 [[delete_edge e (E,V,Ter) = (E DELETE e,V,Ter)]]
#eval delete_edge

#eval phrase 8
def DELETE_EDGE_CLAUSES : thm := keep "DELETE_EDGE_CLAUSES" fun _ => (do
  prove ([[(!G. edges(delete_edge e G) = (edges G) DELETE e) /\
   (!G. vertices(delete_edge e G) = vertices G) /\
   (!G. termini(delete_edge e G) = termini G)]])
   (REWRITE_TAC [FORALL_PAIR_THM, delete_edge, edges, vertices, termini])
  : ExceptT String IO thm).run
#eval DELETE_EDGE_CLAUSES

#eval phrase 9
def GRAPH_DELETE_EDGE : thm := keep "GRAPH_DELETE_EDGE" fun _ => (do
  prove ([[!G e. graph G ==> graph(delete_edge e G)]])
   (REWRITE_TAC [graph, DELETE_EDGE_CLAUSES, IN_DELETE] THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval GRAPH_DELETE_EDGE

/- ------------------------------------------------------------------------- -/
/- Local finiteness: set of edges with given endpoint is finite.             -/
/- ------------------------------------------------------------------------- -/

#eval phrase 10
def locally_finite : thm := keep "locally_finite" fun _ => new_definition
 [[locally_finite G <=>
     !v. v IN vertices(G) ==> FINITE {e | e IN edges G /\ v IN termini G e}]]
#eval locally_finite

/- ------------------------------------------------------------------------- -/
/- Degree of a vertex.                                                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 11
def localdegree : thm := keep "localdegree" fun _ => new_definition
 [[localdegree G v e =
        if termini G e = {v} then 2
        else if v IN termini G e then 1
        else 0]]
#eval localdegree

#eval phrase 12
def degree : thm := keep "degree" fun _ => new_definition
 [[degree G v = nsum {e | e IN edges G /\ v IN termini G e} (localdegree G v)]]
#eval degree

#eval phrase 13
def DEGREE_DELETE_EDGE : thm := keep "DEGREE_DELETE_EDGE" fun _ => (do
  prove ([[!G e:E v:V.
        graph G /\ locally_finite G /\ e IN edges(G)
        ==> degree G v =
                if termini G e = {v} then degree (delete_edge e G) v + 2
                else if v IN termini G e then degree (delete_edge e G) v + 1
                else degree (delete_edge e G) v]])
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [degree, DELETE_EDGE_CLAUSES, IN_DELETE] THEN
    SUBGOAL_THEN ([[{e:E | e IN edges G /\ (v:V) IN termini G e} =
        if v IN termini G e
        then e INSERT {e' | (e' IN edges G /\ ~(e' = e)) /\ v IN termini G e'}
        else {e' | (e' IN edges G /\ ~(e' = e)) /\ v IN termini G e'}]]) SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION] THEN GEN_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC [IN_ELIM_THM, IN_INSERT] THEN
      ASM_MESON_TAC [],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[(v:V) IN termini G (e:E)]]) THEN ASM_REWRITE_TAC [] THENL
     [ALL_TAC,
      COND_CASES_TAC THENL [ASM_MESON_TAC [IN_SING, EXTENSION], ALL_TAC] THEN
      MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC [IN_ELIM_THM, localdegree] THEN
      REWRITE_TAC [DELETE_EDGE_CLAUSES]] THEN
    SUBGOAL_THEN ([[FINITE {e':E | (e' IN edges G /\ ~(e' = e)) /\ (v:V) IN termini G e'}]]) (fun th => SIMP_TAC [NSUM_CLAUSES, th]) THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC ([[{e:E | e IN edges G /\ (v:V) IN termini G e}]]) THEN
      SIMP_TAC [IN_ELIM_THM, SUBSET] THEN
      ASM_MESON_TAC [locally_finite, TERMINI_IN_VERTICES],
      ALL_TAC] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN ASM_REWRITE_TAC [localdegree] THEN
    SUBGOAL_THEN ([[nsum {e':E | (e' IN edges G /\ ~(e' = e)) /\ (v:V) IN termini G e'}
         (localdegree (delete_edge e G) v) =
    nsum {e' | (e' IN edges G /\ ~(e' = e)) /\ v IN termini G e'}
         (localdegree G v)]]) SUBST1_TAC THENL
     [ALL_TAC, COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ARITH_TAC] THEN
    MATCH_MP_TAC NSUM_EQ THEN SIMP_TAC [localdegree, DELETE_EDGE_CLAUSES])
  : ExceptT String IO thm).run
#eval DEGREE_DELETE_EDGE

/- ------------------------------------------------------------------------- -/
/- Definition of Eulerian path.                                              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 14
-- let eulerian_RULES,eulerian_INDUCT,eulerian_CASES = new_inductive_definition ...
def eulerian_RULES_defs : thm × thm × thm :=
  keepIO "eulerian_RULES_defs" fun _ => new_inductive_definition
  [[(!G a. a IN vertices G /\ edges G = {} ==> eulerian G [] (a,a)) /\
  (!G a b c e es. e IN edges(G) /\ connects G e (a,b) /\
                  eulerian (delete_edge e G) es (b,c)
                  ==> eulerian G (CONS e es) (a,c))]]
def eulerian_RULES : thm := eulerian_RULES_defs.1
def eulerian_INDUCT : thm := eulerian_RULES_defs.2.1
def eulerian_CASES : thm := eulerian_RULES_defs.2.2
#eval do IO.println (repr eulerian_RULES); IO.println (repr eulerian_INDUCT); IO.println (repr eulerian_CASES)

#eval phrase 15
def EULERIAN_FINITE : thm := keep "EULERIAN_FINITE" fun _ => (do
  prove ([[!G es ab. eulerian G es ab ==> FINITE (edges G)]])
   (MATCH_MP_TAC eulerian_INDUCT THEN
    SIMP_TAC [DELETE_EDGE_CLAUSES, FINITE_DELETE, FINITE_RULES])
  : ExceptT String IO thm).run
#eval EULERIAN_FINITE

/- ------------------------------------------------------------------------- -/
/- The main result.                                                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 16
def EULERIAN_ODD_LEMMA : thm := keep "EULERIAN_ODD_LEMMA" fun _ => (do
  let h3 ← sr (← ExceptT.mk [[{a,b} = {v} <=> a = b /\ a = v]])
  let h2 ← sr (← ExceptT.mk [[{a,a} = {v} <=> v = a]])
  let h1 ← sr (← ExceptT.mk [[{x | F} = {}]])
  prove ([[!G:(E->bool)#(V->bool)#(E->V->bool) es ab.
        eulerian G es ab
        ==> graph G
            ==> FINITE(edges G) /\
                !v. v IN vertices G
                    ==> (ODD(degree G v) <=>
                         ~(FST ab = SND ab) /\ (v = FST ab \/ v = SND ab))]])
   (MATCH_MP_TAC eulerian_INDUCT THEN CONJ_TAC THENL
     [SIMP_TAC [degree, NOT_IN_EMPTY, h1] THEN
      SIMP_TAC [NSUM_CLAUSES, FINITE_RULES, ARITH],
      ALL_TAC] THEN
    SIMP_TAC [GRAPH_DELETE_EDGE, FINITE_DELETE, DELETE_EDGE_CLAUSES] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC [GRAPH_DELETE_EDGE] THEN STRIP_TAC THEN
    X_GEN_TAC ([[v:V]]) THEN DISCH_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[G:(E->bool)#(V->bool)#(E->V->bool)]]), ([[e:E]]), ([[v:V]])] DEGREE_DELETE_EDGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [locally_finite] THEN GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC ([[edges(G:(E->bool)#(V->bool)#(E->V->bool))]]) THEN
      ASM_SIMP_TAC [SUBSET, IN_ELIM_THM],
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[G:(E->bool)#(V->bool)#(E->V->bool)]]), ([[e:E]])] TERMINI_IN_VERTICES) THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [connects]) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
    ASM_CASES_TAC ([[b:V = a]]) THEN ASM_REWRITE_TAC [] THENL
     [REWRITE_TAC [h2] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC [ODD_ADD, ARITH],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [h3] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [ODD_ADD, ARITH] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval EULERIAN_ODD_LEMMA

#eval phrase 17
def EULERIAN_ODD : thm := keep "EULERIAN_ODD" fun _ => (do
  prove ([[!G es a b.
        graph G /\ eulerian G es (a,b)
        ==> !v. v IN vertices G
                ==> (ODD(degree G v) <=> ~(a = b) /\ (v = a \/ v = b))]])
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP EULERIAN_ODD_LEMMA) THEN
    ASM_SIMP_TAC [FST, SND])
  : ExceptT String IO thm).run
#eval EULERIAN_ODD

/- ------------------------------------------------------------------------- -/
/- Now the actual Koenigsberg configuration.                                 -/
/- ------------------------------------------------------------------------- -/

#eval phrase 18
def KOENIGSBERG : thm := keep "KOENIGSBERG" fun _ => (do
  let h7 ← sr (← ExceptT.mk [[{a,b} = {x} <=> x = a /\ a = b]])
  let h6 ← sr (← ExceptT.mk [[{x | x = a} = {a}]])
  let h5 ← sr (← ExceptT.mk [[{x | x = a \/ P(x)} = a INSERT {x | P(x)}]])
  let h4 ← tt (← ExceptT.mk [[a \/ b ==> c <=> (a ==> c) /\ (b ==> c)]])
  let h3 ← tt (← ExceptT.mk [[a IN s /\ k IN t <=> ~(a IN s ==> ~(k IN t))]])
  let h2 ← tt (← ExceptT.mk [[a \/ b ==> c <=> (a ==> c) /\ (b ==> c)]])
  let h1 ← sr (← ExceptT.mk [[{a,b} = {x,y} <=> a = x /\ b = y \/ a = y /\ b = x]])
  prove ([[!G. vertices(G) = {0,1,2,3} /\
       edges(G) = {10,20,30,40,50,60,70} /\
       termini G (10) = {0,1} /\
       termini G (20) = {0,2} /\
       termini G (30) = {0,3} /\
       termini G (40) = {1,2} /\
       termini G (50) = {1,2} /\
       termini G (60) = {2,3} /\
       termini G (70) = {2,3}
       ==> ~(?es a b. eulerian G es (a,b))]])
   (GEN_TAC THEN STRIP_TAC THEN
    MP_TAC (← HolLight.ISPEC ([[G:(num->bool)#(num->bool)#(num->num->bool)]]) EULERIAN_ODD) THEN
    REWRITE_TAC [NOT_EXISTS_THM] THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC [graph] THEN GEN_TAC THEN
      REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [h1] THEN
      MESON_TAC [],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
    SIMP_TAC [h2] THEN
    ASM_REWRITE_TAC [degree, edges] THEN
    SIMP_TAC [h3] THEN
    ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
    SIMP_TAC [h4] THEN
    ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, ARITH] THEN
    REWRITE_TAC [DE_MORGAN_THM] THEN
    REWRITE_TAC [h5] THEN
    REWRITE_TAC [h6] THEN
    SIMP_TAC [NSUM_CLAUSES, FINITE_INSERT, FINITE_EMPTY] THEN
    REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, ARITH] THEN
    ASM_REWRITE_TAC [localdegree, IN_INSERT, NOT_IN_EMPTY, ARITH] THEN
    REWRITE_TAC [h7] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MP_TAC (← HolLight.SPEC ([[0]]) th) THEN MP_TAC (← HolLight.SPEC ([[1]]) th) THEN
     MP_TAC (← HolLight.SPEC ([[2]]) th) THEN MP_TAC (← HolLight.SPEC ([[3]]) th))) THEN
    REWRITE_TAC [ARITH] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval KOENIGSBERG

end Hol100.Konigsberg
