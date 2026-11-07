/- File: Hol100/Desargues.lean
Translation of HOL Light's 100/desargues.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionMultiLib.Cross
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Iter SessionLibrary.Wo SessionLibrary.Floor SessionLibrary.Products SessionLibrary.Permutations SessionLibrary.Card SessionLibrary.Matroids SessionMultiLib.Misc SessionMultiLib.Vectors SessionMultiLib.Metric SessionMultiLib.Determinants SessionMultiLib.Topology SessionMultiLib.Cross
namespace Hol100.Desargues

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
/-- Print a theorem pair as OCaml's toplevel does: `(|- ...,\n   |- ...)`. -/
private def printPair (p : thm × thm) : IO Unit := do
  IO.println s!"({← HolCore.Printer.string_of_thm p.1},\n   {← HolCore.Printer.string_of_thm p.2})"
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
private def ms (ths : List thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (MESON ths tm)
private def rg (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_RING tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- #87: Desargues's theorem.                                                 -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Multivariate/cross.ml";;
#eval SessionMultiLib.Cross.ensureCross

/- ------------------------------------------------------------------------- -/
/- A lemma we want to justify some of the axioms.                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 2
def NORMAL_EXISTS : thm := keep "NORMAL_EXISTS" fun _ => (do
  prove ([[!u v:real^3. ?w. ~(w = vec 0) /\ orthogonal u w /\ orthogonal v w]])
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [ORTHOGONAL_SYM] THEN
    MP_TAC (← HolLight.ISPEC ([[{u:real^3,v}]]) ORTHOGONAL_TO_SUBSPACE_EXISTS) THEN
    REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY, DIMINDEX_3] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC ([[CARD {u:real^3,v}]]) THEN CONJ_TAC THEN
    SIMP_TAC [DIM_LE_CARD, FINITE_INSERT, FINITE_EMPTY] THEN
    SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval NORMAL_EXISTS

/- ------------------------------------------------------------------------- -/
/- Type of directions.                                                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 3
def direction_tybij : thm := keep "direction_tybij" fun _ => (do
  let h1 ← ms [BASIS_NONZERO, LE_REFL, DIMINDEX_GE_1] (← ExceptT.mk [[?x:real^3. ~(x = vec 0)]])
  ExceptT.mk (new_type_definition "direction" "mk_dir" "dest_dir" h1)
  : ExceptT String IO thm).run
#eval direction_tybij

#eval phrase 4
-- parse_as_infix("||",(11,"right"));;
#eval (parse_as_infix ("||", (11, "right")) : IO Unit)

#eval phrase 5
-- parse_as_infix("_|_",(11,"right"));;
#eval (parse_as_infix ("_|_", (11, "right")) : IO Unit)

#eval phrase 6
def perpdir : thm := keep "perpdir" fun _ => new_definition
 [[x _|_ y <=> orthogonal (dest_dir x) (dest_dir y)]]
#eval perpdir

#eval phrase 7
def pardir : thm := keep "pardir" fun _ => new_definition
 [[x || y <=> (dest_dir x) cross (dest_dir y) = vec 0]]
#eval pardir

#eval phrase 8
def DIRECTION_CLAUSES : thm := keep "DIRECTION_CLAUSES" fun _ => (do
  prove ([[((!x. P(dest_dir x)) <=> (!x. ~(x = vec 0) ==> P x)) /\
   ((?x. P(dest_dir x)) <=> (?x. ~(x = vec 0) /\ P x))]])
   (MESON_TAC [direction_tybij])
  : ExceptT String IO thm).run
#eval DIRECTION_CLAUSES

#eval phrase 9
-- let PARDIR_REFL, PARDIR_SYM, PARDIR_TRANS = (CONJUNCTS o prove) ...
def PARDIR_REFL_PARDIR_SYM_THMS : List thm := keepIO "PARDIR_REFL_PARDIR_SYM_THMS" fun _ => (do
  let th ← prove ([[(!x. x || x) /\
   (!x y. x || y <=> y || x) /\
   (!x y z. x || y /\ y || z ==> x || z)]])
   (REWRITE_TAC [pardir, DIRECTION_CLAUSES] THEN VEC3_TAC)
  pure (HolLight.CONJUNCTS th)
  : ExceptT String IO (List thm)).run
def PARDIR_REFL : thm := PARDIR_REFL_PARDIR_SYM_THMS[0]!
def PARDIR_SYM : thm := PARDIR_REFL_PARDIR_SYM_THMS[1]!
def PARDIR_TRANS : thm := PARDIR_REFL_PARDIR_SYM_THMS[2]!
#eval do IO.println (repr PARDIR_REFL); IO.println (repr PARDIR_SYM); IO.println (repr PARDIR_TRANS)

#eval phrase 10
def PARDIR_EQUIV : thm := keep "PARDIR_EQUIV" fun _ => (do
  prove ([[!x y. ((||) x = (||) y) <=> x || y]])
   (REWRITE_TAC [FUN_EQ_THM] THEN
    MESON_TAC [PARDIR_REFL, PARDIR_SYM, PARDIR_TRANS])
  : ExceptT String IO thm).run
#eval PARDIR_EQUIV

#eval phrase 11
def DIRECTION_AXIOM_1 : thm := keep "DIRECTION_AXIOM_1" fun _ => (do
  prove ([[!p p'. ~(p || p') ==> ?l. p _|_ l /\ p' _|_ l /\
                             !l'. p _|_ l' /\ p' _|_ l' ==> l' || l]])
   (REWRITE_TAC [perpdir, pardir, DIRECTION_CLAUSES] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[p:real^3]]), ([[p':real^3]])] NORMAL_EXISTS) THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN VEC3_TAC)
  : ExceptT String IO thm).run
#eval DIRECTION_AXIOM_1

#eval phrase 12
def DIRECTION_AXIOM_2 : thm := keep "DIRECTION_AXIOM_2" fun _ => (do
  prove ([[!l l'. ?p. p _|_ l /\ p _|_ l']])
   (REWRITE_TAC [perpdir, DIRECTION_CLAUSES] THEN
    MESON_TAC [NORMAL_EXISTS, ORTHOGONAL_SYM])
  : ExceptT String IO thm).run
#eval DIRECTION_AXIOM_2

#eval phrase 13
def DIRECTION_AXIOM_3 : thm := keep "DIRECTION_AXIOM_3" fun _ => (do
  prove ([[?p p' p''.
        ~(p || p') /\ ~(p' || p'') /\ ~(p || p'') /\
        ~(?l. p _|_ l /\ p' _|_ l /\ p'' _|_ l)]])
   (REWRITE_TAC [perpdir, pardir, DIRECTION_CLAUSES] THEN MAP_EVERY (fun t => EXISTS_TAC t THEN SIMP_TAC [BASIS_NONZERO, DIMINDEX_3, ARITH]) [([[basis 1 :real^3]]), ([[basis 2 : real^3]]), ([[basis 3 :real^3]])] THEN
    VEC3_TAC)
  : ExceptT String IO thm).run
#eval DIRECTION_AXIOM_3

#eval phrase 14
def DIRECTION_AXIOM_4_WEAK : thm := keep "DIRECTION_AXIOM_4_WEAK" fun _ => (do
  prove ([[!l. ?p p'. ~(p || p') /\ p _|_ l /\ p' _|_ l]])
   (REWRITE_TAC [DIRECTION_CLAUSES, pardir, perpdir] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[orthogonal (l cross basis 1) l /\ orthogonal (l cross basis 2) l /\
    ~((l cross basis 1) cross (l cross basis 2) = vec 0) \/
    orthogonal (l cross basis 1) l /\ orthogonal (l cross basis 3) l /\
    ~((l cross basis 1) cross (l cross basis 3) = vec 0) \/
    orthogonal (l cross basis 2) l /\ orthogonal (l cross basis 3) l /\
    ~((l cross basis 2) cross (l cross basis 3) = vec 0)]]) MP_TAC THENL [POP_ASSUM MP_TAC THEN VEC3_TAC, MESON_TAC [CROSS_0]])
  : ExceptT String IO thm).run
#eval DIRECTION_AXIOM_4_WEAK

#eval phrase 15
def ORTHOGONAL_COMBINE : thm := keep "ORTHOGONAL_COMBINE" fun _ => (do
  prove ([[!x a b. a _|_ x /\ b _|_ x /\ ~(a || b)
           ==> ?c. c _|_ x /\ ~(a || c) /\ ~(b || c)]])
   (REWRITE_TAC [DIRECTION_CLAUSES, pardir, perpdir] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC ([[a + b:real^3]]) THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN VEC3_TAC)
  : ExceptT String IO thm).run
#eval ORTHOGONAL_COMBINE

#eval phrase 16
def DIRECTION_AXIOM_4 : thm := keep "DIRECTION_AXIOM_4" fun _ => (do
  prove ([[!l. ?p p' p''. ~(p || p') /\ ~(p' || p'') /\ ~(p || p'') /\
                  p _|_ l /\ p' _|_ l /\ p'' _|_ l]])
   (MESON_TAC [DIRECTION_AXIOM_4_WEAK, ORTHOGONAL_COMBINE])
  : ExceptT String IO thm).run
#eval DIRECTION_AXIOM_4

#eval phrase 17
-- let line_tybij = define_quotient_type "line" ("mk_line","dest_line") `(||)`;;
def line_tybij : thm × thm := keepIO "line_tybij" fun _ => (do
  ExceptT.mk (define_quotient_type "line" ("mk_line", "dest_line") (← ExceptT.mk [[(||)]]))
  : ExceptT String IO (thm × thm)).run
#eval printPair line_tybij

#eval phrase 18
def PERPDIR_WELLDEF : thm := keep "PERPDIR_WELLDEF" fun _ => (do
  prove ([[!x y x' y'. x || x' /\ y || y' ==> (x _|_ y <=> x' _|_ y')]])
   (REWRITE_TAC [perpdir, pardir, DIRECTION_CLAUSES] THEN VEC3_TAC)
  : ExceptT String IO thm).run
#eval PERPDIR_WELLDEF

#eval phrase 19
-- let perpl,perpl_th = lift_function (snd line_tybij) (PARDIR_REFL,PARDIR_TRANS) "perpl" PERPDIR_WELLDEF;;
def perpl_defs : thm × thm := keepIO "perpl_defs" fun _ =>
  lift_function line_tybij.2 (PARDIR_REFL, PARDIR_TRANS) "perpl" PERPDIR_WELLDEF
def perpl : thm := perpl_defs.1
def perpl_th : thm := perpl_defs.2
#eval do IO.println (repr perpl); IO.println (repr perpl_th)

#eval phrase 20
-- let line_lift_thm = lift_theorem line_tybij (PARDIR_REFL,PARDIR_SYM,PARDIR_TRANS) [perpl_th];;
def line_lift_thm (th : thm) : ExceptT String IO thm :=
  ExceptT.mk (lift_theorem line_tybij (PARDIR_REFL, PARDIR_SYM, PARDIR_TRANS) [perpl_th] th)
#eval IO.println "<fun>"

#eval phrase 21
-- let LINE_AXIOM_1 = line_lift_thm DIRECTION_AXIOM_1;;
def LINE_AXIOM_1 : thm := keep "LINE_AXIOM_1" fun _ => (line_lift_thm DIRECTION_AXIOM_1).run
#eval LINE_AXIOM_1

#eval phrase 22
-- let LINE_AXIOM_2 = line_lift_thm DIRECTION_AXIOM_2;;
def LINE_AXIOM_2 : thm := keep "LINE_AXIOM_2" fun _ => (line_lift_thm DIRECTION_AXIOM_2).run
#eval LINE_AXIOM_2

#eval phrase 23
-- let LINE_AXIOM_3 = line_lift_thm DIRECTION_AXIOM_3;;
def LINE_AXIOM_3 : thm := keep "LINE_AXIOM_3" fun _ => (line_lift_thm DIRECTION_AXIOM_3).run
#eval LINE_AXIOM_3

#eval phrase 24
-- let LINE_AXIOM_4 = line_lift_thm DIRECTION_AXIOM_4;;
def LINE_AXIOM_4 : thm := keep "LINE_AXIOM_4" fun _ => (line_lift_thm DIRECTION_AXIOM_4).run
#eval LINE_AXIOM_4

#eval phrase 25
def point_tybij : thm := keep "point_tybij" fun _ => (do
  ExceptT.mk (new_type_definition "point" "mk_point" "dest_point" (← prove ([[?x:line. T]])
     (REWRITE_TAC [])))
  : ExceptT String IO thm).run
#eval point_tybij

#eval phrase 26
-- parse_as_infix("on",(11,"right"));;
#eval (parse_as_infix ("on", (11, "right")) : IO Unit)

#eval phrase 27
def on : thm := keep "on" fun _ => new_definition
 [[p on l <=> perpl (dest_point p) l]]
#eval on

#eval phrase 28
def POINT_CLAUSES : thm := keep "POINT_CLAUSES" fun _ => (do
  prove ([[((p = p') <=> (dest_point p = dest_point p')) /\
   ((!p. P (dest_point p)) <=> (!l. P l)) /\
   ((?p. P (dest_point p)) <=> (?l. P l))]])
   (MESON_TAC [point_tybij])
  : ExceptT String IO thm).run
#eval POINT_CLAUSES

#eval phrase 29
-- let POINT_TAC th = REWRITE_TAC[on; POINT_CLAUSES] THEN ACCEPT_TAC th;;
def POINT_TAC (th : thm) : HolCore.Tactics.tactic :=
  REWRITE_TAC [on, POINT_CLAUSES] THEN ACCEPT_TAC th
#eval IO.println "<fun>"

#eval phrase 30
def AXIOM_1 : thm := keep "AXIOM_1" fun _ => (do
  prove ([[!p p'. ~(p = p') ==> ?l. p on l /\ p' on l /\
          !l'. p on l' /\ p' on l' ==> (l' = l)]])
   (POINT_TAC LINE_AXIOM_1)
  : ExceptT String IO thm).run
#eval AXIOM_1

#eval phrase 31
def AXIOM_2 : thm := keep "AXIOM_2" fun _ => (do
  prove ([[!l l'. ?p. p on l /\ p on l']])
   (POINT_TAC LINE_AXIOM_2)
  : ExceptT String IO thm).run
#eval AXIOM_2

#eval phrase 32
def AXIOM_3 : thm := keep "AXIOM_3" fun _ => (do
  prove ([[?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    ~(?l. p on l /\ p' on l /\ p'' on l)]])
   (POINT_TAC LINE_AXIOM_3)
  : ExceptT String IO thm).run
#eval AXIOM_3

#eval phrase 33
def AXIOM_4 : thm := keep "AXIOM_4" fun _ => (do
  prove ([[!l. ?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    p on l /\ p' on l /\ p'' on l]])
   (POINT_TAC LINE_AXIOM_4)
  : ExceptT String IO thm).run
#eval AXIOM_4

/- ------------------------------------------------------------------------- -/
/- Mappings from vectors in R^3 to projective lines and points.              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 34
def projl : thm := keep "projl" fun _ => new_definition
 [[projl x = mk_line((||) (mk_dir x))]]
#eval projl

#eval phrase 35
def projp : thm := keep "projp" fun _ => new_definition
 [[projp x = mk_point(projl x)]]
#eval projp

/- ------------------------------------------------------------------------- -/
/- Mappings in the other direction, to (some) homogeneous coordinates.       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 36
def PROJL_TOTAL : thm := keep "PROJL_TOTAL" fun _ => (do
  prove ([[!l. ?x. ~(x = vec 0) /\ l = projl x]])
   (GEN_TAC THEN
    SUBGOAL_THEN ([[?d. l = mk_line((||) d)]]) (CHOOSE_THEN SUBST1_TAC) THENL
     [MESON_TAC [Prod.fst line_tybij, line_tybij.2],
      REWRITE_TAC [projl] THEN EXISTS_TAC ([[dest_dir d]]) THEN
      MESON_TAC [direction_tybij]])
  : ExceptT String IO thm).run
#eval PROJL_TOTAL

#eval phrase 37
def homol : thm := keep "homol" fun _ => (do
  ExceptT.mk (Session.new_specification ["homol"] (← HolLight.REWRITE_RULE [SKOLEM_THM] PROJL_TOTAL))
  : ExceptT String IO thm).run
#eval homol

#eval phrase 38
def PROJP_TOTAL : thm := keep "PROJP_TOTAL" fun _ => (do
  prove ([[!p. ?x. ~(x = vec 0) /\ p = projp x]])
   (REWRITE_TAC [projp] THEN MESON_TAC [PROJL_TOTAL, point_tybij])
  : ExceptT String IO thm).run
#eval PROJP_TOTAL

#eval phrase 39
def homop_def : thm := keep "homop_def" fun _ => new_definition
 [[homop p = homol(dest_point p)]]
#eval homop_def

#eval phrase 40
def homop : thm := keep "homop" fun _ => (do
  let h1 ← ms [point_tybij] (← ExceptT.mk [[p = mk_point l <=> dest_point p = l]])
  prove ([[!p. ~(homop p = vec 0) /\ p = projp(homop p)]])
   (GEN_TAC THEN REWRITE_TAC [homop_def, projp, h1] THEN
    MATCH_ACCEPT_TAC homol)
  : ExceptT String IO thm).run
#eval homop

/- ------------------------------------------------------------------------- -/
/- Key equivalences of concepts in projective space and homogeneous coords.  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 41
def parallel : thm := keep "parallel" fun _ => new_definition
 [[parallel x y <=> x cross y = vec 0]]
#eval parallel

#eval phrase 42
def ON_HOMOL : thm := keep "ON_HOMOL" fun _ => (do
  prove ([[!p l. p on l <=> orthogonal (homop p) (homol l)]])
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [homop, homol] THEN
    REWRITE_TAC [on, projp, projl, (← HolLight.REWRITE_RULE [] point_tybij)] THEN
    REWRITE_TAC [(← HolLight.GSYM perpl_th), perpdir] THEN BINOP_TAC THEN
    MESON_TAC [homol, homop, direction_tybij])
  : ExceptT String IO thm).run
#eval ON_HOMOL

#eval phrase 43
def EQ_HOMOL : thm := keep "EQ_HOMOL" fun _ => (do
  let h1 ← ms [Prod.fst line_tybij, line_tybij.2] (← ExceptT.mk [[mk_line((||) l) = mk_line((||) l') <=> (||) l = (||) l']])
  prove ([[!l l'. l = l' <=> parallel (homol l) (homol l')]])
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.BINOP_CONV) [homol] THEN
    REWRITE_TAC [projl, h1] THEN
    REWRITE_TAC [PARDIR_EQUIV] THEN REWRITE_TAC [pardir, parallel] THEN
    MESON_TAC [homol, direction_tybij])
  : ExceptT String IO thm).run
#eval EQ_HOMOL

#eval phrase 44
def EQ_HOMOP : thm := keep "EQ_HOMOP" fun _ => (do
  prove ([[!p p'. p = p' <=> parallel (homop p) (homop p')]])
   (REWRITE_TAC [homop_def, (← HolLight.GSYM EQ_HOMOL)] THEN
    MESON_TAC [point_tybij])
  : ExceptT String IO thm).run
#eval EQ_HOMOP

/- ------------------------------------------------------------------------- -/
/- A "welldefinedness" result for homogeneous coordinate map.                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 45
def PARALLEL_PROJL_HOMOL : thm := keep "PARALLEL_PROJL_HOMOL" fun _ => (do
  let h1 ← ms [Prod.fst line_tybij, line_tybij.2] (← ExceptT.mk [[dest_line(mk_line((||) l)) = (||) l]])
  prove ([[!x. parallel x (homol(projl x))]])
   (GEN_TAC THEN REWRITE_TAC [parallel] THEN ASM_CASES_TAC ([[x:real^3 = vec 0]]) THEN
    ASM_REWRITE_TAC [CROSS_0] THEN MP_TAC (← HolLight.ISPEC ([[projl x]]) homol) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [projl] THEN
    DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[dest_line]])) THEN
    REWRITE_TAC [h1] THEN
    REWRITE_TAC [PARDIR_EQUIV] THEN REWRITE_TAC [pardir] THEN
    ASM_MESON_TAC [direction_tybij])
  : ExceptT String IO thm).run
#eval PARALLEL_PROJL_HOMOL

#eval phrase 46
def PARALLEL_PROJP_HOMOP : thm := keep "PARALLEL_PROJP_HOMOP" fun _ => (do
  prove ([[!x. parallel x (homop(projp x))]])
   (REWRITE_TAC [homop_def, projp, (← HolLight.REWRITE_RULE [] point_tybij)] THEN
    REWRITE_TAC [PARALLEL_PROJL_HOMOL])
  : ExceptT String IO thm).run
#eval PARALLEL_PROJP_HOMOP

#eval phrase 47
def PARALLEL_PROJP_HOMOP_EXPLICIT : thm := keep "PARALLEL_PROJP_HOMOP_EXPLICIT" fun _ => (do
  prove ([[!x. ~(x = vec 0) ==> ?a. ~(a = &0) /\ homop(projp x) = a % x]])
   (MP_TAC PARALLEL_PROJP_HOMOP THEN MATCH_MP_TAC MONO_FORALL THEN
    REWRITE_TAC [parallel, CROSS_EQ_0, COLLINEAR_LEMMA] THEN
    GEN_TAC THEN ASM_CASES_TAC ([[x:real^3 = vec 0]]) THEN
    ASM_REWRITE_TAC [homop] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC ([[c:real]]) THEN ASM_CASES_TAC ([[c = &0]]) THEN
    ASM_REWRITE_TAC [homop, VECTOR_MUL_LZERO])
  : ExceptT String IO thm).run
#eval PARALLEL_PROJP_HOMOP_EXPLICIT

/- ------------------------------------------------------------------------- -/
/- Brackets, collinearity and their connection.                              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 48
def bracket : thm := keep "bracket" fun _ => define
 [[bracket[a;b;c] = det(vector[homop a;homop b;homop c])]]
#eval bracket

#eval phrase 49
def COLLINEAR : thm := keep "COLLINEAR" fun _ => new_definition
 [[COLLINEAR s <=> ?l. !p. p IN s ==> p on l]]
#eval COLLINEAR

#eval phrase 50
def COLLINEAR_SINGLETON : thm := keep "COLLINEAR_SINGLETON" fun _ => (do
  prove ([[!a. COLLINEAR {a}]])
   (REWRITE_TAC [COLLINEAR, FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
    MESON_TAC [AXIOM_1, AXIOM_3])
  : ExceptT String IO thm).run
#eval COLLINEAR_SINGLETON

#eval phrase 51
def COLLINEAR_PAIR : thm := keep "COLLINEAR_PAIR" fun _ => (do
  prove ([[!a b. COLLINEAR{a,b}]])
   (REPEAT GEN_TAC THEN ASM_CASES_TAC ([[a:point = b]]) THEN
    ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_SINGLETON] THEN
    REWRITE_TAC [COLLINEAR, FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
    ASM_MESON_TAC [AXIOM_1])
  : ExceptT String IO thm).run
#eval COLLINEAR_PAIR

#eval phrase 52
def COLLINEAR_TRIPLE : thm := keep "COLLINEAR_TRIPLE" fun _ => (do
  prove ([[!a b c. COLLINEAR{a,b,c} <=> ?l. a on l /\ b on l /\ c on l]])
   (REWRITE_TAC [COLLINEAR, FORALL_IN_INSERT, NOT_IN_EMPTY])
  : ExceptT String IO thm).run
#eval COLLINEAR_TRIPLE

#eval phrase 53
def COLLINEAR_BRACKET : thm := keep "COLLINEAR_BRACKET" fun _ => (do
  let lemma ← prove ([[!a b c x y.
          x cross y = vec 0 /\ ~(x = vec 0) /\
          orthogonal a x /\ orthogonal b x /\ orthogonal c x
          ==> orthogonal a y /\ orthogonal b y /\ orthogonal c y]])
     (REWRITE_TAC [orthogonal] THEN VEC3_TAC)
  prove ([[!p1 p2 p3. COLLINEAR {p1,p2,p3} <=> bracket[p1;p2;p3] = &0]])
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [COLLINEAR_TRIPLE, bracket, ON_HOMOL, LEFT_IMP_EXISTS_THM] THEN
      MP_TAC homol THEN MATCH_MP_TAC MONO_FORALL THEN
      GEN_TAC THEN DISCH_THEN (MP_TAC o HolLight.CONJUNCT1) THEN
      REWRITE_TAC [DET_3, orthogonal, DOT_3, VECTOR_3, CART_EQ,
                DIMINDEX_3, FORALL_3, VEC_COMPONENT] THEN
      CONV_TAC REAL_RING,
      ASM_CASES_TAC ([[p1:point = p2]]) THENL
       [ASM_REWRITE_TAC [INSERT_AC, COLLINEAR_PAIR], ALL_TAC] THEN
      POP_ASSUM MP_TAC THEN
      REWRITE_TAC [parallel, COLLINEAR_TRIPLE, bracket, EQ_HOMOP, ON_HOMOL] THEN
      REPEAT STRIP_TAC THEN
      EXISTS_TAC ([[mk_line((||) (mk_dir(homop p1 cross homop p2)))]]) THEN
      MATCH_MP_TAC lemma THEN EXISTS_TAC ([[homop p1 cross homop p2]]) THEN
      ASM_REWRITE_TAC [ORTHOGONAL_CROSS] THEN
      REWRITE_TAC [orthogonal] THEN ONCE_REWRITE_TAC [DOT_SYM] THEN
      ONCE_REWRITE_TAC [CROSS_TRIPLE] THEN ONCE_REWRITE_TAC [DOT_SYM] THEN
      ASM_REWRITE_TAC [DOT_CROSS_DET] THEN
      REWRITE_TAC [(← HolLight.GSYM projl), (← HolLight.GSYM parallel), PARALLEL_PROJL_HOMOL]])
  : ExceptT String IO thm).run
#eval COLLINEAR_BRACKET

/- ------------------------------------------------------------------------- -/
/- Rather crude shuffling of bracket triple into canonical order.            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 54
-- let BRACKET_SWAP, BRACKET_SHUFFLE = (CONJ_PAIR o prove) ...
def BRACKET_SWAP_BRACKET_SHUFFLE_THMS : List thm := keepIO "BRACKET_SWAP_BRACKET_SHUFFLE_THMS" fun _ => (do
  let th ← prove ([[bracket[x;y;z] = --bracket[x;z;y] /\
   bracket[x;y;z] = bracket[y;z;x] /\
   bracket[x;y;z] = bracket[z;x;y] ]])
   (REWRITE_TAC [bracket, DET_3, VECTOR_3] THEN CONV_TAC REAL_RING)
  let p ← HolLight.CONJ_PAIR th
  pure [p.1, p.2]
  : ExceptT String IO (List thm)).run
def BRACKET_SWAP : thm := BRACKET_SWAP_BRACKET_SHUFFLE_THMS[0]!
def BRACKET_SHUFFLE : thm := BRACKET_SWAP_BRACKET_SHUFFLE_THMS[1]!
#eval do IO.println (repr BRACKET_SWAP); IO.println (repr BRACKET_SHUFFLE)

#eval phrase 55
-- let BRACKET_SWAP_CONV = ...;;
def BRACKET_SWAP_CONV (tm : term) : IO (Except String thm) := (do
  let th ← ExceptT.mk (HolLight.GEN_REWRITE_CONV HolCore.Lib.I [BRACKET_SWAP] tm)
  let tm' ← ec (HolCore.Kernel.rand (← ec (HolCore.Kernel.rand (concl th))))
  if HolCore.Simp.term_order tm tm' then pure th else throw "BRACKET_SWAP_CONV"
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Direct proof following Richter-Gebert's "Meditations on Ceva's Theorem",  -/
/- except for a change of variable names. The degenerate conditions here are -/
/- just those that naturally get used in the proof.                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 56
def DESARGUES_DIRECT : thm := keep "DESARGUES_DIRECT" fun _ => (do
  let h3 ← tt (← ExceptT.mk [[!b. (a ==> b) /\ (b ==> c) ==> a ==> c]])
  let h2 ← rg (← ExceptT.mk [[a = b /\ x:real = y ==> a * x = b * y]])
  let h1 ← tt (← ExceptT.mk [[(c ==> d ==> b ==> e) ==> ((a ==> b) /\ c ==> a /\ d ==> e)]])
  prove ([[~COLLINEAR {A',B,S} /\
   ~COLLINEAR {A,P,C} /\
   ~COLLINEAR {A,P,R} /\
   ~COLLINEAR {A,C,B} /\
   ~COLLINEAR {A,B,R} /\
   ~COLLINEAR {C',P,A'} /\
   ~COLLINEAR {C',P,B} /\
   ~COLLINEAR {C',P,B'} /\
   ~COLLINEAR {C',A',S} /\
   ~COLLINEAR {C',A',B'} /\
   ~COLLINEAR {P,C,A'} /\
   ~COLLINEAR {P,C,B} /\
   ~COLLINEAR {P,A',R} /\
   ~COLLINEAR {P,B,Q} /\
   ~COLLINEAR {P,Q,B'} /\
   ~COLLINEAR {C,B,S} /\
   ~COLLINEAR {A',Q,B'}
   ==> COLLINEAR {P,A',A} /\
       COLLINEAR {P,B,B'} /\
       COLLINEAR {P,C',C} /\
       COLLINEAR {B,C,Q} /\
       COLLINEAR {B',C',Q} /\
       COLLINEAR {A,R,C} /\
       COLLINEAR {A',C',R} /\
       COLLINEAR {B,S,A} /\
       COLLINEAR {A',S,B'}
       ==> COLLINEAR {Q,S,R}]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [COLLINEAR_BRACKET] THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[(bracket[P;A';A] = &0
     ==> bracket[P;A';R] * bracket[P;A;C] =
         bracket[P;A';C] * bracket[P;A;R]) /\
    (bracket[P;B;B'] = &0
     ==> bracket[P;B;Q] * bracket[P;B';C'] =
         bracket[P;B;C'] * bracket[P;B';Q]) /\
    (bracket[P;C';C] = &0
     ==> bracket[P;C';B] * bracket[P;C;A'] =
         bracket[P;C';A'] * bracket[P;C;B]) /\
    (bracket[B;C;Q] = &0
     ==> bracket[B;C;P] * bracket[B;Q;S] =
         bracket[B;C;S] * bracket[B;Q;P]) /\
    (bracket[B';C';Q] = &0
     ==> bracket[B';C';A'] * bracket[B';Q;P] =
         bracket[B';C';P] * bracket[B';Q;A']) /\
    (bracket[A;R;C] = &0
     ==> bracket[A;R;P] * bracket[A;C;B] =
         bracket[A;R;B] * bracket[A;C;P]) /\
    (bracket[A';C';R] = &0
     ==> bracket[A';C';P] * bracket[A';R;S] =
         bracket[A';C';S] * bracket[A';R;P]) /\
    (bracket[B;S;A] = &0
     ==> bracket[B;S;C] * bracket[B;A;R] =
         bracket[B;S;R] * bracket[B;A;C]) /\
    (bracket[A';S;B'] = &0
     ==> bracket[A';S;C'] * bracket[A';B';Q] =
         bracket[A';S;Q] * bracket[A';B';C'])]]) MP_TAC THENL
     [REWRITE_TAC [bracket, DET_3, VECTOR_3] THEN CONV_TAC REAL_RING,
      ALL_TAC] THEN
    REPEAT (MATCH_MP_TAC h1) THEN
    DISCH_THEN (fun th => DISCH_THEN (MP_TAC o HolLight.MATCH_MP th)) THEN
    REPEAT (ONCE_REWRITE_TAC [IMP_IMP] THEN
           DISCH_THEN (MP_TAC o HolLight.MATCH_MP h2)) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [BRACKET_SHUFFLE] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV BRACKET_SWAP_CONV) THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_MUL_ASSOC), REAL_MUL_LNEG, REAL_MUL_RNEG] THEN
    REWRITE_TAC [REAL_NEG_NEG, REAL_NEG_EQ_0] THEN DISCH_TAC THEN
    MATCH_MP_TAC h3 THEN
    EXISTS_TAC ([[bracket[B;Q;S] * bracket[A';R;S] =
              bracket[B;R;S] * bracket[A';Q;S] ]]) THEN
    CONJ_TAC THENL [POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING, ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.CONJUNCT1) THEN
    REWRITE_TAC [bracket, DET_3, VECTOR_3] THEN CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval DESARGUES_DIRECT

end Hol100.Desargues
