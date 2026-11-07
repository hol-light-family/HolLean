/- File: Hol100/Pascal.lean
Translation of HOL Light's 100/pascal.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionMultiLib.Cross
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Iter SessionLibrary.Wo SessionLibrary.Floor SessionLibrary.Products SessionLibrary.Permutations SessionLibrary.Card SessionLibrary.Matroids SessionMultiLib.Misc SessionMultiLib.Vectors SessionMultiLib.Metric SessionMultiLib.Determinants SessionMultiLib.Topology SessionMultiLib.Cross
namespace Hol100.Pascal

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
/- Pascal's hexagon theorem for projective and affine planes.                -/
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
/- Conics and bracket condition for 6 points to be on a conic.               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 54
def homogeneous_conic : thm := keep "homogeneous_conic" fun _ => new_definition
 [[homogeneous_conic con <=>
    ?a b c d e f.
       ~(a = &0 /\ b = &0 /\ c = &0 /\ d = &0 /\ e = &0 /\ f = &0) /\
       con = {x:real^3 | a * x$1 pow 2 + b * x$2 pow 2 + c * x$3 pow 2 +
                         d * x$1 * x$2 + e * x$1 * x$3 + f * x$2 * x$3 = &0}]]
#eval homogeneous_conic

#eval phrase 55
def projective_conic : thm := keep "projective_conic" fun _ => new_definition
 [[projective_conic con <=>
        ?c. homogeneous_conic c /\ con = {p | (homop p) IN c}]]
#eval projective_conic

#eval phrase 56
def HOMOGENEOUS_CONIC_BRACKET : thm := keep "HOMOGENEOUS_CONIC_BRACKET" fun _ => (do
  prove ([[!con x1 x2 x3 x4 x5 x6.
        homogeneous_conic con /\
        x1 IN con /\ x2 IN con /\ x3 IN con /\
        x4 IN con /\ x5 IN con /\ x6 IN con
        ==> det(vector[x6;x1;x4]) * det(vector[x6;x2;x3]) *
            det(vector[x5;x1;x3]) * det(vector[x5;x2;x4]) =
            det(vector[x6;x1;x3]) * det(vector[x6;x2;x4]) *
            det(vector[x5;x1;x4]) * det(vector[x5;x2;x3])]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [homogeneous_conic, EXTENSION] THEN
    ONCE_REWRITE_TAC [IMP_CONJ] THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    ASM_REWRITE_TAC [IN_ELIM_THM, DET_3, VECTOR_3] THEN
    CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval HOMOGENEOUS_CONIC_BRACKET

#eval phrase 57
def PROJECTIVE_CONIC_BRACKET : thm := keep "PROJECTIVE_CONIC_BRACKET" fun _ => (do
  prove ([[!con p1 p2 p3 p4 p5 p6.
        projective_conic con /\
        p1 IN con /\ p2 IN con /\ p3 IN con /\
        p4 IN con /\ p5 IN con /\ p6 IN con
        ==> bracket[p6;p1;p4] * bracket[p6;p2;p3] *
            bracket[p5;p1;p3] * bracket[p5;p2;p4] =
            bracket[p6;p1;p3] * bracket[p6;p2;p4] *
            bracket[p5;p1;p4] * bracket[p5;p2;p3] ]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [bracket, projective_conic] THEN
    DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC HOMOGENEOUS_CONIC_BRACKET THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval PROJECTIVE_CONIC_BRACKET

/- ------------------------------------------------------------------------- -/
/- Pascal's theorem with all the nondegeneracy principles we use directly.   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 58
def PASCAL_DIRECT : thm := keep "PASCAL_DIRECT" fun _ => (do
  let h3 ← rg (← ExceptT.mk [[a = b /\ x:real = y ==> a * x = b * y]])
  let h2 ← tt (← ExceptT.mk [[!q. (p ==> q) /\ (q ==> r) ==> p ==> r]])
  let h1 ← tt (← ExceptT.mk [[a /\ b /\ c /\ d /\ e /\ f /\ g /\ h ==> p <=>
                    a /\ b /\ c /\ d /\ e /\ f /\ g ==> h ==> p]])
  prove ([[!con x1 x2 x3 x4 x5 x6 x6 x8 x9.
        ~COLLINEAR {x2,x5,x7} /\
        ~COLLINEAR {x1,x2,x5} /\
        ~COLLINEAR {x1,x3,x6} /\
        ~COLLINEAR {x2,x4,x6} /\
        ~COLLINEAR {x3,x4,x5} /\
        ~COLLINEAR {x1,x5,x7} /\
        ~COLLINEAR {x2,x5,x9} /\
        ~COLLINEAR {x1,x2,x6} /\
        ~COLLINEAR {x3,x6,x8} /\
        ~COLLINEAR {x2,x4,x5} /\
        ~COLLINEAR {x2,x4,x7} /\
        ~COLLINEAR {x2,x6,x8} /\
        ~COLLINEAR {x3,x4,x6} /\
        ~COLLINEAR {x3,x5,x8} /\
        ~COLLINEAR {x1,x3,x5}
        ==> projective_conic con /\
            x1 IN con /\ x2 IN con /\ x3 IN con /\
            x4 IN con /\ x5 IN con /\ x6 IN con /\
            COLLINEAR {x1,x9,x5} /\
            COLLINEAR {x1,x8,x6} /\
            COLLINEAR {x2,x9,x4} /\
            COLLINEAR {x2,x7,x6} /\
            COLLINEAR {x3,x8,x4} /\
            COLLINEAR {x3,x7,x5}
            ==> COLLINEAR {x7,x8,x9}]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [h1] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP PROJECTIVE_CONIC_BRACKET) THEN
    REWRITE_TAC [COLLINEAR_BRACKET, IMP_IMP, (← HolLight.GSYM CONJ_ASSOC)] THEN
    MATCH_MP_TAC h2 THEN
    EXISTS_TAC ([[bracket[x1;x2;x5] * bracket[x1;x3;x6] *
    bracket[x2;x4;x6] * bracket[x3;x4;x5] =
    bracket[x1;x2;x6] * bracket[x1;x3;x5] *
    bracket[x2;x4;x5] * bracket[x3;x4;x6] /\
    bracket[x1;x5;x7] * bracket[x2;x5;x9] =
    --bracket[x1;x2;x5] * bracket[x5;x9;x7] /\
    bracket[x1;x2;x6] * bracket[x3;x6;x8] =
    bracket[x1;x3;x6] * bracket[x2;x6;x8] /\
    bracket[x2;x4;x5] * bracket[x2;x9;x7] =
    --bracket[x2;x4;x7] * bracket[x2;x5;x9] /\
    bracket[x2;x4;x7] * bracket[x2;x6;x8] =
    --bracket[x2;x4;x6] * bracket[x2;x8;x7] /\
    bracket[x3;x4;x6] * bracket[x3;x5;x8] =
    bracket[x3;x4;x5] * bracket[x3;x6;x8] /\
    bracket[x1;x3;x5] * bracket[x5;x8;x7] =
    --bracket[x1;x5;x7] * bracket[x3;x5;x8] ]]) THEN
    CONJ_TAC THENL
     [REPEAT (MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN
      REWRITE_TAC [bracket, DET_3, VECTOR_3] THEN CONV_TAC REAL_RING,
      ALL_TAC] THEN
    REWRITE_TAC [IMP_CONJ] THEN
    REPEAT (ONCE_REWRITE_TAC [IMP_IMP] THEN
           DISCH_THEN (MP_TAC o HolLight.MATCH_MP h3)) THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_MUL_ASSOC), REAL_MUL_LNEG, REAL_MUL_RNEG] THEN
    REWRITE_TAC [REAL_NEG_NEG] THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [COLLINEAR_BRACKET]) THEN
    REWRITE_TAC [REAL_MUL_AC] THEN ASM_REWRITE_TAC [REAL_EQ_MUL_LCANCEL] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [(← HolLight.GSYM REAL_MUL_ASSOC)] THEN
    ASM_REWRITE_TAC [REAL_EQ_MUL_LCANCEL] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.CONJUNCT1) THEN
    REWRITE_TAC [bracket, DET_3, VECTOR_3] THEN CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval PASCAL_DIRECT

/- ------------------------------------------------------------------------- -/
/- With longer but more intuitive non-degeneracy conditions, basically that  -/
/- the 6 points divide into two groups of 3 and no 3 are collinear unless    -/
/- they are all in the same group.                                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 59
def PASCAL : thm := keep "PASCAL" fun _ => (do
  prove ([[!con x1 x2 x3 x4 x5 x6 x6 x8 x9.
        ~COLLINEAR {x1,x2,x4} /\
        ~COLLINEAR {x1,x2,x5} /\
        ~COLLINEAR {x1,x2,x6} /\
        ~COLLINEAR {x1,x3,x4} /\
        ~COLLINEAR {x1,x3,x5} /\
        ~COLLINEAR {x1,x3,x6} /\
        ~COLLINEAR {x2,x3,x4} /\
        ~COLLINEAR {x2,x3,x5} /\
        ~COLLINEAR {x2,x3,x6} /\
        ~COLLINEAR {x4,x5,x1} /\
        ~COLLINEAR {x4,x5,x2} /\
        ~COLLINEAR {x4,x5,x3} /\
        ~COLLINEAR {x4,x6,x1} /\
        ~COLLINEAR {x4,x6,x2} /\
        ~COLLINEAR {x4,x6,x3} /\
        ~COLLINEAR {x5,x6,x1} /\
        ~COLLINEAR {x5,x6,x2} /\
        ~COLLINEAR {x5,x6,x3}
        ==> projective_conic con /\
            x1 IN con /\ x2 IN con /\ x3 IN con /\
            x4 IN con /\ x5 IN con /\ x6 IN con /\
            COLLINEAR {x1,x9,x5} /\
            COLLINEAR {x1,x8,x6} /\
            COLLINEAR {x2,x9,x4} /\
            COLLINEAR {x2,x7,x6} /\
            COLLINEAR {x3,x8,x4} /\
            COLLINEAR {x3,x7,x5}
            ==> COLLINEAR {x7,x8,x9}]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        pure (MATCH_MP_TAC (← tt (← ExceptT.mk [[(~p ==> p) ==> p]])) THEN DISCH_TAC THEN
      MP_TAC th THEN MATCH_MP_TAC PASCAL_DIRECT THEN
      ASSUME_TAC (← funpowR 7 HolLight.CONJUNCT2 th))) THEN
    REPEAT CONJ_TAC THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    REWRITE_TAC [COLLINEAR_BRACKET, bracket, DET_3, VECTOR_3] THEN
    CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval PASCAL

/- ------------------------------------------------------------------------- -/
/- Homogenization and hence mapping from affine to projective plane.         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 60
def homogenize : thm := keep "homogenize" fun _ => new_definition
 [[(homogenize:real^2->real^3) x = vector[x$1; x$2; &1] ]]
#eval homogenize

#eval phrase 61
def projectivize : thm := keep "projectivize" fun _ => new_definition
 [[projectivize = projp o homogenize]]
#eval projectivize

#eval phrase 62
def HOMOGENIZE_NONZERO : thm := keep "HOMOGENIZE_NONZERO" fun _ => (do
  prove ([[!x. ~(homogenize x = vec 0)]])
   (REWRITE_TAC [CART_EQ, DIMINDEX_3, FORALL_3, VEC_COMPONENT, VECTOR_3,
                homogenize] THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval HOMOGENIZE_NONZERO

/- ------------------------------------------------------------------------- -/
/- Conic in affine plane.                                                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 63
def affine_conic : thm := keep "affine_conic" fun _ => new_definition
 [[affine_conic con <=>
    ?a b c d e f.
       ~(a = &0 /\ b = &0 /\ c = &0 /\ d = &0 /\ e = &0 /\ f = &0) /\
       con = {x:real^2 | a * x$1 pow 2 + b * x$2 pow 2 + c * x$1 * x$2 +
                         d * x$1 + e * x$2 + f = &0}]]
#eval affine_conic

/- ------------------------------------------------------------------------- -/
/- Relationships between affine and projective notions.                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 64
def COLLINEAR_PROJECTIVIZE : thm := keep "COLLINEAR_PROJECTIVIZE" fun _ => (do
  prove ([[!a b c. collinear{a,b,c} <=>
           COLLINEAR{projectivize a,projectivize b,projectivize c}]])
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [COLLINEAR_3] THEN
    REWRITE_TAC [(← HolLight.GSYM DOT_CAUCHY_SCHWARZ_EQUAL)] THEN
    REWRITE_TAC [COLLINEAR_BRACKET, projectivize, o_THM, bracket] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[det(vector[homogenize a; homogenize b; homogenize c]) = &0]]) THEN
    CONJ_TAC THENL
     [REWRITE_TAC [homogenize, DOT_2, VECTOR_SUB_COMPONENT, DET_3, VECTOR_3] THEN
      CONV_TAC REAL_RING,
      MAP_EVERY (MP_TAC o HolCore.Lib.C HolLight.SPEC PARALLEL_PROJP_HOMOP) [([[homogenize a]]), ([[homogenize b]]), ([[homogenize c]])] THEN
      MAP_EVERY (MP_TAC o HolCore.Lib.C HolLight.SPEC HOMOGENIZE_NONZERO) [([[a:real^2]]), ([[b:real^2]]), ([[c:real^2]])] THEN
      MAP_EVERY (MP_TAC o HolLight.CONJUNCT1 o HolCore.Lib.C HolLight.SPEC homop) [([[projp(homogenize a)]]), ([[projp(homogenize b)]]), ([[projp(homogenize c)]])] THEN
      REWRITE_TAC [parallel, cross, CART_EQ, DIMINDEX_3, FORALL_3, VECTOR_3,
                  DET_3, VEC_COMPONENT] THEN
      CONV_TAC REAL_RING])
  : ExceptT String IO thm).run
#eval COLLINEAR_PROJECTIVIZE

#eval phrase 65
def AFFINE_PROJECTIVE_CONIC : thm := keep "AFFINE_PROJECTIVE_CONIC" fun _ => (do
  let h1 ← ms [] (← ExceptT.mk [[(?con' con a b c d e f. P con' con a b c d e f) <=>
    (?a b d e f c con' con. P con' con a b c d e f)]])
  prove ([[!con. affine_conic con <=> ?con'. projective_conic con' /\
                                     con = {x | projectivize x IN con'}]])
   (REWRITE_TAC [affine_conic, projective_conic, homogeneous_conic] THEN
    GEN_TAC THEN REWRITE_TAC [LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [h1] THEN
    MAP_EVERY (fun s => HolLight.tactic_of do
        pure (AP_TERM_TAC THEN GEN_REWRITE_TAC HolCore.Lib.I [FUN_EQ_THM] THEN
     X_GEN_TAC (mk_var s (← ExceptT.mk (HolCore.Parser.parse_type "real"))) THEN REWRITE_TAC [])) ["a", "b", "c", "d", "e", "f"] THEN
    REWRITE_TAC [RIGHT_EXISTS_AND_THM, UNWIND_THM2, (← HolLight.GSYM CONJ_ASSOC)] THEN
    REWRITE_TAC [IN_ELIM_THM, projectivize, o_THM] THEN
    BINOP_TAC THENL [CONV_TAC HolLight.TAUT, AP_TERM_TAC] THEN
    REWRITE_TAC [EXTENSION] THEN X_GEN_TAC ([[x:real^2]]) THEN
    MP_TAC (← HolLight.SPEC ([[x:real^2]]) HOMOGENIZE_NONZERO) THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP PARALLEL_PROJP_HOMOP_EXPLICIT) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k:real]]) STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [IN_ELIM_THM, VECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC [homogenize, VECTOR_3] THEN
    UNDISCH_TAC ([[~(k = &0)]]) THEN CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval AFFINE_PROJECTIVE_CONIC

/- ------------------------------------------------------------------------- -/
/- Hence Pascal's theorem for the affine plane.                              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 66
def PASCAL_AFFINE : thm := keep "PASCAL_AFFINE" fun _ => (do
  prove ([[!con x1 x2 x3 x4 x5 x6 x7 x8 x9:real^2.
        ~collinear {x1,x2,x4} /\
        ~collinear {x1,x2,x5} /\
        ~collinear {x1,x2,x6} /\
        ~collinear {x1,x3,x4} /\
        ~collinear {x1,x3,x5} /\
        ~collinear {x1,x3,x6} /\
        ~collinear {x2,x3,x4} /\
        ~collinear {x2,x3,x5} /\
        ~collinear {x2,x3,x6} /\
        ~collinear {x4,x5,x1} /\
        ~collinear {x4,x5,x2} /\
        ~collinear {x4,x5,x3} /\
        ~collinear {x4,x6,x1} /\
        ~collinear {x4,x6,x2} /\
        ~collinear {x4,x6,x3} /\
        ~collinear {x5,x6,x1} /\
        ~collinear {x5,x6,x2} /\
        ~collinear {x5,x6,x3}
        ==> affine_conic con /\
            x1 IN con /\ x2 IN con /\ x3 IN con /\
            x4 IN con /\ x5 IN con /\ x6 IN con /\
            collinear {x1,x9,x5} /\
            collinear {x1,x8,x6} /\
            collinear {x2,x9,x4} /\
            collinear {x2,x7,x6} /\
            collinear {x3,x8,x4} /\
            collinear {x3,x7,x5}
            ==> collinear {x7,x8,x9}]])
   (REWRITE_TAC [COLLINEAR_PROJECTIVIZE, AFFINE_PROJECTIVE_CONIC] THEN
    REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP PASCAL) THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    MATCH_MP_TAC MONO_EXISTS THEN HolLight.ASM SET_TAC [])
  : ExceptT String IO thm).run
#eval PASCAL_AFFINE

/- ------------------------------------------------------------------------- -/
/- Special case of a circle where nondegeneracy is simpler.                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 67
def COLLINEAR_NOT_COCIRCULAR : thm := keep "COLLINEAR_NOT_COCIRCULAR" fun _ => (do
  prove ([[!r c x y z:real^2.
        dist(c,x) = r /\ dist(c,y) = r /\ dist(c,z) = r /\
        ~(x = y) /\ ~(x = z) /\ ~(y = z)
        ==> ~collinear {x,y,z}]])
   (ONCE_REWRITE_TAC [(← HolLight.GSYM VECTOR_SUB_EQ)] THEN
    REWRITE_TAC [(← HolLight.GSYM DOT_EQ_0)] THEN
    ONCE_REWRITE_TAC [COLLINEAR_3] THEN
    REWRITE_TAC [(← HolLight.GSYM DOT_CAUCHY_SCHWARZ_EQUAL), DOT_2] THEN
    REWRITE_TAC [SessionMultiLib.Vectors.dist, NORM_EQ_SQUARE, CART_EQ, DIMINDEX_2, FORALL_2,
                DOT_2, VECTOR_SUB_COMPONENT] THEN
    CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval COLLINEAR_NOT_COCIRCULAR

#eval phrase 68
def PASCAL_AFFINE_CIRCLE : thm := keep "PASCAL_AFFINE_CIRCLE" fun _ => (do
  prove ([[!c r x1 x2 x3 x4 x5 x6 x7 x8 x9:real^2.
        PAIRWISE (\x y. ~(x = y)) [x1;x2;x3;x4;x5;x6] /\
        dist(c,x1) = r /\ dist(c,x2) = r /\ dist(c,x3) = r /\
        dist(c,x4) = r /\ dist(c,x5) = r /\ dist(c,x6) = r /\
        collinear {x1,x9,x5} /\
        collinear {x1,x8,x6} /\
        collinear {x2,x9,x4} /\
        collinear {x2,x7,x6} /\
        collinear {x3,x8,x4} /\
        collinear {x3,x7,x5}
        ==> collinear {x7,x8,x9}]])
   (GEN_TAC THEN GEN_TAC THEN
    MP_TAC (← HolLight.SPEC ([[{x:real^2 | dist(c,x) = r}]]) PASCAL_AFFINE) THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    REWRITE_TAC [Session.listDefs.PAIRWISE, Session.listDefs.ALL, IN_ELIM_THM] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [IMP_IMP] THEN
    DISCH_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC COLLINEAR_NOT_COCIRCULAR THEN
      MAP_EVERY EXISTS_TAC [([[r:real]]), ([[c:real^2]])] THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [affine_conic, SessionMultiLib.Vectors.dist, NORM_EQ_SQUARE] THEN
      ASM_CASES_TAC ([[&0 <= r]]) THEN ASM_REWRITE_TAC [] THENL
       [MAP_EVERY EXISTS_TAC [([[&1]]), ([[&1]]), ([[&0]]), ([[-- &2 * (c:real^2)$1]]), ([[-- &2 * (c:real^2)$2]]),
          ([[(c:real^2)$1 pow 2 + (c:real^2)$2 pow 2 - r pow 2]])] THEN
        REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
        REWRITE_TAC [DOT_2, VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC2,
        REPLICATE_TAC 5 (EXISTS_TAC ([[&0]])) THEN EXISTS_TAC ([[&1]]) THEN
        REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN REAL_ARITH_TAC2]])
  : ExceptT String IO thm).run
#eval PASCAL_AFFINE_CIRCLE

end Hol100.Pascal
