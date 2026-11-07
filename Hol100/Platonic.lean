/- File: Hol100/Platonic.lean
Translation of HOL Light's 100/platonic.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import Hol100.Polyhedron
import SessionMultiLib.Cross
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Binomial SessionLibrary.Iter SessionLibrary.Wo SessionLibrary.Floor SessionLibrary.Products SessionLibrary.Permutations SessionLibrary.Frag SessionLibrary.Prime SessionLibrary.Card Hol100.InclusionExclusion SessionLibrary.Matroids Hol100.Combinations SessionMultiLib.Misc SessionLibrary.GroupTheory SessionMultiLib.Vectors SessionMultiLib.Metric SessionMultiLib.Determinants SessionMultiLib.Homology SessionMultiLib.Topology SessionMultiLib.Cross SessionMultiLib.Convex SessionMultiLib.Paths SessionMultiLib.Polytope Hol100.Polyhedron
namespace Hol100.Platonic

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
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def ia (tm : term) : ExceptT String IO thm := ExceptT.mk (INT_ARITH tm)
private def ms (ths : List thm) (tm : term) : ExceptT String IO thm :=
  ExceptT.mk (MESON ths tm)
private def ng (tm : term) : ExceptT String IO thm := ExceptT.mk (NUM_RING tm)
private def rf (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_FIELD tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)
private def v3r (tm : term) : ExceptT String IO thm := ExceptT.mk (VEC3_RULE tm)
private def va (tm : term) : ExceptT String IO thm := ExceptT.mk (VECTOR_ARITH tm)

/- ========================================================================= -/
/- The five Platonic solids exist and there are no others.                   -/
/- ========================================================================= -/

#eval phrase 1
-- needs "100/polyhedron.ml";;
#eval Hol100.Polyhedron.ensure

#eval phrase 2
-- needs "Multivariate/cross.ml";;
#eval SessionMultiLib.Cross.ensureCross

#eval phrase 3
#eval Session.prioritize_real

/- ------------------------------------------------------------------------- -/
/- Some standard regular polyhedra (vertex coordinates from Wikipedia).      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 4
def std_tetrahedron : thm := keep "std_tetrahedron" fun _ => new_definition
 [[std_tetrahedron =
     convex hull
       {vector[&1;&1;&1],vector[-- &1;-- &1;&1],
        vector[-- &1;&1;-- &1],vector[&1;-- &1;-- &1]}:real^3->bool]]
#eval std_tetrahedron

#eval phrase 5
def std_cube : thm := keep "std_cube" fun _ => new_definition
 [[std_cube =
     convex hull
       {vector[&1;&1;&1],vector[&1;&1;-- &1],
        vector[&1;-- &1;&1],vector[&1;-- &1;-- &1],
        vector[-- &1;&1;&1],vector[-- &1;&1;-- &1],
        vector[-- &1;-- &1;&1],vector[-- &1;-- &1;-- &1]}:real^3->bool]]
#eval std_cube

#eval phrase 6
def std_octahedron : thm := keep "std_octahedron" fun _ => new_definition
 [[std_octahedron =
      convex hull
       {vector[&1;&0;&0],vector[-- &1;&0;&0],
        vector[&0;&0;&1],vector[&0;&0;-- &1],
        vector[&0;&1;&0],vector[&0;-- &1;&0]}:real^3->bool]]
#eval std_octahedron

#eval phrase 7
def std_dodecahedron : thm := keep "std_dodecahedron" fun _ => new_definition
 [[std_dodecahedron =
      let p = (&1 + sqrt(&5)) / &2 in
      convex hull
       {vector[&1;&1;&1],vector[&1;&1;-- &1],
        vector[&1;-- &1;&1],vector[&1;-- &1;-- &1],
        vector[-- &1;&1;&1],vector[-- &1;&1;-- &1],
        vector[-- &1;-- &1;&1],vector[-- &1;-- &1;-- &1],
        vector[&0;inv p;p],vector[&0;inv p;--p],
        vector[&0;--inv p;p],vector[&0;--inv p;--p],
        vector[inv p;p;&0],vector[inv p;--p;&0],
        vector[--inv p;p;&0],vector[--inv p;--p;&0],
        vector[p;&0;inv p],vector[--p;&0;inv p],
        vector[p;&0;--inv p],vector[--p;&0;--inv p]}:real^3->bool]]
#eval std_dodecahedron

#eval phrase 8
def std_icosahedron : thm := keep "std_icosahedron" fun _ => new_definition
 [[std_icosahedron =
      let p = (&1 + sqrt(&5)) / &2 in
      convex hull
       {vector[&0; &1; p],vector[&0; &1; --p],
        vector[&0; -- &1; p],vector[&0; -- &1; --p],
        vector[&1; p; &0],vector[&1; --p; &0],
        vector[-- &1; p; &0],vector[-- &1; --p; &0],
        vector[p; &0; &1],vector[--p; &0; &1],
        vector[p; &0; -- &1],vector[--p; &0; -- &1]}:real^3->bool]]
#eval std_icosahedron

/- ------------------------------------------------------------------------- -/
/- Slightly ad hoc conversions for computation in Q[sqrt(5)].                -/
/- Numbers are canonically represented as either a rational constant r or an -/
/- expression r1 + r2 * sqrt(5) where r2 is nonzero but r1 may be zero and   -/
/- must be present.                                                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 9
-- let REAL_RAT5_OF_RAT_CONV = ...;;
def REAL_RAT5_OF_RAT_CONV_pth : thm := keep "REAL_RAT5_OF_RAT_CONV_pth" fun _ => (do
  prove ([[p = p + &0 * sqrt(&5)]]) REAL_ARITH_TAC2
  : ExceptT String IO thm).run
def REAL_RAT5_OF_RAT_CONV (tm : term) : IO (Except String thm) := (do
  if is_ratconst tm then ExceptT.mk (HolLight.REWR_CONV REAL_RAT5_OF_RAT_CONV_pth tm)
  else pure (HolCore.Kernel.REFL tm)
  : ExceptT String IO thm).run
#eval (do replay REAL_RAT5_OF_RAT_CONV_pth; IO.println "<fun>" : IO Unit)

#eval phrase 10
-- let REAL_RAT_OF_RAT5_CONV = ...;;
def REAL_RAT_OF_RAT5_CONV_lets : thm := keepIO "REAL_RAT_OF_RAT5_CONV_lets" fun _ => (do
  let pth ← prove ([[p + &0 * sqrt(&5) = p]])
     (REAL_ARITH_TAC2)
  pure (pth)
  : ExceptT String IO (thm)).run
def REAL_RAT_OF_RAT5_CONV : HolCore.Equal.ioconv := fun tm => (do
  let (pth) := REAL_RAT_OF_RAT5_CONV_lets
  ExceptT.mk ((HolLight.GEN_REWRITE_CONV HolLight.TRY_CONV [pth]) tm)
  : ExceptT String IO thm).run
#eval (do replay REAL_RAT_OF_RAT5_CONV_lets; IO.println "<fun>" : IO Unit)

#eval phrase 11
-- let REAL_RAT5_ADD_CONV = ...;;
def REAL_RAT5_ADD_CONV_lets : thm := keepIO "REAL_RAT5_ADD_CONV_lets" fun _ => (do
  let pth ← prove ([[(a1 + b1 * sqrt(&5)) + (a2 + b2 * sqrt(&5)) =
      (a1 + a2) + (b1 + b2) * sqrt(&5)]])
     (REAL_ARITH_TAC2)
  pure (pth)
  : ExceptT String IO (thm)).run
def REAL_RAT5_ADD_CONV : HolCore.Equal.ioconv := fun tm => (do
  let (pth) := REAL_RAT5_ADD_CONV_lets
  ExceptT.mk ((REAL_RAT_ADD_CONV ORELSEC
    (HolLight.BINOP_CONV REAL_RAT5_OF_RAT_CONV THENC
     HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth] THENC
     HolLight.LAND_CONV REAL_RAT_ADD_CONV THENC
     HolLight.RAND_CONV (HolLight.LAND_CONV REAL_RAT_ADD_CONV) THENC
     REAL_RAT_OF_RAT5_CONV)) tm)
  : ExceptT String IO thm).run
#eval (do replay REAL_RAT5_ADD_CONV_lets; IO.println "<fun>" : IO Unit)

#eval phrase 12
-- let REAL_RAT5_SUB_CONV = ...;;
def REAL_RAT5_SUB_CONV_lets : thm := keepIO "REAL_RAT5_SUB_CONV_lets" fun _ => (do
  let pth ← prove ([[(a1 + b1 * sqrt(&5)) - (a2 + b2 * sqrt(&5)) =
      (a1 - a2) + (b1 - b2) * sqrt(&5)]])
     (REAL_ARITH_TAC2)
  pure (pth)
  : ExceptT String IO (thm)).run
def REAL_RAT5_SUB_CONV : HolCore.Equal.ioconv := fun tm => (do
  let (pth) := REAL_RAT5_SUB_CONV_lets
  ExceptT.mk ((REAL_RAT_SUB_CONV ORELSEC
    (HolLight.BINOP_CONV REAL_RAT5_OF_RAT_CONV THENC
     HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth] THENC
     HolLight.LAND_CONV REAL_RAT_SUB_CONV THENC
     HolLight.RAND_CONV (HolLight.LAND_CONV REAL_RAT_SUB_CONV) THENC
     REAL_RAT_OF_RAT5_CONV)) tm)
  : ExceptT String IO thm).run
#eval (do replay REAL_RAT5_SUB_CONV_lets; IO.println "<fun>" : IO Unit)

#eval phrase 13
-- let REAL_RAT5_MUL_CONV = ...;;
def REAL_RAT5_MUL_CONV_lets : thm := keepIO "REAL_RAT5_MUL_CONV_lets" fun _ => (do
  let pth ← prove ([[(a1 + b1 * sqrt(&5)) * (a2 + b2 * sqrt(&5)) =
      (a1 * a2 + &5 * b1 * b2) + (a1 * b2 + a2 * b1) * sqrt(&5)]])
     (MP_TAC (← HolLight.ISPEC ([[&5]]) SQRT_POW_2) THEN CONV_TAC rf)
  pure (pth)
  : ExceptT String IO (thm)).run
def REAL_RAT5_MUL_CONV : HolCore.Equal.ioconv := fun tm => (do
  let (pth) := REAL_RAT5_MUL_CONV_lets
  ExceptT.mk ((REAL_RAT_MUL_CONV ORELSEC
    (HolLight.BINOP_CONV REAL_RAT5_OF_RAT_CONV THENC
     HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth] THENC
     HolLight.LAND_CONV (HolLight.COMB_CONV (HolLight.RAND_CONV REAL_RAT_MUL_CONV) THENC
               HolLight.RAND_CONV REAL_RAT_MUL_CONV THENC
               REAL_RAT_ADD_CONV) THENC
     HolLight.RAND_CONV (HolLight.LAND_CONV (HolLight.BINOP_CONV REAL_RAT_MUL_CONV THENC REAL_RAT_ADD_CONV)) THENC
     REAL_RAT_OF_RAT5_CONV)) tm)
  : ExceptT String IO thm).run
#eval (do replay REAL_RAT5_MUL_CONV_lets; IO.println "<fun>" : IO Unit)

#eval phrase 14
-- let REAL_RAT5_INV_CONV = ...;;
def REAL_RAT5_INV_CONV_pth : thm := keep "REAL_RAT5_INV_CONV_pth" fun _ => (do
  prove ([[~(a pow 2 = &5 * b pow 2)
     ==> inv(a + b * sqrt(&5)) =
         a / (a pow 2 - &5 * b pow 2) +
         --b / (a pow 2 - &5 * b pow 2) * sqrt(&5)]])
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.ONCE_DEPTH_CONV) [(← HolLight.GSYM REAL_SUB_0)] THEN
    SUBGOAL_THEN
     ([[a pow 2 - &5 * b pow 2 = (a + b * sqrt(&5)) * (a - b * sqrt(&5))]])
    SUBST1_TAC THENL
     [MP_TAC (← HolLight.SPEC ([[&5]]) SQRT_POW_2) THEN CONV_TAC REAL_FIELD,
      REWRITE_TAC [REAL_ENTIRE, DE_MORGAN_THM] THEN CONV_TAC REAL_FIELD])
  : ExceptT String IO thm).run
def REAL_RAT5_INV_CONV (tm : term) : IO (Except String thm) := do
  match ← REAL_RAT_INV_CONV tm with
  | .ok th => pure (.ok th)
  | .error _ => (do
    let th1 ← HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) REAL_RAT5_INV_CONV_pth tm
    let th2 ← HolLight.MP th1 (← HolLight.EQT_ELIM
      (← ExceptT.mk (REAL_RAT_REDUCE_CONV (← ec (HolCore.Equal.lhand (concl th1))))))
    let th3 ← HolLight.CONV_RULE (HolCore.Lib.funpow 2 HolLight.RAND_CONV
      (HolCore.Lib.funpow 2 HolLight.LAND_CONV REAL_RAT_NEG_CONV)) th2
    let den := HolLight.RAND_CONV (HolLight.LAND_CONV REAL_RAT_POW_CONV THENC
                 HolLight.RAND_CONV (HolLight.RAND_CONV REAL_RAT_POW_CONV THENC REAL_RAT_MUL_CONV) THENC
                 REAL_RAT_SUB_CONV) THENC REAL_RAT_DIV_CONV
    let th4 ← HolLight.CONV_RULE (HolLight.RAND_CONV (HolLight.RAND_CONV (HolLight.LAND_CONV den))) th3
    HolLight.CONV_RULE (HolLight.RAND_CONV (HolLight.LAND_CONV den)) th4
    : ExceptT String IO thm).run
#eval (do replay REAL_RAT5_INV_CONV_pth; IO.println "<fun>" : IO Unit)

#eval phrase 15
-- let REAL_RAT5_DIV_CONV = ...;;
def REAL_RAT5_DIV_CONV : HolCore.Equal.ioconv :=
  HolLight.GEN_REWRITE_CONV HolCore.Lib.I [real_div] THENC
    HolLight.RAND_CONV REAL_RAT5_INV_CONV THENC
    REAL_RAT5_MUL_CONV
#eval IO.println "<fun>"

#eval phrase 16
-- let REAL_RAT5_LE_CONV = ...;;
def REAL_RAT5_LE_CONV_lets : thm × thm := keepIO "REAL_RAT5_LE_CONV_lets" fun _ => (do
  let lemma ← prove ([[!x y. x <= y * sqrt(&5) <=>
           x <= &0 /\ &0 <= y \/
           &0 <= x /\ &0 <= y /\ x pow 2 <= &5 * y pow 2 \/
           x <= &0 /\ y <= &0 /\ &5 * y pow 2 <= x pow 2]])
     (REPEAT GEN_TAC THEN MP_TAC (← HolLight.ISPEC ([[&5]]) SQRT_POW_2) THEN
      REWRITE_TAC [REAL_POS] THEN DISCH_THEN (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.ONCE_DEPTH_CONV) [(← HolLight.SYM th)])) THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_POW_MUL), (← HolLight.GSYM REAL_LE_SQUARE_ABS)] THEN
      MP_TAC (← HolLight.ISPECL [([[sqrt(&5)]]), ([[y:real]])] (← HolLight.CONJUNCT1 REAL_LE_MUL_EQ)) THEN
      SIMP_TAC [SQRT_POS_LT, REAL_OF_NUM_LT, ARITH] THEN REAL_ARITH_TAC2)
  let pth ← prove ([[(a1 + b1 * sqrt(&5)) <= (a2 + b2 * sqrt(&5)) <=>
        a1 <= a2 /\ b1 <= b2 \/
        a2 <= a1 /\ b1 <= b2 /\ (a1 - a2) pow 2 <= &5 * (b2 - b1) pow 2 \/
        a1 <= a2 /\ b2 <= b1 /\ &5 * (b2 - b1) pow 2 <= (a1 - a2) pow 2]])
     (REWRITE_TAC [(← rr (← ExceptT.mk [[a + b * x <= a' + b' * x <=> a - a' <= (b' - b) * x]]))] THEN
      REWRITE_TAC [lemma] THEN REAL_ARITH_TAC2)
  pure (lemma, pth)
  : ExceptT String IO (thm × thm)).run
def REAL_RAT5_LE_CONV : HolCore.Equal.ioconv := fun tm => (do
  let (_lemma, pth) := REAL_RAT5_LE_CONV_lets
  ExceptT.mk ((REAL_RAT_LE_CONV ORELSEC
    (HolLight.BINOP_CONV REAL_RAT5_OF_RAT_CONV THENC
     HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth] THENC
     REAL_RAT_REDUCE_CONV)) tm)
  : ExceptT String IO thm).run
#eval (do replay REAL_RAT5_LE_CONV_lets; IO.println "<fun>" : IO Unit)

#eval phrase 17
-- let REAL_RAT5_EQ_CONV = ...;;
def REAL_RAT5_EQ_CONV : HolCore.Equal.ioconv := fun tm => (do
  ExceptT.mk ((HolLight.GEN_REWRITE_CONV HolCore.Lib.I [(← HolLight.GSYM REAL_LE_ANTISYM)] THENC
    HolLight.BINOP_CONV REAL_RAT5_LE_CONV THENC
    HolLight.GEN_REWRITE_CONV HolCore.Lib.I [AND_CLAUSES]) tm)
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Conversions for operations on 3D vectors with coordinates in Q[sqrt(5)]   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 18
-- let VECTOR3_SUB_CONV = ...;;
def VECTOR3_SUB_CONV_lets : thm := keepIO "VECTOR3_SUB_CONV_lets" fun _ => (do
  let pth ← prove ([[vector[x1;x2;x3] - vector[y1;y2;y3]:real^3 =
     vector[x1-y1; x2-y2; x3-y3] ]])
     (SIMP_TAC [CART_EQ, DIMINDEX_3, FORALL_3] THEN
      REWRITE_TAC [VECTOR_3, VECTOR_SUB_COMPONENT])
  pure (pth)
  : ExceptT String IO (thm)).run
def VECTOR3_SUB_CONV : HolCore.Equal.ioconv := fun tm => (do
  let (pth) := VECTOR3_SUB_CONV_lets
  ExceptT.mk ((HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth] THENC HolLight.RAND_CONV (LIST_CONV_IO REAL_RAT5_SUB_CONV)) tm)
  : ExceptT String IO thm).run
#eval (do replay VECTOR3_SUB_CONV_lets; IO.println "<fun>" : IO Unit)

#eval phrase 19
-- let VECTOR3_CROSS_CONV = ...;;
def VECTOR3_CROSS_CONV_lets : thm := keepIO "VECTOR3_CROSS_CONV_lets" fun _ => (do
  let pth ← prove ([[(vector[x1;x2;x3]) cross (vector[y1;y2;y3]) =
     vector[x2 * y3 - x3 * y2; x3 * y1 - x1 * y3; x1 * y2 - x2 * y1] ]])
     (REWRITE_TAC [cross, VECTOR_3])
  pure (pth)
  : ExceptT String IO (thm)).run
def VECTOR3_CROSS_CONV : HolCore.Equal.ioconv := fun tm => (do
  let (pth) := VECTOR3_CROSS_CONV_lets
  ExceptT.mk ((HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth] THENC
    HolLight.RAND_CONV (LIST_CONV_IO (HolLight.BINOP_CONV REAL_RAT5_MUL_CONV THENC REAL_RAT5_SUB_CONV))) tm)
  : ExceptT String IO thm).run
#eval (do replay VECTOR3_CROSS_CONV_lets; IO.println "<fun>" : IO Unit)

#eval phrase 20
-- let VECTOR3_EQ_0_CONV = ...;;
def VECTOR3_EQ_0_CONV_lets : thm := keepIO "VECTOR3_EQ_0_CONV_lets" fun _ => (do
  let pth ← prove ([[vector[x1;x2;x3]:real^3 = vec 0 <=>
        x1 = &0 /\ x2 = &0 /\ x3 = &0]])
     (SIMP_TAC [CART_EQ, DIMINDEX_3, FORALL_3] THEN
      REWRITE_TAC [VECTOR_3, VEC_COMPONENT])
  pure (pth)
  : ExceptT String IO (thm)).run
def VECTOR3_EQ_0_CONV : HolCore.Equal.ioconv := fun tm => (do
  let (pth) := VECTOR3_EQ_0_CONV_lets
  ExceptT.mk ((HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth] THENC
    HolCore.Simp.depthBinopConvIO (← ExceptT.mk [[(/\)]]) REAL_RAT5_EQ_CONV THENC
    HolLight.REWRITE_CONV []) tm)
  : ExceptT String IO thm).run
#eval (do replay VECTOR3_EQ_0_CONV_lets; IO.println "<fun>" : IO Unit)

#eval phrase 21
-- let VECTOR3_DOT_CONV = ...;;
def VECTOR3_DOT_CONV_lets : thm := keepIO "VECTOR3_DOT_CONV_lets" fun _ => (do
  let pth ← prove ([[(vector[x1;x2;x3]:real^3) dot (vector[y1;y2;y3]) =
        x1*y1 + x2*y2 + x3*y3]])
     (REWRITE_TAC [DOT_3, VECTOR_3])
  pure (pth)
  : ExceptT String IO (thm)).run
def VECTOR3_DOT_CONV : HolCore.Equal.ioconv := fun tm => (do
  let (pth) := VECTOR3_DOT_CONV_lets
  ExceptT.mk ((HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth] THENC
    HolCore.Simp.depthBinopConvIO (← ExceptT.mk [[(+):real->real->real]]) REAL_RAT5_MUL_CONV THENC
    HolLight.RAND_CONV REAL_RAT5_ADD_CONV THENC
    REAL_RAT5_ADD_CONV) tm)
  : ExceptT String IO thm).run
#eval (do replay VECTOR3_DOT_CONV_lets; IO.println "<fun>" : IO Unit)

/- ------------------------------------------------------------------------- -/
/- Put any irrational coordinates in our standard form.                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 22
def STD_DODECAHEDRON : thm := keep "STD_DODECAHEDRON" fun _ => (do
  let golden_inverse ← prove ([[inv((&1 + sqrt(&5)) / &2) = -- &1 / &2 + &1 / &2 * sqrt(&5)]])
     (MP_TAC (← HolLight.ISPEC ([[&5]]) SQRT_POW_2) THEN CONV_TAC rf)
  let h2 ← rr (← ExceptT.mk [[--(a + b * sqrt(&5)) = --a + --b * sqrt(&5)]])
  let h1 ← rr (← ExceptT.mk [[(&1 + s) / &2 = &1 / &2 + &1 / &2 * s]])
  prove ([[std_dodecahedron =
   convex hull
    { vector[&1; &1; &1],
      vector[&1; &1; -- &1],
      vector[&1; -- &1; &1],
      vector[&1; -- &1; -- &1],
      vector[-- &1; &1; &1],
      vector[-- &1; &1; -- &1],
      vector[-- &1; -- &1; &1],
      vector[-- &1; -- &1; -- &1],
      vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)],
      vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)],
      vector[-- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0],
      vector[-- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0],
      vector[&1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0],
      vector[&1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0],
      vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)],
      vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)]}]])
   (REWRITE_TAC [std_dodecahedron] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC [golden_inverse] THEN
    REWRITE_TAC [h1] THEN
    REWRITE_TAC [h2] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval STD_DODECAHEDRON

#eval phrase 23
def STD_ICOSAHEDRON : thm := keep "STD_ICOSAHEDRON" fun _ => (do
  let h2 ← rr (← ExceptT.mk [[--(a + b * sqrt(&5)) = --a + --b * sqrt(&5)]])
  let h1 ← rr (← ExceptT.mk [[(&1 + s) / &2 = &1 / &2 + &1 / &2 * s]])
  prove ([[std_icosahedron =
   convex hull
    { vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)],
      vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)],
      vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0],
      vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0],
      vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0],
      vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0],
      vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1],
      vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1],
      vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1],
      vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1]}]])
   (REWRITE_TAC [std_icosahedron] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC [h1] THEN
    REWRITE_TAC [h2] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval STD_ICOSAHEDRON

/- ------------------------------------------------------------------------- -/
/- Explicit computation of facets.                                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 24
def COMPUTE_FACES_2 : thm := keep "COMPUTE_FACES_2" fun _ => (do
  let h26 ← sr (← ExceptT.mk [[{x,y,z} = {z,x,y}]])
  let h25 ← sr (← ExceptT.mk [[(!x. x IN s ==> P x) <=> s SUBSET {x | P x}]])
  let h24 ← sr (← ExceptT.mk [[(!x. x IN s ==> P x) <=> s SUBSET {x | P x}]])
  let h23 ← sr (← ExceptT.mk [[x IN s ==> s SUBSET t ==> x IN t]])
  let h22 ← sr (← ExceptT.mk [[(a:real^3) dot q > b <=> q IN {x | a dot x > b}]])
  let h21 ← sr (← ExceptT.mk [[x IN s ==> s SUBSET t ==> x IN t]])
  let h20 ← rr (← ExceptT.mk [[(&1 - u) * p = (&1 - u) * b /\ u * b < u * q
          ==> (&1 - u) * p + u * q > b]])
  let h19 ← rr (← ExceptT.mk [[x > y ==> ~(x = y)]])
  let h18 ← sr (← ExceptT.mk [[x IN s ==> s SUBSET t ==> x IN t]])
  let h17 ← sr (← ExceptT.mk [[(a:real^3) dot q < b <=> q IN {x | a dot x < b}]])
  let h16 ← sr (← ExceptT.mk [[x IN s ==> s SUBSET t ==> x IN t]])
  let h15 ← rr (← ExceptT.mk [[(&1 - u) * p = (&1 - u) * b /\ u * q < u * b
          ==> (&1 - u) * p + u * q < b]])
  let h14 ← rr (← ExceptT.mk [[x < y ==> ~(x = y)]])
  let h13 ← tt (← ExceptT.mk [[~p ==> p ==> q]])
  let h12 ← va (← ExceptT.mk [[(&1 - &0) % p + &0 % q:real^N = p]])
  let h11 ← sr (← ExceptT.mk [[s INTER t SUBSET (P hull (s INTER t)) /\
          s DIFF t SUBSET (P hull (s DIFF t))
          ==> s SUBSET (P hull (s INTER t)) UNION (P hull (s DIFF t))]])
  let h10 ← sr (← ExceptT.mk [[s SUBSET t ==> (s INTER u) SUBSET (t INTER u)]])
  let h9 ← sr (← ExceptT.mk [[s SUBSET t ==> s INTER t = s]])
  let h8 ← sr (← ExceptT.mk [[s = t ==> s SUBSET t]])
  let h7 ← sr (← ExceptT.mk [[s = t ==> s SUBSET t]])
  let h6 ← rr (← ExceptT.mk [[a < b ==> a = b ==> F]])
  let h5 ← sr (← ExceptT.mk [[f x <= b /\ ~(f x = b) <=>
                    x IN {x | f x <= b} /\ ~(x IN {x | f x = b})]])
  let h4 ← tt (← ExceptT.mk [[(~p /\ ~q ==> F) ==> p \/ q]])
  let h3 ← sr (← ExceptT.mk [[s SUBSET t ==> s INTER t = s]])
  let h2 ← sr (← ExceptT.mk [[{x,y,z} = {z,x,y}]])
  let h1 ← ia (← ExceptT.mk [[aff_dim(u:real^3->bool) = &2 /\ aff_dim u = &(CARD u) - &1
        ==> &(CARD u):int = &3]])
  prove ([[!f s:real^3->bool.
        FINITE s
        ==> (f face_of (convex hull s) /\ aff_dim f = &2 <=>
             ?x y z. x IN s /\ y IN s /\ z IN s /\
                     let a = (z - x) cross (y - x) in
                     ~(a = vec 0) /\
                     let b = a dot x in
                     ((!w. w IN s ==> a dot w <= b) \/
                      (!w. w IN s ==> a dot w >= b)) /\
                     f = convex hull (s INTER {x | a dot x = b}))]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN ([[?t:real^3->bool. t SUBSET s /\ f = convex hull t]]) MP_TAC THENL
       [MATCH_MP_TAC FACE_OF_CONVEX_HULL_SUBSET THEN
        ASM_SIMP_TAC [FINITE_IMP_COMPACT],
        DISCH_THEN (X_CHOOSE_THEN ([[t:real^3->bool]]) MP_TAC)] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [AFF_DIM_CONVEX_HULL]) THEN
      MP_TAC (← HolLight.ISPEC ([[t:real^3->bool]]) AFFINE_BASIS_EXISTS) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[u:real^3->bool]]) STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN ([[(u:real^3->bool) HAS_SIZE 3]]) MP_TAC THENL
       [ASM_SIMP_TAC [HAS_SIZE, AFFINE_INDEPENDENT_IMP_FINITE] THEN
        REWRITE_TAC [(← HolLight.GSYM INT_OF_NUM_EQ)] THEN MATCH_MP_TAC h1 THEN CONJ_TAC THENL [ASM_MESON_TAC [AFF_DIM_AFFINE_HULL], ASM_MESON_TAC [AFF_DIM_UNIQUE]],
        ALL_TAC] THEN
      CONV_TAC (HolLight.LAND_CONV HAS_SIZE_CONV) THEN SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[x:real^3]]), ([[y:real^3]]), ([[z:real^3]])] THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      MAP_EVERY EXISTS_TAC [([[x:real^3]]), ([[y:real^3]]), ([[z:real^3]])] THEN
      REPLICATE_TAC 3 (CONJ_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC]) THEN
      REPEAT LET_TAC THEN
      SUBGOAL_THEN ([[~collinear{x:real^3,y,z}]]) MP_TAC THENL
       [ASM_REWRITE_TAC [COLLINEAR_3_EQ_AFFINE_DEPENDENT], ALL_TAC] THEN
      ONCE_REWRITE_TAC [h2] THEN
      ONCE_REWRITE_TAC [COLLINEAR_3] THEN ASM_REWRITE_TAC [(← HolLight.GSYM CROSS_EQ_0)] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[(a:real^3) dot y = b /\ (a:real^3) dot z = b]]) STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [([[(z - x) cross (y - x) = a]]), ([[(a:real^3) dot x = b]])] THEN VEC3_TAC,
        ALL_TAC] THEN
      MP_TAC (← HolLight.ISPECL [([[convex hull s:real^3->bool]]), ([[convex hull t:real^3->bool]])] EXPOSED_FACE_OF_POLYHEDRON) THEN
      ASM_SIMP_TAC [POLYHEDRON_CONVEX_HULL, exposed_face_of] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[a':real^3]]), ([[b':real]])] THEN
      DISCH_THEN (STRIP_ASSUME_TAC o HolLight.GSYM) THEN
      SUBGOAL_THEN ([[aff_dim(t:real^3->bool)
      <= aff_dim({x:real^3 | a dot x = b} INTER {x | a' dot x = b'})]]) MP_TAC THENL
       [GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM AFF_DIM_AFFINE_HULL)] THEN
        FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [(← HolLight.SYM th)])) THEN
        REWRITE_TAC [AFF_DIM_AFFINE_HULL] THEN MATCH_MP_TAC AFF_DIM_SUBSET THEN
        REWRITE_TAC [SUBSET_INTER] THEN CONJ_TAC THENL
         [HolLight.ASM SET_TAC [],
          MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC ([[t:real^3->bool]]) THEN
          ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC ([[convex hull t:real^3->bool]]) THEN
          REWRITE_TAC [HULL_SUBSET] THEN HolLight.ASM SET_TAC []],
        ALL_TAC] THEN
      ASM_SIMP_TAC [AFF_DIM_AFFINE_INTER_HYPERPLANE, AFF_DIM_HYPERPLANE,
                   AFFINE_HYPERPLANE, DIMINDEX_3] THEN
      REPEAT (COND_CASES_TAC THEN CONV_TAC INT_REDUCE_CONV) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [SUBSET_HYPERPLANES]) THEN
      ASM_REWRITE_TAC [HYPERPLANE_EQ_EMPTY] THEN
      DISCH_THEN (DISJ_CASES_THEN2 SUBST_ALL_TAC (MP_TAC o HolLight.SYM)) THENL
       [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [INTER_UNIV]) THEN
        SUBGOAL_THEN ([[s SUBSET {x:real^3 | a dot x = b}]]) ASSUME_TAC THENL
         [MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC ([[convex hull s:real^3->bool]]) THEN
          REWRITE_TAC [HULL_SUBSET] THEN ASM_REWRITE_TAC [] THEN
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC ([[affine hull t:real^3->bool]]) THEN
          REWRITE_TAC [CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
          FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.SYM th)])) THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [AFFINE_HYPERPLANE] THEN
          HolLight.ASM SET_TAC [],
          ALL_TAC] THEN
        CONJ_TAC THENL
         [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [SUBSET, IN_ELIM_THM]) THEN
          ASM_SIMP_TAC [real_ge, REAL_LE_REFL],
          ASM_SIMP_TAC [h3]],
        ALL_TAC] THEN
      DISCH_THEN (fun th => SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC h4 THEN
        REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, real_ge, REAL_NOT_LE] THEN
        DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC ([[u:real^3]])) (X_CHOOSE_TAC ([[v:real^3]]))) THEN
        SUBGOAL_THEN ([[(a':real^3) dot u < b' /\ a' dot v < b']]) ASSUME_TAC THENL
         [REWRITE_TAC [REAL_LT_LE] THEN REWRITE_TAC [h5] THEN
          ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [IN_ELIM_THM, REAL_LT_IMP_NE] THEN
          SUBGOAL_THEN ([[(u:real^3) IN convex hull s /\ v IN convex hull s]]) MP_TAC THENL [ASM_SIMP_TAC [HULL_INC], HolLight.ASM SET_TAC []],
          ALL_TAC] THEN
        SUBGOAL_THEN ([[?w:real^3. w IN segment[u,v] /\ w IN {w | a' dot w = b'}]]) MP_TAC THENL
         [ASM_REWRITE_TAC [] THEN REWRITE_TAC [IN_ELIM_THM] THEN
          MATCH_MP_TAC CONNECTED_IVT_HYPERPLANE THEN
          MAP_EVERY EXISTS_TAC [([[v:real^3]]), ([[u:real^3]])] THEN
          ASM_SIMP_TAC [ENDS_IN_SEGMENT, CONNECTED_SEGMENT, REAL_LT_IMP_LE],
          REWRITE_TAC [IN_SEGMENT, IN_ELIM_THM, LEFT_AND_EXISTS_THM] THEN
          ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
          REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC), RIGHT_EXISTS_AND_THM] THEN
          REWRITE_TAC [UNWIND_THM2, DOT_RADD, DOT_RMUL, CONJ_ASSOC] THEN
          DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
          MATCH_MP_TAC h6 THEN
          MATCH_MP_TAC REAL_CONVEX_BOUND_LT THEN ASM_REAL_ARITH_TAC],
        MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC [SUBSET_INTER] THEN
          ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC ([[convex hull t:real^3->bool]]) THEN
          REWRITE_TAC [HULL_SUBSET] THEN HolLight.ASM SET_TAC [],
          FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.SYM th)])) THEN
          REWRITE_TAC [SUBSET_INTER] THEN
          SIMP_TAC [HULL_MONO, INTER_SUBSET] THEN
          ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC ([[convex hull {x:real^3 | a dot x = b}]]) THEN
          SIMP_TAC [HULL_MONO, INTER_SUBSET] THEN
          MATCH_MP_TAC h7 THEN
          REWRITE_TAC [CONVEX_HULL_EQ, CONVEX_HYPERPLANE]]],
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[x:real^3]]), ([[y:real^3]]), ([[z:real^3]])] THEN
      REPEAT LET_TAC THEN
      DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN ([[convex hull (s INTER {x:real^3 | a dot x = b}) =
        (convex hull s) INTER {x | a dot x = b}]]) SUBST1_TAC THENL
         [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
           [SIMP_TAC [SUBSET_INTER, HULL_MONO, INTER_SUBSET] THEN
            MATCH_MP_TAC SUBSET_TRANS THEN
            EXISTS_TAC ([[convex hull {x:real^3 | a dot x = b}]]) THEN
            SIMP_TAC [HULL_MONO, INTER_SUBSET] THEN
            MATCH_MP_TAC h8 THEN
            REWRITE_TAC [CONVEX_HULL_EQ, CONVEX_HYPERPLANE],
          ALL_TAC] THEN
        ASM_CASES_TAC ([[s SUBSET {x:real^3 | a dot x = b}]]) THENL
         [ASM_SIMP_TAC [h9] THEN SET_TAC [],
          ALL_TAC] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC ([[convex hull (convex hull (s INTER {x:real^3 | a dot x = b}) UNION
                     convex hull (s DIFF {x | a dot x = b})) INTER
        {x | a dot x = b}]]) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC h10 THEN
          MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC h11 THEN
          REWRITE_TAC [HULL_SUBSET],
          ALL_TAC] THEN
        HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
          let t ← ec (HolCore.Equal.lhand (← ec (HolCore.Equal.lhand w)))
          pure (MP_TAC (← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) CONVEX_HULL_UNION_NONEMPTY_EXPLICIT t)))) THEN
        ANTS_TAC THENL
         [SIMP_TAC [CONVEX_CONVEX_HULL, CONVEX_HULL_EQ_EMPTY] THEN HolLight.ASM SET_TAC [],
          DISCH_THEN SUBST1_TAC] THEN
        REWRITE_TAC [SUBSET, IN_INTER, IMP_CONJ, FORALL_IN_GSPEC] THEN
        MAP_EVERY X_GEN_TAC [([[p:real^3]]), ([[u:real]]), ([[q:real^3]])] THEN
        REPLICATE_TAC 4 DISCH_TAC THEN ASM_CASES_TAC ([[u = &0]]) THEN
        ASM_REWRITE_TAC [h12] THEN
        MATCH_MP_TAC h13 THEN REWRITE_TAC [IN_ELIM_THM] THEN
        REWRITE_TAC [DOT_RADD, DOT_RMUL] THEN FIRST_X_ASSUM DISJ_CASES_TAC THENL
         [MATCH_MP_TAC h14 THEN
          MATCH_MP_TAC h15 THEN
          CONJ_TAC THENL
           [SUBGOAL_THEN ([[p IN {x:real^3 | a dot x = b}]]) MP_TAC THENL
             [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h16) THEN
              MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_HYPERPLANE] THEN
              SET_TAC [],
              SIMP_TAC [IN_ELIM_THM]],
            MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
             [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
            ONCE_REWRITE_TAC [h17] THEN
            FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h18) THEN
            MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_HALFSPACE_LT] THEN
            ASM_SIMP_TAC [SUBSET, IN_DIFF, IN_ELIM_THM, REAL_LT_LE]],
          MATCH_MP_TAC h19 THEN
          MATCH_MP_TAC h20 THEN
          CONJ_TAC THENL
           [SUBGOAL_THEN ([[p IN {x:real^3 | a dot x = b}]]) MP_TAC THENL
             [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h21) THEN
              MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_HYPERPLANE] THEN
              SET_TAC [],
              SIMP_TAC [IN_ELIM_THM]],
            MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
             [ASM_REAL_ARITH_TAC, REWRITE_TAC [(← HolLight.GSYM real_gt)]] THEN
            ONCE_REWRITE_TAC [h22] THEN
            FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h23) THEN
            MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_HALFSPACE_GT] THEN
            RULE_ASSUM_TAC (HolLight.REWRITE_RULE [real_ge]) THEN
            ASM_SIMP_TAC [SUBSET, IN_DIFF, IN_ELIM_THM, real_gt, REAL_LT_LE]]],
          ALL_TAC] THEN
        FIRST_X_ASSUM DISJ_CASES_TAC THENL
         [MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
          REWRITE_TAC [CONVEX_CONVEX_HULL] THEN
          SIMP_TAC [h24] THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_HALFSPACE_LE] THEN
          ASM_SIMP_TAC [SUBSET, IN_ELIM_THM],
          MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE THEN
          REWRITE_TAC [CONVEX_CONVEX_HULL] THEN
          SIMP_TAC [h25] THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_HALFSPACE_GE] THEN
          ASM_SIMP_TAC [SUBSET, IN_ELIM_THM]],
        REWRITE_TAC [(← HolLight.GSYM INT_LE_ANTISYM)] THEN CONJ_TAC THENL
         [MATCH_MP_TAC INT_LE_TRANS THEN
          EXISTS_TAC ([[aff_dim {x:real^3 | a dot x = b}]]) THEN CONJ_TAC THENL
           [MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM_REWRITE_TAC [] THEN
            MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_HYPERPLANE] THEN
            SET_TAC [],
            ASM_SIMP_TAC [AFF_DIM_HYPERPLANE, DIMINDEX_3] THEN INT_ARITH_TAC],
          MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC ([[aff_dim {x:real^3,y,z}]]) THEN
          CONJ_TAC THENL
           [SUBGOAL_THEN ([[~collinear{x:real^3,y,z}]]) MP_TAC THENL
             [ONCE_REWRITE_TAC [h26] THEN
              ONCE_REWRITE_TAC [COLLINEAR_3] THEN
              ASM_REWRITE_TAC [(← HolLight.GSYM CROSS_EQ_0)],
              REWRITE_TAC [COLLINEAR_3_EQ_AFFINE_DEPENDENT, DE_MORGAN_THM] THEN
              STRIP_TAC] THEN
            ASM_SIMP_TAC [AFF_DIM_AFFINE_INDEPENDENT] THEN
            SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY] THEN
            ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, ARITH] THEN
            CONV_TAC INT_REDUCE_CONV,
            MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM_REWRITE_TAC [INSERT_SUBSET] THEN
            REWRITE_TAC [EMPTY_SUBSET] THEN REPEAT CONJ_TAC THEN
            MATCH_MP_TAC HULL_INC THEN
            ASM_REWRITE_TAC [IN_INTER, IN_ELIM_THM] THEN
            MAP_EVERY UNDISCH_TAC [([[(z - x) cross (y - x) = a]]), ([[(a:real^3) dot x = b]])] THEN
            VEC3_TAC]]]])
  : ExceptT String IO thm).run
#eval COMPUTE_FACES_2

#eval phrase 25
def COMPUTE_FACES_2_STEP_1 : thm := keep "COMPUTE_FACES_2_STEP_1" fun _ => (do
  let h2 ← v3r (← ExceptT.mk [[((z - x) cross (y - x)) dot y = ((z - x) cross (y - x)) dot x]])
  let v3b ← v3r (← ExceptT.mk [[(y - x) cross (z - x) =  --((z - x) cross (y - x))]])
  let v3a ← v3r (← ExceptT.mk [[(z - y) cross (x - y) = --((z - x) cross (y - x))]])
  let h1 ← ms [] (← ExceptT.mk [[(!x y z. Q x y z ==> Q x z y) /\
        (!x y z. Q x y z ==> Q y x z) /\
        (!x z. ~(Q x x z))
        ==> ((?x y z. (x = v \/ P x) /\ (y = v \/ P y) /\ (z = v \/ P z) /\
             Q x y z) <=>
            (?y z. P y /\ P z /\ Q v y z) \/
            (?x y z. P x /\ P y /\ P z /\ Q x y z))]])
  prove ([[!f v s t:real^3->bool.
       (?x y z. x IN (v INSERT s) /\ y IN (v INSERT s) /\ z IN (v INSERT s) /\
                let a = (z - x) cross (y - x) in
                ~(a = vec 0) /\
                let b = a dot x in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b})) <=>
       (?y z. y IN s /\ z IN s /\
                let a = (z - v) cross (y - v) in
                ~(a = vec 0) /\
                let b = a dot v in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b})) \/
       (?x y z. x IN s /\ y IN s /\ z IN s /\
                let a = (z - x) cross (y - x) in
                ~(a = vec 0) /\
                let b = a dot x in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b}))]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [IN_INSERT] THEN MATCH_MP_TAC h1 THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC [VECTOR_SUB_REFL, CROSS_0] THEN
    CONJ_TAC THEN REPEAT GEN_TAC THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV let_CONV) THEN
    MAP_EVERY SUBST1_TAC [v3a, v3b] THEN
    REWRITE_TAC [VECTOR_NEG_EQ_0, DOT_LNEG, REAL_EQ_NEG2, REAL_LE_NEG2,
                real_ge] THEN
    REWRITE_TAC [DISJ_ACI] THEN
    REWRITE_TAC [h2])
  : ExceptT String IO thm).run
#eval COMPUTE_FACES_2_STEP_1

#eval phrase 26
def COMPUTE_FACES_2_STEP_2 : thm := keep "COMPUTE_FACES_2_STEP_2" fun _ => (do
  let h2 ← v3r (← ExceptT.mk [[(x - v) cross (y - v) = --((y - v) cross (x - v))]])
  let h1 ← ms [] (← ExceptT.mk [[(!x y. Q x y ==> Q y x) /\
        (!x. ~(Q x x))
        ==> ((?y z. (y = u \/ P y) /\ (z = u \/ P z) /\
             Q y z) <=>
            (?z. P z /\ Q u z) \/
            (?y z. P y /\ P z /\ Q y z))]])
  prove ([[!f u v s:real^3->bool.
         (?y z. y IN (u INSERT s) /\ z IN (u INSERT s) /\
                let a = (z - v) cross (y - v) in
                ~(a = vec 0) /\
                let b = a dot v in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b})) <=>
         (?z. z IN s /\
              let a = (z - v) cross (u - v) in
              ~(a = vec 0) /\
              let b = a dot v in
              ((!w. w IN t ==> a dot w <= b) \/
               (!w. w IN t ==> a dot w >= b)) /\
              f = convex hull (t INTER {x | a dot x = b})) \/
         (?y z. y IN s /\ z IN s /\
                let a = (z - v) cross (y - v) in
                ~(a = vec 0) /\
                let b = a dot v in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b}))]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [IN_INSERT] THEN MATCH_MP_TAC h1 THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC [CROSS_REFL] THEN REPEAT GEN_TAC THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV let_CONV) THEN SUBST1_TAC h2 THEN
    REWRITE_TAC [VECTOR_NEG_EQ_0, DOT_LNEG, REAL_EQ_NEG2, REAL_LE_NEG2,
                real_ge] THEN REWRITE_TAC [DISJ_ACI])
  : ExceptT String IO thm).run
#eval COMPUTE_FACES_2_STEP_2

#eval phrase 27
-- let COMPUTE_FACES_TAC = ...;;
def COMPUTE_FACES_TAC_lets : thm := keepIO "COMPUTE_FACES_TAC_lets" fun _ => (do
  let lemma ← prove ([[(x INSERT s) INTER {x | P x} =
                        if P x then x INSERT (s INTER {x | P x})
                        else s INTER {x | P x}]])
     (COND_CASES_TAC THEN HolLight.ASM SET_TAC [])
  pure (lemma)
  : ExceptT String IO (thm)).run
def COMPUTE_FACES_TAC : HolCore.Tactics.tactic := HolLight.tactic_of do
  let (lemma) := COMPUTE_FACES_TAC_lets
  pure (SIMP_TAC [COMPUTE_FACES_2, FINITE_INSERT, FINITE_EMPTY] THEN
    REWRITE_TAC [COMPUTE_FACES_2_STEP_1] THEN
    REWRITE_TAC [COMPUTE_FACES_2_STEP_2] THEN
    REWRITE_TAC [NOT_IN_EMPTY] THEN
    REWRITE_TAC [EXISTS_IN_INSERT, NOT_IN_EMPTY] THEN
    REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV VECTOR3_CROSS_CONV) THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV let_CONV) THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV VECTOR3_EQ_0_CONV) THEN
    REWRITE_TAC [real_ge] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV VECTOR3_DOT_CONV) THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV let_CONV) THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV REAL_RAT5_LE_CONV) THEN
    REWRITE_TAC [INSERT_AC] THEN REWRITE_TAC [DISJ_ACI] THEN
    REPEAT (CHANGED_TAC (ONCE_REWRITE_TAC [lemma] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV (HolLight.LAND_CONV VECTOR3_DOT_CONV THENC REAL_RAT5_EQ_CONV))) THEN
      REWRITE_TAC []) THEN
    REWRITE_TAC [INTER_EMPTY] THEN
    REWRITE_TAC [INSERT_AC] THEN REWRITE_TAC [DISJ_ACI])
#eval (do replay COMPUTE_FACES_TAC_lets; IO.println "<fun>" : IO Unit)

/- ------------------------------------------------------------------------- -/
/- Apply this to our standard Platonic solids to derive facets.              -/
/- Note: this is quite slow and can take a couple of hours.                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 28
def TETRAHEDRON_FACETS : thm := keep "TETRAHEDRON_FACETS" fun _ => (do
  let g ← ExceptT.mk [[!f:real^3->bool.
        f face_of std_tetrahedron /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; -- &1], vector[&1; -- &1; -- &1]} \/
        f = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; -- &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[-- &1; -- &1; &1], vector[&1; -- &1; -- &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[-- &1; &1; -- &1], vector[&1; -- &1; -- &1], vector[&1; &1; &1]}]]
  let tac := GEN_TAC THEN REWRITE_TAC [std_tetrahedron] THEN COMPUTE_FACES_TAC
  ExceptT.mk (HolCore.Lib.time (fun _ => Session.prove g tac) ())
  : ExceptT String IO thm).run
#eval TETRAHEDRON_FACETS

#eval phrase 29
def CUBE_FACETS : thm := keep "CUBE_FACETS" fun _ => (do
  let g ← ExceptT.mk [[!f:real^3->bool.
        f face_of std_cube /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; -- &1; &1], vector[-- &1; &1; -- &1], vector[-- &1; &1; &1]} \/
        f = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; -- &1; &1], vector[&1; -- &1; -- &1], vector[&1; -- &1; &1]} \/
        f = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; &1; -- &1], vector[&1; -- &1; -- &1], vector[&1; &1; -- &1]} \/
        f = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; &1], vector[&1; -- &1; &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[-- &1; &1; -- &1], vector[-- &1; &1; &1], vector[&1; &1; -- &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[&1; -- &1; -- &1], vector[&1; -- &1; &1], vector[&1; &1; -- &1], vector[&1; &1; &1]}]]
  let tac := GEN_TAC THEN REWRITE_TAC [std_cube] THEN COMPUTE_FACES_TAC
  ExceptT.mk (HolCore.Lib.time (fun _ => Session.prove g tac) ())
  : ExceptT String IO thm).run
#eval CUBE_FACETS

#eval phrase 30
def OCTAHEDRON_FACETS : thm := keep "OCTAHEDRON_FACETS" fun _ => (do
  let g ← ExceptT.mk [[!f:real^3->bool.
        f face_of std_octahedron /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1; &0; &0], vector[&0; -- &1; &0], vector[&0; &0; -- &1]} \/
        f = convex hull {vector[-- &1; &0; &0], vector[&0; -- &1; &0], vector[&0; &0; &1]} \/
        f = convex hull {vector[-- &1; &0; &0], vector[&0; &1; &0], vector[&0; &0; -- &1]} \/
        f = convex hull {vector[-- &1; &0; &0], vector[&0; &1; &0], vector[&0; &0; &1]} \/
        f = convex hull {vector[&1; &0; &0], vector[&0; -- &1; &0], vector[&0; &0; -- &1]} \/
        f = convex hull {vector[&1; &0; &0], vector[&0; -- &1; &0], vector[&0; &0; &1]} \/
        f = convex hull {vector[&1; &0; &0], vector[&0; &1; &0], vector[&0; &0; -- &1]} \/
        f = convex hull {vector[&1; &0; &0], vector[&0; &1; &0], vector[&0; &0; &1]}]]
  let tac := GEN_TAC THEN REWRITE_TAC [std_octahedron] THEN COMPUTE_FACES_TAC
  ExceptT.mk (HolCore.Lib.time (fun _ => Session.prove g tac) ())
  : ExceptT String IO thm).run
#eval OCTAHEDRON_FACETS

#eval phrase 31
def ICOSAHEDRON_FACETS : thm := keep "ICOSAHEDRON_FACETS" fun _ => (do
  let g ← ExceptT.mk [[!f:real^3->bool.
        f face_of std_icosahedron /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]}]]
  let tac := GEN_TAC THEN REWRITE_TAC [STD_ICOSAHEDRON] THEN COMPUTE_FACES_TAC
  ExceptT.mk (HolCore.Lib.time (fun _ => Session.prove g tac) ())
  : ExceptT String IO thm).run
#eval ICOSAHEDRON_FACETS

#eval phrase 32
def DODECAHEDRON_FACETS : thm := keep "DODECAHEDRON_FACETS" fun _ => (do
  let g ← ExceptT.mk [[!f:real^3->bool.
        f face_of std_dodecahedron /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[-- &1; -- &1; -- &1], vector[-- &1; -- &1; &1]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[-- &1; &1; -- &1], vector[-- &1; &1; &1]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[-- &1; -- &1; &1], vector[-- &1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[-- &1; -- &1; -- &1], vector[-- &1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[-- &1; -- &1; -- &1], vector[&1; -- &1; -- &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[-- &1; -- &1; &1], vector[&1; -- &1; &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1; -- &1; -- &1], vector[&1; -- &1; &1]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[-- &1; &1; -- &1], vector[&1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[-- &1; &1; &1], vector[&1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1; &1; -- &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[&1; -- &1; &1], vector[&1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1; -- &1; -- &1], vector[&1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]}]]
  let tac := GEN_TAC THEN REWRITE_TAC [STD_DODECAHEDRON] THEN COMPUTE_FACES_TAC
  ExceptT.mk (HolCore.Lib.time (fun _ => Session.prove g tac) ())
  : ExceptT String IO thm).run
#eval DODECAHEDRON_FACETS

/- ------------------------------------------------------------------------- -/
/- Given a coplanar set, return a hyperplane containing it.                  -/
/- Maps term s to theorem |- !x. x IN s ==> n dot x = d                      -/
/- Currently assumes |s| >= 3 but it would be trivial to do other cases.     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 33
-- let COPLANAR_HYPERPLANE_RULE = ...;;
partial def allsets {α : Type} : Nat → List α → List (List α)
  | 0, _ => [List.nil]
  | _, [] => []
  | m + 1, h :: t => (allsets m t).map (fun g => h :: g) ++ allsets (m + 1) t
def COPLANAR_HYPERPLANE_RULE (tm : term) : IO (Except String thm) := (do
  let mk_bin (op : term) (a b : term) : ExceptT String IO term := do
    ec ((← ec (HolCore.Basics.mk_binop op a)) b)
  let sub_tm ← ExceptT.mk [[(-):real^3->real^3->real^3]]
  let cross_tm ← ExceptT.mk [[cross]]
  let dot_tm ← ExceptT.mk [[(dot):real^3->real^3->real]]
  let zerovec_tm ← ExceptT.mk [[vector[&0;&0;&0]:real^3]]
  let template ← ExceptT.mk [[(!x:real^3. x IN s ==> n dot x = d)]]
  let s_tm ← ExceptT.mk [[s:real^3->bool]]
  let n_tm ← ExceptT.mk [[n:real^3]]
  let d_tm ← ExceptT.mk [[d:real]]
  let check_normal (t : List term) : IO (Except String term) := (do
    let (x, y, z) ← match t with
      | [x, y, z] => pure (x, y, z) | _ => throw "Match_failure"
    let nt ← mk_bin cross_tm (← mk_bin sub_tm y x) (← mk_bin sub_tm z x)
    let th ← ExceptT.mk ((HolLight.BINOP_CONV VECTOR3_SUB_CONV THENC VECTOR3_CROSS_CONV) nt)
    let n ← ec (rand (concl th))
    if n == zerovec_tm then throw "check_normal" else pure n
    : ExceptT String IO term).run
  let s ← ec (dest_setenum tm)
  if s.length < 3 then throw "COPLANAR_HYPERPLANE_RULE: trivial"
  let n ← ExceptT.mk (HolCore.Lib.tryfindM check_normal (allsets 3 s))
  let d ← ec (rand (concl (← ExceptT.mk (VECTOR3_DOT_CONV (← mk_bin dot_tm n (← ec (HolCore.Lib.hd s)))))))
  let ptm ← pure ((← ec (HolCore.Kernel.vsubst [(tm, s_tm), (n, n_tm), (d, d_tm)])) template)
  HolLight.EQT_ELIM (← ExceptT.mk ((HolLight.REWRITE_CONV [FORALL_IN_INSERT, NOT_IN_EMPTY] THENC
      HolCore.Simp.depthBinopConvIO (← ExceptT.mk [[(/\)]])
       (HolLight.LAND_CONV VECTOR3_DOT_CONV THENC REAL_RAT5_EQ_CONV) THENC
      HolLight.GEN_REWRITE_CONV HolLight.DEPTH_CONV [AND_CLAUSES]) ptm))
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Explicit computation of edges, assuming hyperplane containing the set.    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 34
def COMPUTE_FACES_1 : thm := keep "COMPUTE_FACES_1" fun _ => (do
  let h27 ← sr (← ExceptT.mk [[(!x. x IN s ==> P x) <=> s SUBSET {x | P x}]])
  let h26 ← sr (← ExceptT.mk [[(!x. x IN s ==> P x) <=> s SUBSET {x | P x}]])
  let h25 ← sr (← ExceptT.mk [[x IN s ==> s SUBSET t ==> x IN t]])
  let h24 ← sr (← ExceptT.mk [[(a:real^3) dot q > b <=> q IN {x | a dot x > b}]])
  let h23 ← sr (← ExceptT.mk [[x IN s ==> s SUBSET t ==> x IN t]])
  let h22 ← rr (← ExceptT.mk [[(&1 - u) * p = (&1 - u) * b /\ u * b < u * q
          ==> (&1 - u) * p + u * q > b]])
  let h21 ← rr (← ExceptT.mk [[x > y ==> ~(x = y)]])
  let h20 ← sr (← ExceptT.mk [[x IN s ==> s SUBSET t ==> x IN t]])
  let h19 ← sr (← ExceptT.mk [[(a:real^3) dot q < b <=> q IN {x | a dot x < b}]])
  let h18 ← sr (← ExceptT.mk [[x IN s ==> s SUBSET t ==> x IN t]])
  let h17 ← rr (← ExceptT.mk [[(&1 - u) * p = (&1 - u) * b /\ u * q < u * b
          ==> (&1 - u) * p + u * q < b]])
  let h16 ← rr (← ExceptT.mk [[x < y ==> ~(x = y)]])
  let h15 ← tt (← ExceptT.mk [[~p ==> p ==> q]])
  let h14 ← va (← ExceptT.mk [[(&1 - &0) % p + &0 % q:real^N = p]])
  let h13 ← sr (← ExceptT.mk [[s INTER t SUBSET (P hull (s INTER t)) /\
          s DIFF t SUBSET (P hull (s DIFF t))
          ==> s SUBSET (P hull (s INTER t)) UNION (P hull (s DIFF t))]])
  let h12 ← sr (← ExceptT.mk [[s SUBSET t ==> (s INTER u) SUBSET (t INTER u)]])
  let h11 ← sr (← ExceptT.mk [[s SUBSET t ==> s INTER t = s]])
  let h10 ← sr (← ExceptT.mk [[s = t ==> s SUBSET t]])
  let h9 ← sr (← ExceptT.mk [[s = t ==> s SUBSET t]])
  let h8 ← rr (← ExceptT.mk [[a < b ==> a = b ==> F]])
  let h7 ← sr (← ExceptT.mk [[f x <= b /\ ~(f x = b) <=>
                    x IN {x | f x <= b} /\ ~(x IN {x | f x = b})]])
  let h6 ← tt (← ExceptT.mk [[(~p /\ ~q ==> F) ==> p \/ q]])
  let h5 ← rr (← ExceptT.mk [[x:real = d /\ y = d ==> x = y]])
  let h4 ← tt (← ExceptT.mk [[p /\ q /\ ~r ==> (p /\ q ==> r) ==> s]])
  let h3 ← sr (← ExceptT.mk [[s INTER t SUBSET u ==> !x. x IN s /\ x IN t ==> x IN u]])
  let h2 ← sr (← ExceptT.mk [[s = s INTER t <=> s SUBSET t]])
  let h1 ← ia (← ExceptT.mk [[aff_dim(u:real^3->bool) = &1 /\ aff_dim u = &(CARD u) - &1
        ==> &(CARD u):int = &2]])
  prove ([[!s:real^3->bool n d.
        (!x. x IN s ==> n dot x = d)
        ==> FINITE s /\ ~(n = vec 0)
            ==> !f. f face_of (convex hull s) /\ aff_dim f = &1 <=>
                    ?x y. x IN s /\ y IN s /\
                          let a = n cross (y - x) in
                          ~(a = vec 0) /\
                          let b = a dot x in
                          ((!w. w IN s ==> a dot w <= b) \/
                           (!w. w IN s ==> a dot w >= b)) /\
                          f = convex hull (s INTER {x | a dot x = b})]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN ([[?t:real^3->bool. t SUBSET s /\ f = convex hull t]]) MP_TAC THENL
       [MATCH_MP_TAC FACE_OF_CONVEX_HULL_SUBSET THEN
        ASM_SIMP_TAC [FINITE_IMP_COMPACT],
        DISCH_THEN (X_CHOOSE_THEN ([[t:real^3->bool]]) MP_TAC)] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [AFF_DIM_CONVEX_HULL]) THEN
      MP_TAC (← HolLight.ISPEC ([[t:real^3->bool]]) AFFINE_BASIS_EXISTS) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[u:real^3->bool]]) STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN ([[(u:real^3->bool) HAS_SIZE 2]]) MP_TAC THENL
       [ASM_SIMP_TAC [HAS_SIZE, AFFINE_INDEPENDENT_IMP_FINITE] THEN
        REWRITE_TAC [(← HolLight.GSYM INT_OF_NUM_EQ)] THEN MATCH_MP_TAC h1 THEN CONJ_TAC THENL [ASM_MESON_TAC [AFF_DIM_AFFINE_HULL], ASM_MESON_TAC [AFF_DIM_UNIQUE]],
        ALL_TAC] THEN
      CONV_TAC (HolLight.LAND_CONV HAS_SIZE_CONV) THEN SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[x:real^3]]), ([[y:real^3]])] THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
      MAP_EVERY EXISTS_TAC [([[x:real^3]]), ([[y:real^3]])] THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [HolLight.ASM SET_TAC [], ALL_TAC]) THEN
      SUBGOAL_THEN ([[(x:real^3) IN s /\ y IN s]]) STRIP_ASSUME_TAC THENL
       [HolLight.ASM SET_TAC [], ALL_TAC] THEN
      REPEAT LET_TAC THEN
      MP_TAC (← HolLight.ISPECL [([[n:real^3]]), ([[y - x:real^3]])] NORM_AND_CROSS_EQ_0) THEN
      ASM_SIMP_TAC [DOT_RSUB, VECTOR_SUB_EQ, REAL_SUB_0] THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[(a:real^3) dot y = b]]) ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [([[n cross (y - x) = a]]), ([[(a:real^3) dot x = b]])] THEN VEC3_TAC,
        ALL_TAC] THEN
      MP_TAC (← HolLight.ISPECL [([[convex hull s:real^3->bool]]), ([[convex hull t:real^3->bool]])] EXPOSED_FACE_OF_POLYHEDRON) THEN
      ASM_SIMP_TAC [POLYHEDRON_CONVEX_HULL, EXPOSED_FACE_OF_PARALLEL] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[a':real^3]]), ([[b':real]])] THEN
      SUBGOAL_THEN ([[~(convex hull t:real^3->bool = {})]]) ASSUME_TAC THENL
       [REWRITE_TAC [(← HolLight.GSYM MEMBER_NOT_EMPTY)] THEN EXISTS_TAC ([[x:real^3]]) THEN
        MATCH_MP_TAC HULL_INC THEN HolLight.ASM SET_TAC [],
        ASM_REWRITE_TAC []] THEN
      ASM_CASES_TAC ([[convex hull t:real^3->bool = convex hull s]]) THEN
      ASM_REWRITE_TAC [] THENL
       [FIRST_X_ASSUM (ASSUME_TAC o HolLight.GEN_REWRITE_RULE HolLight.RAND_CONV [(← HolLight.GSYM AFFINE_HULL_CONVEX_HULL)]) THEN
        UNDISCH_THEN ([[convex hull t:real^3->bool = convex hull s]]) (fun th => SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
        RULE_ASSUM_TAC (HolLight.REWRITE_RULE [AFFINE_HULL_CONVEX_HULL]) THEN
        REWRITE_TAC [h2] THEN STRIP_TAC THEN
        SUBGOAL_THEN ([[s SUBSET {x:real^3 | a dot x = b}]]) ASSUME_TAC THENL
         [MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC ([[affine hull s:real^3->bool]]) THEN
          REWRITE_TAC [HULL_SUBSET] THEN
          FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.SYM th)])) THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [AFFINE_HYPERPLANE] THEN
          HolLight.ASM SET_TAC [],
          CONJ_TAC THENL
           [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [SUBSET, IN_ELIM_THM]) THEN
            ASM_SIMP_TAC [real_ge, REAL_LE_REFL],
            AP_TERM_TAC THEN HolLight.ASM SET_TAC []]],
        STRIP_TAC] THEN
      RULE_ASSUM_TAC (HolLight.REWRITE_RULE [AFFINE_HULL_CONVEX_HULL]) THEN
      SUBGOAL_THEN ([[aff_dim(t:real^3->bool)
      <= aff_dim(({x:real^3 | a dot x = b} INTER {x:real^3 | a' dot x = b'})
                 INTER {x | n dot x = d})]]) MP_TAC THENL
       [GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM AFF_DIM_AFFINE_HULL)] THEN
        FIRST_X_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [(← HolLight.SYM th)])) THEN
        REWRITE_TAC [AFF_DIM_AFFINE_HULL] THEN MATCH_MP_TAC AFF_DIM_SUBSET THEN
        REWRITE_TAC [SUBSET_INTER, INSERT_SUBSET, EMPTY_SUBSET, IN_ELIM_THM] THEN
        ASM_SIMP_TAC [] THEN
        SUBGOAL_THEN ([[(x:real^3) IN convex hull t /\ y IN convex hull t]]) MP_TAC THENL
         [CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN HolLight.ASM SET_TAC [],
          HolLight.ASM SET_TAC []],
        ALL_TAC] THEN
      ASM_SIMP_TAC [AFF_DIM_AFFINE_INTER_HYPERPLANE, AFF_DIM_HYPERPLANE,
                   AFFINE_HYPERPLANE, DIMINDEX_3, AFFINE_INTER] THEN
      ASM_CASES_TAC ([[{x:real^3 | a dot x = b} SUBSET {v | a' dot v = b'}]]) THEN
      ASM_REWRITE_TAC [] THENL
       [ALL_TAC,
        REPEAT (COND_CASES_TAC THEN CONV_TAC INT_REDUCE_CONV) THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP h3) THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[x + n:real^3]])) THEN
        MATCH_MP_TAC h4 THEN
        ASM_SIMP_TAC [IN_ELIM_THM, DOT_RADD] THEN REPEAT CONJ_TAC THENL
         [EXPAND_TAC "a" THEN VEC3_TAC,
          ALL_TAC,
          ASM_REWRITE_TAC [REAL_EQ_ADD_LCANCEL_0, DOT_EQ_0]] THEN
        SUBGOAL_THEN ([[a' dot (x:real^3) = b']]) SUBST1_TAC THENL
         [SUBGOAL_THEN ([[(x:real^3) IN convex hull t]]) MP_TAC THENL
           [MATCH_MP_TAC HULL_INC THEN HolLight.ASM SET_TAC [], HolLight.ASM SET_TAC []],
          ALL_TAC] THEN
        SUBGOAL_THEN ([[(n:real^3) dot (x + a') = n dot x]]) MP_TAC THENL
         [ALL_TAC,
          SIMP_TAC [DOT_RADD] THEN REWRITE_TAC [DOT_SYM] THEN REAL_ARITH_TAC2] THEN
        MATCH_MP_TAC h5 THEN
        SUBGOAL_THEN ([[affine hull s SUBSET {x:real^3 | n dot x = d}]]) MP_TAC THENL
         [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [AFFINE_HYPERPLANE] THEN
          ASM_SIMP_TAC [SUBSET, IN_ELIM_THM],
          REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_SIMP_TAC [HULL_INC]]] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [SUBSET_HYPERPLANES]) THEN
      ASM_REWRITE_TAC [HYPERPLANE_EQ_EMPTY, HYPERPLANE_EQ_UNIV] THEN
      DISCH_THEN (fun th => HolLight.tactic_of do
        pure (DISCH_THEN ((fun _ => ALL_TAC)) THEN MP_TAC (← HolLight.SYM th))) THEN
      DISCH_THEN (fun th => SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC h6 THEN
        REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, real_ge, REAL_NOT_LE] THEN
        DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC ([[u:real^3]])) (X_CHOOSE_TAC ([[v:real^3]]))) THEN
        SUBGOAL_THEN ([[(a':real^3) dot u < b' /\ a' dot v < b']]) ASSUME_TAC THENL
         [REWRITE_TAC [REAL_LT_LE] THEN REWRITE_TAC [h7] THEN
          ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [IN_ELIM_THM, REAL_LT_IMP_NE] THEN
          SUBGOAL_THEN ([[(u:real^3) IN convex hull s /\ v IN convex hull s]]) MP_TAC THENL [ASM_SIMP_TAC [HULL_INC], HolLight.ASM SET_TAC []],
          ALL_TAC] THEN
        SUBGOAL_THEN ([[?w:real^3. w IN segment[u,v] /\ w IN {w | a' dot w = b'}]]) MP_TAC THENL
         [ASM_REWRITE_TAC [] THEN REWRITE_TAC [IN_ELIM_THM] THEN
          MATCH_MP_TAC CONNECTED_IVT_HYPERPLANE THEN
          MAP_EVERY EXISTS_TAC [([[v:real^3]]), ([[u:real^3]])] THEN
          ASM_SIMP_TAC [ENDS_IN_SEGMENT, CONNECTED_SEGMENT, REAL_LT_IMP_LE],
          REWRITE_TAC [IN_SEGMENT, IN_ELIM_THM, LEFT_AND_EXISTS_THM] THEN
          ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
          REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC), RIGHT_EXISTS_AND_THM] THEN
          REWRITE_TAC [UNWIND_THM2, DOT_RADD, DOT_RMUL, CONJ_ASSOC] THEN
          DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
          MATCH_MP_TAC h8 THEN
          MATCH_MP_TAC REAL_CONVEX_BOUND_LT THEN ASM_REAL_ARITH_TAC],
        FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.SYM th)])) THEN
        MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC [SUBSET_INTER] THEN
          ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC ([[convex hull t:real^3->bool]]) THEN
          REWRITE_TAC [HULL_SUBSET] THEN HolLight.ASM SET_TAC [],
          ASM_REWRITE_TAC [SUBSET_INTER] THEN
          SIMP_TAC [HULL_MONO, INTER_SUBSET] THEN
          ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC ([[convex hull {x:real^3 | a dot x = b}]]) THEN
          SIMP_TAC [HULL_MONO, INTER_SUBSET] THEN
          MATCH_MP_TAC h9 THEN
          REWRITE_TAC [CONVEX_HULL_EQ, CONVEX_HYPERPLANE]]],
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [([[x:real^3]]), ([[y:real^3]])] THEN
      REPEAT LET_TAC THEN
      DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN ([[convex hull (s INTER {x:real^3 | a dot x = b}) =
        (convex hull s) INTER {x | a dot x = b}]]) SUBST1_TAC THENL
         [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
           [SIMP_TAC [SUBSET_INTER, HULL_MONO, INTER_SUBSET] THEN
            MATCH_MP_TAC SUBSET_TRANS THEN
            EXISTS_TAC ([[convex hull {x:real^3 | a dot x = b}]]) THEN
            SIMP_TAC [HULL_MONO, INTER_SUBSET] THEN
            MATCH_MP_TAC h10 THEN
            REWRITE_TAC [CONVEX_HULL_EQ, CONVEX_HYPERPLANE],
            ALL_TAC] THEN
        ASM_CASES_TAC ([[s SUBSET {x:real^3 | a dot x = b}]]) THENL
         [ASM_SIMP_TAC [h11] THEN SET_TAC [],
          ALL_TAC] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC ([[convex hull (convex hull (s INTER {x:real^3 | a dot x = b}) UNION
                     convex hull (s DIFF {x | a dot x = b})) INTER
        {x | a dot x = b}]]) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC h12 THEN
          MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC h13 THEN
          REWRITE_TAC [HULL_SUBSET],
          ALL_TAC] THEN
        HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
          let t ← ec (HolCore.Equal.lhand (← ec (HolCore.Equal.lhand w)))
          pure (MP_TAC (← ExceptT.mk (HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) CONVEX_HULL_UNION_NONEMPTY_EXPLICIT t)))) THEN
        ANTS_TAC THENL
         [SIMP_TAC [CONVEX_CONVEX_HULL, CONVEX_HULL_EQ_EMPTY] THEN HolLight.ASM SET_TAC [],
          DISCH_THEN SUBST1_TAC] THEN
        REWRITE_TAC [SUBSET, IN_INTER, IMP_CONJ, FORALL_IN_GSPEC] THEN
        MAP_EVERY X_GEN_TAC [([[p:real^3]]), ([[u:real]]), ([[q:real^3]])] THEN
        REPLICATE_TAC 4 DISCH_TAC THEN ASM_CASES_TAC ([[u = &0]]) THEN
        ASM_REWRITE_TAC [h14] THEN
        MATCH_MP_TAC h15 THEN REWRITE_TAC [IN_ELIM_THM] THEN
        REWRITE_TAC [DOT_RADD, DOT_RMUL] THEN FIRST_X_ASSUM DISJ_CASES_TAC THENL
         [MATCH_MP_TAC h16 THEN
          MATCH_MP_TAC h17 THEN
          CONJ_TAC THENL
           [SUBGOAL_THEN ([[p IN {x:real^3 | a dot x = b}]]) MP_TAC THENL
             [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h18) THEN
              MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_HYPERPLANE] THEN
              SET_TAC [],
              SIMP_TAC [IN_ELIM_THM]],
            MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
             [ASM_REAL_ARITH_TAC, ALL_TAC] THEN
            ONCE_REWRITE_TAC [h19] THEN
            FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h20) THEN
            MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_HALFSPACE_LT] THEN
            ASM_SIMP_TAC [SUBSET, IN_DIFF, IN_ELIM_THM, REAL_LT_LE]],
          MATCH_MP_TAC h21 THEN
          MATCH_MP_TAC h22 THEN
          CONJ_TAC THENL
           [SUBGOAL_THEN ([[p IN {x:real^3 | a dot x = b}]]) MP_TAC THENL
             [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h23) THEN
              MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_HYPERPLANE] THEN
              SET_TAC [],
              SIMP_TAC [IN_ELIM_THM]],
            MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
             [ASM_REAL_ARITH_TAC, REWRITE_TAC [(← HolLight.GSYM real_gt)]] THEN
            ONCE_REWRITE_TAC [h24] THEN
            FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h25) THEN
            MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_HALFSPACE_GT] THEN
            RULE_ASSUM_TAC (HolLight.REWRITE_RULE [real_ge]) THEN
            ASM_SIMP_TAC [SUBSET, IN_DIFF, IN_ELIM_THM, real_gt, REAL_LT_LE]]],
          ALL_TAC] THEN
        FIRST_X_ASSUM DISJ_CASES_TAC THENL
         [MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
          REWRITE_TAC [CONVEX_CONVEX_HULL] THEN
          SIMP_TAC [h26] THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_HALFSPACE_LE] THEN
          ASM_SIMP_TAC [SUBSET, IN_ELIM_THM],
          MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE THEN
          REWRITE_TAC [CONVEX_CONVEX_HULL] THEN
          SIMP_TAC [h27] THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [CONVEX_HALFSPACE_GE] THEN
          ASM_SIMP_TAC [SUBSET, IN_ELIM_THM]],
        ASM_REWRITE_TAC [(← HolLight.GSYM INT_LE_ANTISYM)] THEN CONJ_TAC THENL
         [ALL_TAC,
          MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC ([[aff_dim{x:real^3,y}]]) THEN
          CONJ_TAC THENL
           [ASM_REWRITE_TAC [AFF_DIM_2] THEN
            ASM_MESON_TAC [CROSS_0, VECTOR_SUB_REFL, INT_LE_REFL],
            MATCH_MP_TAC AFF_DIM_SUBSET THEN
            REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET] THEN
            CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN
            ASM_REWRITE_TAC [IN_INTER, IN_ELIM_THM] THEN
            MAP_EVERY UNDISCH_TAC [([[n cross (y - x) = a]]), ([[(a:real^3) dot x = b]])] THEN
            VEC3_TAC]] THEN
        REWRITE_TAC [AFF_DIM_CONVEX_HULL] THEN MATCH_MP_TAC INT_LE_TRANS THEN
        EXISTS_TAC ([[aff_dim({x:real^3 | a dot x = b} INTER {x | n dot x = d})]]) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC AFF_DIM_SUBSET THEN HolLight.ASM SET_TAC [], ALL_TAC] THEN
        ASM_SIMP_TAC [AFF_DIM_AFFINE_INTER_HYPERPLANE, AFFINE_HYPERPLANE,
                     AFF_DIM_HYPERPLANE, DIMINDEX_3] THEN
        REPEAT (COND_CASES_TAC THEN CONV_TAC INT_REDUCE_CONV) THEN
        FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[x + n:real^3]]) o
          HolLight.GEN_REWRITE_RULE HolCore.Lib.I [SUBSET]) THEN
        ASM_SIMP_TAC [IN_ELIM_THM, DOT_RADD, REAL_EQ_ADD_LCANCEL_0, DOT_EQ_0] THEN
        EXPAND_TAC "a" THEN VEC3_TAC]])
  : ExceptT String IO thm).run
#eval COMPUTE_FACES_1

/- ------------------------------------------------------------------------- -/
/- Given a coplanar set, return exhaustive edge case theorem.                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 35
-- let COMPUTE_EDGES_CONV = ...;;
def COMPUTE_EDGES_CONV_lemma : thm := keep "COMPUTE_EDGES_CONV_lemma" fun _ => (do
  prove ([[(x INSERT s) INTER {x | P x} =
                        if P x then x INSERT (s INTER {x | P x})
                        else s INTER {x | P x}]])
   (COND_CASES_TAC THEN HolLight.ASM SET_TAC [])
  : ExceptT String IO thm).run
def COMPUTE_EDGES_CONV (tm : term) : IO (Except String thm) := (do
  let lemma := COMPUTE_EDGES_CONV_lemma
  let th1 ← HolLight.MATCH_MP COMPUTE_FACES_1 (← ExceptT.mk (COPLANAR_HYPERPLANE_RULE tm))
  let th2 ← HolLight.MP (← HolLight.CONV_RULE (HolLight.LAND_CONV
     (HolLight.COMB2_CONV (HolLight.RAND_CONV (HolLight.PURE_REWRITE_CONV [FINITE_INSERT, FINITE_EMPTY]))
                 (HolLight.RAND_CONV VECTOR3_EQ_0_CONV THENC
                  HolLight.GEN_REWRITE_CONV HolCore.Lib.I [NOT_CLAUSES]) THENC
      HolLight.GEN_REWRITE_CONV HolCore.Lib.I [AND_CLAUSES])) th1) TRUTH
  HolLight.CONV_RULE
     (HolLight.BINDER_CONV (HolLight.RAND_CONV
        (HolLight.REWRITE_CONV [RIGHT_EXISTS_AND_THM] THENC
         HolLight.REWRITE_CONV [EXISTS_IN_INSERT, NOT_IN_EMPTY] THENC
         HolLight.REWRITE_CONV [FORALL_IN_INSERT, NOT_IN_EMPTY] THENC
         HolLight.ONCE_DEPTH_CONV VECTOR3_SUB_CONV THENC
         HolLight.ONCE_DEPTH_CONV VECTOR3_CROSS_CONV THENC
         HolLight.ONCE_DEPTH_CONV let_CONV THENC
         HolLight.ONCE_DEPTH_CONV VECTOR3_EQ_0_CONV THENC
         HolLight.REWRITE_CONV [real_ge] THENC
         HolLight.ONCE_DEPTH_CONV VECTOR3_DOT_CONV THENC
         HolLight.ONCE_DEPTH_CONV let_CONV THENC
         HolLight.ONCE_DEPTH_CONV REAL_RAT5_LE_CONV THENC
         HolLight.REWRITE_CONV [INSERT_AC] THENC HolLight.REWRITE_CONV [DISJ_ACI] THENC
         HolLight.REPEATC (HolLight.CHANGED_CONV
          (HolLight.ONCE_REWRITE_CONV [lemma] THENC
           HolLight.ONCE_DEPTH_CONV (HolLight.LAND_CONV VECTOR3_DOT_CONV THENC
                           REAL_RAT5_EQ_CONV) THENC
           HolLight.REWRITE_CONV [])) THENC
         HolLight.REWRITE_CONV [INTER_EMPTY] THENC
         HolLight.REWRITE_CONV [INSERT_AC] THENC HolLight.REWRITE_CONV [DISJ_ACI]))) th2
  : ExceptT String IO thm).run
#eval (do replay COMPUTE_EDGES_CONV_lemma; IO.println "<fun>" : IO Unit)

/- ------------------------------------------------------------------------- -/
/- Use this to prove the number of edges per face for each Platonic solid.   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 36
def CARD_EQ_LEMMA : thm := keep "CARD_EQ_LEMMA" fun _ => (do
  prove ([[!x s n. 0 < n /\ ~(x IN s) /\ s HAS_SIZE (n - 1)
           ==> (x INSERT s) HAS_SIZE n]])
   (REWRITE_TAC [HAS_SIZE] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [CARD_CLAUSES, FINITE_INSERT] THEN ASM_ARITH_TAC)
  : ExceptT String IO thm).run
#eval CARD_EQ_LEMMA

#eval phrase 37
-- let EDGES_PER_FACE_TAC = ...;;
def EDGES_PER_FACE_TAC (th : thm) : HolCore.Tactics.tactic :=
  HolLight.tactic_of do
  let h4 ← sr (← ExceptT.mk [[~(a = c /\ b = d) /\ ~(a = d /\ b = c) /\ ~(a = b /\ c = d)
       ==> ~({a,b} = {c,d})]])
  let h3 ← ms [HAS_SIZE] (← ExceptT.mk [[s HAS_SIZE n ==> CARD s = n]])
  let h2 ← sr (← ExceptT.mk [[{x | x IN s} = s]])
  let h1 ← sr (← ExceptT.mk [[x = a \/ x = b <=> x IN {a,b}]])
  pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[CARD  {e:real^3->bool | e face_of f /\ aff_dim(e) = &1}]]) THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
      REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_MESON_TAC [FACE_OF_FACE, FACE_OF_TRANS, FACE_OF_IMP_SUBSET],
      ALL_TAC] THEN
    MP_TAC (← HolLight.ISPEC ([[f:real^3->bool]]) th) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        pure (REWRITE_TAC [COMPUTE_EDGES_CONV (← ec (HolCore.Basics.find_term is_setenum w))])) THEN
    REWRITE_TAC [h1] THEN
    REWRITE_TAC [(← HolLight.GSYM IN_INSERT), h2] THEN
    REWRITE_TAC [(← HolLight.GSYM SEGMENT_CONVEX_HULL)] THEN MATCH_MP_TAC h3 THEN
    REPEAT (MATCH_MP_TAC CARD_EQ_LEMMA THEN REPEAT CONJ_TAC THENL
      [CONV_TAC NUM_REDUCE_CONV THEN HolCore.Tactics.NO_TAC,
       REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, SEGMENT_EQ, DE_MORGAN_THM] THEN
       REPEAT CONJ_TAC THEN MATCH_MP_TAC h4 THEN
       PURE_ONCE_REWRITE_TAC [(← HolLight.GSYM VECTOR_SUB_EQ)] THEN
       CONV_TAC (HolLight.ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
       CONV_TAC (HolLight.ONCE_DEPTH_CONV VECTOR3_EQ_0_CONV) THEN
       REWRITE_TAC [] THEN HolCore.Tactics.NO_TAC,
       ALL_TAC]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [(← HolLight.CONJUNCT1 HAS_SIZE_CLAUSES)])
#eval IO.println "<fun>"

#eval phrase 38
def TETRAHEDRON_EDGES_PER_FACE : thm := keep "TETRAHEDRON_EDGES_PER_FACE" fun _ => (do
  prove ([[!f. f face_of std_tetrahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_tetrahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 3]])
   (EDGES_PER_FACE_TAC TETRAHEDRON_FACETS)
  : ExceptT String IO thm).run
#eval TETRAHEDRON_EDGES_PER_FACE

#eval phrase 39
def CUBE_EDGES_PER_FACE : thm := keep "CUBE_EDGES_PER_FACE" fun _ => (do
  prove ([[!f. f face_of std_cube /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_cube /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 4]])
   (EDGES_PER_FACE_TAC CUBE_FACETS)
  : ExceptT String IO thm).run
#eval CUBE_EDGES_PER_FACE

#eval phrase 40
def OCTAHEDRON_EDGES_PER_FACE : thm := keep "OCTAHEDRON_EDGES_PER_FACE" fun _ => (do
  prove ([[!f. f face_of std_octahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_octahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 3]])
   (EDGES_PER_FACE_TAC OCTAHEDRON_FACETS)
  : ExceptT String IO thm).run
#eval OCTAHEDRON_EDGES_PER_FACE

#eval phrase 41
def DODECAHEDRON_EDGES_PER_FACE : thm := keep "DODECAHEDRON_EDGES_PER_FACE" fun _ => (do
  prove ([[!f. f face_of std_dodecahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_dodecahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 5]])
   (EDGES_PER_FACE_TAC DODECAHEDRON_FACETS)
  : ExceptT String IO thm).run
#eval DODECAHEDRON_EDGES_PER_FACE

#eval phrase 42
def ICOSAHEDRON_EDGES_PER_FACE : thm := keep "ICOSAHEDRON_EDGES_PER_FACE" fun _ => (do
  prove ([[!f. f face_of std_icosahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_icosahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 3]])
   (EDGES_PER_FACE_TAC ICOSAHEDRON_FACETS)
  : ExceptT String IO thm).run
#eval ICOSAHEDRON_EDGES_PER_FACE

/- ------------------------------------------------------------------------- -/
/- Show that the Platonic solids are all full-dimensional.                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 43
def POLYTOPE_3D_LEMMA : thm := keep "POLYTOPE_3D_LEMMA" fun _ => (do
  let h1 ← sr (← ExceptT.mk [[x IN s ==> s SUBSET t ==> x IN t]])
  prove ([[(let a = (z - x) cross (y - x) in
    ~(a = vec 0) /\ ?w. w IN s /\ ~(a dot w = a dot x))
   ==> aff_dim(convex hull (x INSERT y INSERT z INSERT s:real^3->bool)) = &3]])
   (REPEAT GEN_TAC THEN LET_TAC THEN STRIP_TAC THEN
    REWRITE_TAC [(← HolLight.GSYM INT_LE_ANTISYM)] THEN CONJ_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM DIMINDEX_3), AFF_DIM_LE_UNIV], ALL_TAC] THEN
    REWRITE_TAC [AFF_DIM_CONVEX_HULL] THEN MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC ([[aff_dim {w:real^3,x,y,z}]]) THEN CONJ_TAC THENL
     [ALL_TAC, MATCH_MP_TAC AFF_DIM_SUBSET THEN HolLight.ASM SET_TAC []] THEN
    ONCE_REWRITE_TAC [AFF_DIM_INSERT] THEN COND_CASES_TAC THENL
     [SUBGOAL_THEN ([[w IN {w:real^3 | a dot w = a dot x}]]) MP_TAC THENL
       [FIRST_X_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h1) THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC [AFFINE_HYPERPLANE] THEN
        REWRITE_TAC [INSERT_SUBSET, EMPTY_SUBSET, IN_ELIM_THM] THEN
        UNDISCH_TAC ([[~(a:real^3 = vec 0)]]) THEN EXPAND_TAC "a" THEN VEC3_TAC,
        ASM_REWRITE_TAC [IN_ELIM_THM]],
      UNDISCH_TAC ([[~(a:real^3 = vec 0)]]) THEN EXPAND_TAC "a" THEN
      REWRITE_TAC [CROSS_EQ_0, (← HolLight.GSYM COLLINEAR_3)] THEN
      REWRITE_TAC [COLLINEAR_3_EQ_AFFINE_DEPENDENT, INSERT_AC, DE_MORGAN_THM] THEN
      STRIP_TAC THEN ASM_SIMP_TAC [AFF_DIM_AFFINE_INDEPENDENT] THEN
      SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY] THEN
      ASM_REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, ARITH] THEN INT_ARITH_TAC])
  : ExceptT String IO thm).run
#eval POLYTOPE_3D_LEMMA

#eval phrase 44
-- let POLYTOPE_FULLDIM_TAC = ...;;
def POLYTOPE_FULLDIM_TAC : HolCore.Tactics.tactic :=
  MATCH_MP_TAC POLYTOPE_3D_LEMMA THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV VECTOR3_CROSS_CONV) THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV let_CONV) THEN CONJ_TAC THENL
     [CONV_TAC (HolLight.RAND_CONV VECTOR3_EQ_0_CONV) THEN REWRITE_TAC [],
      CONV_TAC (HolLight.ONCE_DEPTH_CONV VECTOR3_DOT_CONV) THEN
      REWRITE_TAC [EXISTS_IN_INSERT, NOT_IN_EMPTY] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV VECTOR3_DOT_CONV) THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV REAL_RAT5_EQ_CONV) THEN
      REWRITE_TAC []]
#eval IO.println "<fun>"

#eval phrase 45
def STD_TETRAHEDRON_FULLDIM : thm := keep "STD_TETRAHEDRON_FULLDIM" fun _ => (do
  prove ([[aff_dim std_tetrahedron = &3]])
   (REWRITE_TAC [std_tetrahedron] THEN POLYTOPE_FULLDIM_TAC)
  : ExceptT String IO thm).run
#eval STD_TETRAHEDRON_FULLDIM

#eval phrase 46
def STD_CUBE_FULLDIM : thm := keep "STD_CUBE_FULLDIM" fun _ => (do
  prove ([[aff_dim std_cube = &3]])
   (REWRITE_TAC [std_cube] THEN POLYTOPE_FULLDIM_TAC)
  : ExceptT String IO thm).run
#eval STD_CUBE_FULLDIM

#eval phrase 47
def STD_OCTAHEDRON_FULLDIM : thm := keep "STD_OCTAHEDRON_FULLDIM" fun _ => (do
  prove ([[aff_dim std_octahedron = &3]])
   (REWRITE_TAC [std_octahedron] THEN POLYTOPE_FULLDIM_TAC)
  : ExceptT String IO thm).run
#eval STD_OCTAHEDRON_FULLDIM

#eval phrase 48
def STD_DODECAHEDRON_FULLDIM : thm := keep "STD_DODECAHEDRON_FULLDIM" fun _ => (do
  prove ([[aff_dim std_dodecahedron = &3]])
   (REWRITE_TAC [STD_DODECAHEDRON] THEN POLYTOPE_FULLDIM_TAC)
  : ExceptT String IO thm).run
#eval STD_DODECAHEDRON_FULLDIM

#eval phrase 49
def STD_ICOSAHEDRON_FULLDIM : thm := keep "STD_ICOSAHEDRON_FULLDIM" fun _ => (do
  prove ([[aff_dim std_icosahedron = &3]])
   (REWRITE_TAC [STD_ICOSAHEDRON] THEN POLYTOPE_FULLDIM_TAC)
  : ExceptT String IO thm).run
#eval STD_ICOSAHEDRON_FULLDIM

/- ------------------------------------------------------------------------- -/
/- Complete list of edges for each Platonic solid.                           -/
/- ------------------------------------------------------------------------- -/

#eval phrase 50
-- let COMPUTE_EDGES_TAC = ...;;
def COMPUTE_EDGES_TAC (defn : thm) (fulldim : thm) (facets : thm) : HolCore.Tactics.tactic :=
  HolLight.tactic_of do
  let h1 ← tt (← ExceptT.mk [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]])
  pure (GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (((← ec (HolCore.Kernel.vsubst [((← ec (HolCore.Equal.lhs (concl defn))), (← ExceptT.mk [[p:real^3->bool]]))])) (← ExceptT.mk [[?f:real^3->bool. (f face_of p /\ aff_dim f = &2) /\
                        (e face_of f /\ aff_dim e = &1)]]))) THEN
    CONJ_TAC THENL
     [EQ_TAC THENL [STRIP_TAC, MESON_TAC [FACE_OF_TRANS]] THEN
      MP_TAC (← HolLight.ISPECL [(← ec (HolCore.Equal.lhs (concl defn))), ([[e:real^3->bool]])] FACE_OF_POLYHEDRON_SUBSET_FACET) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
         [REWRITE_TAC [defn] THEN
          MATCH_MP_TAC POLYHEDRON_CONVEX_HULL THEN
          REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY],
          CONJ_TAC THEN
          DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[aff_dim:(real^3->bool)->int]])) THEN
          ASM_REWRITE_TAC [fulldim, AFF_DIM_EMPTY] THEN
          CONV_TAC INT_REDUCE_CONV],
        MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC [facet_of] THEN
        REWRITE_TAC [fulldim] THEN CONV_TAC INT_REDUCE_CONV THEN
        ASM_MESON_TAC [FACE_OF_FACE]],
      REWRITE_TAC [facets] THEN
      REWRITE_TAC [h1] THEN
      REWRITE_TAC [EXISTS_OR_THM, UNWIND_THM2] THEN
      CONV_TAC (HolLight.LAND_CONV (HolCore.Simp.depthBinopConvIO (← ExceptT.mk [[\/]]) (fun tm => (do
        ExceptT.mk (HolLight.REWR_CONV (← ExceptT.mk (COMPUTE_EDGES_CONV (← ec (HolCore.Kernel.rand (← ec (HolCore.Kernel.rand (← ec (HolCore.Equal.lhand tm)))))))) tm)
        : ExceptT String IO thm).run))) THEN
      REWRITE_TAC [INSERT_AC] THEN REWRITE_TAC [DISJ_ACI]])
#eval IO.println "<fun>"

#eval phrase 51
def TETRAHEDRON_EDGES : thm := keep "TETRAHEDRON_EDGES" fun _ => (do
  prove ([[!e. e face_of std_tetrahedron /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[&1; &1; &1]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1; -- &1; -- &1], vector[&1; &1; &1]}]])
   (COMPUTE_EDGES_TAC std_tetrahedron STD_TETRAHEDRON_FULLDIM TETRAHEDRON_FACETS)
  : ExceptT String IO thm).run
#eval TETRAHEDRON_EDGES

#eval phrase 52
def CUBE_EDGES : thm := keep "CUBE_EDGES" fun _ => (do
  prove ([[!e. e face_of std_cube /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; -- &1; &1]} \/
       e = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; -- &1], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; &1]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[&1; -- &1; &1]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[-- &1; &1; &1]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[&1; &1; -- &1]} \/
       e = convex hull {vector[-- &1; &1; &1], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1; -- &1; -- &1], vector[&1; -- &1; &1]} \/
       e = convex hull {vector[&1; -- &1; -- &1], vector[&1; &1; -- &1]} \/
       e = convex hull {vector[&1; -- &1; &1], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1; &1; -- &1], vector[&1; &1; &1]}]])
   (COMPUTE_EDGES_TAC std_cube STD_CUBE_FULLDIM CUBE_FACETS)
  : ExceptT String IO thm).run
#eval CUBE_EDGES

#eval phrase 53
def OCTAHEDRON_EDGES : thm := keep "OCTAHEDRON_EDGES" fun _ => (do
  prove ([[!e. e face_of std_octahedron /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1; &0; &0], vector[&0; -- &1; &0]} \/
       e = convex hull {vector[-- &1; &0; &0], vector[&0; &1; &0]} \/
       e = convex hull {vector[-- &1; &0; &0], vector[&0; &0; -- &1]} \/
       e = convex hull {vector[-- &1; &0; &0], vector[&0; &0; &1]} \/
       e = convex hull {vector[&1; &0; &0], vector[&0; -- &1; &0]} \/
       e = convex hull {vector[&1; &0; &0], vector[&0; &1; &0]} \/
       e = convex hull {vector[&1; &0; &0], vector[&0; &0; -- &1]} \/
       e = convex hull {vector[&1; &0; &0], vector[&0; &0; &1]} \/
       e = convex hull {vector[&0; -- &1; &0], vector[&0; &0; -- &1]} \/
       e = convex hull {vector[&0; -- &1; &0], vector[&0; &0; &1]} \/
       e = convex hull {vector[&0; &1; &0], vector[&0; &0; -- &1]} \/
       e = convex hull {vector[&0; &1; &0], vector[&0; &0; &1]}]])
   (COMPUTE_EDGES_TAC std_octahedron STD_OCTAHEDRON_FULLDIM OCTAHEDRON_FACETS)
  : ExceptT String IO thm).run
#eval OCTAHEDRON_EDGES

#eval phrase 54
def DODECAHEDRON_EDGES : thm := keep "DODECAHEDRON_EDGES" fun _ => (do
  prove ([[!e. e face_of std_dodecahedron /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[-- &1; -- &1; &1]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[-- &1; &1; &1]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[-- &1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[-- &1; &1; -- &1]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1; -- &1; &1]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1; &1; -- &1]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[-- &1; -- &1; -- &1]} \/
       e = convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[-- &1; -- &1; &1]} \/
       e = convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[-- &1; &1; -- &1]} \/
       e = convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[-- &1; &1; &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[&1; -- &1; &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&1; &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; -- &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; -- &1; -- &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; -- &1; &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]}]])
   (COMPUTE_EDGES_TAC STD_DODECAHEDRON STD_DODECAHEDRON_FULLDIM DODECAHEDRON_FACETS)
  : ExceptT String IO thm).run
#eval DODECAHEDRON_EDGES

#eval phrase 55
def ICOSAHEDRON_EDGES : thm := keep "ICOSAHEDRON_EDGES" fun _ => (do
  prove ([[!e. e face_of std_icosahedron /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]}]])
   (COMPUTE_EDGES_TAC STD_ICOSAHEDRON STD_ICOSAHEDRON_FULLDIM ICOSAHEDRON_FACETS)
  : ExceptT String IO thm).run
#eval ICOSAHEDRON_EDGES

/- ------------------------------------------------------------------------- -/
/- Enumerate all the vertices.                                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 56
-- let COMPUTE_VERTICES_TAC = ...;;
def COMPUTE_VERTICES_TAC (defn : thm) (fulldim : thm) (edges : thm) : HolCore.Tactics.tactic :=
  HolLight.tactic_of do
  let h3 ← tt (← ExceptT.mk [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]])
  let h2 ← ms [] (← ExceptT.mk [[v face_of s /\ v = {a} <=> {a} face_of s /\ v = {a}]])
  let h1 ← tt (← ExceptT.mk [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]])
  pure (GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (((← ec (HolCore.Kernel.vsubst [((← ec (HolCore.Equal.lhs (concl defn))), (← ExceptT.mk [[p:real^3->bool]]))])) (← ExceptT.mk [[?e:real^3->bool. (e face_of p /\ aff_dim e = &1) /\
                        (v face_of e /\ aff_dim v = &0)]]))) THEN
    CONJ_TAC THENL
     [EQ_TAC THENL [STRIP_TAC, MESON_TAC [FACE_OF_TRANS]] THEN
      MP_TAC (← HolLight.ISPECL [(← ec (HolCore.Equal.lhs (concl defn))), ([[v:real^3->bool]])] FACE_OF_POLYHEDRON_SUBSET_FACET) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
         [REWRITE_TAC [defn] THEN
          MATCH_MP_TAC POLYHEDRON_CONVEX_HULL THEN
          REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY],
          CONJ_TAC THEN
          DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[aff_dim:(real^3->bool)->int]])) THEN
          ASM_REWRITE_TAC [fulldim, AFF_DIM_EMPTY] THEN
          CONV_TAC INT_REDUCE_CONV],
        REWRITE_TAC [facet_of] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[f:real^3->bool]]) STRIP_ASSUME_TAC)] THEN
      MP_TAC (← HolLight.ISPECL [([[f:real^3->bool]]), ([[v:real^3->bool]])] FACE_OF_POLYHEDRON_SUBSET_FACET) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC FACE_OF_POLYHEDRON_POLYHEDRON THEN
          FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (EXISTS_TAC (← ec (HolCore.Kernel.rand (concl th))) THEN
            CONJ_TAC THENL [ALL_TAC, ACCEPT_TAC th])) THEN
          REWRITE_TAC [defn] THEN
          MATCH_MP_TAC POLYHEDRON_CONVEX_HULL THEN
          REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY],
          ASM_MESON_TAC [FACE_OF_FACE],
          DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[aff_dim:(real^3->bool)->int]])) THEN
          ASM_REWRITE_TAC [fulldim, AFF_DIM_EMPTY] THEN
          CONV_TAC INT_REDUCE_CONV,
          DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[aff_dim:(real^3->bool)->int]])) THEN
          ASM_REWRITE_TAC [fulldim, AFF_DIM_EMPTY] THEN
          CONV_TAC INT_REDUCE_CONV],
        MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC [facet_of] THEN
        ASM_REWRITE_TAC [fulldim] THEN CONV_TAC INT_REDUCE_CONV THEN
        ASM_MESON_TAC [FACE_OF_FACE, FACE_OF_TRANS]],
      REWRITE_TAC [edges] THEN
      REWRITE_TAC [h1] THEN
      REWRITE_TAC [EXISTS_OR_THM, UNWIND_THM2] THEN
      REWRITE_TAC [AFF_DIM_EQ_0, RIGHT_AND_EXISTS_THM] THEN
      ONCE_REWRITE_TAC [h2] THEN
      REWRITE_TAC [(← HolLight.GSYM SEGMENT_CONVEX_HULL), FACE_OF_SING] THEN
      REWRITE_TAC [EXTREME_POINT_OF_SEGMENT] THEN
      REWRITE_TAC [h3] THEN
      REWRITE_TAC [EXISTS_OR_THM, UNWIND_THM2] THEN
      REWRITE_TAC [DISJ_ACI]])
#eval IO.println "<fun>"

#eval phrase 57
def TETRAHEDRON_VERTICES : thm := keep "TETRAHEDRON_VERTICES" fun _ => (do
  prove ([[!v. v face_of std_tetrahedron /\ aff_dim v = &0 <=>
       v = {vector [-- &1; -- &1; &1]} \/
       v = {vector [-- &1; &1; -- &1]} \/
       v = {vector [&1; -- &1; -- &1]} \/
       v = {vector [&1; &1; &1]}]])
   (COMPUTE_VERTICES_TAC std_tetrahedron STD_TETRAHEDRON_FULLDIM TETRAHEDRON_EDGES)
  : ExceptT String IO thm).run
#eval TETRAHEDRON_VERTICES

#eval phrase 58
def CUBE_VERTICES : thm := keep "CUBE_VERTICES" fun _ => (do
  prove ([[!v. v face_of std_cube /\ aff_dim v = &0 <=>
       v = {vector [-- &1; -- &1; -- &1]} \/
       v = {vector [-- &1; -- &1; &1]} \/
       v = {vector [-- &1; &1; -- &1]} \/
       v = {vector [-- &1; &1; &1]} \/
       v = {vector [&1; -- &1; -- &1]} \/
       v = {vector [&1; -- &1; &1]} \/
       v = {vector [&1; &1; -- &1]} \/
       v = {vector [&1; &1; &1]}]])
   (COMPUTE_VERTICES_TAC std_cube STD_CUBE_FULLDIM CUBE_EDGES)
  : ExceptT String IO thm).run
#eval CUBE_VERTICES

#eval phrase 59
def OCTAHEDRON_VERTICES : thm := keep "OCTAHEDRON_VERTICES" fun _ => (do
  prove ([[!v. v face_of std_octahedron /\ aff_dim v = &0 <=>
       v = {vector [-- &1; &0; &0]} \/
       v = {vector [&1; &0; &0]} \/
       v = {vector [&0; -- &1; &0]} \/
       v = {vector [&0; &1; &0]} \/
       v = {vector [&0; &0; -- &1]} \/
       v = {vector [&0; &0; &1]}]])
   (COMPUTE_VERTICES_TAC std_octahedron STD_OCTAHEDRON_FULLDIM OCTAHEDRON_EDGES)
  : ExceptT String IO thm).run
#eval OCTAHEDRON_VERTICES

#eval phrase 60
def DODECAHEDRON_VERTICES : thm := keep "DODECAHEDRON_VERTICES" fun _ => (do
  prove ([[!v. v face_of std_dodecahedron /\ aff_dim v = &0 <=>
       v = {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       v = {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       v = {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       v = {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       v = {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       v = {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       v = {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector[-- &1; -- &1; -- &1]} \/
       v = {vector[-- &1; -- &1; &1]} \/
       v = {vector[-- &1; &1; -- &1]} \/
       v = {vector[-- &1; &1; &1]} \/
       v = {vector[&1; -- &1; -- &1]} \/
       v = {vector[&1; -- &1; &1]} \/
       v = {vector[&1; &1; -- &1]} \/
       v = {vector[&1; &1; &1]} \/
       v = {vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       v = {vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]}]])
   (COMPUTE_VERTICES_TAC STD_DODECAHEDRON STD_DODECAHEDRON_FULLDIM DODECAHEDRON_EDGES)
  : ExceptT String IO thm).run
#eval DODECAHEDRON_VERTICES

#eval phrase 61
def ICOSAHEDRON_VERTICES : thm := keep "ICOSAHEDRON_VERTICES" fun _ => (do
  prove ([[!v. v face_of std_icosahedron /\ aff_dim v = &0 <=>
       v = {vector [-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1]} \/
       v = {vector [-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1]} \/
       v = {vector [&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1]} \/
       v = {vector [&1 / &2 + &1 / &2 * sqrt (&5); &0; &1]} \/
       v = {vector [-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       v = {vector [-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       v = {vector [&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       v = {vector [&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       v = {vector [&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector [&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       v = {vector [&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector [&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]}]])
   (COMPUTE_VERTICES_TAC STD_ICOSAHEDRON STD_ICOSAHEDRON_FULLDIM ICOSAHEDRON_EDGES)
  : ExceptT String IO thm).run
#eval ICOSAHEDRON_VERTICES

/- ------------------------------------------------------------------------- -/
/- Number of edges meeting at each vertex.                                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 62
-- let EDGES_PER_VERTEX_TAC = ...;;
def EDGES_PER_VERTEX_TAC (defn : thm) (edges : thm) (verts : thm) : HolCore.Tactics.tactic :=
  HolLight.tactic_of do
  let h6 ← sr (← ExceptT.mk [[~(a = c /\ b = d) /\ ~(a = d /\ b = c) /\ ~(a = b /\ c = d)
       ==> ~({a,b} = {c,d})]])
  let h5 ← ms [HAS_SIZE] (← ExceptT.mk [[s HAS_SIZE n ==> CARD s = n]])
  let h4 ← sr (← ExceptT.mk [[{x} UNION s = x INSERT s]])
  let h3 ← sr (← ExceptT.mk [[{x | x = a} = {a}]])
  let h2 ← ms [FACE_OF_SING] (← ExceptT.mk [[e = a /\ {x} face_of e <=> e = a /\ x extreme_point_of a]])
  let h1 ← sr (← ExceptT.mk [[{e | (P e \/ Q e) /\ R e} =
    {e | P e /\ R e} UNION {e | Q e /\ R e}]])
  pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (((← ec (HolCore.Kernel.vsubst [((← ec (HolCore.Equal.lhs (concl defn))), (← ExceptT.mk [[p:real^3->bool]]))])) (← ExceptT.mk [[CARD {e | (e face_of p /\ aff_dim(e) = &1) /\
                (v:real^3->bool) face_of e}]]))) THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
      ASM_MESON_TAC [FACE_OF_FACE],
      ALL_TAC] THEN
    MP_TAC (← HolLight.ISPEC ([[v:real^3->bool]]) verts) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC [edges] THEN
    REWRITE_TAC [h1] THEN
    REWRITE_TAC [h2] THEN
    REWRITE_TAC [(← HolLight.GSYM SEGMENT_CONVEX_HULL), EXTREME_POINT_OF_SEGMENT] THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM VECTOR_SUB_EQ)] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV VECTOR3_EQ_0_CONV) THEN
    REWRITE_TAC [EMPTY_GSPEC, UNION_EMPTY] THEN
    REWRITE_TAC [h3] THEN
    REWRITE_TAC [h4] THEN MATCH_MP_TAC h5 THEN
    REPEAT (MATCH_MP_TAC CARD_EQ_LEMMA THEN REPEAT CONJ_TAC THENL
      [CONV_TAC NUM_REDUCE_CONV THEN HolCore.Tactics.NO_TAC,
       REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY, DE_MORGAN_THM, SEGMENT_EQ] THEN
       REPEAT CONJ_TAC THEN MATCH_MP_TAC h6 THEN
       PURE_ONCE_REWRITE_TAC [(← HolLight.GSYM VECTOR_SUB_EQ)] THEN
       CONV_TAC (HolLight.ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
       CONV_TAC (HolLight.ONCE_DEPTH_CONV VECTOR3_EQ_0_CONV) THEN
       REWRITE_TAC [] THEN HolCore.Tactics.NO_TAC,
       ALL_TAC]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [(← HolLight.CONJUNCT1 HAS_SIZE_CLAUSES)])
#eval IO.println "<fun>"

#eval phrase 63
def TETRAHEDRON_EDGES_PER_VERTEX : thm := keep "TETRAHEDRON_EDGES_PER_VERTEX" fun _ => (do
  prove ([[!v. v face_of std_tetrahedron /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_tetrahedron /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 3]])
   (EDGES_PER_VERTEX_TAC std_tetrahedron TETRAHEDRON_EDGES TETRAHEDRON_VERTICES)
  : ExceptT String IO thm).run
#eval TETRAHEDRON_EDGES_PER_VERTEX

#eval phrase 64
def CUBE_EDGES_PER_VERTEX : thm := keep "CUBE_EDGES_PER_VERTEX" fun _ => (do
  prove ([[!v. v face_of std_cube /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_cube /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 3]])
   (EDGES_PER_VERTEX_TAC std_cube CUBE_EDGES CUBE_VERTICES)
  : ExceptT String IO thm).run
#eval CUBE_EDGES_PER_VERTEX

#eval phrase 65
def OCTAHEDRON_EDGES_PER_VERTEX : thm := keep "OCTAHEDRON_EDGES_PER_VERTEX" fun _ => (do
  prove ([[!v. v face_of std_octahedron /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_octahedron /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 4]])
   (EDGES_PER_VERTEX_TAC std_octahedron OCTAHEDRON_EDGES OCTAHEDRON_VERTICES)
  : ExceptT String IO thm).run
#eval OCTAHEDRON_EDGES_PER_VERTEX

#eval phrase 66
def DODECAHEDRON_EDGES_PER_VERTEX : thm := keep "DODECAHEDRON_EDGES_PER_VERTEX" fun _ => (do
  prove ([[!v. v face_of std_dodecahedron /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_dodecahedron /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 3]])
   (EDGES_PER_VERTEX_TAC STD_DODECAHEDRON DODECAHEDRON_EDGES DODECAHEDRON_VERTICES)
  : ExceptT String IO thm).run
#eval DODECAHEDRON_EDGES_PER_VERTEX

#eval phrase 67
def ICOSAHEDRON_EDGES_PER_VERTEX : thm := keep "ICOSAHEDRON_EDGES_PER_VERTEX" fun _ => (do
  prove ([[!v. v face_of std_icosahedron /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_icosahedron /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 5]])
   (EDGES_PER_VERTEX_TAC STD_ICOSAHEDRON ICOSAHEDRON_EDGES ICOSAHEDRON_VERTICES)
  : ExceptT String IO thm).run
#eval ICOSAHEDRON_EDGES_PER_VERTEX

/- ------------------------------------------------------------------------- -/
/- Number of Platonic solids.                                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 68
def MULTIPLE_COUNTING_LEMMA : thm := keep "MULTIPLE_COUNTING_LEMMA" fun _ => (do
  prove ([[!R:A->B->bool s t.
        FINITE s /\ FINITE t /\
        (!x. x IN s ==> CARD {y | y IN t /\ R x y} = m) /\
        (!y. y IN t ==> CARD {x | x IN s /\ R x y} = n)
        ==> m * CARD s = n * CARD t]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[R:A->B->bool]]), ([[\x:A y:B. 1]]), ([[s:A->bool]]), ([[t:B->bool]])] NSUM_NSUM_RESTRICT) THEN
    ASM_SIMP_TAC [NSUM_CONST, FINITE_RESTRICT] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval MULTIPLE_COUNTING_LEMMA

#eval phrase 69
def SIZE_ZERO_DIMENSIONAL_FACES : thm := keep "SIZE_ZERO_DIMENSIONAL_FACES" fun _ => (do
  prove ([[!s:real^N->bool.
        polyhedron s
        ==> CARD {f | f face_of s /\ aff_dim f = &0} =
            CARD {v | v extreme_point_of s} /\
            (FINITE {f | f face_of s /\ aff_dim f = &0} <=>
             FINITE {v | v extreme_point_of s}) /\
            (!n. {f | f face_of s /\ aff_dim f = &0} HAS_SIZE n <=>
                 {v | v extreme_point_of s} HAS_SIZE n)]])
   (REWRITE_TAC [RIGHT_AND_FORALL_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[{f | f face_of s /\ aff_dim f = &0} =
                IMAGE (\v:real^N. {v}) {v | v extreme_point_of s}]]) SUBST1_TAC THENL
     [CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
      REWRITE_TAC [AFF_DIM_SING, FACE_OF_SING, IN_ELIM_THM] THEN
      REWRITE_TAC [AFF_DIM_EQ_0] THEN MESON_TAC [],
      REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC CARD_IMAGE_INJ,
        MATCH_MP_TAC FINITE_IMAGE_INJ_EQ,
        MATCH_MP_TAC HAS_SIZE_IMAGE_INJ_EQ] THEN
      ASM_SIMP_TAC [FINITE_POLYHEDRON_EXTREME_POINTS] THEN SET_TAC []])
  : ExceptT String IO thm).run
#eval SIZE_ZERO_DIMENSIONAL_FACES

#eval phrase 70
def PLATONIC_SOLIDS_LIMITS : thm := keep "PLATONIC_SOLIDS_LIMITS" fun _ => (do
  let h22 ← ar (← ExceptT.mk [[3 <= m ==> (m <= 5 <=> m = 3 \/ m = 4 \/ m = 5)]])
  let h21 ← ar (← ExceptT.mk [[m < 4 + 2 <=> m <= 5]])
  let h20 ← rr (← ExceptT.mk [[(m - &2) * (n - &2) < &4 <=>
                            m * n < &2 * (m + n)]])
  let h19 ← ar (← ExceptT.mk [[2 < n <=> 3 <= n]])
  let h18 ← tt (← ExceptT.mk [[~p ==> p ==> q]])
  let h17 ← ar (← ExceptT.mk [[m * n * (E + 2) <= E * m * n <=>
                                  2 * m * n = 0]])
  let h16 ← ng (← ExceptT.mk [[E * c = 2 * E ==> E = 0 \/ c = 2]])
  let h15 ← ar (← ExceptT.mk [[E * 2 * (n + 2) = n * 2 * (E + 2) <=>
                                E = n]])
  let h14 ← ar (← ExceptT.mk [[n:num < m ==> ~(m = n)]])
  let h13 ← tt (← ExceptT.mk [[~p ==> p ==> q]])
  let h12 ← ar (← ExceptT.mk [[E * 2 * (n + 1) = n * (E + 2) <=> E * (n + 2) = 2 * n]])
  let h11 ← ar (← ExceptT.mk [[m * 2 * e + n * 2 * e = m * n * (e + 2) <=>
                          e * 2 * (m + n) = m * n * (e + 2)]])
  let h10 ← ng (← ExceptT.mk [[v + f = e + 2 ==> !m n. m * n * v + n * m * f = m * n * (e + 2)]])
  let h9 ← ar (← ExceptT.mk [[0 * x = 2 * e ==> e = 0]])
  let h8 ← ar (← ExceptT.mk [[3 <= m ==> ~(m = 0)]])
  let h7 ← ar (← ExceptT.mk [[v + f = e + 2 ==> 4 <= v /\ 4 <= f ==> 6 <= e]])
  let h6 ← ia (← ExceptT.mk [[~(&2:int = -- &1)]])
  let h5 ← ar (← ExceptT.mk [[(a + b) - c = 2 ==> a + b = c + 2]])
  let h4 ← sr (← ExceptT.mk [[{x | x = a \/ x = b} = {a,b}]])
  let h3 ← sr (← ExceptT.mk [[{x | x = a \/ x = b} = {a,b}]])
  let h2 ← ia (← ExceptT.mk [[&1:int = b - &1 <=> b = &2]])
  let h1 ← sr (← ExceptT.mk [[f face_of s <=> f IN {f | f face_of s}]])
  prove ([[!p:real^3->bool m n.
    polytope p /\ aff_dim p = &3 /\
    (!f. f face_of p /\ aff_dim(f) = &2
         ==> CARD {e | e face_of p /\ aff_dim(e) = &1 /\ e SUBSET f} = m) /\
    (!v. v face_of p /\ aff_dim(v) = &0
         ==> CARD {e | e face_of p /\ aff_dim(e) = &1 /\ v SUBSET e} = n)
    ==> m = 3 /\ n = 3 \/       // Tetrahedron
        m = 4 /\ n = 3 \/       // Cube
        m = 3 /\ n = 4 \/       // Octahedron
        m = 5 /\ n = 3 \/       // Dodecahedron
        m = 3 /\ n = 5          // Icosahedron]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPEC ([[p:real^3->bool]]) EULER_RELATION) THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[m * CARD {f:real^3->bool | f face_of p /\ aff_dim f = &2} =
    2 * CARD {e | e face_of p /\ aff_dim e = &1} /\
    n * CARD {v | v face_of p /\ aff_dim v = &0} =
    2 * CARD {e | e face_of p /\ aff_dim e = &1}]]) MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MULTIPLE_COUNTING_LEMMA THENL
       [EXISTS_TAC ([[\(f:real^3->bool) (e:real^3->bool). e SUBSET f]]),
        EXISTS_TAC ([[\(v:real^3->bool) (e:real^3->bool). v SUBSET e]])] THEN
      ONCE_REWRITE_TAC [h1] THEN
      ASM_SIMP_TAC [FINITE_POLYTOPE_FACES, FINITE_RESTRICT] THEN
      ASM_REWRITE_TAC [IN_ELIM_THM, (← HolLight.GSYM CONJ_ASSOC)] THEN
      X_GEN_TAC ([[e:real^3->bool]]) THEN STRIP_TAC THENL
       [MP_TAC (← HolLight.ISPECL [([[p:real^3->bool]]), ([[e:real^3->bool]])] POLYHEDRON_RIDGE_TWO_FACETS) THEN
        ASM_SIMP_TAC [POLYTOPE_IMP_POLYHEDRON] THEN ANTS_TAC THENL
         [CONV_TAC INT_REDUCE_CONV THEN DISCH_THEN SUBST_ALL_TAC THEN
          RULE_ASSUM_TAC (HolLight.REWRITE_RULE [AFF_DIM_EMPTY]) THEN ASM_INT_ARITH_TAC,
          CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
          MAP_EVERY X_GEN_TAC [([[f1:real^3->bool]]), ([[f2:real^3->bool]])] THEN
          STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
          EXISTS_TAC ([[CARD {f1:real^3->bool,f2}]]) THEN CONJ_TAC THENL
           [AP_TERM_TAC THEN GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN
            REWRITE_TAC [IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY] THEN
            ASM_MESON_TAC [],
            ASM_SIMP_TAC [CARD_CLAUSES, IN_INSERT, FINITE_RULES,
                         NOT_IN_EMPTY, ARITH]]],
        SUBGOAL_THEN ([[?a b:real^3. e = segment[a,b] ]]) STRIP_ASSUME_TAC THENL
         [MATCH_MP_TAC COMPACT_CONVEX_COLLINEAR_SEGMENT THEN
          REPEAT CONJ_TAC THENL
           [DISCH_THEN SUBST_ALL_TAC THEN
            RULE_ASSUM_TAC (HolLight.REWRITE_RULE [AFF_DIM_EMPTY]) THEN ASM_INT_ARITH_TAC,
            MATCH_MP_TAC FACE_OF_IMP_COMPACT THEN
            EXISTS_TAC ([[p:real^3->bool]]) THEN
            ASM_SIMP_TAC [POLYTOPE_IMP_CONVEX, POLYTOPE_IMP_COMPACT],
            ASM_MESON_TAC [FACE_OF_IMP_CONVEX],
            MP_TAC (← HolLight.ISPEC ([[e:real^3->bool]]) AFF_DIM) THEN
            DISCH_THEN (X_CHOOSE_THEN ([[b:real^3->bool]]) MP_TAC) THEN
            ASM_REWRITE_TAC [h2] THEN
            DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC o HolLight.SYM) MP_TAC) THEN
            ASM_CASES_TAC ([[FINITE(b:real^3->bool)]]) THENL
             [ALL_TAC, ASM_MESON_TAC [AFFINE_INDEPENDENT_IMP_FINITE]] THEN
            REWRITE_TAC [INT_OF_NUM_EQ] THEN STRIP_TAC THEN
            SUBGOAL_THEN ([[(b:real^3->bool) HAS_SIZE 2]]) MP_TAC THENL
             [ASM_REWRITE_TAC [HAS_SIZE], CONV_TAC (HolLight.LAND_CONV HAS_SIZE_CONV)] THEN
            REWRITE_TAC [COLLINEAR_AFFINE_HULL] THEN
            REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
            ASM_MESON_TAC [HULL_SUBSET]],
          ASM_CASES_TAC ([[a:real^3 = b]]) THENL
           [UNDISCH_TAC ([[aff_dim(e:real^3->bool) = &1]]) THEN
            ASM_REWRITE_TAC [SEGMENT_REFL, AFF_DIM_SING, INT_OF_NUM_EQ, ARITH_EQ],
            ALL_TAC] THEN
          MATCH_MP_TAC EQ_TRANS THEN
          EXISTS_TAC ([[CARD {v:real^3 | v extreme_point_of segment[a,b]}]]) THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN
            EXISTS_TAC ([[\v:real^3. {v}]]) THEN
            REWRITE_TAC [IN_ELIM_THM, FACE_OF_SING, AFF_DIM_SING] THEN
            REPEAT CONJ_TAC THENL
             [ASM_REWRITE_TAC [EXTREME_POINT_OF_SEGMENT] THEN
              REWRITE_TAC [h3] THEN
              REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY],
              X_GEN_TAC ([[v:real^3]]) THEN REWRITE_TAC [(← HolLight.GSYM FACE_OF_SING)] THEN
              ASM_MESON_TAC [FACE_OF_TRANS, FACE_OF_IMP_SUBSET],
              X_GEN_TAC ([[s:real^3->bool]]) THEN REWRITE_TAC [AFF_DIM_EQ_0] THEN
              DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
              DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
              DISCH_THEN (X_CHOOSE_THEN ([[v:real^3]]) SUBST_ALL_TAC) THEN
              REWRITE_TAC [EXISTS_UNIQUE] THEN EXISTS_TAC ([[v:real^3]]) THEN
              ASM_REWRITE_TAC [(← HolLight.GSYM FACE_OF_SING)] THEN CONJ_TAC THENL
               [ASM_MESON_TAC [FACE_OF_FACE], SET_TAC []]],
            ASM_REWRITE_TAC [EXTREME_POINT_OF_SEGMENT] THEN
            REWRITE_TAC [h4] THEN
            ASM_SIMP_TAC [FINITE_INSERT, CARD_CLAUSES, FINITE_EMPTY] THEN
            ASM_REWRITE_TAC [IN_SING, NOT_IN_EMPTY, ARITH]]]],
      ALL_TAC] THEN
    STRIP_TAC THEN
    DISCH_THEN (ASSUME_TAC o HolLight.MATCH_MP h5) THEN
    SUBGOAL_THEN ([[4 <= CARD {v:real^3->bool | v face_of p /\ aff_dim v = &0}]]) ASSUME_TAC THENL
     [ASM_SIMP_TAC [SIZE_ZERO_DIMENSIONAL_FACES, POLYTOPE_IMP_POLYHEDRON] THEN
      MP_TAC (← HolLight.ISPEC ([[p:real^3->bool]]) POLYTOPE_VERTEX_LOWER_BOUND) THEN
      ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV THEN
      REWRITE_TAC [INT_OF_NUM_LE],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[4 <= CARD {f:real^3->bool | f face_of p /\ aff_dim f = &2}]]) ASSUME_TAC THENL
     [MP_TAC (← HolLight.ISPEC ([[p:real^3->bool]]) POLYTOPE_FACET_LOWER_BOUND) THEN
      ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV THEN
      ASM_REWRITE_TAC [INT_OF_NUM_LE, facet_of] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN
      CONV_TAC INT_REDUCE_CONV THEN GEN_TAC THEN EQ_TAC THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [h6, AFF_DIM_EMPTY],
      ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP h7) THEN
    ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC ([[CARD {e:real^3->bool | e face_of p /\ aff_dim e = &1} = 0]]) THEN
    ASM_REWRITE_TAC [ARITH] THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[3 <= m]]) ASSUME_TAC THENL
     [ASM_CASES_TAC ([[{f:real^3->bool | f face_of p /\ aff_dim f = &2} = {}]]) THENL
       [UNDISCH_TAC ([[4 <= CARD {f:real^3->bool | f face_of p /\ aff_dim f = &2}]]) THEN
        ASM_REWRITE_TAC [CARD_CLAUSES] THEN ARITH_TAC,
        FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [(← HolLight.GSYM MEMBER_NOT_EMPTY)])] THEN
      REWRITE_TAC [IN_ELIM_THM] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[f:real^3->bool]]) MP_TAC) THEN
      DISCH_THEN (fun th => STRIP_ASSUME_TAC th THEN
       FIRST_X_ASSUM (SUBST1_TAC o HolLight.SYM o HolCore.Lib.C HolLight.MATCH_MP th)) THEN
      MP_TAC (← HolLight.ISPEC ([[f:real^3->bool]]) POLYTOPE_FACET_LOWER_BOUND) THEN
      ASM_REWRITE_TAC [facet_of] THEN CONV_TAC INT_REDUCE_CONV THEN
      ANTS_TAC THENL [ASM_MESON_TAC [FACE_OF_POLYTOPE_POLYTOPE], ALL_TAC] THEN
      REWRITE_TAC [INT_OF_NUM_LE] THEN MATCH_MP_TAC EQ_IMP THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC HolCore.Lib.I [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN
      CONV_TAC INT_REDUCE_CONV THEN X_GEN_TAC ([[e:real^3->bool]]) THEN
      EQ_TAC THEN ASM_CASES_TAC ([[e:real^3->bool = {}]]) THEN
      ASM_SIMP_TAC [AFF_DIM_EMPTY] THEN CONV_TAC INT_REDUCE_CONV THENL
       [ASM_MESON_TAC [FACE_OF_TRANS, FACE_OF_IMP_SUBSET],
        ASM_MESON_TAC [FACE_OF_FACE]],
      ALL_TAC] THEN
    FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP h8) THEN
    ASM_CASES_TAC ([[n = 0]]) THENL
     [UNDISCH_THEN ([[n = 0]]) SUBST_ALL_TAC THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP h9) THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP h10) THEN
    DISCH_THEN (MP_TAC o HolLight.SPECL [([[m:num]]), ([[n:num]])]) THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [h11] THEN
    ABBREV_TAC ([[E = CARD {e:real^3->bool | e face_of p /\ aff_dim e = &1}]]) THEN
    ASM_CASES_TAC ([[n = 1]]) THENL
     [ASM_REWRITE_TAC [MULT_CLAUSES, h12] THEN
      MATCH_MP_TAC h13 THEN
      MATCH_MP_TAC h14 THEN
      MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC ([[2 * (m + 2)]]) THEN
      CONJ_TAC THENL [ARITH_TAC, MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[n = 2]]) THENL
     [ASM_REWRITE_TAC [h15] THEN
      DISCH_THEN (SUBST_ALL_TAC o HolLight.SYM) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP h16) THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN ([[3 <= n]]) ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    ASM_CASES_TAC ([[m * n < 2 * (m + n)]]) THENL
     [DISCH_TAC,
      DISCH_TAC THEN RULE_ASSUM_TAC (HolLight.REWRITE_RULE [NOT_LT]) THEN
      SUBGOAL_THEN ([[E * 2 * (m + n) <= E * m * n]]) MP_TAC THENL
       [REWRITE_TAC [LE_MULT_LCANCEL] THEN ASM_ARITH_TAC,
        ASM_REWRITE_TAC [h17] THEN
        MATCH_MP_TAC h18 THEN
        REWRITE_TAC [MULT_EQ_0] THEN ASM_ARITH_TAC]] THEN
    SUBGOAL_THEN ([[&m - &2:real < &4 /\ &n - &2 < &4]]) MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC ([[&n - &2]]),
        MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC ([[&m - &2]])] THEN
      ASM_SIMP_TAC [REAL_SUB_LT, REAL_OF_NUM_LT,
                   h19] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC ([[&4]]) THEN
      REWRITE_TAC [h20] THEN
      ASM_REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_ADD, REAL_OF_NUM_LT] THEN
      REWRITE_TAC [REAL_SUB_LDISTRIB, REAL_SUB_RDISTRIB, REAL_LE_SUB_LADD] THEN
      REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_ADD, REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [REAL_LT_SUB_RADD, REAL_OF_NUM_ADD, REAL_OF_NUM_LT] THEN
    REWRITE_TAC [h21] THEN
    ASM_SIMP_TAC [h22] THEN
    STRIP_TAC THEN UNDISCH_TAC ([[E * 2 * (m + n) = m * n * (E + 2)]]) THEN
    ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC)
  : ExceptT String IO thm).run
#eval PLATONIC_SOLIDS_LIMITS

/- ------------------------------------------------------------------------- -/
/- If-and-only-if version.                                                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 71
def PLATONIC_SOLIDS : thm := keep "PLATONIC_SOLIDS" fun _ => (do
  prove ([[!m n.
   (?p:real^3->bool.
     polytope p /\ aff_dim p = &3 /\
     (!f. f face_of p /\ aff_dim(f) = &2
          ==> CARD {e | e face_of p /\ aff_dim(e) = &1 /\ e SUBSET f} = m) /\
     (!v. v face_of p /\ aff_dim(v) = &0
          ==> CARD {e | e face_of p /\ aff_dim(e) = &1 /\ v SUBSET e} = n)) <=>
     m = 3 /\ n = 3 \/       // Tetrahedron
     m = 4 /\ n = 3 \/       // Cube
     m = 3 /\ n = 4 \/       // Octahedron
     m = 5 /\ n = 3 \/       // Dodecahedron
     m = 3 /\ n = 5          // Icosahedron]])
   (REPEAT GEN_TAC THEN EQ_TAC THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM, PLATONIC_SOLIDS_LIMITS] THEN
    STRIP_TAC THENL
     [EXISTS_TAC ([[std_tetrahedron]]) THEN
      ASM_REWRITE_TAC [TETRAHEDRON_EDGES_PER_VERTEX, TETRAHEDRON_EDGES_PER_FACE,
                      STD_TETRAHEDRON_FULLDIM] THEN
      REWRITE_TAC [std_tetrahedron] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
      REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY],
      EXISTS_TAC ([[std_cube]]) THEN
      ASM_REWRITE_TAC [CUBE_EDGES_PER_VERTEX, CUBE_EDGES_PER_FACE,
                      STD_CUBE_FULLDIM] THEN
      REWRITE_TAC [std_cube] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
      REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY],
      EXISTS_TAC ([[std_octahedron]]) THEN
      ASM_REWRITE_TAC [OCTAHEDRON_EDGES_PER_VERTEX, OCTAHEDRON_EDGES_PER_FACE,
                      STD_OCTAHEDRON_FULLDIM] THEN
      REWRITE_TAC [std_octahedron] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
      REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY],
      EXISTS_TAC ([[std_dodecahedron]]) THEN
      ASM_REWRITE_TAC [DODECAHEDRON_EDGES_PER_VERTEX, DODECAHEDRON_EDGES_PER_FACE,
                      STD_DODECAHEDRON_FULLDIM] THEN
      REWRITE_TAC [STD_DODECAHEDRON] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
      REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY],
      EXISTS_TAC ([[std_icosahedron]]) THEN
      ASM_REWRITE_TAC [ICOSAHEDRON_EDGES_PER_VERTEX, ICOSAHEDRON_EDGES_PER_FACE,
                      STD_ICOSAHEDRON_FULLDIM] THEN
      REWRITE_TAC [STD_ICOSAHEDRON] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
      REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY]])
  : ExceptT String IO thm).run
#eval PLATONIC_SOLIDS

/- ------------------------------------------------------------------------- -/
/- Show that the regular polyhedra do have all edges and faces congruent.    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 72
-- parse_as_infix("congruent",(12,"right"));;
#eval (parse_as_infix ("congruent", (12, "right")) : IO Unit)

#eval phrase 73
def congruent : thm := keep "congruent" fun _ => new_definition
 [[(s:real^N->bool) congruent (t:real^N->bool) <=>
        ?c f. orthogonal_transformation f /\ t = IMAGE (\x. c + f x) s]]
#eval congruent

#eval phrase 74
def CONGRUENT_SIMPLE : thm := keep "CONGRUENT_SIMPLE" fun _ => (do
  prove ([[(?A:real^3^3. orthogonal_matrix A /\ IMAGE (\x:real^3. A ** x) s = t)
   ==> (convex hull s) congruent (convex hull t)]])
   (REPEAT GEN_TAC THEN
    DISCH_THEN (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o HolLight.SYM))) THEN
    SIMP_TAC [CONVEX_HULL_LINEAR_IMAGE, MATRIX_VECTOR_MUL_LINEAR] THEN
    REWRITE_TAC [congruent] THEN EXISTS_TAC ([[vec 0:real^3]]) THEN
    EXISTS_TAC ([[\x:real^3. (A:real^3^3) ** x]]) THEN
    REWRITE_TAC [VECTOR_ADD_LID, ORTHOGONAL_TRANSFORMATION_MATRIX] THEN
    ASM_SIMP_TAC [MATRIX_OF_MATRIX_VECTOR_MUL, MATRIX_VECTOR_MUL_LINEAR])
  : ExceptT String IO thm).run
#eval CONGRUENT_SIMPLE

#eval phrase 75
def CONGRUENT_SEGMENTS : thm := keep "CONGRUENT_SEGMENTS" fun _ => (do
  let h1 ← va (← ExceptT.mk [[d:real^N = c - a + b <=> b - a = d - c]])
  prove ([[!a b c d:real^N.
        dist(a,b) = dist(c,d)
        ==> segment[a,b] congruent segment[c,d] ]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.ISPECL [([[b - a:real^N]]), ([[d - c:real^N]])] ORTHOGONAL_TRANSFORMATION_EXISTS) THEN
    ANTS_TAC THENL [POP_ASSUM MP_TAC THEN NORM_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[f:real^N->real^N]]) STRIP_ASSUME_TAC) THEN
    REWRITE_TAC [congruent] THEN
    EXISTS_TAC ([[c - (f:real^N->real^N) a]]) THEN
    EXISTS_TAC ([[f:real^N->real^N]]) THEN
    FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
    SUBGOAL_THEN ([[(\x. (c - f a) + (f:real^N->real^N) x) = (\x. (c - f a) + x) o f]]) SUBST1_TAC THENL [REWRITE_TAC [FUN_EQ_THM, o_THM], ALL_TAC] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM CONVEX_HULL_LINEAR_IMAGE), SEGMENT_CONVEX_HULL, IMAGE_o,
                 (← HolLight.GSYM CONVEX_HULL_TRANSLATION)] THEN
    REWRITE_TAC [IMAGE_CLAUSES] THEN
    AP_TERM_TAC THEN BINOP_TAC THENL
     [VECTOR_ARITH_TAC, AP_THM_TAC THEN AP_TERM_TAC] THEN
    REWRITE_TAC [h1] THEN
    ASM_MESON_TAC [LINEAR_SUB])
  : ExceptT String IO thm).run
#eval CONGRUENT_SEGMENTS

#eval phrase 76
-- let compute_dist = ...;;
def compute_dist (v1 v2 : term) : ExceptT String IO term := do
  let sub_tm ← ExceptT.mk [[(-):real^3->real^3->real^3]]
  let dot_tm ← ExceptT.mk [[(dot):real^3->real^3->real]]
  let vth ← ExceptT.mk (VECTOR3_SUB_CONV (← ec ((← ec (HolCore.Basics.mk_binop sub_tm v1)) v2)))
  let dth ← HolLight.CONV_RULE (HolLight.RAND_CONV VECTOR3_DOT_CONV)
    (← HolLight.MK_COMB ((← HolLight.AP_TERM dot_tm vth), vth))
  ec (rand (concl dth))
#eval IO.println "<fun>"

#eval phrase 77
-- let le_rat5 = ...;;
def le_rat5 (r1 r2 : term) : ExceptT String IO Bool := do
  let le_tm ← ExceptT.mk [[(<=):real->real->bool]]
  let th ← ExceptT.mk (REAL_RAT5_LE_CONV (← ec ((← ec (HolCore.Basics.mk_binop le_tm r1)) r2)))
  pure ((← ec (rand (concl th))) == (← ExceptT.mk [[T]]))
#eval IO.println "<fun>"

#eval phrase 78
-- let three_adjacent_points s = ...;;
def three_adjacent_points (s : List term) : ExceptT String IO (term × term × term) := do
  match s with
  | x :: t =>
    let ds ← t.mapM fun y => do pure (y, ← compute_dist x y)
    -- OCaml's (stable merge) sort with le_rat5 on the distances
    let rec ins (p : term × term) : List (term × term) → ExceptT String IO (List (term × term))
      | [] => pure [p]
      | q :: qs => do if ← le_rat5 p.2 q.2 then pure (p :: q :: qs) else pure (q :: (← ins p qs))
    let sorted ← ds.foldrM (fun p acc => ins p acc) []
    match sorted with
    | (y, _) :: (z, _) :: _ => pure (x, y, z)
    | _ => throw "Match_failure"
  | _ => throw "three_adjacent_points: no points"
#eval IO.println "<fun>"

#eval phrase 79
-- let mk_33matrix = ...;;
def mk_33matrix (l : List term) : ExceptT String IO term := do
  let vs ← [ [[a11:real]], [[a12:real]], [[a13:real]], [[a21:real]], [[a22:real]], [[a23:real]],
            [[a31:real]], [[a32:real]], [[a33:real]] ].mapM fun (q : IO (Except String term)) => ExceptT.mk q
  let pat_tm ← ExceptT.mk [[vector[vector[a11; a12; a13];
           vector[a21; a22; a23];
           vector[a31; a32; a33] ]:real^3^3]]
  if l.length != 9 then throw "Match_failure"
  pure ((← ec (HolCore.Kernel.vsubst (l.zip vs))) pat_tm)
#eval IO.println "<fun>"

#eval phrase 80
def MATRIX_VECTOR_MUL_3 : thm := keep "MATRIX_VECTOR_MUL_3" fun _ => (do
  prove ([[(vector[vector[a11;a12;a13];
           vector[a21; a22; a23];
           vector[a31; a32; a33] ]:real^3^3) **
   (vector[x1;x2;x3]:real^3) =
   vector[a11 * x1 + a12 * x2 + a13 * x3;
          a21 * x1 + a22 * x2 + a23 * x3;
          a31 * x1 + a32 * x2 + a33 * x3] ]])
   (SIMP_TAC [CART_EQ, matrix_vector_mul, LAMBDA_BETA] THEN
    REWRITE_TAC [DIMINDEX_3, FORALL_3, SUM_3, VECTOR_3])
  : ExceptT String IO thm).run
#eval MATRIX_VECTOR_MUL_3

#eval phrase 81
def MATRIX_LEMMA : thm := keep "MATRIX_LEMMA" fun _ => (do
  prove ([[!A:real^3^3.
   A ** x1 = x2 /\
   A ** y1 = y2 /\
   A ** z1 = z2 <=>
   (vector [x1; y1; z1]:real^3^3) ** (row 1 A:real^3) =
   vector [x2$1; y2$1; z2$1] /\
   (vector [x1; y1; z1]:real^3^3) ** (row 2 A:real^3) =
   vector [x2$2; y2$2; z2$2] /\
   (vector [x1; y1; z1]:real^3^3) ** (row 3 A:real^3) =
   vector [x2$3; y2$3; z2$3] ]])
   (SIMP_TAC [CART_EQ, transp, matrix_vector_mul, row, VECTOR_3, LAMBDA_BETA] THEN
    REWRITE_TAC [FORALL_3, DIMINDEX_3, VECTOR_3, SUM_3] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval MATRIX_LEMMA

#eval phrase 82
def MATRIX_BY_CRAMER_LEMMA : thm := keep "MATRIX_BY_CRAMER_LEMMA" fun _ => (do
  prove ([[!A:real^3^3.
        ~(det(vector[x1; y1; z1]:real^3^3) = &0)
        ==> (A ** x1 = x2 /\
             A ** y1 = y2 /\
             A ** z1 = z2 <=>
             A = lambda m k. det((lambda i j.
                                  if j = k
                                  then (vector[x2$m; y2$m; z2$m]:real^3)$i
                                  else (vector[x1; y1; z1]:real^3^3)$i$j)
                                 :real^3^3) /
                             det(vector[x1;y1;z1]:real^3^3))]])
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC HolLight.LAND_CONV [MATRIX_LEMMA] THEN
    ASM_SIMP_TAC [CRAMER] THEN REWRITE_TAC [CART_EQ, row] THEN
    SIMP_TAC [LAMBDA_BETA] THEN REWRITE_TAC [DIMINDEX_3, FORALL_3])
  : ExceptT String IO thm).run
#eval MATRIX_BY_CRAMER_LEMMA

#eval phrase 83
def MATRIX_BY_CRAMER : thm := keep "MATRIX_BY_CRAMER" fun _ => (do
  prove ([[!A:real^3^3 x1 y1 z1 x2 y2 z2.
        let d = det(vector[x1; y1; z1]:real^3^3) in
        ~(d = &0)
        ==> (A ** x1 = x2 /\
             A ** y1 = y2 /\
             A ** z1 = z2 <=>
               A$1$1 =
               (x2$1 * y1$2 * z1$3 +
                x1$2 * y1$3 * z2$1 +
                x1$3 * y2$1 * z1$2 -
                x2$1 * y1$3 * z1$2 -
                x1$2 * y2$1 * z1$3 -
                x1$3 * y1$2 * z2$1) / d /\
               A$1$2 =
               (x1$1 * y2$1 * z1$3 +
                x2$1 * y1$3 * z1$1 +
                x1$3 * y1$1 * z2$1 -
                x1$1 * y1$3 * z2$1 -
                x2$1 * y1$1 * z1$3 -
                x1$3 * y2$1 * z1$1) / d /\
               A$1$3 =
               (x1$1 * y1$2 * z2$1 +
                x1$2 * y2$1 * z1$1 +
                x2$1 * y1$1 * z1$2 -
                x1$1 * y2$1 * z1$2 -
                x1$2 * y1$1 * z2$1 -
                x2$1 * y1$2 * z1$1) / d /\
               A$2$1 =
               (x2$2 * y1$2 * z1$3 +
                x1$2 * y1$3 * z2$2 +
                x1$3 * y2$2 * z1$2 -
                x2$2 * y1$3 * z1$2 -
                x1$2 * y2$2 * z1$3 -
                x1$3 * y1$2 * z2$2) / d /\
               A$2$2 =
               (x1$1 * y2$2 * z1$3 +
                x2$2 * y1$3 * z1$1 +
                x1$3 * y1$1 * z2$2 -
                x1$1 * y1$3 * z2$2 -
                x2$2 * y1$1 * z1$3 -
                x1$3 * y2$2 * z1$1) / d /\
               A$2$3 =
               (x1$1 * y1$2 * z2$2 +
                x1$2 * y2$2 * z1$1 +
                x2$2 * y1$1 * z1$2 -
                x1$1 * y2$2 * z1$2 -
                x1$2 * y1$1 * z2$2 -
                x2$2 * y1$2 * z1$1) / d /\
               A$3$1 =
               (x2$3 * y1$2 * z1$3 +
                x1$2 * y1$3 * z2$3 +
                x1$3 * y2$3 * z1$2 -
                x2$3 * y1$3 * z1$2 -
                x1$2 * y2$3 * z1$3 -
                x1$3 * y1$2 * z2$3) / d /\
               A$3$2 =
               (x1$1 * y2$3 * z1$3 +
                x2$3 * y1$3 * z1$1 +
                x1$3 * y1$1 * z2$3 -
                x1$1 * y1$3 * z2$3 -
                x2$3 * y1$1 * z1$3 -
                x1$3 * y2$3 * z1$1) / d /\
               A$3$3 =
               (x1$1 * y1$2 * z2$3 +
                x1$2 * y2$3 * z1$1 +
                x2$3 * y1$1 * z1$2 -
                x1$1 * y2$3 * z1$2 -
                x1$2 * y1$1 * z2$3 -
                x2$3 * y1$2 * z1$1) / d)]])
   (REPEAT GEN_TAC THEN CONV_TAC let_CONV THEN DISCH_TAC THEN
    ASM_SIMP_TAC [MATRIX_BY_CRAMER_LEMMA] THEN
    REWRITE_TAC [DET_3, CART_EQ] THEN
    SIMP_TAC [LAMBDA_BETA, DIMINDEX_3, ARITH, VECTOR_3] THEN
    REWRITE_TAC [FORALL_3, ARITH, VECTOR_3] THEN REWRITE_TAC [CONJ_ACI])
  : ExceptT String IO thm).run
#eval MATRIX_BY_CRAMER

#eval phrase 84
-- let CONGRUENT_EDGES_TAC = ...;;
def CONGRUENT_EDGES_TAC (edges : thm) : HolCore.Tactics.tactic :=
  HolLight.tactic_of do
  pure (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN REWRITE_TAC [IMP_IMP] THEN
    REWRITE_TAC [edges] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [(← HolLight.GSYM SEGMENT_CONVEX_HULL)] THEN
    MATCH_MP_TAC CONGRUENT_SEGMENTS THEN REWRITE_TAC [DIST_EQ] THEN
    REWRITE_TAC [SessionMultiLib.Vectors.dist, NORM_POW_2] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV VECTOR3_DOT_CONV) THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV REAL_RAT5_EQ_CONV) THEN
    REWRITE_TAC [])
#eval IO.println "<fun>"

#eval phrase 85
-- let CONGRUENT_FACES_TAC = ...;;
def CONGRUENT_FACES_TAC (facets : thm) : HolCore.Tactics.tactic :=
  REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN REWRITE_TAC [IMP_IMP] THEN
    REWRITE_TAC [facets] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        let t1 ← ec (HolCore.Kernel.rand (← ec (HolCore.Equal.lhand w)))
        pure (HolLight.tactic_of do
        let t2 ← ec (HolCore.Kernel.rand (← ec (HolCore.Kernel.rand w)))
        pure (HolLight.tactic_of do
        let ( x1, y1, z1 ) ← three_adjacent_points (← ec (dest_setenum t1))
        pure (HolLight.tactic_of do
        let ( x2, y2, z2 ) ← three_adjacent_points (← ec (dest_setenum t2))
        pure (HolLight.tactic_of do
        let th1 ← HolLight.SPECL [([[A:real^3^3]]), x1, y1, z1, x2, y2, z2] MATRIX_BY_CRAMER
        pure (HolLight.tactic_of do
        let th2 ← HolLight.REWRITE_RULE [VECTOR_3, DET_3] th1
        pure (HolLight.tactic_of do
        let th3 ← HolLight.CONV_RULE (HolLight.DEPTH_CONV REAL_RAT5_MUL_CONV) th2
        pure (HolLight.tactic_of do
        let th4 ← HolLight.CONV_RULE (HolLight.DEPTH_CONV (REAL_RAT5_ADD_CONV ORELSEC REAL_RAT5_SUB_CONV)) th3
        pure (HolLight.tactic_of do
        let th5 ← HolLight.CONV_RULE let_CONV th4
        pure (HolLight.tactic_of do
        let th6 ← HolLight.CONV_RULE (HolLight.ONCE_DEPTH_CONV REAL_RAT5_DIV_CONV) th5
        pure (HolLight.tactic_of do
        let th7 ← HolLight.CONV_RULE (HolLight.ONCE_DEPTH_CONV REAL_RAT5_EQ_CONV) th6
        pure (HolLight.tactic_of do
        let th8 ← HolLight.MP th7 (← HolLight.EQT_ELIM (← ExceptT.mk (HolLight.REWRITE_CONV [] (← ec (HolCore.Equal.lhand (concl th7))))))
        pure (HolLight.tactic_of do
        let tms ← ec (((HolCore.Basics.conjuncts (← ec (HolCore.Kernel.rand (concl th8))))).mapM HolCore.Equal.rhs)
        pure (HolLight.tactic_of do
        let matt ← mk_33matrix tms
        pure (MATCH_MP_TAC CONGRUENT_SIMPLE THEN EXISTS_TAC matt THEN CONJ_TAC THENL
           [REWRITE_TAC [ORTHOGONAL_MATRIX, CART_EQ] THEN
            SIMP_TAC [transp, LAMBDA_BETA, matrix_mul, mat] THEN
            REWRITE_TAC [DIMINDEX_3, SUM_3, FORALL_3, VECTOR_3, ARITH] THEN
            CONV_TAC (HolLight.ONCE_DEPTH_CONV REAL_RAT5_MUL_CONV) THEN
            CONV_TAC (HolLight.DEPTH_CONV REAL_RAT5_ADD_CONV) THEN
            CONV_TAC (HolLight.ONCE_DEPTH_CONV REAL_RAT5_EQ_CONV) THEN
            REWRITE_TAC [] THEN HolCore.Tactics.NO_TAC,
            REWRITE_TAC [IMAGE_CLAUSES, MATRIX_VECTOR_MUL_3] THEN
            CONV_TAC (HolLight.ONCE_DEPTH_CONV REAL_RAT5_MUL_CONV) THEN
            CONV_TAC (HolLight.DEPTH_CONV REAL_RAT5_ADD_CONV) THEN
            REWRITE_TAC [INSERT_AC]])))))))))))))))
#eval IO.println "<fun>"

#eval phrase 86
def TETRAHEDRON_CONGRUENT_EDGES : thm := keep "TETRAHEDRON_CONGRUENT_EDGES" fun _ => (do
  prove ([[!e1 e2. e1 face_of std_tetrahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_tetrahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2]])
   (CONGRUENT_EDGES_TAC TETRAHEDRON_EDGES)
  : ExceptT String IO thm).run
#eval TETRAHEDRON_CONGRUENT_EDGES

#eval phrase 87
def TETRAHEDRON_CONGRUENT_FACETS : thm := keep "TETRAHEDRON_CONGRUENT_FACETS" fun _ => (do
  prove ([[!f1 f2. f1 face_of std_tetrahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_tetrahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2]])
   (CONGRUENT_FACES_TAC TETRAHEDRON_FACETS)
  : ExceptT String IO thm).run
#eval TETRAHEDRON_CONGRUENT_FACETS

#eval phrase 88
def CUBE_CONGRUENT_EDGES : thm := keep "CUBE_CONGRUENT_EDGES" fun _ => (do
  prove ([[!e1 e2. e1 face_of std_cube /\ aff_dim e1 = &1 /\
           e2 face_of std_cube /\ aff_dim e2 = &1
           ==> e1 congruent e2]])
   (CONGRUENT_EDGES_TAC CUBE_EDGES)
  : ExceptT String IO thm).run
#eval CUBE_CONGRUENT_EDGES

#eval phrase 89
def CUBE_CONGRUENT_FACETS : thm := keep "CUBE_CONGRUENT_FACETS" fun _ => (do
  prove ([[!f1 f2. f1 face_of std_cube /\ aff_dim f1 = &2 /\
           f2 face_of std_cube /\ aff_dim f2 = &2
           ==> f1 congruent f2]])
   (CONGRUENT_FACES_TAC CUBE_FACETS)
  : ExceptT String IO thm).run
#eval CUBE_CONGRUENT_FACETS

#eval phrase 90
def OCTAHEDRON_CONGRUENT_EDGES : thm := keep "OCTAHEDRON_CONGRUENT_EDGES" fun _ => (do
  prove ([[!e1 e2. e1 face_of std_octahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_octahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2]])
   (CONGRUENT_EDGES_TAC OCTAHEDRON_EDGES)
  : ExceptT String IO thm).run
#eval OCTAHEDRON_CONGRUENT_EDGES

#eval phrase 91
def OCTAHEDRON_CONGRUENT_FACETS : thm := keep "OCTAHEDRON_CONGRUENT_FACETS" fun _ => (do
  prove ([[!f1 f2. f1 face_of std_octahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_octahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2]])
   (CONGRUENT_FACES_TAC OCTAHEDRON_FACETS)
  : ExceptT String IO thm).run
#eval OCTAHEDRON_CONGRUENT_FACETS

#eval phrase 92
def DODECAHEDRON_CONGRUENT_EDGES : thm := keep "DODECAHEDRON_CONGRUENT_EDGES" fun _ => (do
  prove ([[!e1 e2. e1 face_of std_dodecahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_dodecahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2]])
   (CONGRUENT_EDGES_TAC DODECAHEDRON_EDGES)
  : ExceptT String IO thm).run
#eval DODECAHEDRON_CONGRUENT_EDGES

#eval phrase 93
def DODECAHEDRON_CONGRUENT_FACETS : thm := keep "DODECAHEDRON_CONGRUENT_FACETS" fun _ => (do
  prove ([[!f1 f2. f1 face_of std_dodecahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_dodecahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2]])
   (CONGRUENT_FACES_TAC DODECAHEDRON_FACETS)
  : ExceptT String IO thm).run
#eval DODECAHEDRON_CONGRUENT_FACETS

#eval phrase 94
def ICOSAHEDRON_CONGRUENT_EDGES : thm := keep "ICOSAHEDRON_CONGRUENT_EDGES" fun _ => (do
  prove ([[!e1 e2. e1 face_of std_icosahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_icosahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2]])
   (CONGRUENT_EDGES_TAC ICOSAHEDRON_EDGES)
  : ExceptT String IO thm).run
#eval ICOSAHEDRON_CONGRUENT_EDGES

#eval phrase 95
def ICOSAHEDRON_CONGRUENT_FACETS : thm := keep "ICOSAHEDRON_CONGRUENT_FACETS" fun _ => (do
  prove ([[!f1 f2. f1 face_of std_icosahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_icosahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2]])
   (CONGRUENT_FACES_TAC ICOSAHEDRON_FACETS)
  : ExceptT String IO thm).run
#eval ICOSAHEDRON_CONGRUENT_FACETS

end Hol100.Platonic
