/- File: HolExamples/InverseBugPuzzleTac.lean
Translation of HOL Light's Examples/inverse_bug_puzzle_tac.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
import SessionMultiLib.Determinants
open HolCore.Kernel Session HolLight.Syntax HolExamples
open SessionMultiLib.Misc SessionMultiLib.Vectors SessionMultiLib.Determinants
namespace HolExamples.InverseBugPuzzleTac

/- Helpers: the session's `prove` lifted into `ExceptT String IO`, so tactic
   scripts read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def sr (tm : term) : ExceptT String IO thm := ExceptT.mk (SET_RULE tm)
private def nd (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.new_definition tm)

-- ========================================================================= --
--                (c) Copyright, Bill Richter 2013                           --
--          Distributed under the same license as HOL Light                  --
--                                                                           --
-- Proof of the Bug Puzzle conjecture of the HOL Light tutorial: Any two     --
-- triples of points in the plane with the same oriented area can be         --
-- connected in 5 moves or less (FivemovesOrLess).  Much of the code is      --
-- due to John Harrison: a proof (NOTENOUGH_4) showing this is the best      --
-- possible result; an early version of Noncollinear_2Span; the              --
-- definition of move, which defines a closed subset                         --
--       {(A,B,C,A',B',C') | move (A,B,C) (A',B',C')} of R^6 x R^6,          --
-- i.e. the zero set of a continuous function; FivemovesOrLess_STRONG,       --
-- which handles the degenerate case (collinear or non-distinct triples),    --
-- giving a satisfying answer using this "closed" definition of move.        --
--                                                                           --
-- The mathematical proofs are essentially due to Tom Hales.  The code       --
-- tries to mix declarative and procedural proof styles, using ideas due     --
-- to John Harrison (section 12.1 "Towards more readable proofs" of the      --
-- HOL Light tutorial), Freek Wiedijk (arxiv.org/pdf/1201.3601 "A            --
-- Synthesis of the Procedural and Declarative Styles of Interactive         --
-- Theorem Proving"), Marco Maggesi, who wrote the tactic constructs         --
-- INTRO_TAC & HYP, which goes well with the older SUBGOAL_TAC, and Petros   --
-- Papapanagiotou, coauthor of IsabelleLight, who wrote BuildExist below, a  --
-- a crucial part of consider.                                               --
-- ========================================================================= --

#eval phrase 1
-- needs "Multivariate/determinants.ml";;
#eval SessionMultiLib.Determinants.ensureDeterminants

#eval phrase 2
-- new_type_abbrev("triple",`:real^2#real^2#real^2`);;
#eval show IO Unit from do
  match ← HolCore.Parser.parse_type "real^2#real^2#real^2" with
  | .ok ty => Session.new_type_abbrev "triple" ty
  | .error e => failure e

#eval phrase 3
def so (tac : HolCore.Tactics.tactic) : HolCore.Tactics.tactic := FIRST_ASSUM MP_TAC THEN tac
#eval IO.println "<fun>"

#eval phrase 4
def BuildExist (x t : term) : ExceptT String IO term := do
  let try_type (tp : hol_type) (tm : term) : term :=
    match HolCore.Basics.type_match (type_of tm) tp [] with
    | .ok i => inst i tm
    | .error _ => tm
  -- Check if two variables match allowing only type instantiations:
  let vars_match (tm1 tm2 : term) : IO (Except String term) := do
    let i : HolCore.Drule.instantiation ←
      match ← HolCore.Drule.term_match [] tm1 tm2 with
      | .ok i => pure i
      | .error _ => pure ([], [(tm2, tm1)], [])
    match i with
    | ([], [], _) => return .ok tm2
    | _ => return .error "vars_match: no match"
  -- Find the type of a matching variable in t.
  let r : Except String term ← (MonadLiftT.monadLift
    (HolCore.Lib.tryfindM (vars_match x) (frees t) : IO (Except String term)) : ExceptT String IO _)
  let tp : hol_type ← match r with
    | .ok v => pure (type_of v)
    | .error _ => do
        HolCore.Lib.warn true ("BuildExist: `" ++ (← HolCore.Printer.string_of_term x) ++
          "` not be found in\n  `" ++ (← HolCore.Printer.string_of_term t) ++ "`")
        pure (type_of x)
  -- Try to force x to type tp.
  let x' := try_type tp x
  liftExcept (HolCore.Bool.mk_exists x' t)
#eval IO.println "<fun>"

#eval phrase 5
/-- `consider vars_SuchThat t prfs lab`.  The OCaml computes the subgoal
    when the tactic is built (parsing the variable names), so this is an
    action returning the tactic. -/
def consider (vars_SuchThat : String) (t : term) (prfs : List HolCore.Tactics.tactic)
    (lab : String) : ExceptT String IO HolCore.Tactics.tactic := do
  -- Functions ident and parse_using borrowed from HYP in tactics.ml
  let rec findSuchThat (n : Nat) : Nat :=
    if n + 9 > vars_SuchThat.length then n
    else if ((vars_SuchThat.drop n).take 9).toString == "such that" then n
    else findSuchThat (n + 1)
  termination_by vars_SuchThat.length - n
  let n := findSuchThat 1
  let vars := (vars_SuchThat.take (n - 1)).toString
  let c ← HolCore.Parser.mkCtx
  let toks ← match HolCore.Parser.lex c (HolCore.Lib.explode vars) with
    | .ok toks => pure toks
    | .error e => throw (HolCore.Parser.perrMsg e)
  let rec idents : List HolCore.Parser.lexcode → List String
    | .Ident s :: rest => if HolCore.Printer.isalnum s then s :: idents rest else []
    | _ => []
  let xl ← (idents toks).mapM (fun s => ExceptT.mk (HolCore.Parser.parse_term s))
  let tm ← xl.foldrM (fun x acc => BuildExist x acc) t
  match prfs with
  | p :: ps =>
    HolCore.Lib.warn (!ps.isEmpty) "consider: additional subproofs ignored"
    return (SUBGOAL_THEN tm (DESTRUCT_TAC ("@" ++ vars ++ "." ++ lab))
      THENL [p, ALL_TAC])
  | [] => throw "consider: no subproof given"
#eval IO.println "<fun>"

#eval phrase 6
def cases (sDestruct : String) (disjthm : term) (tac : List HolCore.Tactics.tactic) :
    HolCore.Tactics.tactic :=
  SUBGOAL_TAC "" disjthm tac THEN FIRST_X_ASSUM
  (DESTRUCT_TAC sDestruct)
#eval IO.println "<fun>"

#eval phrase 7
def raa (lab : String) (t : term) (tac : HolCore.Tactics.tactic) : HolCore.Tactics.tactic :=
  fun g => do
    match HolCore.Bool.mk_imp t (← HolCore.Parser.parse_term "F").toOption.get! with
    | .ok tm => (SUBGOAL_THEN tm (LABEL_TAC lab) THENL [INTRO_TAC lab, tac]) g
    | .error e => return .error e
#eval IO.println "<fun>"

#eval phrase 8
def VEC2_TAC : HolCore.Tactics.tactic :=
  SIMP_TAC [CART_EQ, LAMBDA_BETA, FORALL_2, SUM_2, DIMINDEX_2, VECTOR_2,
           vector_add, vec, dot, orthogonal, basis,
           vector_neg, vector_sub, vector_mul, ARITH] THEN
  CONV_TAC REAL_RING
#eval IO.println "<fun>"

#eval phrase 9
def COLLINEAR_3_2Dzero : thm := keep "COLLINEAR_3_2Dzero" fun _ => (do
  prove ([[!y z:real^2. collinear{vec 0,y,z} <=>
                  z$1 * y$2 = y$1 * z$2]])
   (REWRITE_TAC [COLLINEAR_3_2D] THEN VEC2_TAC)
  : ExceptT String IO thm).run
#eval COLLINEAR_3_2Dzero

#eval phrase 10
def Noncollinear_3ImpliesDistinct : thm := keep "Noncollinear_3ImpliesDistinct" fun _ => (do
  prove ([[~collinear {a,b,c}  ==>  ~(a = b) /\ ~(a = c) /\ ~(b = c)]])
   (MESON_TAC [COLLINEAR_BETWEEN_CASES, BETWEEN_REFL])
  : ExceptT String IO thm).run
#eval Noncollinear_3ImpliesDistinct

#eval phrase 11
def collinearSymmetry : thm := keep "collinearSymmetry" fun _ => (do
  let b1 ← sr ([[{A,C,B} SUBSET {A,B,C} /\  {B,A,C} SUBSET {A,B,C} /\
    {B,C,A} SUBSET {A,B,C} /\  {C,A,B} SUBSET {A,B,C} /\  {C,B,A} SUBSET {A,B,C}]])
  prove ([[collinear {A,B,C}
         ==> collinear {A,C,B} /\ collinear {B,A,C} /\
             collinear {B,C,A} /\ collinear {C,A,B} /\ collinear {C,B,A}]])
   (MESON_TAC [b1,
    COLLINEAR_SUBSET])
  : ExceptT String IO thm).run
#eval collinearSymmetry

#eval phrase 12
def Noncollinear_2Span : thm := keep "Noncollinear_2Span" fun _ => (do
  -- OCaml builds the tactic (and the `prove` pair) right to left: the
  -- build-time steps run bottom-first, so their output prints in that order.
  let b3 ← consider "x such that" ([[(M:real^2^2) ** (x:real^2) = u]])
    [so (MESON_TAC [(← ar ([[~(r < n)  /\  r <= MIN n n  ==>  r = n]])),
    DET_EQ_0_RANK, RANK_BOUND, MATRIX_FULL_LINEAR_EQUATIONS])] "xDef"
  let b1 ← consider "M such that"
    ([[M = transp(vector[v:real^2;w:real^2]):real^2^2]]) [MESON_TAC []] "Mexists"
  prove ([[!u v w:real^2. ~collinear  {vec 0,v,w} ==> ? s t. s % v + t % w = u]])
   (INTRO_TAC "!u v w; H1" THEN
    SUBGOAL_TAC "H1'" ([[~(v$1 * w$2 - (w:real^2)$1 * (v:real^2)$2 = &0)]])
    [HYP MESON_TAC "H1" [COLLINEAR_3_2Dzero, REAL_SUB_0]] THEN
    b1 THEN
    SUBGOAL_TAC "MatMult" ([[~(det (M:real^2^2) = &0) /\
    (! x. (M ** x)$1 = (v:real^2)$1 * x$1 + (w:real^2)$1 * x$2  /\
    (M ** x)$2 = v$2 * x$1 + w$2 * x$2)]])
    [HYP SIMP_TAC "H1' Mexists" [matrix_vector_mul, DIMINDEX_2, SUM_2,
    TRANSP_COMPONENT, VECTOR_2, LAMBDA_BETA, ARITH, CART_EQ, FORALL_2, DET_2] THEN VEC2_TAC] THEN
    b3 THEN
    MAP_EVERY EXISTS_TAC [([[(x:real^2)$1]]), ([[(x:real^2)$2]])] THEN SUBGOAL_TAC ""
    ([[(x:real^2)$1 * (v:real^2)$1 + (x:real^2)$2 * (w:real^2)$1 = (u:real^2)$1  /\
    x$1 * v$2 + x$2 * w$2 = u$2]]) [HYP MESON_TAC "MatMult xDef" [REAL_MUL_SYM]]
    THEN so (SIMP_TAC [CART_EQ, LAMBDA_BETA, FORALL_2, SUM_2, DIMINDEX_2, VECTOR_2, vector_add, vector_mul, ARITH]))
  : ExceptT String IO thm).run
#eval Noncollinear_2Span

#eval phrase 13
def oriented_area : thm := keep "oriented_area" fun _ => (do
  nd ([[oriented_area (a:real^2,b:real^2,c:real^2) =
  ((b$1 - a$1) * (c$2 - a$2) - (c$1 - a$1) * (b$2 - a$2)) / &2]])
  : ExceptT String IO thm).run
#eval oriented_area

#eval phrase 14
def oriented_areaSymmetry : thm := keep "oriented_areaSymmetry" fun _ => (do
  prove ([[oriented_area (A,B,C) = oriented_area(A',B',C')  ==>
  oriented_area (B,C,A) = oriented_area (B',C',A')  /\
  oriented_area (C,A,B) = oriented_area (C',A',B')  /\
  oriented_area (A,C,B) = oriented_area (A',C',B')  /\
  oriented_area (B,A,C) = oriented_area (B',A',C')  /\
  oriented_area (C,B,A) = oriented_area (C',B',A')]])
   (REWRITE_TAC [oriented_area] THEN VEC2_TAC)
  : ExceptT String IO thm).run
#eval oriented_areaSymmetry

#eval phrase 15
def move : thm := keep "move" fun _ => (do
  nd ([[!A B C A' B' C':real^2. move (A,B,C) (A',B',C') <=>
  (B = B' /\ C = C' /\ collinear {vec 0,C - B,A' - A} \/
  A = A' /\ C = C' /\ collinear {vec 0,C - A,B' - B} \/
  A = A' /\ B = B' /\ collinear {vec 0,B - A,C' - C})]])
  : ExceptT String IO thm).run
#eval move

#eval phrase 16
def moveInvariant : thm := keep "moveInvariant" fun _ => (do
  prove ([[!p p'. move p p' ==> oriented_area p = oriented_area p']])
   (REWRITE_TAC [FORALL_PAIR_THM, move, oriented_area, COLLINEAR_LEMMA,  vector_mul] THEN VEC2_TAC)
  : ExceptT String IO thm).run
#eval moveInvariant

#eval phrase 17
def reachable : thm := keep "reachable" fun _ => (do
  nd ([[!p p'.
  reachable p p' <=> ?n. ?s.
  s 0 = p /\ s n = p' /\
  (!m. 0 <= m /\ m < n ==> move (s m) (s (SUC m)))]])
  : ExceptT String IO thm).run
#eval reachable

#eval phrase 18
def reachableN : thm := keep "reachableN" fun _ => (do
  nd ([[!p p'. !n.
  reachableN p p' n <=> ?s.
  s 0 = p /\ s n = p' /\
  (!m. 0 <= m /\ m < n ==> move (s m) (s (SUC m)))]])
  : ExceptT String IO thm).run
#eval reachableN

#eval phrase 19
def ReachLemma : thm := keep "ReachLemma" fun _ => (do
  prove ([[!p p'. reachable p p'  <=>  ?n.  reachableN p p' n]])
   (REWRITE_TAC [reachable, reachableN])
  : ExceptT String IO thm).run
#eval ReachLemma

#eval phrase 20
def reachableN_CLAUSES : thm := keep "reachableN_CLAUSES" fun _ => (do
  -- Right-to-left build order (see phrase 12).
  let c4 ← consider "s such that"
    ([[s 0 = p /\ s n = q /\ !m. m < n ==> move (s m) (s (SUC m))]])
    [HYP MESON_TAC "nReach" [reachableN, LT, LE_0]] "sDef"
  let c3 ← consider "q such that" ([[q:triple = s n]]) [MESON_TAC []]  "qDef"
  let c2 ← consider "s such that"
    ([[s 0 = p /\ s (SUC n) = p' /\ !m. m < SUC n ==> move (s m) (s (SUC m))]])
    [HYP MESON_TAC "H1" [LE_0, reachableN]] "sDef"
  let c1 ← consider "s0 such that" ([[s0 =  \m:num. p':triple]]) [MESON_TAC []] "s0exists"
  prove ([[! p p'. (reachableN p p' 0  <=>  p = p') /\
  ! n. reachableN p p' (SUC n)  <=>  ? q. reachableN p q n  /\ move q p']])
   (INTRO_TAC "!p p'" THEN
    c1 THEN
    SUBGOAL_TAC "0CLAUSE" ([[reachableN p p' 0  <=>  p = p']])
    [HYP MESON_TAC "s0exists" [LE_0, reachableN, LT]] THEN SUBGOAL_TAC "Imp1"
    ([[! n. reachableN p p' (SUC n)  ==>  ? q. reachableN p q n  /\ move q p']])
    [INTRO_TAC "!n; H1" THEN
    c2 THEN
    c3 THEN
    HYP MESON_TAC "sDef qDef" [LE_0, reachableN, LT]] THEN SUBGOAL_TAC "Imp2"
    ([[!n. (? q. reachableN p q n  /\ move q p')  ==>  reachableN p p' (SUC n)]])
    [INTRO_TAC "!n" THEN REWRITE_TAC [IMP_CONJ, LEFT_IMP_EXISTS_THM] THEN
    INTRO_TAC "!q; nReach; move_qp'" THEN
    c4 THEN
    REWRITE_TAC [reachableN, LT, LE_0] THEN
    EXISTS_TAC ([[\m. if m < SUC n then s m else p':triple]]) THEN
    HYP MESON_TAC "sDef move_qp'" [LT_0, LT_REFL, LT, LT_SUC]] THEN
    HYP MESON_TAC "0CLAUSE Imp1 Imp2" [])
  : ExceptT String IO thm).run
#eval reachableN_CLAUSES

#eval phrase 21
def reachableInvariant : thm := keep "reachableInvariant" fun _ => (do
  prove ([[!p p'. reachable p p'  ==>  oriented_area p = oriented_area p']])
   (SIMP_TAC [ReachLemma, LEFT_IMP_EXISTS_THM, SWAP_FORALL_THM] THEN
    INDUCT_TAC THEN ASM_MESON_TAC [reachableN_CLAUSES, moveInvariant])
  : ExceptT String IO thm).run
#eval reachableInvariant

#eval phrase 22
def move2Cond : thm := keep "move2Cond" fun _ => (do
  nd ([[! A B A' B':real^2. move2Cond A B A' B'  <=>
  ~collinear {B,A,A'} /\ ~collinear {A',B,B'}   \/
  ~collinear {A,B,B'} /\ ~collinear {B',A,A'}]])
  : ExceptT String IO thm).run
#eval move2Cond

#eval phrase 23
def reachableN_One : thm := keep "reachableN_One" fun _ => (do
  prove ([[reachableN P0 P1 1 <=> move P0 P1]])
   (MESON_TAC [ONE, reachableN, reachableN_CLAUSES])
  : ExceptT String IO thm).run
#eval reachableN_One

#eval phrase 24
def reachableN_Two : thm := keep "reachableN_Two" fun _ => (do
  prove ([[reachableN P0 P2 2 <=> ?P1. move P0 P1 /\ move P1 P2]])
   (MESON_TAC [TWO, reachableN_One, reachableN_CLAUSES])
  : ExceptT String IO thm).run
#eval reachableN_Two

#eval phrase 25
def reachableN_Three : thm := keep "reachableN_Three" fun _ => (do
  let b1 ← ar ([[3 = SUC 2]])
  prove ([[reachableN P0 P3 3  <=>  ?P1 P2. move P0 P1 /\ move P1 P2 /\ move P2 P3]])
   (MESON_TAC [b1, reachableN_Two, reachableN_CLAUSES])
  : ExceptT String IO thm).run
#eval reachableN_Three

#eval phrase 26
def reachableN_Four : thm := keep "reachableN_Four" fun _ => (do
  let b1 ← ar ([[4 = SUC 3]])
  prove ([[reachableN P0 P4 4  <=>  ?P1 P2 P3. move P0 P1 /\ move P1 P2 /\
  move P2 P3 /\ move P3 P4]])
   (MESON_TAC [b1, reachableN_Three, reachableN_CLAUSES])
  : ExceptT String IO thm).run
#eval reachableN_Four

#eval phrase 27
def reachableN_Five : thm := keep "reachableN_Five" fun _ => (do
  let b1 ← ar ([[5 = SUC 4]])
  prove ([[reachableN P0 P5 5  <=>  ?P1 P2 P3 P4. move P0 P1 /\ move P1 P2 /\
  move P2 P3 /\ move P3 P4 /\ move P4 P5]])
   (REWRITE_TAC [b1, reachableN_CLAUSES] THEN
    MESON_TAC [reachableN_Four])
  : ExceptT String IO thm).run
#eval reachableN_Five

#eval phrase 28
def moveSymmetry : thm := keep "moveSymmetry" fun _ => (do
  prove ([[move (A,B,C) (A',B',C') ==>
  move (B,C,A) (B',C',A') /\ move (C,A,B) (C',A',B') /\
  move (A,C,B) (A',C',B') /\ move (B,A,C) (B',A',C') /\ move (C,B,A) (C',B',A')]])
   (SUBGOAL_TAC "" ([[!A B C A':real^2. collinear {vec 0, C - B, A' - A}
    ==> collinear {vec 0, B - C, A' - A}]])
    [REWRITE_TAC [COLLINEAR_3_2Dzero] THEN VEC2_TAC] THEN
    so (REWRITE_TAC [move]) THEN MESON_TAC [])
  : ExceptT String IO thm).run
#eval moveSymmetry

#eval phrase 29
def reachableNSymmetry : thm := keep "reachableNSymmetry" fun _ => (do
  prove ([[! n. ! A B C A' B' C'. reachableN (A,B,C) (A',B',C') n  ==>
reachableN (B,C,A) (B',C',A') n  /\  reachableN (C,A,B) (C',A',B') n /\
reachableN (A,C,B) (A',C',B') n  /\  reachableN (B,A,C) (B',A',C') n /\
reachableN (C,B,A) (C',B',A') n]])
   (MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC [reachableN_CLAUSES] THEN
    SIMP_TAC [PAIR_EQ] THEN
    INTRO_TAC "!n;nStep; !A B C A' B' C'" THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM, FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [([[X:real^2]]), ([[Y:real^2]]), ([[Z:real^2]])] THEN
    INTRO_TAC "XYZexists" THEN
    REWRITE_TAC [RIGHT_AND_EXISTS_THM, LEFT_AND_EXISTS_THM] THEN
    MAP_EVERY EXISTS_TAC [([[(Y,Z,X):triple]]), ([[(Z,X,Y):triple]]),
    ([[(X,Z,Y):triple]]), ([[(Y,X,Z):triple]]), ([[(Z,Y,X):triple]])] THEN
    HYP SIMP_TAC "nStep XYZexists" [moveSymmetry])
  : ExceptT String IO thm).run
#eval reachableNSymmetry

#eval phrase 30
def ORIENTED_AREA_COLLINEAR_CONG : thm := keep "ORIENTED_AREA_COLLINEAR_CONG" fun _ => (do
  prove ([[! A B C A' B' C.
        oriented_area (A,B,C) = oriented_area (A',B',C')
        ==> (collinear {A,B,C} <=> collinear {A',B',C'})]])
   (REWRITE_TAC [COLLINEAR_3_2D, oriented_area] THEN CONV_TAC REAL_RING)
  : ExceptT String IO thm).run
#eval ORIENTED_AREA_COLLINEAR_CONG

#eval phrase 31
def Basic2move_THM : thm := keep "Basic2move_THM" fun _ => (do
  -- Right-to-left build order (see phrase 12).
  let c2 ← consider "s X such that" ([[s = r / t  /\  X:real^2 = C + s % (A - B)]])
    [HYP MESON_TAC "rExists" []] "Xexists"
  let c1 ← consider "r t such that" ([[A' - (A:real^2) = r % (A - B) + t % (C - B)]])
    [HYP MESON_TAC "H1" [COLLINEAR_3, Noncollinear_2Span]] "rExists"
  prove ([[! A B C A'. ~collinear {A,B,C} /\ ~collinear {B,A,A'} ==>
  ?X. move (A,B,C) (A,B,X)  /\  move (A,B,X) (A',B,X)]])
   (INTRO_TAC "!A B C A'; H1 H2" THEN SUBGOAL_TAC "add0vector_mul"
    ([[!r. r % ((A:real^2) - B) = (--r) % (B - A)  /\
    r % (A - B) = r % (A - B) + &0 % (C - B)]]) [VEC2_TAC] THEN
    SUBGOAL_TAC "H2'" ([[~ ? r. A' - (A:real^2) = r % (A - B)]])
    [so (HYP MESON_TAC "H2" [COLLINEAR_3, COLLINEAR_LEMMA])] THEN
    c1 THEN
    SUBGOAL_TAC "tNonzero" ([[~(t = &0)]])
    [so (HYP MESON_TAC "add0vector_mul H2'" [])] THEN
    c2 THEN
    SUBGOAL_TAC "" ([[A' - (A:real^2) = (t * s) % (A - B) + t % (C - B)]])
    [so (HYP MESON_TAC "rExists tNonzero" [REAL_DIV_LMUL])] THEN SUBGOAL_TAC ""
    ([[A' - (A:real^2) = t % (X - B) /\ X - C = (-- s) % (B - (A:real^2))]])
    [(so (HYP REWRITE_TAC "Xexists" [])) THEN VEC2_TAC] THEN SUBGOAL_TAC ""
    ([[collinear {vec 0,B - (A:real^2),X - C}  /\  collinear {vec 0,X - B,A' - A}]])
    [so (HYP MESON_TAC "" [COLLINEAR_LEMMA])] THEN so (MESON_TAC [move]))
  : ExceptT String IO thm).run
#eval Basic2move_THM

#eval phrase 32
def FourStepMoveAB : thm := keep "FourStepMoveAB" fun _ => (do
  let c2 ← consider "Y such that" ([[move (B,A',X) (B,A',Y)  /\  move (B,A',Y) (B',A',Y)]])
    [so (HYP MESON_TAC "H2" [Basic2move_THM])]  "BA'Y"
  let c1 ← consider "X such that" ([[move (A,B,C) (A,B,X)  /\  move (A,B,X) (A',B,X)]])
    [HYP MESON_TAC "H1 H2" [Basic2move_THM]] "ABX"
  prove ([[!A B C A' B'. ~collinear {A,B,C} ==>
  ~collinear {B,A,A'} /\ ~collinear {A',B,B'} ==>
  ? X Y. move (A,B,C) (A,B,X)  /\  move (A,B,X) (A',B,X)  /\
  move (A',B,X) (A',B,Y)  /\  move (A',B,Y) (A',B',Y)]])
   (INTRO_TAC "!A B C A' B'; H1; H2" THEN
    c1 THEN
    SUBGOAL_TAC "" ([[~collinear {(A:real^2),B,X} /\ ~collinear {A',B,X}]])
    [so (HYP MESON_TAC "H1" [moveInvariant, ORIENTED_AREA_COLLINEAR_CONG])]
    THEN SUBGOAL_TAC "" ([[~collinear {(B:real^2),A',X}]])
    [so (MESON_TAC [collinearSymmetry])] THEN
    c2 THEN
    SUBGOAL_TAC "" ([[move (A',B,X) (A',B,Y)  /\  move (A',B,Y) (A',B',Y)]])
    [HYP MESON_TAC "BA'Y" [moveSymmetry]] THEN so (HYP MESON_TAC "ABX" []))
  : ExceptT String IO thm).run
#eval FourStepMoveAB

#eval phrase 33
def FourStepMoveABBAreach : thm := keep "FourStepMoveABBAreach" fun _ => (do
  let c1 ← consider "X Y such that"
    ([[move (B,A,C) (B,A,X)  /\  move (B,A,X) (B',A,X)  /\
    move (B',A,X) (B',A,Y)  /\  move (B',A,Y) (B',A',Y)]])
    [so (HYP MESON_TAC "Case2" [FourStepMoveAB])] "BAX"
  prove ([[!A B C A' B'. ~collinear {A,B,C} /\ move2Cond A B A' B' ==>
  ? Y. reachableN (A,B,C) (A',B',Y) 4]])
   (INTRO_TAC "!A B C A' B'; H1 H2" THEN
    cases "Case1 | Case2"
    ([[~collinear {B,(A:real^2),A'} /\ ~collinear {A',B,B'}  \/
    ~collinear {A,B,B'} /\ ~collinear {B',A,A'}]])
    [HYP MESON_TAC "H2" [move2Cond]]
    THENL
    [so (HYP MESON_TAC "H1" [FourStepMoveAB, reachableN_Four]),
    SUBGOAL_TAC "" ([[~collinear {B,(A:real^2),C}]])
    [HYP MESON_TAC "H1" [collinearSymmetry]]] THEN
    SUBGOAL_TAC "" ([[~collinear {B,(A:real^2),C}]])
    [HYP MESON_TAC "H1" [collinearSymmetry]] THEN
    c1 THEN
    HYP MESON_TAC "BAX" [moveSymmetry, reachableN_Four])
  : ExceptT String IO thm).run
#eval FourStepMoveABBAreach

#eval phrase 34
def NotMove2ImpliesCollinear : thm := keep "NotMove2ImpliesCollinear" fun _ => (do
  prove ([[!A B C A' B' C'. ~collinear {A,B,C} /\ ~collinear {A',B',C'} /\
  ~(A = A') /\ ~(B = B') /\ ~move2Cond A B A' B' ==>
  collinear {A,B,A',B'}]])
   (INTRO_TAC "!A B C A' B' C'; H1 H1' H2 H2' H3" THEN
    SUBGOAL_TAC "Distinct" ([[~((A:real^2) = B) /\ ~((A':real^2) = B')]])
    [HYP MESON_TAC "H1 H1'" [Noncollinear_3ImpliesDistinct]] THEN
    SUBGOAL_TAC "set4symmetry" ([[{(A:real^2),B,A',B'} SUBSET {A,A',B,B'}  /\
    {A,B,A',B'} SUBSET {B,B',A',A}  /\  {A,B,A',B'} SUBSET {A',B',B,A}]]) [SET_TAC []] THEN
    cases "Case1 | Case2 | Case3 | Case4"
    ([[collinear {B,(A:real^2),A'} /\ collinear {A,B,B'}  \/
    collinear {B,A,A'} /\ collinear {B',A,A'}  \/
    collinear {A',B,B'} /\ collinear {A,B,B'}  \/
    collinear {A',B,B'} /\ collinear {B',A,A'}]])
    [HYP MESON_TAC "H3" [move2Cond]] THEN
    so (HYP MESON_TAC "Distinct H2 H2' set4symmetry"
    [collinearSymmetry, COLLINEAR_4_3, COLLINEAR_SUBSET]))
  : ExceptT String IO thm).run
#eval NotMove2ImpliesCollinear

#eval phrase 35
def DistinctImplies2moveable : thm := keep "DistinctImplies2moveable" fun _ => (do
  prove ([[!A B C A' B' C'. ~collinear {A,B,C} /\ ~collinear {A',B',C'} /\
  ~(A = A') /\ ~(B = B') /\ ~(C = C')  ==>
  move2Cond A B A' B' \/ move2Cond B C B' C']])
   (INTRO_TAC "!A B C A' B' C'; H1 H1' H2a H2b H2c" THEN SUBGOAL_TAC "3subset4"
    ([[{(A:real^2),B,B'} SUBSET {A,B,A',B'} /\ {B,B',C} SUBSET {B,C,B',C'}]])
    [SET_TAC []] THEN
    raa "Con" ([[~move2Cond A B A' B'  /\
    ~move2Cond B C B' C']]) (HYP MESON_TAC "Con" []) THEN
    SUBGOAL_TAC "" ([[collinear {(A:real^2),B,A',B'} /\ collinear {B,C,B',C'}]])
    [so (HYP MESON_TAC "H1 H1' H2a H2b H2c" [collinearSymmetry, NotMove2ImpliesCollinear])]
    THEN SUBGOAL_TAC "" ([[collinear {(A:real^2),B,C}]])
    [so (HYP MESON_TAC "3subset4 H2a H2b H2c" [COLLINEAR_SUBSET, COLLINEAR_3_TRANS])]
    THEN so (HYP MESON_TAC "H1 H1'" []))
  : ExceptT String IO thm).run
#eval DistinctImplies2moveable

#eval phrase 36
def SameCdiffAB : thm := keep "SameCdiffAB" fun _ => (do
  let c1 ← consider "X such that" ([[move (B,C,A) (B,C,X) /\ move (B,C,X) (B',C',X)]])
    [so (HYP MESON_TAC "easy_set H1 H2" [collinearSymmetry, Basic2move_THM])] "BCX"
  prove ([[!A B C A' B' C'.  ~collinear {A,B,C} /\ ~collinear {A',B',C'} ==>
 C = C' /\ ~(A = A') /\ ~(B = B') ==>
  ? Y. reachableN (A,B,C) (Y,B',C') 2  \/ reachableN (A,B,C) (A',B',Y) 4]])
   (INTRO_TAC "!A B C A' B' C'; H1; H2" THEN SUBGOAL_TAC "easy_set"
    ([[{B,B',(A:real^2)} SUBSET {A,B,A',B'}  /\  {A,B,C} SUBSET {B,B',A,C}]]) [SET_TAC []]  THEN
    cases "Ncol | move | col_Nmove"
    ([[~collinear {C,B,B'}  \/
    move2Cond A B A' B'  \/
    collinear {C,B,B'} /\ ~move2Cond A B A' B']])
    [MESON_TAC []] THENL
    [c1
    THEN HYP MESON_TAC "BCX" [reachableN_Two, reachableNSymmetry],
    so (HYP MESON_TAC "H1" [FourStepMoveABBAreach]),
    SUBGOAL_TAC "" ([[collinear {(B:real^2),B',A} /\ collinear {B,B',C}]])
    [so (HYP MESON_TAC "H1 H2 easy_set"
    [NotMove2ImpliesCollinear, COLLINEAR_SUBSET, collinearSymmetry])]  THEN
    so (HYP MESON_TAC "H2 easy_set H1" [COLLINEAR_4_3, COLLINEAR_SUBSET])])
  : ExceptT String IO thm).run
#eval SameCdiffAB

#eval phrase 37
def FourMovesToCorrectTwo : thm := keep "FourMovesToCorrectTwo" fun _ => (do
  prove ([[!A B C A' B' C'. ~collinear {A,B,C} /\ ~collinear {A',B',C'} ==>
  ? n. n < 5 /\ ? Y. reachableN (A,B,C) (A',B',Y) n  \/
  reachableN (A,B,C) (A',Y,C') n  \/ reachableN (A,B,C) (Y,B',C') n]])
   (INTRO_TAC "!A B C A' B' C'; H1" THEN
    SUBGOAL_TAC "H1'" ([[~collinear {B,C,(A:real^2)} /\
    ~collinear{B',C',(A':real^2)} /\ ~collinear {C,A,B} /\ ~collinear {C',A',B'}]])
    [HYP MESON_TAC "H1" [collinearSymmetry]]   THEN
    SUBGOAL_TAC "easy_arith" ([[0 < 5 /\ 2 < 5 /\ 3 < 5 /\ 4 < 5]]) [ARITH_TAC] THEN
    cases "case01 | case2 | case3"
    ([[((A:real^2) = A' /\ (B:real^2) = B' /\ (C:real^2) = C'  \/
    A = A' /\ B = B' /\ ~(C = C')  \/  A = A' /\ ~(B = B') /\ C = C' \/
    ~(A = A') /\ B = B' /\ C = C')  \/
    (A = A' /\ ~(B = B') /\ ~(C = C')  \/
    ~(A = A') /\ B = B' /\ ~(C = C')  \/  ~(A = A') /\ ~(B = B') /\ C = C')  \/
    ~(A = A') /\ ~(B = B') /\ ~(C = C')]])
    [MESON_TAC []] THENL
    [so (HYP MESON_TAC "easy_arith" [reachableN_CLAUSES]),
    so (HYP MESON_TAC "H1 H1' easy_arith" [SameCdiffAB, reachableNSymmetry]),
    EXISTS_TAC ([[4]]) THEN HYP SIMP_TAC "easy_arith" [] THEN
    so (HYP MESON_TAC "H1  H1'" [DistinctImplies2moveable, FourStepMoveABBAreach,
    reachableNSymmetry, reachableN_Four])])
  : ExceptT String IO thm).run
#eval FourMovesToCorrectTwo

#eval phrase 38
def CorrectFinalPoint : thm := keep "CorrectFinalPoint" fun _ => (do
  prove ([[oriented_area (A,B,C) = oriented_area (A,B,C') ==>
  move (A,B,C) (A,B,C')]])
   (REWRITE_TAC [move, oriented_area, COLLINEAR_3_2Dzero]  THEN VEC2_TAC)
  : ExceptT String IO thm).run
#eval CorrectFinalPoint

#eval phrase 39
def FiveMovesOrLess : thm := keep "FiveMovesOrLess" fun _ => (do
  let c1 ← consider "n Y such that"
    ([[n < 5 /\ (reachableN (A,B,C) (A',B',Y) n \/
    reachableN (A,B,C) (A',Y,C') n \/ reachableN (A,B,C) (Y,B',C') n)]])
    [HYP MESON_TAC "H1 H1'" [FourMovesToCorrectTwo]] "2Correct"
  prove ([[!A B C A' B' C'. ~collinear {A,B,C} ==>
  oriented_area (A,B,C) = oriented_area (A',B',C') ==>
  ? n. n <= 5 /\ reachableN (A,B,C) (A',B',C') n]])
   (INTRO_TAC "!A B C A' B' C'; H1; H2"  THEN
    SUBGOAL_TAC "H1'" ([[~collinear {(A':real^2),B',C'}]])
    [HYP MESON_TAC "H1 H2" [ORIENTED_AREA_COLLINEAR_CONG]]  THEN
    SUBGOAL_TAC "Distinct" ([[~((A:real^2) = B) /\ ~(A = C) /\ ~(B = C) /\
    ~((A':real^2) = B') /\ ~(A' = C') /\ ~(B' = C')]])
    [so (HYP MESON_TAC "H1" [Noncollinear_3ImpliesDistinct])]  THEN
    c1 THEN
    cases "A'B'Y | A'YC' | YB'C'"
    ([[reachableN (A,B,C) (A',B',Y) n  \/
    reachableN (A,B,C) (A',Y,C') n  \/
    reachableN (A,B,C) (Y,B',C') n]]) [HYP MESON_TAC "2Correct" []] THENL
    [SUBGOAL_TAC "" ([[oriented_area (A',B',Y) = oriented_area (A',B',C')]])
    [so (HYP MESON_TAC "H2" [ReachLemma, reachableInvariant])]  THEN
    SUBGOAL_TAC "" ([[move (A',B',Y) (A',B',C')]])
    [so (HYP MESON_TAC "Distinct" [CorrectFinalPoint])]  THEN
    so (HYP MESON_TAC "A'B'Y 2Correct" [reachableN_CLAUSES, LE_SUC_LT]),
    SUBGOAL_TAC "" ([[oriented_area (A',C',Y) = oriented_area (A',C',B')]])
    [so (HYP MESON_TAC "H2" [ReachLemma, reachableInvariant, oriented_areaSymmetry])]
    THEN SUBGOAL_TAC "" ([[move (A',Y,C') (A',B',C')]])
    [so (HYP MESON_TAC "Distinct" [CorrectFinalPoint, moveSymmetry])]  THEN
    so (HYP MESON_TAC "A'YC' 2Correct" [reachableN_CLAUSES, LE_SUC_LT]),
  SUBGOAL_TAC "" ([[oriented_area (B',C',Y) = oriented_area (B',C',A')]])
    [so (HYP MESON_TAC "H2" [ReachLemma, reachableInvariant, oriented_areaSymmetry])]
    THEN SUBGOAL_TAC "" ([[move (Y,B',C') (A',B',C')]])
    [so (HYP MESON_TAC "Distinct" [CorrectFinalPoint, moveSymmetry])]  THEN
    so (HYP MESON_TAC "YB'C' 2Correct" [reachableN_CLAUSES, LE_SUC_LT])])
  : ExceptT String IO thm).run
#eval FiveMovesOrLess

#eval phrase 40
def NOTENOUGH_4 : thm := keep "NOTENOUGH_4" fun _ => (do
  let c1 ← consider "p0 p4 such that"
    ([[p0:triple = vector [&0;&0],vector [&0;&1],vector [&1;&0]  /\
    p4:triple = vector [&1;&1],vector [&1;&2],vector [&2;&1] ]])
    [MESON_TAC []] "p04Def"
  prove ([[?p0 p4. oriented_area p0 = oriented_area p4 /\ ~reachableN p0 p4 4]])
   (c1 THEN
    SUBGOAL_TAC "equal_areas" ([[oriented_area p0 = oriented_area p4]])
    [HYP REWRITE_TAC "p04Def" [oriented_area] THEN VEC2_TAC] THEN
    SUBGOAL_TAC "" ([[~reachableN p0 p4 4]])
    [HYP REWRITE_TAC "p04Def" [reachableN_Four, NOT_EXISTS_THM, FORALL_PAIR_THM,  move, COLLINEAR_3_2Dzero, FORALL_VECTOR_2] THEN VEC2_TAC] THEN
    so (HYP MESON_TAC "equal_areas" []))
  : ExceptT String IO thm).run
#eval NOTENOUGH_4

#eval phrase 41
def FiveMovesOrLess_STRONG : thm := keep "FiveMovesOrLess_STRONG" fun _ => (do
  let c1 ← consider "P1 P2 P3 P4 such that"
    ([[P1:triple = A,C,C  /\  P2:triple = B',C,C  /\  P3 = B',B',C  /\
    P4:triple = B',B',C']]) [MESON_TAC []] "P1234exist"
  prove ([[!A B C A' B' C'.
  oriented_area (A,B,C) = oriented_area (A',B',C') ==>
  ?n. n <= 5 /\ reachableN (A,B,C) (A',B',C') n]])
   (INTRO_TAC "!A B C A' B' C'; H1" THEN
    SUBGOAL_TAC "EZcollinear"
    ([[(!X Y:real^2. collinear {X,Y,Y}) /\
    (!A B A'. move (A,B,B) (A',B,B))  /\
    !A B C B'. (collinear {A,B,C} /\ collinear {A,B',C}  ==>
    move (A,B,C) (A,B',C))]])
    [REWRITE_TAC [move, COLLINEAR_3_2D] THEN VEC2_TAC] THEN
    cases "ABCncol | ABCcol"
    ([[~collinear {(A:real^2),B,C}  \/  collinear {A,B,C}]])
    [MESON_TAC []] THENL
    [so (HYP MESON_TAC "H1" [FiveMovesOrLess]),
    SUBGOAL_TAC "A'B'C'col" ([[collinear {(A':real^2),B',C'}]])
    [so (HYP MESON_TAC "H1" [ORIENTED_AREA_COLLINEAR_CONG])] THEN
    c1 THEN
    SUBGOAL_TAC "" ([[move (A,B,C) (P1:triple)  /\  move P1 P2  /\
    move P2 P3  /\  move P3 P4  /\  move P4 (A',B',C')]])
    [HYP MESON_TAC "ABCcol A'B'C'col EZcollinear P1234exist"
    [collinearSymmetry, moveSymmetry]] THEN
    so (MESON_TAC [reachableN_Five, LE_REFL])])
  : ExceptT String IO thm).run
#eval FiveMovesOrLess_STRONG
end HolExamples.InverseBugPuzzleTac
