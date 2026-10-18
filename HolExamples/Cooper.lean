/- File: HolExamples/Cooper.lean
Translation of HOL Light's Examples/cooper.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.

Cooper's decision procedure for Presburger arithmetic, implemented via
proforma theorems (John Harrison).  The proforma theorems are proved with the
usual tactic scripts; the OCaml algorithm (syntax functions, the arithmetic
conversions, the shadow-syntax quantifier-elimination conversions and the
overall `COOPER_CONV`) is ported with the same names and the same algorithm.
HOL Light's kernel rules and conversions are `Except String` / `ExceptT String
IO`-valued here, so OCaml's `failwith`/`try ... with Failure _` control flow
becomes `Except`/`tryWith`, and the IO conversion combinators
(`THENC`, `RAND_CONV`, `GEN_REWRITE_CONV`, ...) come from HolMath/Base.lean.
-/
import HolExamples.Common
open HolCore.Kernel HolCore.Lib HolCore.Basics Session HolLight.Syntax
     HolExamples
open scoped HolLight
namespace HolExamples.Cooper

/- Helpers: the session's IO-valued rules lifted into `ExceptT String IO`, so
   the term-building functions and tactic scripts read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ec {α : Type} (x : Except String α) : ExceptT String IO α := ExceptT.mk (pure x)

/-- Proforma lemma: prove, cache and print as the OCaml toplevel's `let`. -/
private unsafe def proveThm (name : String) (g : term) (tac : HolCore.Tactics.tactic) : thm :=
  keep name fun _ =>
    match unsafeIO (Session.prove g tac) with
    | .ok (.ok th) => th
    | .ok (.error e) => panic! e
    | .error e => panic! (toString e)

/-- Cache an `ExceptT String IO thm` computation under `name` (a toplevel
    `let`), for lemmas whose tactic needs `INT_ARITH`/`TAUT` subterms built
    monadically first. -/
private unsafe def keepThm (name : String) (m : ExceptT String IO thm) : thm :=
  keep name fun _ =>
    match unsafeIO m.run with
    | .ok (.ok th) => th
    | .ok (.error e) => panic! e
    | .error e => panic! (toString e)

/-- Cache a value built by an `ExceptT String IO` computation (a toplevel
    `let` whose right-hand side builds conversions/data from proved theorems). -/
private unsafe def keepE {α : Type} [Inhabited α] (name : String)
    (m : ExceptT String IO α) : α :=
  keep name fun _ =>
    match unsafeIO m.run with
    | .ok (.ok v) => v
    | .ok (.error e) => panic! e
    | .error e => panic! (toString e)

#eval phrase 1
-- (* ===================================================================== *)
-- (* Implementation of Cooper's algorithm via proforma theorems.          *)
-- (* ===================================================================== *)
#eval prioritize_int

#eval phrase 2
-- (* Basic syntax on integer terms. *)
-- let dest_mul = dest_binop `(*)`;;
unsafe def dest_mul : term → Except String (term × term) :=
  dest_binop [[( * )]]
#eval IO.println "<fun>"

#eval phrase 3
-- let dest_add = dest_binop `(+)`;;
unsafe def dest_add : term → Except String (term × term) :=
  dest_binop [[(+)]]
#eval IO.println "<fun>"

#eval phrase 4
-- (* Divisibility. *)
-- parse_as_infix("divides",(12,"right"));;
#eval parse_as_infix ("divides", (12, "right"))

#eval phrase 5
-- let divides = new_definition
--   `a divides b <=> ?x. b = a * x`;;
unsafe def divides : thm := keep "divides" fun _ => (do
  ExceptT.mk (new_definition [[a divides b <=> ?x. b = a * x]])
  : ExceptT String IO thm).run
#eval divides

#eval phrase 6
-- (* Trivial lemmas about integers. *)
-- let INT_DOWN2 = prove ...
unsafe def INT_DOWN2 : thm := proveThm "INT_DOWN2"
  ([[!a b. ?c. !x. x < c ==> x < a /\ x < b]])
  (MESON_TAC [INT_LE_TOTAL, INT_LET_TRANS])
#eval INT_DOWN2

#eval phrase 7
-- (* Trivial lemmas about divisibility. *)
-- let DIVIDES_ADD = prove ...
unsafe def DIVIDES_ADD : thm := proveThm "DIVIDES_ADD"
  ([[!d a b. d divides a /\ d divides b ==> d divides (a + b)]])
  (MESON_TAC [divides, INT_ADD_LDISTRIB])
#eval DIVIDES_ADD

#eval phrase 8
-- let DIVIDES_SUB = prove ...
unsafe def DIVIDES_SUB : thm := proveThm "DIVIDES_SUB"
  ([[!d a b. d divides a /\ d divides b ==> d divides (a - b)]])
  (MESON_TAC [divides, INT_SUB_LDISTRIB])
#eval DIVIDES_SUB

#eval phrase 9
-- let DIVIDES_ADD_REVR = prove ...
unsafe def DIVIDES_ADD_REVR : thm := keepThm "DIVIDES_ADD_REVR" (do
  prove ([[!d a b. d divides a /\ d divides (a + b) ==> d divides b]])
    (MESON_TAC [DIVIDES_SUB, (← ExceptT.mk (INT_ARITH [[(a + b) - a = b]]))]))
#eval DIVIDES_ADD_REVR

#eval phrase 10
-- let DIVIDES_ADD_REVL = prove ...
unsafe def DIVIDES_ADD_REVL : thm := keepThm "DIVIDES_ADD_REVL" (do
  prove ([[!d a b. d divides b /\ d divides (a + b) ==> d divides a]])
    (MESON_TAC [DIVIDES_SUB, (← ExceptT.mk (INT_ARITH [[(a + b) - b = a]]))]))
#eval DIVIDES_ADD_REVL

#eval phrase 11
-- let DIVIDES_LMUL = prove ...
unsafe def DIVIDES_LMUL : thm := keepThm "DIVIDES_LMUL" (do
  prove ([[!d a x. d divides a ==> d divides (x * a)]])
    (ASM_MESON_TAC [divides, (← ExceptT.mk (INT_ARITH [[a * b * c = b * a * c]]))]))
#eval DIVIDES_LMUL

#eval phrase 12
-- let DIVIDES_RNEG = prove ...
unsafe def DIVIDES_RNEG : thm := proveThm "DIVIDES_RNEG"
  ([[!d a. d divides (--a) <=> d divides a]])
  (REWRITE_TAC [divides] THEN MESON_TAC [INT_MUL_RNEG, INT_NEG_NEG])
#eval DIVIDES_RNEG

#eval phrase 13
-- let DIVIDES_LNEG = prove ...
unsafe def DIVIDES_LNEG : thm := proveThm "DIVIDES_LNEG"
  ([[!d a. (--d) divides a <=> d divides a]])
  (REWRITE_TAC [divides] THEN
   MESON_TAC [INT_MUL_RNEG, INT_MUL_LNEG, INT_NEG_NEG])
#eval DIVIDES_LNEG

#eval phrase 14
-- (* More specialized lemmas (see footnotes on p4 and p5). *)
-- let INT_DOWN_MUL_LT = prove ...
unsafe def INT_DOWN_MUL_LT : thm := keepThm "INT_DOWN_MUL_LT" (do
  prove ([[!x y d. &0 < d ==> ?c. x + c * d < y]])
    (MESON_TAC [INT_ARCH, INT_LT_REFL,
                (← ExceptT.mk (INT_ARITH [[x - y < c * d <=> x + --c * d < y]]))]))
#eval INT_DOWN_MUL_LT

#eval phrase 15
-- let INT_MOD_LEMMA = prove ...
unsafe def INT_MOD_LEMMA : thm := keepThm "INT_MOD_LEMMA" (do
  let a1 ← ExceptT.mk (INT_ARITH [[&0 < d ==> ~(d = &0)]])
  let a2 ← ExceptT.mk (INT_ARITH
    [[(&0 < --c1 ==> &0 < --cd) /\ xcod < &0
     ==> --xcod < cd ==> &0 <= c1]])
  let a3 ← ExceptT.mk (HolLight.GSYM INT_MUL_LNEG)
  let a4 ← ExceptT.mk (TAUT [[a /\ b <=> ~(a ==> ~b)]])
  let a5 ← ExceptT.mk (HolLight.GSYM NOT_FORALL_THM)
  let a6 ← ExceptT.mk (HolLight.GSYM INT_FORALL_POS)
  let a7 ← ExceptT.mk (INT_ARITH [[(--(x + a * d)) < b * d <=> &1 <= x + (a + b) * d]])
  let ar8 ← ExceptT.mk (ARITH_RULE [[SUC n - 1 = n]])
  let a9 ← ExceptT.mk (HolLight.GSYM INT_OF_NUM_SUC)
  prove ([[!d x. &0 < d ==> ?c. &1 <= x + c * d /\ x + c * d <= d]])
    (REPEAT STRIP_TAC THEN
     FIRST_ASSUM (MP_TAC o HolLight.SPECL [([[x:int]]), ([[&0]])] o HolLight.MATCH_MP INT_DOWN_MUL_LT) THEN
     DISCH_THEN (X_CHOOSE_TAC ([[c0:int]])) THEN
     SUBGOAL_THEN ([[?c1. &0 <= c1 /\ --(x + c0 * d) < c1 * d]]) MP_TAC THENL
      [SUBGOAL_THEN ([[?c1. --(x + c0 * d) < c1 * d]]) MP_TAC THENL
        [ASM_MESON_TAC [INT_ARCH, a1], ALL_TAC] THEN
       MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN SIMP_TAC [] THEN
       MATCH_MP_TAC a2 THEN
       ASM_SIMP_TAC [a3, INT_LT_MUL], ALL_TAC] THEN
     REWRITE_TAC [a4, a5] THEN
     REWRITE_TAC [a6] THEN
     REWRITE_TAC [NOT_FORALL_THM] THEN GEN_REWRITE_TAC HolLight.LAND_CONV [num_WOP] THEN
     REWRITE_TAC [a7] THEN
     DISCH_THEN (X_CHOOSE_THEN ([[n:num]]) STRIP_ASSUME_TAC) THEN
     EXISTS_TAC ([[c0 + &n]]) THEN ASM_REWRITE_TAC [] THEN
     FIRST_X_ASSUM (MP_TAC o SPEC ([[n - 1]])) THEN
     UNDISCH_TAC ([[&1 <= x + (c0 + &n) * d]]) THEN SPEC_TAC ([[n:num]], [[n:num]]) THEN
     INDUCT_TAC THEN REWRITE_TAC [ar8] THENL
      [REWRITE_TAC [SUB_0, LT_REFL, INT_ADD_RID] THEN
       POP_ASSUM_LIST (fun ths => HolLight.tactic_of do
         pure (MP_TAC (← HolLight.end_itlist HolLight.CONJ ths))) THEN INT_ARITH_TAC,
       REWRITE_TAC [a9, LT] THEN INT_ARITH_TAC]))
#eval INT_MOD_LEMMA

#eval phrase 16
-- (* Shadow for restricted class of formulas. *)
-- let cform_INDUCT,cform_RECURSION = define_type "cform = ...";;
unsafe def cform_INDUCT_cform_RECURSION : thm × thm := keep "cform_types" fun _ =>
  match unsafeIO (define_type
    "cform = Lt int
           | Gt int
           | Eq int
           | Ne int
           | Divides int int
           | Ndivides int int
           | And cform cform
           | Or cform cform
           | Nox bool") with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
unsafe def cform_INDUCT : thm := cform_INDUCT_cform_RECURSION.1
unsafe def cform_RECURSION : thm := cform_INDUCT_cform_RECURSION.2
#eval (do IO.println (← HolCore.Printer.string_of_thm cform_INDUCT)
          IO.println (← HolCore.Printer.string_of_thm cform_RECURSION) : IO Unit)

#eval phrase 17
-- (* Interpretation of a cform. *)
-- let interp = new_recursive_definition cform_RECURSION ...
unsafe def interp : thm := keep "interp" fun _ => (do
  ExceptT.mk (new_recursive_definition cform_RECURSION
   [[(interp x (Lt e) <=> x + e < &0) /\
     (interp x (Gt e) <=> x + e > &0) /\
     (interp x (Eq e) <=> (x + e = &0)) /\
     (interp x (Ne e) <=> ~(x + e = &0)) /\
     (interp x (Divides c e) <=> c divides (x + e)) /\
     (interp x (Ndivides c e) <=> ~(c divides (x + e))) /\
     (interp x (And p q) <=> interp x p /\ interp x q) /\
     (interp x (Or p q) <=> interp x p \/ interp x q) /\
     (interp x (Nox P) <=> P)]])
  : ExceptT String IO thm).run
#eval interp

#eval phrase 18
-- (* The "minus infinity" and "plus infinity" variants. *)
-- let minusinf = new_recursive_definition cform_RECURSION ...
unsafe def minusinf : thm := keep "minusinf" fun _ => (do
  ExceptT.mk (new_recursive_definition cform_RECURSION
   [[(minusinf (Lt e) = Nox T) /\
     (minusinf (Gt e) = Nox F) /\
     (minusinf (Eq e) = Nox F) /\
     (minusinf (Ne e) = Nox T) /\
     (minusinf (Divides c e) = Divides c e) /\
     (minusinf (Ndivides c e) = Ndivides c e) /\
     (minusinf (And p q) = And (minusinf p) (minusinf q)) /\
     (minusinf (Or p q) = Or (minusinf p) (minusinf q)) /\
     (minusinf (Nox P) = Nox P)]])
  : ExceptT String IO thm).run
#eval minusinf

#eval phrase 19
-- let plusinf = new_recursive_definition cform_RECURSION ...
unsafe def plusinf : thm := keep "plusinf" fun _ => (do
  ExceptT.mk (new_recursive_definition cform_RECURSION
   [[(plusinf (Lt e) = Nox F) /\
     (plusinf (Gt e) = Nox T) /\
     (plusinf (Eq e) = Nox F) /\
     (plusinf (Ne e) = Nox T) /\
     (plusinf (Divides c e) = Divides c e) /\
     (plusinf (Ndivides c e) = Ndivides c e) /\
     (plusinf (And p q) = And (plusinf p) (plusinf q)) /\
     (plusinf (Or p q) = Or (plusinf p) (plusinf q)) /\
     (plusinf (Nox P) = Nox P)]])
  : ExceptT String IO thm).run
#eval plusinf

#eval phrase 20
-- (* All the "dividing" things divide the given constant (e.g. their LCM). *)
-- let alldivide = new_recursive_definition cform_RECURSION ...
unsafe def alldivide : thm := keep "alldivide" fun _ => (do
  ExceptT.mk (new_recursive_definition cform_RECURSION
   [[(alldivide d (Lt e) <=> T) /\
     (alldivide d (Gt e) <=> T) /\
     (alldivide d (Eq e) <=> T) /\
     (alldivide d (Ne e) <=> T) /\
     (alldivide d (Divides c e) <=> c divides d) /\
     (alldivide d (Ndivides c e) <=> c divides d) /\
     (alldivide d (And p q) <=> alldivide d p /\ alldivide d q) /\
     (alldivide d (Or p q) <=> alldivide d p /\ alldivide d q) /\
     (alldivide d (Nox P) <=> T)]])
  : ExceptT String IO thm).run
#eval alldivide

#eval phrase 21
-- (* A-sets and B-sets. *)
-- let aset = new_recursive_definition cform_RECURSION ...
unsafe def aset : thm := keep "aset" fun _ => (do
  ExceptT.mk (new_recursive_definition cform_RECURSION
   [[(aset (Lt e) = {(--e)}) /\
     (aset (Gt e) = {}) /\
     (aset (Eq e) = {(--e + &1)}) /\
     (aset (Ne e) = {(--e)}) /\
     (aset (Divides c e) = {}) /\
     (aset (Ndivides c e) = {}) /\
     (aset (And p q) = (aset p) UNION (aset q)) /\
     (aset (Or p q) = (aset p) UNION (aset q)) /\
     (aset (Nox P) = {})]])
  : ExceptT String IO thm).run
#eval aset

#eval phrase 22
-- let bset = new_recursive_definition cform_RECURSION ...
unsafe def bset : thm := keep "bset" fun _ => (do
  ExceptT.mk (new_recursive_definition cform_RECURSION
   [[(bset (Lt e) = {}) /\
     (bset (Gt e) = {(--e)}) /\
     (bset (Eq e) = {(--(e + &1))}) /\
     (bset (Ne e) = {(--e)}) /\
     (bset (Divides c e) = {}) /\
     (bset (Ndivides c e) = {}) /\
     (bset (And p q) = (bset p) UNION (bset q)) /\
     (bset (Or p q) = (bset p) UNION (bset q)) /\
     (bset (Nox P) = {})]])
  : ExceptT String IO thm).run
#eval bset

#eval phrase 23
-- (* The key minimality case analysis for the integers. *)
-- let INT_EXISTS_CASES = prove ...
unsafe def INT_EXISTS_CASES : thm := keepThm "INT_EXISTS_CASES" (do
  let t1 ← ExceptT.mk (TAUT [[(~b ==> a) ==> a \/ b]])
  let t2 ← ExceptT.mk (TAUT [[~(p /\ q) <=> p ==> ~q]])
  let i1 ← ExceptT.mk (INT_ARITH [[x < y \/ &0 <= x - y]])
  let i2 ← ExceptT.mk (INT_ARITH [[x - (x - y) = y]])
  let i3 ← ExceptT.mk (INT_ARITH [[z < y /\ y < x - &n ==> z < x - (&n + &1)]])
  prove ([[(?x. P x) <=> (!y. ?x. x < y /\ P x) \/ (?x. P x /\ !y. y < x ==> ~P y)]])
    (EQ_TAC THENL [ALL_TAC, MESON_TAC []] THEN
     DISCH_THEN (X_CHOOSE_TAC ([[x:int]])) THEN
     MATCH_MP_TAC t1 THEN
     REWRITE_TAC [NOT_EXISTS_THM, t2, NOT_FORALL_THM, NOT_IMP] THEN
     STRIP_TAC THEN X_GEN_TAC ([[y:int]]) THEN
     DISJ_CASES_TAC i1 THENL
      [ASM_MESON_TAC [], ALL_TAC] THEN
     SUBGOAL_THEN ([[!n. ?y. y < x - &n /\ P y]]) MP_TAC THENL
      [ALL_TAC,
       REWRITE_TAC [INT_FORALL_POS] THEN
       DISCH_THEN (MP_TAC o SPEC ([[x - y]])) THEN
       ASM_REWRITE_TAC [i2]] THEN
     INDUCT_TAC THEN
     REWRITE_TAC [INT_SUB_RZERO, (← ExceptT.mk (HolLight.GSYM INT_OF_NUM_SUC))] THEN
     ASM_MESON_TAC [i3]))
#eval INT_EXISTS_CASES

#eval phrase 24
-- (* Lemmas towards the main theorems (following my book). *)
-- let MINUSINF_LEMMA = prove ...
unsafe def MINUSINF_LEMMA : thm := keepThm "MINUSINF_LEMMA" (do
  let t1 ← ExceptT.mk (TAUT
    [[(a /\ b /\ c /\ d) /\ (e /\ f) ==> a /\ b /\ c /\ d /\ e /\ f]])
  let i1 ← ExceptT.mk (INT_ARITH [[x < --a ==> x + a < &0]])
  prove ([[!p. ?y. !x. x < y ==> (interp x p <=> interp x (minusinf p))]])
    (MATCH_MP_TAC cform_INDUCT THEN
     REWRITE_TAC [interp, minusinf] THEN
     MATCH_MP_TAC t1 THEN
     CONJ_TAC THENL
      [MESON_TAC [i1, INT_GT, INT_LT_ANTISYM, INT_LT_REFL],
       ALL_TAC] THEN
     CONJ_TAC THEN REPEAT GEN_TAC THEN
     REWRITE_TAC [LEFT_AND_EXISTS_THM,
        RIGHT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
     MAP_EVERY X_GEN_TAC [([[a:int]]), ([[b:int]])] THEN STRIP_TAC THEN
     MP_TAC (← ExceptT.mk (HolLight.SPECL [([[a:int]]), ([[b:int]])] INT_DOWN2)) THEN
     MATCH_MP_TAC MONO_EXISTS THEN ASM_SIMP_TAC []))
#eval MINUSINF_LEMMA

#eval phrase 25
-- let MINUSINF_REPEATS = prove ...
unsafe def MINUSINF_REPEATS : thm := keepThm "MINUSINF_REPEATS" (do
  let i1 ← ExceptT.mk (INT_ARITH [[(x + d) + y = (x + y) + d]])
  prove ([[!p c d x. alldivide d p
              ==> (interp x (minusinf p) <=> interp (x + c * d) (minusinf p))]])
    (CONV_TAC (HolLight.ONCE_DEPTH_CONV HolLight.SYM_CONV) THEN MATCH_MP_TAC cform_INDUCT THEN
     SIMP_TAC [interp, minusinf, alldivide] THEN
     ONCE_REWRITE_TAC [i1] THEN
     MESON_TAC [DIVIDES_LMUL, DIVIDES_ADD_REVL, DIVIDES_ADD]))
#eval MINUSINF_REPEATS

#eval phrase 26
-- let NOMINIMAL_EQUIV = prove ...
unsafe def NOMINIMAL_EQUIV : thm := proveThm "NOMINIMAL_EQUIV"
  ([[alldivide d p /\ &0 < d
     ==> ((!y. ?x. x < y /\ interp x p) <=>
          ?j. &1 <= j /\ j <= d /\ interp j (minusinf p))]])
  (ASM_MESON_TAC [MINUSINF_LEMMA, MINUSINF_REPEATS, INT_DOWN_MUL_LT,
                  INT_DOWN2, INT_MOD_LEMMA])
#eval NOMINIMAL_EQUIV

#eval phrase 27
-- let BDISJ_REPEATS_LEMMA = prove ...
unsafe def BDISJ_REPEATS_LEMMA : thm := keepThm "BDISJ_REPEATS_LEMMA" (do
  let t0 ← ExceptT.mk (TAUT [[a /\ b ==> c <=> b ==> a ==> c]])
  let t1 ← ExceptT.mk (TAUT [[(a /\ b /\ c /\ d /\ e /\ f) /\ g /\ h
                     ==> a /\ b /\ c /\ d /\ e /\ f /\ g /\ h]])
  let t2 ← ExceptT.mk (TAUT [[~a \/ a]])
  let t3 ← ExceptT.mk (TAUT [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]])
  let t4 ← ExceptT.mk (TAUT [[a /\ (b \/ c) <=> a /\ b \/ a /\ c]])
  let t5 ← ExceptT.mk (TAUT [[a \/ b ==> c <=> (a ==> c) /\ (b ==> c)]])
  let i1 ← ExceptT.mk (INT_ARITH [[(x - y) + z = (x + z) - y]])
  let i2 ← ExceptT.mk (INT_ARITH [[(x - y) + y = x]])
  prove ([[!d p. alldivide d p /\ &0 < d
         ==> !x. interp x p /\ ~(interp (x - d) p)
                 ==> ?j b. &1 <= j /\ j <= d /\ b IN bset p /\ (x = b + j)]])
    (GEN_TAC THEN ONCE_REWRITE_TAC [t0] THEN
     REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
     MATCH_MP_TAC cform_INDUCT THEN
     REWRITE_TAC [interp, alldivide, bset, NOT_IN_EMPTY] THEN
     MATCH_MP_TAC t1 THEN
     CONJ_TAC THENL
      [ALL_TAC,
       SIMP_TAC [t2, t3, t4, t5,
                DE_MORGAN_THM, IN_UNION, EXISTS_OR_THM, FORALL_AND_THM]] THEN
     REPEAT STRIP_TAC THENL
      [ALL_TAC,
       MAP_EVERY EXISTS_TAC [([[x + a]]), ([[(--a)]])],
       MAP_EVERY EXISTS_TAC [([[&1]]), ([[(--a) - &1]])],
       MAP_EVERY EXISTS_TAC [([[d:int]]), ([[(--a)]])],
       ASM_MESON_TAC [i1, DIVIDES_SUB],
       ASM_MESON_TAC [i1, i2, DIVIDES_ADD]] THEN
     POP_ASSUM_LIST (fun ths => HolLight.tactic_of do
       pure (MP_TAC (← HolLight.end_itlist HolLight.CONJ ths))) THEN
     REWRITE_TAC [IN_SING] THEN INT_ARITH_TAC))
#eval BDISJ_REPEATS_LEMMA

#eval phrase 28
-- let MAINTHM_B = prove ...
unsafe def MAINTHM_B : thm := keepThm "MAINTHM_B" (do
  let t1 ← ExceptT.mk (TAUT [[a /\ (b \/ c) <=> a /\ b \/ a /\ c]])
  let t2 ← ExceptT.mk (TAUT
    [[!a1 a2. (a <=> a1 \/ a2) /\ (a1 <=> b) /\ (a2 ==> c) /\ (c ==> a)
            ==> (a <=> b \/ c)]])
  let i1 ← ExceptT.mk (INT_ARITH [[&0 < d ==> x - d < x]])
  prove ([[!p d. alldivide d p /\ &0 < d
         ==> ((?x. interp x p) <=>
              ?j. &1 <= j /\ j <= d /\
                  (interp j (minusinf p) \/
                   ?b. b IN bset p /\ interp (b + j) p))]])
    (REPEAT GEN_TAC THEN DISCH_TAC THEN
     REWRITE_TAC [t1, EXISTS_OR_THM] THEN
     MATCH_MP_TAC t2 THEN
     EXISTS_TAC ([[!y. ?x. x < y /\ interp x p]]) THEN
     EXISTS_TAC ([[?x. interp x p /\ !y. y < x ==> ~(interp y p)]]) THEN
     REPEAT CONJ_TAC THENL
      [REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM INT_EXISTS_CASES))],
       ASM_MESON_TAC [NOMINIMAL_EQUIV],
       ALL_TAC,
       MESON_TAC []] THEN
     DISCH_THEN (X_CHOOSE_THEN ([[x:int]])
      (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC ([[x - d]])))) THEN
     ASM_SIMP_TAC [i1] THEN
     DISCH_TAC THEN
     MP_TAC (← ExceptT.mk (HolLight.SPECL [([[d:int]]), ([[p:cform]])] BDISJ_REPEATS_LEMMA)) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (MP_TAC o SPEC ([[x:int]])) THEN ASM_MESON_TAC []))
#eval MAINTHM_B

#eval phrase 29
-- (* Deduce the other one by a symmetry argument rather than a similar proof. *)
-- let mirror = new_recursive_definition cform_RECURSION ...
unsafe def mirror : thm := keep "mirror" fun _ => (do
  ExceptT.mk (new_recursive_definition cform_RECURSION
   [[(mirror (Lt e) = Gt(--e)) /\
     (mirror (Gt e) = Lt(--e)) /\
     (mirror (Eq e) = Eq(--e)) /\
     (mirror (Ne e) = Ne(--e)) /\
     (mirror (Divides c e) = Divides c (--e)) /\
     (mirror (Ndivides c e) = Ndivides c (--e)) /\
     (mirror (And p q) = And (mirror p) (mirror q)) /\
     (mirror (Or p q) = Or (mirror p) (mirror q)) /\
     (mirror (Nox P) = Nox P)]])
  : ExceptT String IO thm).run
#eval mirror

#eval phrase 30
-- let INTERP_MIRROR_LEMMA = prove ...
unsafe def INTERP_MIRROR_LEMMA : thm := keepThm "INTERP_MIRROR_LEMMA" (do
  prove ([[!p x. interp (--x) (mirror p) <=> interp x p]])
    (MATCH_MP_TAC cform_INDUCT THEN SIMP_TAC [mirror, interp] THEN
     REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM INT_NEG_ADD)), DIVIDES_RNEG] THEN INT_ARITH_TAC))
#eval INTERP_MIRROR_LEMMA

#eval phrase 31
-- let INTERP_MIRROR = prove ...
unsafe def INTERP_MIRROR : thm := proveThm "INTERP_MIRROR"
  ([[!p x. interp x (mirror p) <=> interp (--x) p]])
  (MESON_TAC [INTERP_MIRROR_LEMMA, INT_NEG_NEG])
#eval INTERP_MIRROR

#eval phrase 32
-- let BSET_MIRROR = prove ...
unsafe def BSET_MIRROR : thm := proveThm "BSET_MIRROR"
  ([[!p. bset(mirror p) = IMAGE (--) (aset p)]])
  (MATCH_MP_TAC cform_INDUCT THEN SIMP_TAC [mirror, aset, bset] THEN
   REWRITE_TAC [IMAGE_CLAUSES, IMAGE_UNION] THEN
   REWRITE_TAC [EXTENSION, IN_SING] THEN INT_ARITH_TAC)
#eval BSET_MIRROR

#eval phrase 33
-- let MINUSINF_MIRROR = prove ...
unsafe def MINUSINF_MIRROR : thm := proveThm "MINUSINF_MIRROR"
  ([[!p. minusinf (mirror p) = mirror (plusinf p)]])
  (MATCH_MP_TAC cform_INDUCT THEN SIMP_TAC [plusinf, minusinf, mirror])
#eval MINUSINF_MIRROR

#eval phrase 34
-- let PLUSINF_MIRROR = prove ...
unsafe def PLUSINF_MIRROR : thm := proveThm "PLUSINF_MIRROR"
  ([[!p. plusinf p = mirror(minusinf (mirror p))]])
  (MATCH_MP_TAC cform_INDUCT THEN
   SIMP_TAC [plusinf, minusinf, mirror, INT_NEG_NEG])
#eval PLUSINF_MIRROR

#eval phrase 35
-- let ALLDIVIDE_MIRROR = prove ...
unsafe def ALLDIVIDE_MIRROR : thm := proveThm "ALLDIVIDE_MIRROR"
  ([[!p d. alldivide d (mirror p) = alldivide d p]])
  (MATCH_MP_TAC cform_INDUCT THEN SIMP_TAC [mirror, alldivide])
#eval ALLDIVIDE_MIRROR

#eval phrase 36
-- let EXISTS_NEG = prove ...
unsafe def EXISTS_NEG : thm := proveThm "EXISTS_NEG"
  ([[(?x. P(--x)) <=> (?x. P(x))]])
  (MESON_TAC [INT_NEG_NEG])
#eval EXISTS_NEG

#eval phrase 37
-- let FORALL_NEG = prove ...
unsafe def FORALL_NEG : thm := proveThm "FORALL_NEG"
  ([[(!x. P(--x)) <=> (!x. P x)]])
  (MESON_TAC [INT_NEG_NEG])
#eval FORALL_NEG

#eval phrase 38
-- let EXISTS_MOD_IMP = prove ...
unsafe def EXISTS_MOD_IMP : thm := keepThm "EXISTS_MOD_IMP" (do
  let i1 ← ExceptT.mk (INT_ARITH [[d + --(&2) * d = --d]])
  let i2 ← ExceptT.mk (INT_ARITH [[(--j) + &1 * d = d - j]])
  prove ([[!P d. (!c x. P(x + c * d) <=> P(x)) /\ (?j. &1 <= j /\ j <= d /\ P(--j))
         ==> ?j. &1 <= j /\ j <= d /\ P(j)]])
    (REPEAT STRIP_TAC THEN ASM_CASES_TAC ([[d:int = j]]) THENL
      [FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[(--(&2))]]), ([[d:int]])]) THEN
       ASM_REWRITE_TAC [i1] THEN
       ASM_MESON_TAC [INT_LE_REFL],
       FIRST_X_ASSUM (MP_TAC o HolLight.SPECL [([[&1]]), ([[(--j)]])]) THEN
       ASM_REWRITE_TAC [i2] THEN
       DISCH_TAC THEN EXISTS_TAC ([[d - j]]) THEN ASM_REWRITE_TAC [] THEN
       MAP_EVERY UNDISCH_TAC [([[&1 <= j]]), ([[j <= d]]), ([[~(d:int = j)]])] THEN
       INT_ARITH_TAC]))
#eval EXISTS_MOD_IMP

#eval phrase 39
-- let EXISTS_MOD_EQ = prove ...
unsafe def EXISTS_MOD_EQ : thm := keepThm "EXISTS_MOD_EQ" (do
  let i1 ← ExceptT.mk (INT_ARITH [[(--(x + c * d)) = --x + --c * d]])
  prove ([[!P d. (!c x. P(x + c * d) <=> P(x))
         ==> ((?j. &1 <= j /\ j <= d /\ P(--j)) <=>
              (?j. &1 <= j /\ j <= d /\ P(j)))]])
    (REPEAT STRIP_TAC THEN EQ_TAC THENL
      [MP_TAC (← ExceptT.mk (HolLight.SPEC ([[P:int->bool]]) EXISTS_MOD_IMP)),
       MP_TAC (← ExceptT.mk (HolLight.SPEC ([[\x. P(--x):bool]]) EXISTS_MOD_IMP))] THEN
     DISCH_THEN (MP_TAC o SPEC ([[d:int]])) THEN ASM_REWRITE_TAC [INT_NEG_NEG] THEN
     ASM_REWRITE_TAC [i1, FORALL_NEG] THEN
     MESON_TAC []))
#eval EXISTS_MOD_EQ

#eval phrase 40
-- let MAINTHM_A = prove ...
unsafe def MAINTHM_A : thm := keepThm "MAINTHM_A" (do
  let t1 ← ExceptT.mk (TAUT [[a /\ (b \/ c) <=> a /\ b \/ a /\ c]])
  let t2 ← ExceptT.mk (TAUT [[(a \/ b) /\ c <=> a /\ c \/ b /\ c]])
  let i1 ← ExceptT.mk (INT_ARITH [[(--(b + j)) = --b - j]])
  prove ([[!p d. alldivide d p /\ &0 < d
         ==> ((?x. interp x p) <=>
              ?j. &1 <= j /\ j <= d /\
                  (interp j (plusinf p) \/
                   ?a. a IN aset p /\ interp (a - j) p))]])
    (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC HolLight.LAND_CONV [(← ExceptT.mk (HolLight.GSYM EXISTS_NEG))] THEN
     REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM INTERP_MIRROR))] THEN
     MP_TAC (← ExceptT.mk (HolLight.SPECL [([[mirror p]]), ([[d:int]])] MAINTHM_B)) THEN
     ASM_REWRITE_TAC [ALLDIVIDE_MIRROR] THEN DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [t1, t2, EXISTS_OR_THM] THEN
     BINOP_TAC THENL
      [ALL_TAC,
       REWRITE_TAC [INTERP_MIRROR, MINUSINF_MIRROR, BSET_MIRROR] THEN
       REWRITE_TAC [i1, IN_IMAGE] THEN
       MESON_TAC [INT_NEG_NEG]] THEN
     REWRITE_TAC [PLUSINF_MIRROR] THEN
     FIRST_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [(← ExceptT.mk (HolLight.GSYM ALLDIVIDE_MIRROR))]) THEN
     SPEC_TAC ([[mirror p]], [[q:cform]]) THEN REWRITE_TAC [INTERP_MIRROR] THEN
     REPEAT STRIP_TAC THEN MATCH_MP_TAC (← ExceptT.mk (HolLight.GSYM EXISTS_MOD_EQ)) THEN
     ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM MINUSINF_REPEATS))]))
#eval MAINTHM_A

#eval phrase 41
-- (* Proforma for elimination of coefficient of main variable. *)
-- let EXISTS_MULTIPLE_THM_1 = prove ...
unsafe def EXISTS_MULTIPLE_THM_1 : thm := proveThm "EXISTS_MULTIPLE_THM_1"
  ([[(?x. P(&1 * x)) <=> ?x. P(x)]])
  (REWRITE_TAC [INT_MUL_LID])
#eval EXISTS_MULTIPLE_THM_1

#eval phrase 42
-- let EXISTS_MULTIPLE_THM = prove ...
unsafe def EXISTS_MULTIPLE_THM : thm := proveThm "EXISTS_MULTIPLE_THM"
  ([[(?x. P(c * x)) <=> ?x. c divides x /\ P(x)]])
  (MESON_TAC [divides])
#eval EXISTS_MULTIPLE_THM

#eval phrase 43
-- (* Ordering of variables determined by a list, *with* trivial default. *)
-- let rec earlier vars x y = ...
unsafe def earlier : List term → term → term → Bool
  | z :: ovs, x, y => if z == y then false
                      else if z == x then true
                      else earlier ovs x y
  | [], x, y => HolMath.RealArith.term_lt x y
#eval IO.println "<fun>"

#eval phrase 44
-- (* Conversion of integer constant to ML rational number. *)
-- (* This is a tweaked copy of the real-type versions in "real.ml". *)
-- let is_num_const = let ptm = `&` in fun tm -> ...
unsafe def is_num_const : term → Bool :=
  let ptm := keep "is_num_const.ptm" fun _ =>
    match unsafeIO (HolCore.Parser.parse_term "&") with | .ok (.ok t) => t | _ => panic! "ptm"
  fun tm => match dest_comb tm with
            | .ok (l, r) => l == ptm && is_numeral r
            | .error _ => false
#eval IO.println "<fun>"

#eval phrase 45
-- let mk_num_const,dest_num_const = let ptm = `&` in ...
unsafe def mk_num_const : Rat → Except String term :=
  let ptm := keep "mk_num_const.ptm" fun _ =>
    match unsafeIO (HolCore.Parser.parse_term "&") with | .ok (.ok t) => t | _ => panic! "ptm"
  fun n => do mk_comb ptm (← mk_numeral n)
unsafe def dest_num_const : term → Except String Rat :=
  let ptm := keep "dest_num_const.ptm" fun _ =>
    match unsafeIO (HolCore.Parser.parse_term "&") with | .ok (.ok t) => t | _ => panic! "ptm"
  fun tm => do
    let (l, r) ← dest_comb tm
    if l == ptm then dest_numeral r else failwith "dest_num_const"
#eval IO.println "<fun>"
#eval IO.println "<fun>"

#eval phrase 46
-- let is_int_const = let ptm = `(--)` in fun tm -> ...
unsafe def is_int_const : term → Bool :=
  let ptm := keep "is_int_const.ptm" fun _ =>
    match unsafeIO (HolCore.Parser.parse_term "(--)") with | .ok (.ok t) => t | _ => panic! "ptm"
  fun tm =>
    is_num_const tm ||
    (match dest_comb tm with
     | .ok (l, r) => l == ptm && is_num_const r
     | .error _ => false)
#eval IO.println "<fun>"

#eval phrase 47
-- let mk_int_const,dest_int_const = let ptm = `(--)` in ...
unsafe def mk_int_const : Rat → Except String term :=
  let ptm := keep "mk_int_const.ptm" fun _ =>
    match unsafeIO (HolCore.Parser.parse_term "(--)") with | .ok (.ok t) => t | _ => panic! "ptm"
  fun n => if n < HolCore.Lib.num_0 then do mk_comb ptm (← mk_num_const (-n))
           else mk_num_const n
unsafe def dest_int_const : term → Except String Rat :=
  let ptm := keep "dest_int_const.ptm" fun _ =>
    match unsafeIO (HolCore.Parser.parse_term "(--)") with | .ok (.ok t) => t | _ => panic! "ptm"
  fun tm =>
    if (match rator tm with | .ok r => r == ptm | .error _ => false) then do
      let r ← rand tm
      pure (-(← dest_num_const r))
    else dest_num_const tm
#eval IO.println "<fun>"
#eval IO.println "<fun>"

#eval phrase 48
-- (* Similar tweaks of all the REAL_INT_..._CONV arith convs in real.ml *)
-- let INT_LE_CONV,INT_LT_CONV,INT_GE_CONV,INT_GT_CONV,INT_EQ_CONV = ...
unsafe structure IntCompareConvs where
  INT_LE_CONV : HolCore.Equal.ioconv
  INT_LT_CONV : HolCore.Equal.ioconv
  INT_GE_CONV : HolCore.Equal.ioconv
  INT_GT_CONV : HolCore.Equal.ioconv
  INT_EQ_CONV : HolCore.Equal.ioconv
unsafe instance : Inhabited IntCompareConvs :=
  ⟨⟨fun _ => pure (.error ""), fun _ => pure (.error ""), fun _ => pure (.error ""),
    fun _ => pure (.error ""), fun _ => pure (.error "")⟩⟩
unsafe def intCompareConvs : IntCompareConvs := keepE "intCompareConvs" (do
  let tth ← ExceptT.mk (TAUT [[(F /\ F <=> F) /\ (F /\ T <=> F) /\
          (T /\ F <=> F) /\ (T /\ T <=> T)]])
  let nth ← ExceptT.mk (TAUT [[(~T <=> F) /\ (~F <=> T)]])
  let NUM2_EQ_CONV :=
    HolLight.COMB2_CONV (HolLight.RAND_CONV NUM_EQ_CONV) NUM_EQ_CONV THENC
    HolLight.GEN_REWRITE_CONV HolCore.Lib.I [tth]
  let NUM2_NE_CONV :=
    HolLight.RAND_CONV NUM2_EQ_CONV THENC
    HolLight.GEN_REWRITE_CONV HolCore.Lib.I [nth]
  let [pth_le1, pth_le2a, pth_le2b, pth_le3] := CONJUNCTS (← prove
   ([[(--(&m) <= &n <=> T) /\
     (&m <= &n <=> m <= n) /\
     (--(&m) <= --(&n) <=> n <= m) /\
     (&m <= --(&n) <=> (m = 0) /\ (n = 0))]])
    (REWRITE_TAC [INT_LE_NEG2] THEN
     REWRITE_TAC [INT_LE_LNEG, INT_LE_RNEG] THEN
     REWRITE_TAC [INT_OF_NUM_ADD, INT_OF_NUM_LE, LE_0] THEN
     REWRITE_TAC [LE, ADD_EQ_0])) | throw "pth_le"
  let INT_LE_CONV := HolLight.FIRST_CONV
   [HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_le1],
    HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_le2a, pth_le2b] THENC NUM_LE_CONV,
    HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_le3] THENC NUM2_EQ_CONV]
  let [pth_lt1, pth_lt2a, pth_lt2b, pth_lt3] := CONJUNCTS (← prove
   ([[(&m < --(&n) <=> F) /\
     (&m < &n <=> m < n) /\
     (--(&m) < --(&n) <=> n < m) /\
     (--(&m) < &n <=> ~((m = 0) /\ (n = 0)))]])
    (REWRITE_TAC [pth_le1, pth_le2a, pth_le2b, pth_le3,
                (← ExceptT.mk (HolLight.GSYM NOT_LE)), (← ExceptT.mk (HolLight.GSYM INT_NOT_LE))] THEN
     CONV_TAC TAUT)) | throw "pth_lt"
  let INT_LT_CONV := HolLight.FIRST_CONV
   [HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_lt1],
    HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_lt2a, pth_lt2b] THENC NUM_LT_CONV,
    HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_lt3] THENC NUM2_NE_CONV]
  let [pth_ge1, pth_ge2a, pth_ge2b, pth_ge3] := CONJUNCTS (← prove
   ([[(&m >= --(&n) <=> T) /\
     (&m >= &n <=> n <= m) /\
     (--(&m) >= --(&n) <=> m <= n) /\
     (--(&m) >= &n <=> (m = 0) /\ (n = 0))]])
    (REWRITE_TAC [pth_le1, pth_le2a, pth_le2b, pth_le3, INT_GE] THEN
     CONV_TAC TAUT)) | throw "pth_ge"
  let INT_GE_CONV := HolLight.FIRST_CONV
   [HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_ge1],
    HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_ge2a, pth_ge2b] THENC NUM_LE_CONV,
    HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_ge3] THENC NUM2_EQ_CONV]
  let [pth_gt1, pth_gt2a, pth_gt2b, pth_gt3] := CONJUNCTS (← prove
   ([[(--(&m) > &n <=> F) /\
     (&m > &n <=> n < m) /\
     (--(&m) > --(&n) <=> m < n) /\
     (&m > --(&n) <=> ~((m = 0) /\ (n = 0)))]])
    (REWRITE_TAC [pth_lt1, pth_lt2a, pth_lt2b, pth_lt3, INT_GT] THEN
     CONV_TAC TAUT)) | throw "pth_gt"
  let INT_GT_CONV := HolLight.FIRST_CONV
   [HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_gt1],
    HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_gt2a, pth_gt2b] THENC NUM_LT_CONV,
    HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_gt3] THENC NUM2_NE_CONV]
  let [pth_eq1a, pth_eq1b, pth_eq2a, pth_eq2b] := CONJUNCTS (← prove
   ([[((&m = &n) <=> (m = n)) /\
     ((--(&m) = --(&n)) <=> (m = n)) /\
     ((--(&m) = &n) <=> (m = 0) /\ (n = 0)) /\
     ((&m = --(&n)) <=> (m = 0) /\ (n = 0))]])
    (REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM INT_LE_ANTISYM)), (← ExceptT.mk (HolLight.GSYM LE_ANTISYM))] THEN
     REWRITE_TAC [pth_le1, pth_le2a, pth_le2b, pth_le3, LE, LE_0] THEN
     CONV_TAC TAUT)) | throw "pth_eq"
  let INT_EQ_CONV := HolLight.FIRST_CONV
   [HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_eq1a, pth_eq1b] THENC NUM_EQ_CONV,
    HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_eq2a, pth_eq2b] THENC NUM2_EQ_CONV]
  pure { INT_LE_CONV, INT_LT_CONV, INT_GE_CONV, INT_GT_CONV, INT_EQ_CONV })
unsafe def INT_LE_CONV : HolCore.Equal.ioconv := intCompareConvs.INT_LE_CONV
unsafe def INT_LT_CONV : HolCore.Equal.ioconv := intCompareConvs.INT_LT_CONV
unsafe def INT_GE_CONV : HolCore.Equal.ioconv := intCompareConvs.INT_GE_CONV
unsafe def INT_GT_CONV : HolCore.Equal.ioconv := intCompareConvs.INT_GT_CONV
unsafe def INT_EQ_CONV : HolCore.Equal.ioconv := intCompareConvs.INT_EQ_CONV
#eval IO.println "<fun>"
#eval IO.println "<fun>"
#eval IO.println "<fun>"
#eval IO.println "<fun>"
#eval IO.println "<fun>"

#eval phrase 49
-- let INT_NEG_CONV = ...
unsafe def INT_NEG_CONV : HolCore.Equal.ioconv := keepE "INT_NEG_CONV" (do
  let pth ← prove
   ([[(--(&0) = &0) /\
     (--(--(&x)) = &x)]])
    (REWRITE_TAC [INT_NEG_NEG, INT_NEG_0])
  pure (HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth]))
#eval IO.println "<fun>"

#eval phrase 50
-- let INT_MUL_CONV = ...
unsafe def INT_MUL_CONV : HolCore.Equal.ioconv := keepE "INT_MUL_CONV" (do
  let pth0 ← prove
   ([[(&0 * &x = &0) /\
     (&0 * --(&x) = &0) /\
     (&x * &0 = &0) /\
     (--(&x) * &0 = &0)]])
    (REWRITE_TAC [INT_MUL_LZERO, INT_MUL_RZERO])
  let (pth1, pth2) ← CONJ_PAIR (← prove
   ([[((&m * &n = &(m * n)) /\
      (--(&m) * --(&n) = &(m * n))) /\
     ((--(&m) * &n = --(&(m * n))) /\
      (&m * --(&n) = --(&(m * n))))]])
    (REWRITE_TAC [INT_MUL_LNEG, INT_MUL_RNEG, INT_NEG_NEG] THEN
     REWRITE_TAC [INT_OF_NUM_MUL]))
  pure (HolLight.FIRST_CONV
   [HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth0],
    HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth1] THENC HolLight.RAND_CONV NUM_MULT_CONV,
    HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth2] THENC HolLight.RAND_CONV (HolLight.RAND_CONV NUM_MULT_CONV)]))
#eval IO.println "<fun>"

#eval phrase 51
-- let INT_ADD_CONV = ...
unsafe def INT_ADD_CONV : HolCore.Equal.ioconv := keepE "INT_ADD_CONV" (do
  let neg_tm ← ExceptT.mk (HolCore.Parser.parse_term "(--)")
  let amp_tm ← ExceptT.mk (HolCore.Parser.parse_term "&")
  let add_tm ← ExceptT.mk (HolCore.Parser.parse_term "(+)")
  let dest := dest_binop add_tm
  let m_tm ← ExceptT.mk (HolCore.Parser.parse_term "m:num")
  let n_tm ← ExceptT.mk (HolCore.Parser.parse_term "n:num")
  let pth0 ← prove
   ([[(--(&m) + &m = &0) /\
     (&m + --(&m) = &0)]])
    (REWRITE_TAC [INT_ADD_LINV, INT_ADD_RINV])
  let [pth1, pth2, pth3, pth4, pth5, pth6] := CONJUNCTS (← prove
   ([[(--(&m) + --(&n) = --(&(m + n))) /\
     (--(&m) + &(m + n) = &n) /\
     (--(&(m + n)) + &m = --(&n)) /\
     (&(m + n) + --(&m) = &n) /\
     (&m + --(&(m + n)) = --(&n)) /\
     (&m + &n = &(m + n))]])
    (REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM INT_OF_NUM_ADD)), INT_NEG_ADD] THEN
     REWRITE_TAC [INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_LID] THEN
     REWRITE_TAC [INT_ADD_RINV, INT_ADD_LID] THEN
     ONCE_REWRITE_TAC [INT_ADD_SYM] THEN
     REWRITE_TAC [INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_LID] THEN
     REWRITE_TAC [INT_ADD_RINV, INT_ADD_LID])) | throw "pth_add"
  -- the main conversion: fun tm -> try ... with Failure _ -> failwith "INT_ADD_CONV"
  let conv : term → IO (Except String thm) := fun tm => (ExceptT.run do
    let (l, r) ← liftExcept (dest tm)
    if (← liftExcept (rator l)) == neg_tm then
      if (← liftExcept (rator r)) == neg_tm then
        let th1 ← liftExcept (HolCore.Kernel.INST [(← liftExcept (rand (← liftExcept (rand l))), m_tm), (← liftExcept (rand (← liftExcept (rand r))), n_tm)] pth1)
        let tm1 ← liftExcept (rand (← liftExcept (rand (← liftExcept (rand (concl th1))))))
        let th2 ← ExceptT.mk (HolLight.AP_TERM neg_tm (← ExceptT.mk (HolLight.AP_TERM amp_tm (← ExceptT.mk (NUM_ADD_CONV tm1)))))
        ExceptT.mk (HolLight.TRANS th1 th2)
      else
        let m ← liftExcept (rand (← liftExcept (rand l)))
        let n ← liftExcept (rand r)
        let m' ← liftExcept (dest_numeral m)
        let n' ← liftExcept (dest_numeral n)
        if m' <= n' then
          let p ← liftExcept (mk_numeral (n' - m'))
          let th1 ← liftExcept (HolCore.Kernel.INST [(m, m_tm), (p, n_tm)] pth2)
          let th2 ← ExceptT.mk (NUM_ADD_CONV (← liftExcept (rand (← liftExcept (rand (← liftExcept (HolCore.Equal.lhand (concl th1))))))))
          let th3 ← ExceptT.mk (HolLight.AP_TERM (← liftExcept (rator tm)) (← ExceptT.mk (HolLight.AP_TERM amp_tm (← ExceptT.mk (HolLight.SYM th2)))))
          ExceptT.mk (HolLight.TRANS th3 th1)
        else
          let p ← liftExcept (mk_numeral (m' - n'))
          let th1 ← liftExcept (HolCore.Kernel.INST [(n, m_tm), (p, n_tm)] pth3)
          let th2 ← ExceptT.mk (NUM_ADD_CONV (← liftExcept (rand (← liftExcept (rand (← liftExcept (HolCore.Equal.lhand (← liftExcept (HolCore.Equal.lhand (concl th1)))))))))) 
          let th3 ← ExceptT.mk (HolLight.AP_TERM neg_tm (← ExceptT.mk (HolLight.AP_TERM amp_tm (← ExceptT.mk (HolLight.SYM th2)))))
          let th4 ← ExceptT.mk (HolLight.AP_THM (← ExceptT.mk (HolLight.AP_TERM add_tm th3)) (← liftExcept (rand tm)))
          ExceptT.mk (HolLight.TRANS th4 th1)
    else
      if (← liftExcept (rator r)) == neg_tm then
        let m ← liftExcept (rand l)
        let n ← liftExcept (rand (← liftExcept (rand r)))
        let m' ← liftExcept (dest_numeral m)
        let n' ← liftExcept (dest_numeral n)
        if n' <= m' then
          let p ← liftExcept (mk_numeral (m' - n'))
          let th1 ← liftExcept (HolCore.Kernel.INST [(n, m_tm), (p, n_tm)] pth4)
          let th2 ← ExceptT.mk (NUM_ADD_CONV (← liftExcept (rand (← liftExcept (HolCore.Equal.lhand (← liftExcept (HolCore.Equal.lhand (concl th1))))))))
          let th3 ← ExceptT.mk (HolLight.AP_TERM add_tm (← ExceptT.mk (HolLight.AP_TERM amp_tm (← ExceptT.mk (HolLight.SYM th2)))))
          let th4 ← ExceptT.mk (HolLight.AP_THM th3 (← liftExcept (rand tm)))
          ExceptT.mk (HolLight.TRANS th4 th1)
        else
          let p ← liftExcept (mk_numeral (n' - m'))
          let th1 ← liftExcept (HolCore.Kernel.INST [(m, m_tm), (p, n_tm)] pth5)
          let th2 ← ExceptT.mk (NUM_ADD_CONV (← liftExcept (rand (← liftExcept (rand (← liftExcept (rand (← liftExcept (HolCore.Equal.lhand (concl th1)))))))))) 
          let th3 ← ExceptT.mk (HolLight.AP_TERM neg_tm (← ExceptT.mk (HolLight.AP_TERM amp_tm (← ExceptT.mk (HolLight.SYM th2)))))
          let th4 ← ExceptT.mk (HolLight.AP_TERM (← liftExcept (rator tm)) th3)
          ExceptT.mk (HolLight.TRANS th4 th1)
      else
        let th1 ← liftExcept (HolCore.Kernel.INST [(← liftExcept (rand l), m_tm), (← liftExcept (rand r), n_tm)] pth6)
        let tm1 ← liftExcept (rand (← liftExcept (rand (concl th1))))
        let th2 ← ExceptT.mk (HolLight.AP_TERM amp_tm (← ExceptT.mk (NUM_ADD_CONV tm1)))
        ExceptT.mk (HolLight.TRANS th1 th2))
  let convFail : term → IO (Except String thm) := fun tm => do
    match ← conv tm with
    | .ok th => pure (.ok th)
    | .error _ => pure (.error "INT_ADD_CONV")
  pure (HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth0] ORELSEC convFail))
#eval IO.println "<fun>"

#eval phrase 52
-- let INT_SUB_CONV = ...
unsafe def INT_SUB_CONV : HolCore.Equal.ioconv := keepE "INT_SUB_CONV" (do
  pure (HolLight.GEN_REWRITE_CONV HolCore.Lib.I [INT_SUB] THENC
        HolLight.TRY_CONV (HolLight.RAND_CONV INT_NEG_CONV) THENC
        INT_ADD_CONV))
#eval IO.println "<fun>"

#eval phrase 53
-- let INT_POW_CONV = ...
unsafe def INT_POW_CONV : HolCore.Equal.ioconv := keepE "INT_POW_CONV" (do
  let (pth1, pth2) ← CONJ_PAIR (← prove
   ([[(&x pow n = &(x EXP n)) /\
     ((--(&x)) pow n = if EVEN n then &(x EXP n) else --(&(x EXP n)))]])
    (REWRITE_TAC [INT_OF_NUM_POW, INT_POW_NEG]))
  let tth ← prove
   ([[((if T then x:int else y) = x) /\ ((if F then x:int else y) = y)]])
    (REWRITE_TAC [])
  let neg_tm ← ExceptT.mk (HolCore.Parser.parse_term "(--)")
  pure ((HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth1] THENC HolLight.RAND_CONV NUM_EXP_CONV) ORELSEC
   (HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth2] THENC
    HolLight.RATOR_CONV (HolLight.RATOR_CONV (HolLight.RAND_CONV NUM_EVEN_CONV)) THENC
    HolLight.GEN_REWRITE_CONV HolCore.Lib.I [tth] THENC
    (fun tm => do
       match rator tm with
       | .ok rt => if rt == neg_tm then HolLight.RAND_CONV (HolLight.RAND_CONV NUM_EXP_CONV) tm
                   else HolLight.RAND_CONV NUM_EXP_CONV tm
       | .error e => pure (.error e)))))
#eval IO.println "<fun>"

#eval phrase 54
-- (* Handy utility functions for int arithmetic terms. *)
-- let dest_add = dest_binop `(+)`;;
unsafe def dest_add_2 : term → Except String (term × term) :=
  dest_binop [[(+)]]
#eval IO.println "<fun>"

#eval phrase 55
-- let dest_mul = dest_binop `(*)`;;
unsafe def dest_mul_2 : term → Except String (term × term) :=
  dest_binop [[( * )]]
#eval IO.println "<fun>"

#eval phrase 56
-- let dest_pow = dest_binop `(pow)`;;
unsafe def dest_pow : term → Except String (term × term) :=
  dest_binop [[(pow)]]
#eval IO.println "<fun>"

#eval phrase 57
-- let dest_sub = dest_binop `(-)`;;
unsafe def dest_sub : term → Except String (term × term) :=
  dest_binop [[(-)]]
#eval IO.println "<fun>"

#eval phrase 58
-- let is_add = is_binop `(+)`;;
unsafe def is_add : term → Bool := is_binop [[(+)]]
#eval IO.println "<fun>"

#eval phrase 59
-- let is_mul = is_binop `(*)`;;
unsafe def is_mul : term → Bool := is_binop [[( * )]]
#eval IO.println "<fun>"

#eval phrase 60
-- let is_pow = is_binop `(pow)`;;
unsafe def is_pow : term → Bool := is_binop [[(pow)]]
#eval IO.println "<fun>"

#eval phrase 61
-- let is_sub = is_binop `(-)`;;
unsafe def is_sub : term → Bool := is_binop [[(-)]]
#eval IO.println "<fun>"

#eval phrase 62
-- (* Instantiate the normalizer. *)
-- let POLYNOMIAL_NORMALIZERS = ...
--   fun vars -> NORMALIZERS(earlier vars);;
/-- `sth` and `rth`, proved once (as the OCaml `let ... and ...` does). -/
unsafe def POLYNOMIAL_NORMALIZERS_sth : thm := keepThm "PN_sth" (do
  prove ([[(!x y z. x + (y + z) = (x + y) + z) /\
     (!x y. x + y = y + x) /\
     (!x. &0 + x = x) /\
     (!x y z. x * (y * z) = (x * y) * z) /\
     (!x y. x * y = y * x) /\
     (!x. &1 * x = x) /\
     (!x. &0 * x = &0) /\
     (!x y z. x * (y + z) = x * y + x * z) /\
     (!x. x pow 0 = &1) /\
     (!x n. x pow (SUC n) = x * x pow n)]])
    (REWRITE_TAC [INT_POW] THEN INT_ARITH_TAC))
unsafe def POLYNOMIAL_NORMALIZERS_rth : thm := keepThm "PN_rth" (do
  prove ([[(!x. --x = --(&1) * x) /\
     (!x y. x - y = x + --(&1) * y)]])
    INT_ARITH_TAC)
unsafe def POLYNOMIAL_NORMALIZERS (vars : List term) :
    ExceptT String IO (HolCore.Equal.ioconv × HolCore.Equal.ioconv × HolCore.Equal.ioconv ×
                        HolCore.Equal.ioconv × HolCore.Equal.ioconv × HolCore.Equal.ioconv) :=
  Session.SEMIRING_NORMALIZERS_CONV POLYNOMIAL_NORMALIZERS_sth POLYNOMIAL_NORMALIZERS_rth
    (is_int_const, INT_ADD_CONV, INT_MUL_CONV, INT_POW_CONV) (earlier vars)
#eval IO.println "<fun>"

#eval phrase 63
-- let POLYNOMIAL_NEG_CONV vars = let cnv,_,_,_,_,_ = POLYNOMIAL_NORMALIZERS vars in cnv;;
unsafe def POLYNOMIAL_NEG_CONV (vars : List term) : HolCore.Equal.ioconv := fun tm => do
  match ← (POLYNOMIAL_NORMALIZERS vars).run with
  | .ok (cnv, _, _, _, _, _) => cnv tm
  | .error e => pure (.error e)
#eval IO.println "<fun>"

#eval phrase 64
-- let POLYNOMIAL_ADD_CONV vars = let _,cnv,_,_,_,_ = POLYNOMIAL_NORMALIZERS vars in cnv;;
unsafe def POLYNOMIAL_ADD_CONV (vars : List term) : HolCore.Equal.ioconv := fun tm => do
  match ← (POLYNOMIAL_NORMALIZERS vars).run with
  | .ok (_, cnv, _, _, _, _) => cnv tm
  | .error e => pure (.error e)
#eval IO.println "<fun>"

#eval phrase 65
-- let POLYNOMIAL_SUB_CONV vars = let _,_,cnv,_,_,_ = POLYNOMIAL_NORMALIZERS vars in cnv;;
unsafe def POLYNOMIAL_SUB_CONV (vars : List term) : HolCore.Equal.ioconv := fun tm => do
  match ← (POLYNOMIAL_NORMALIZERS vars).run with
  | .ok (_, _, cnv, _, _, _) => cnv tm
  | .error e => pure (.error e)
#eval IO.println "<fun>"

#eval phrase 66
-- let POLYNOMIAL_MUL_CONV vars = let _,_,_,cnv,_,_ = POLYNOMIAL_NORMALIZERS vars in cnv;;
unsafe def POLYNOMIAL_MUL_CONV (vars : List term) : HolCore.Equal.ioconv := fun tm => do
  match ← (POLYNOMIAL_NORMALIZERS vars).run with
  | .ok (_, _, _, cnv, _, _) => cnv tm
  | .error e => pure (.error e)
#eval IO.println "<fun>"

#eval phrase 67
-- let POLYNOMIAL_POW_CONV vars = let _,_,_,_,cnv,_ = POLYNOMIAL_NORMALIZERS vars in cnv;;
unsafe def POLYNOMIAL_POW_CONV (vars : List term) : HolCore.Equal.ioconv := fun tm => do
  match ← (POLYNOMIAL_NORMALIZERS vars).run with
  | .ok (_, _, _, _, cnv, _) => cnv tm
  | .error e => pure (.error e)
#eval IO.println "<fun>"

#eval phrase 68
-- let POLYNOMIAL_CONV vars = let _,_,_,_,_,cnv = POLYNOMIAL_NORMALIZERS vars in cnv;;
unsafe def POLYNOMIAL_CONV (vars : List term) : HolCore.Equal.ioconv := fun tm => do
  match ← (POLYNOMIAL_NORMALIZERS vars).run with
  | .ok (_, _, _, _, _, cnv) => cnv tm
  | .error e => pure (.error e)
#eval IO.println "<fun>"

#eval phrase 69
-- (* Slight variants of these functions for procedure below. *)
-- let LINEAR_CMUL = let mul_tm = `(*)` in
--   fun vars n tm -> POLYNOMIAL_MUL_CONV vars (mk_comb(mk_comb(mul_tm,mk_int_const n),tm));;
unsafe def LINEAR_CMUL : List term → Rat → term → IO (Except String thm) :=
  let mul_tm := keep "LINEAR_CMUL.mul_tm" fun _ =>
    match unsafeIO (HolCore.Parser.parse_term "( * )") with | .ok (.ok t) => t | _ => panic! "mul_tm"
  fun vars n tm => (ExceptT.run do
    POLYNOMIAL_MUL_CONV vars (← liftExcept (do mk_comb (← mk_comb mul_tm (← mk_int_const n)) tm)))
#eval IO.println "<fun>"

#eval phrase 70
-- (* Linearize a formula, dealing with non-strict inequalities. *)
-- let LINEARIZE_CONV = ...
unsafe def LINEARIZE_CONV : List term → HolCore.Equal.ioconv := keepE "LINEARIZE_CONV" (do
  let i1 ← ExceptT.mk (INT_ARITH
    [[(s < t <=> &0 < t - s) /\
      (~(s < t) <=> &0 < (s + &1) - t) /\
      (s > t <=> &0 < s - t) /\
      (~(s > t) <=> &0 < (t + &1) - s) /\
      (s <= t <=> &0 < (t + &1) - s) /\
      (~(s <= t) <=> &0 < s - t) /\
      (s >= t <=> &0 < (s + &1) - t) /\
      (~(s >= t) <=> &0 < t - s) /\
      ((s = t) <=> (&0 = s - t))]])
  let rew_conv := HolLight.GEN_REWRITE_CONV HolCore.Lib.I
    [(← HolLight.CONJ (HolCore.Kernel.REFL [[c divides e]]) i1)]
  let true_tm ← ExceptT.mk (HolCore.Parser.parse_term "T")
  let false_tm ← ExceptT.mk (HolCore.Parser.parse_term "F")
  let rec conv (vars : List term) (tm : term) : IO (Except String thm) := do
    match ← (rew_conv THENC HolLight.RAND_CONV (POLYNOMIAL_CONV vars)) tm with
    | .ok th => pure (.ok th)
    | .error _ =>
      if is_exists tm || is_forall tm then
        match rand tm with
        | .ok rtm => match bndvar rtm with
                     | .ok x => HolLight.BINDER_CONV (conv (x :: vars)) tm
                     | .error e => pure (.error e)
        | .error e => pure (.error e)
      else if is_neg tm then
        HolLight.RAND_CONV (conv vars) tm
      else if is_conj tm || is_disj tm || is_imp tm || HolCore.Bool.is_iff tm then
        HolLight.BINOP_CONV (conv vars) tm
      else if tm == true_tm || tm == false_tm then (pure (.ok (HolCore.Kernel.REFL tm)) : IO (Except String thm))
      else pure (.error "LINEARIZE_CONV: Unexpected term type")
  pure conv)
#eval IO.println "<fun>"

#eval phrase 71
-- (* Get the coefficient of x, assumed to be first term, if there at all. *)
-- let coefficient x tm = ...
unsafe def coefficient (x : term) (tm : term) : Rat :=
  match (do
      let (l, _r) ← dest_add tm
      if l == x then pure HolCore.Lib.num_1 else do
        let (c, y) ← dest_mul l
        if y == x then dest_int_const c else pure HolCore.Lib.num_0
    : Except String Rat) with
  | .ok v => v
  | .error _ =>
    match (do
        let (c, y) ← dest_mul tm
        if y == x then dest_int_const c else pure HolCore.Lib.num_0
      : Except String Rat) with
    | .ok v => v
    | .error _ => HolCore.Lib.num_1
#eval IO.println "<fun>"

#eval phrase 72
-- (* Find (always positive) LCM of all the multiples of x in formula tm. *)
-- let lcm_num x y = abs_num((x */ y) // gcd_num x y);;
unsafe def lcm_num (x y : Rat) : Rat :=
  HolCore.Lib.abs_num (HolCore.Lib.divide_num (x * y) (HolCore.Lib.gcd_num x y))
#eval IO.println "<fun>"

#eval phrase 73
-- let rec formlcm x tm = ...
unsafe def formlcm (x : term) : term → Rat := fun tm =>
  if is_neg tm then formlcm x (match rand tm with | .ok t => t | .error _ => tm)
  else if is_conj tm || is_disj tm || is_imp tm || HolCore.Bool.is_iff tm then
     lcm_num (formlcm x (match HolCore.Equal.lhand tm with | .ok t => t | .error _ => tm))
             (formlcm x (match rand tm with | .ok t => t | .error _ => tm))
  else if is_forall tm || is_exists tm then
     formlcm x (match (do body (← rand tm) : Except String term) with | .ok t => t | .error _ => tm)
  else if !(mem x (frees tm)) then HolCore.Lib.num_1
  else let c := coefficient x (match rand tm with | .ok t => t | .error _ => tm)
       if c == HolCore.Lib.num_0 then HolCore.Lib.num_1 else c
#eval IO.println "<fun>"

#eval phrase 74
-- (* Switch from "x [+ ...]" to "&1 * x [+ ...]" to suit later proforma. *)
-- let MULTIPLY_1_CONV = ...
unsafe def MULTIPLY_1_CONV : List term → term → IO (Except String thm) := keepE "MULTIPLY_1_CONV" (do
  let conv_0 := HolLight.REWR_CONV (← ExceptT.mk (INT_ARITH [[x = &1 * x]]))
  let conv_1 := HolLight.REWR_CONV (← ExceptT.mk (INT_ARITH [[x + a = &1 * x + a]]))
  pure (fun vars tm => do
    let x := List.headD vars default
    if tm == x then conv_0 tm
    else if is_add tm && (match HolCore.Equal.lhand tm with | .ok l => l == x | .error _ => false) then conv_1 tm
    else (pure (.ok (HolCore.Kernel.REFL tm)) : IO (Except String thm))))
#eval IO.println "<fun>"

#eval phrase 75
-- (* Adjust all coefficients of x (head variable) to match l in formula tm. *)
-- let ADJUSTCOEFF_CONV = ...
unsafe def ADJUSTCOEFF_CONV : List term → Rat → term → IO (Except String thm) :=
  keepE "ADJUSTCOEFF_CONV" (do
  let op_eq ← ExceptT.mk (HolCore.Parser.parse_term "(=):int->int->bool")
  let op_lt ← ExceptT.mk (HolCore.Parser.parse_term "(<):int->int->bool")
  let op_gt ← ExceptT.mk (HolCore.Parser.parse_term "(>):int->int->bool")
  let op_divides ← ExceptT.mk (HolCore.Parser.parse_term "(divides):int->int->bool")
  let c_tm ← ExceptT.mk (HolCore.Parser.parse_term "c:int")
  let d_tm ← ExceptT.mk (HolCore.Parser.parse_term "d:int")
  let e_tm ← ExceptT.mk (HolCore.Parser.parse_term "e:int")
  let pth_divides ← prove
   ([[~(d = &0) ==> (c divides e <=> (d * c) divides (d * e))]])
    (SIMP_TAC [divides, (← ExceptT.mk (HolLight.GSYM INT_MUL_ASSOC)), INT_EQ_MUL_LCANCEL])
  let pth_eq ← prove
   ([[~(d = &0) ==> ((&0 = e) <=> (&0 = d * e))]])
    (DISCH_TAC THEN CONV_TAC (HolLight.BINOP_CONV HolLight.SYM_CONV) THEN
     ASM_REWRITE_TAC [INT_ENTIRE])
  let pth_lt_pos ← prove
   ([[&0 < d ==> (&0 < e <=> &0 < d * e)]])
    (DISCH_TAC THEN SUBGOAL_THEN ([[&0 < e <=> d * &0 < d * e]]) SUBST1_TAC THENL
      [ASM_SIMP_TAC [INT_LT_LMUL_EQ], REWRITE_TAC [INT_MUL_RZERO]])
  let pth_gt_pos ← prove
   ([[&0 < d ==> (&0 > e <=> &0 > d * e)]])
    (DISCH_TAC THEN REWRITE_TAC [INT_GT] THEN
     SUBGOAL_THEN ([[e < &0 <=> d * e < d * &0]]) SUBST1_TAC THENL
      [ASM_SIMP_TAC [INT_LT_LMUL_EQ], REWRITE_TAC [INT_MUL_RZERO]])
  let true_tm ← ExceptT.mk (HolCore.Parser.parse_term "T")
  let false_tm ← ExceptT.mk (HolCore.Parser.parse_term "F")
  let pth_lt_neg ← prove
   ([[d < &0 ==> (&0 < e <=> &0 > d * e)]])
    (REWRITE_TAC [(← ExceptT.mk (INT_ARITH [[&0 > d * e <=> &0 < --d * e]])),
                (← ExceptT.mk (INT_ARITH [[d < &0 <=> &0 < --d]])), pth_lt_pos])
  let pth_gt_neg ← prove
   ([[d < &0 ==> (&0 > e <=> &0 < d * e)]])
    (REWRITE_TAC [(← ExceptT.mk (INT_ARITH [[&0 < d * e <=> &0 > --d * e]])),
                (← ExceptT.mk (INT_ARITH [[d < &0 <=> &0 < --d]])), pth_gt_pos])
  let rec go (vars : List term) (l : Rat) (tm : term) : IO (Except String thm) := ExceptT.run do
    if tm == true_tm || tm == false_tm then pure (HolCore.Kernel.REFL tm)
    else if is_exists tm || is_forall tm then
      ExceptT.mk (HolLight.BINDER_CONV (go vars l) tm)
    else if is_neg tm then
      ExceptT.mk (HolLight.RAND_CONV (go vars l) tm)
    else if is_conj tm || is_disj tm || is_imp tm || HolCore.Bool.is_iff tm then
      ExceptT.mk (HolLight.BINOP_CONV (go vars l) tm)
    else do
      let (lop, t) ← liftExcept (dest_comb tm)
      let (op, z) ← liftExcept (dest_comb lop)
      let c := coefficient (List.headD vars default) t
      if c == HolCore.Lib.num_0 then pure (HolCore.Kernel.REFL tm) else do
        let th1 ←
          if c == l then pure (HolCore.Kernel.REFL tm) else do
            let m := HolCore.Lib.divide_num l c
            let th0 ← if op == op_eq then pure pth_eq
                      else if op == op_divides then pure pth_divides
                      else if op == op_lt then
                        if m > HolCore.Lib.num_0 then pure pth_lt_pos else pure pth_lt_neg
                      else if op == op_gt then
                        if m > HolCore.Lib.num_0 then pure pth_gt_pos else pure pth_gt_neg
                      else ExceptT.mk (pure (.error "ADJUSTCOEFF_CONV: unknown predicate"))
            let th1 ← liftExcept (HolCore.Kernel.INST [(← liftExcept (mk_int_const m), d_tm), (z, c_tm), (t, e_tm)] th0)
            let tm1 ← liftExcept (HolCore.Equal.lhand (concl th1))
            let th2 ← if is_neg tm1 then
                        (do let e ← ExceptT.mk (INT_EQ_CONV (← liftExcept (rand tm1)))
                            HolLight.EQF_ELIM e)
                      else
                        (do let e ← ExceptT.mk (INT_LT_CONV tm1)
                            HolLight.EQT_ELIM e)
            let th3 ← ExceptT.mk (HolLight.MP th1 th2)
            if op == op_divides then do
              let th3 ← ExceptT.mk (HolLight.MP th1 th2)
              let tm2 ← liftExcept (rand (concl th3))
              let (l2, r2) ← liftExcept (dest_comb tm2)
              let th4 ← ExceptT.mk (HolLight.AP_TERM (← liftExcept (rator l2)) (← ExceptT.mk (INT_MUL_CONV (← liftExcept (rand l2)))))
              let th5 ← ExceptT.mk (HolLight.AP_THM th4 r2)
              let tm3 ← liftExcept (rator (← liftExcept (rand (concl th5))))
              let th6 ← ExceptT.mk (HolLight.TRANS th5 (← ExceptT.mk (HolLight.AP_TERM tm3 (← ExceptT.mk (LINEAR_CMUL vars m t)))))
              ExceptT.mk (HolLight.TRANS th3 th6)
            else do
              let tm2 ← liftExcept (rator (← liftExcept (rand (concl th3))))
              ExceptT.mk (HolLight.TRANS th3 (← ExceptT.mk (HolLight.AP_TERM tm2 (← ExceptT.mk (LINEAR_CMUL vars m t)))))
        if l == HolCore.Lib.num_1 then
          ExceptT.mk (HolLight.CONV_RULE (HolCore.Lib.funpow 2 HolLight.RAND_CONV (MULTIPLY_1_CONV vars)) th1)
        else pure th1
  pure go)
#eval IO.println "<fun>"

#eval phrase 76
-- (* Now normalize all the x terms to have same coefficient and eliminate it. *)
-- let NORMALIZE_COEFF_CONV = ...
unsafe def NORMALIZE_COEFF_CONV : List term → term → IO (Except String thm) :=
  keepE "NORMALIZE_COEFF_CONV" (do
  let c_tm ← ExceptT.mk (HolCore.Parser.parse_term "c:int")
  let pth ← prove
   ([[(?x. P(c * x)) <=> (?x. c divides x /\ P x)]])
    (REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM EXISTS_MULTIPLE_THM))])
  pure (fun vars tm => ExceptT.run do
    let (x, _bod) ← liftExcept (dest_exists tm)
    let l := formlcm x tm
    let th1 ← ExceptT.mk (ADJUSTCOEFF_CONV (x :: vars) l tm)
    let th2 ← if l == HolCore.Lib.num_1 then pure EXISTS_MULTIPLE_THM_1
              else liftExcept (HolCore.Kernel.INST [(← liftExcept (mk_int_const l), c_tm)] pth)
    ExceptT.mk (HolLight.TRANS th1 (← ExceptT.mk (HolLight.REWR_CONV th2 (← liftExcept (rand (concl th1))))))))
#eval IO.println "<fun>"

#eval phrase 77
-- (* Convert to shadow syntax. *)
-- let SHADOW_CONV = ...
unsafe def SHADOW_CONV : term → IO (Except String thm) :=
  keepE "SHADOW_CONV" (do
  let pth_trivial ← prove
   ([[P = interp x (Nox P)]])
    (REWRITE_TAC [interp])
  let pth_composite ← prove
   ([[(interp x p /\ interp x q <=> interp x (And p q)) /\
     (interp x p \/ interp x q <=> interp x (Or p q))]])
    (REWRITE_TAC [interp])
  let pth_literal_nontrivial ← prove
   ([[(&0 > x + e <=> interp x (Lt e)) /\
     (&0 < x + e <=> interp x (Gt e)) /\
     ((&0 = x + e) <=> interp x (Eq e)) /\
     (~(&0 = x + e) <=> interp x (Ne e)) /\
     (c divides (x + e) <=> interp x (Divides c e)) /\
     (~(c divides (x + e)) <=> interp x (Ndivides c e))]])
    (REWRITE_TAC [interp, INT_ADD_RID] THEN INT_ARITH_TAC)
  let pth_literal_trivial ← prove
   ([[(&0 > x <=> interp x (Lt(&0))) /\
     (&0 < x <=> interp x (Gt(&0))) /\
     ((&0 = x) <=> interp x (Eq(&0))) /\
     (~(&0 = x) <=> interp x (Ne(&0))) /\
     (c divides x <=> interp x (Divides c (&0))) /\
     (~(c divides x) <=> interp x (Ndivides c (&0)))]])
    (REWRITE_TAC [interp, INT_ADD_RID] THEN INT_ARITH_TAC)
  let rewr_composite := HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_composite]
  let rewr_literal := HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_literal_nontrivial] ORELSEC
                      HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_literal_trivial]
  let x_tm ← ExceptT.mk (HolCore.Parser.parse_term "x:int")
  let p_tm ← ExceptT.mk (HolCore.Parser.parse_term "P:bool")
  let rec shadow (x : term) (tm : term) : IO (Except String thm) := ExceptT.run do
    if !(mem x (frees tm)) then
       liftExcept (HolCore.Kernel.INST [(tm, p_tm), (x, x_tm)] pth_trivial)
    else if is_conj tm || is_disj tm then do
      let (l, r) ← liftExcept (match dest_conj tm with | .ok p => .ok p | .error _ => dest_disj tm)
      let thl ← ExceptT.mk (shadow x l)
      let thr ← ExceptT.mk (shadow x r)
      let th1 ← ExceptT.mk (HolLight.MK_COMB ((← ExceptT.mk (HolLight.AP_TERM (← liftExcept (rator (← liftExcept (rator tm)))) thl)), thr))
      ExceptT.mk (HolLight.TRANS th1 (← ExceptT.mk (rewr_composite (← liftExcept (rand (concl th1))))))
    else ExceptT.mk (rewr_literal tm)
  pure (fun tm => ExceptT.run do
    let (x, bod) ← liftExcept (dest_exists tm)
    ExceptT.mk (HolLight.MK_EXISTS x (← ExceptT.mk (shadow x bod)))))
#eval IO.println "<fun>"

#eval phrase 78
-- (* Get the LCM of the dividing things. *)
-- let dplcm = ...
unsafe def dplcm : term → Except String Rat :=
  let divides_tm := keep "dplcm.divides_tm" fun _ =>
    match unsafeIO (HolCore.Parser.parse_term "Divides") with | .ok (.ok t) => t | _ => panic! "d"
  let ndivides_tm := keep "dplcm.ndivides_tm" fun _ =>
    match unsafeIO (HolCore.Parser.parse_term "Ndivides") with | .ok (.ok t) => t | _ => panic! "nd"
  let and_tm := keep "dplcm.and_tm" fun _ =>
    match unsafeIO (HolCore.Parser.parse_term "And") with | .ok (.ok t) => t | _ => panic! "a"
  let or_tm := keep "dplcm.or_tm" fun _ =>
    match unsafeIO (HolCore.Parser.parse_term "Or") with | .ok (.ok t) => t | _ => panic! "o"
  let rec go (tm : term) : Except String Rat := do
    let (hop, args) := strip_comb tm
    if hop == divides_tm || hop == ndivides_tm then dest_int_const (List.headD args default)
    else if hop == and_tm || hop == or_tm
    then do end_itlist lcm_num (← args.mapM go)
    else pure HolCore.Lib.num_1
  go
#eval IO.println "<fun>"

#eval phrase 79
-- (* Conversion for true formulas "(--) &m divides (--) &n". *)
-- let PROVE_DIVIDES_CONV_POS = ...
unsafe def PROVE_DIVIDES_CONV_POS : term → IO (Except String thm) :=
  keepE "PROVE_DIVIDES_CONV_POS" (do
  let pth ← prove
   ([[(p * m = n) ==> &p divides &n]])
    (DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
     REWRITE_TAC [divides] THEN EXISTS_TAC ([[&m]]) THEN
     REWRITE_TAC [INT_OF_NUM_MUL])
  let m_tm ← ExceptT.mk (HolCore.Parser.parse_term "m:num")
  let n_tm ← ExceptT.mk (HolCore.Parser.parse_term "n:num")
  let p_tm ← ExceptT.mk (HolCore.Parser.parse_term "p:num")
  pure (fun tm => ExceptT.run do
    let n ← liftExcept (rand (← liftExcept (rand tm)))
    let p ← liftExcept (rand (← liftExcept (HolCore.Equal.lhand tm)))
    let m ← liftExcept (do mk_numeral (HolCore.Lib.divide_num (← dest_numeral n) (← dest_numeral p)))
    let th1 ← liftExcept (HolCore.Kernel.INST [(m, m_tm), (n, n_tm), (p, p_tm)] pth)
    ExceptT.mk (do HolLight.EQT_INTRO (← ExceptT.mk (HolLight.MP th1 (← ExceptT.mk (NUM_MULT_CONV (← liftExcept (HolCore.Equal.lhand (← liftExcept (HolCore.Equal.lhand (concl th1)))))))))).run))
#eval IO.println "<fun>"

#eval phrase 80
-- let PROVE_DIVIDES_CONV = ...
unsafe def PROVE_DIVIDES_CONV : term → IO (Except String thm) :=
  HolLight.GEN_REWRITE_CONV HolLight.REPEATC [DIVIDES_LNEG, DIVIDES_RNEG] THENC
  PROVE_DIVIDES_CONV_POS
#eval IO.println "<fun>"

#eval phrase 81
-- (* General version that works for positive and negative. *)
-- let INT_DIVIDES_NUM = prove ...
unsafe def INT_DIVIDES_NUM : thm := keepThm "INT_DIVIDES_NUM" (do
  prove ([[&p divides &n <=> ?m. (n = p * m)]])
    (REWRITE_TAC [divides] THEN EQ_TAC THENL
      [DISCH_THEN (X_CHOOSE_THEN ([[x:int]]) MP_TAC) THEN
       DISJ_CASES_THEN (X_CHOOSE_THEN ([[q:num]]) SUBST1_TAC)
        (← ExceptT.mk (HolLight.SPEC ([[x:int]]) INT_IMAGE)) THEN
       DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[abs:int->int]])) THEN
       REWRITE_TAC [INT_ABS_MUL, INT_ABS_NUM, INT_ABS_NEG] THEN
       REWRITE_TAC [INT_OF_NUM_MUL, INT_OF_NUM_EQ] THEN MESON_TAC [],
       MESON_TAC [INT_OF_NUM_MUL]]))
#eval INT_DIVIDES_NUM

#eval phrase 82
-- let INT_DIVIDES_POS_CONV = ...
unsafe def INT_DIVIDES_POS_CONV : term → IO (Except String thm) :=
  keepE "INT_DIVIDES_POS_CONV" (do
  let pth ← prove
   ([[(&p divides &n) <=> (p = 0) /\ (n = 0) \/ ~(p = 0) /\ (n MOD p = 0)]])
    (REWRITE_TAC [INT_DIVIDES_NUM] THEN
     ASM_CASES_TAC ([[p = 0]]) THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN EQ_TAC THENL
      [ASM_MESON_TAC [MOD_MULT],
       DISCH_TAC THEN
       FIRST_ASSUM (MP_TAC o SPEC ([[n:num]]) o HolLight.MATCH_MP DIVISION) THEN
       ASM_REWRITE_TAC [ADD_CLAUSES] THEN MESON_TAC [MULT_SYM]])
  pure (HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth] THENC NUM_REDUCE_CONV))
#eval (do let _ ← INT_DIVIDES_POS_CONV [[&6 divides &12]]; IO.println "<fun>")

#eval phrase 83
-- let INT_DIVIDES_CONV = ...
unsafe def INT_DIVIDES_CONV : term → IO (Except String thm) :=
  HolLight.GEN_REWRITE_CONV HolLight.REPEATC [DIVIDES_LNEG, DIVIDES_RNEG] THENC
  INT_DIVIDES_POS_CONV
#eval IO.println "<fun>"

#eval phrase 84
-- (* Conversion for "alldivide d p" (which should be true!) *)
-- let ALLDIVIDE_CONV = ...
unsafe def ALLDIVIDE_CONV : term → IO (Except String thm) :=
  keepE "ALLDIVIDE_CONV" (do
  let pth_atom ← prove
   ([[(alldivide d (Lt e) <=> T) /\
     (alldivide d (Gt e) <=> T) /\
     (alldivide d (Eq e) <=> T) /\
     (alldivide d (Ne e) <=> T) /\
     (alldivide d (Nox P) <=> T)]])
    (REWRITE_TAC [alldivide])
  let pth_div ← prove
   ([[(alldivide d (Divides c e) <=> c divides d) /\
      (alldivide d (Ndivides c e) <=> c divides d)]])
    (REWRITE_TAC [alldivide])
  let pth_comp ← prove
   ([[(alldivide d (And p q) <=> alldivide d p /\ alldivide d q) /\
     (alldivide d (Or p q) <=> alldivide d p /\ alldivide d q)]])
    (REWRITE_TAC [alldivide])
  let pth_taut ← ExceptT.mk (TAUT [[(T /\ T <=> T)]])
  let basnet0 ← (CONJUNCTS pth_div).foldrM (fun th net => do
      ExceptT.mk (HolCore.Nets.enter' [] ((← liftExcept (HolCore.Equal.lhand (concl th)),
        (HolLight.REWR_CONV th THENC PROVE_DIVIDES_CONV : HolCore.Equal.ioconv))) net))
      HolCore.Nets.empty_net
  let basnet ← (CONJUNCTS pth_atom).foldrM (fun th net => do
      ExceptT.mk (HolCore.Nets.enter' [] ((← liftExcept (HolCore.Equal.lhand (concl th)),
        (HolLight.REWR_CONV th : HolCore.Equal.ioconv))) net))
      basnet0
  let comp_rewr := HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_comp]
  let rec go (tm : term) : IO (Except String thm) := do
    match ← (HolCore.Lib.tryfindM (fun f => f tm) (HolCore.Nets.lookup tm basnet)) with
    | .ok th => pure (.ok th)
    | .error _ => ExceptT.run do
      let th ← ExceptT.mk ((comp_rewr THENC HolLight.BINOP_CONV go) tm)
      ExceptT.mk (HolLight.TRANS th pth_taut)
  pure go)
#eval IO.println "<fun>"

#eval phrase 85
-- (* Conversion for "?b. b IN bset p /\ P b";; *)
-- let EXISTS_IN_BSET_CONV = ...
unsafe def EXISTS_IN_BSET_CONV : List term → term → IO (Except String thm) :=
  keepE "EXISTS_IN_BSET_CONV" (do
  let pth_false ← prove
   ([[((?b. b IN bset (Lt e) /\ P b) <=> F) /\
     ((?b. b IN bset (Divides c e) /\ P b) <=> F) /\
     ((?b. b IN bset (Ndivides c e) /\ P b) <=> F) /\
     ((?b. b IN bset(Nox Q) /\ P b) <=> F)]])
    (REWRITE_TAC [bset, NOT_IN_EMPTY])
  let pth_neg ← prove
   ([[((?b. b IN bset (Gt e) /\ P b) <=> P(--e)) /\
     ((?b. b IN bset (Ne e) /\ P b) <=> P(--e))]])
    (REWRITE_TAC [bset, IN_SING, INT_MUL_LID, UNWIND_THM2])
  let pth_add ← prove
   ([[(?b. b IN bset (Eq e) /\ P b) <=> P(--(e + &1))]])
    (REWRITE_TAC [bset, IN_SING, INT_MUL_LID, UNWIND_THM2])
  let pth_comp ← prove
   ([[((?b. b IN bset (And p q) /\ P b) <=>
              (?b. b IN bset p /\ P b) \/
              (?b. b IN bset q /\ P b)) /\
     ((?b. b IN bset (Or p q) /\ P b) <=>
              (?b. b IN bset p /\ P b) \/
                   (?b. b IN bset q /\ P b))]])
    (REWRITE_TAC [bset, IN_UNION] THEN MESON_TAC [])
  let taut ← ExceptT.mk (TAUT [[(F \/ P <=> P) /\ (P \/ F <=> P)]])
  let conv_neg : List term → HolCore.Equal.ioconv := fun vars =>
    HolLight.LAND_CONV (HolLight.LAND_CONV (POLYNOMIAL_NEG_CONV vars))
  let conv_add : List term → HolCore.Equal.ioconv := fun vars =>
    HolLight.LAND_CONV (HolLight.LAND_CONV (HolLight.RAND_CONV (POLYNOMIAL_ADD_CONV vars) THENC
                        POLYNOMIAL_NEG_CONV vars))
  let conv_comp := HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_comp]
  let net1 ← (CONJUNCTS pth_false).foldrM (fun th net => do
      ExceptT.mk (HolCore.Nets.enter' [] ((← liftExcept (HolCore.Equal.lhand (concl th)),
        (HolCore.Lib.K (HolLight.REWR_CONV th) : List term → HolCore.Equal.ioconv))) net))
      HolCore.Nets.empty_net
  let net2 ← (CONJUNCTS pth_neg).foldrM (fun th net => do
      let cnv : List term → HolCore.Equal.ioconv := HolCore.Lib.K (HolLight.REWR_CONV th)
      ExceptT.mk (HolCore.Nets.enter' [] ((← liftExcept (HolCore.Equal.lhand (concl th)),
        (fun v => cnv v THENC conv_neg v : List term → HolCore.Equal.ioconv))) net))
      net1
  let basnet ← do
      let cnv : List term → HolCore.Equal.ioconv := HolCore.Lib.K (HolLight.REWR_CONV pth_add)
      ExceptT.mk (HolCore.Nets.enter' [] ((← liftExcept (HolCore.Equal.lhand (concl pth_add)),
        (fun v => cnv v THENC conv_add v : List term → HolCore.Equal.ioconv))) net2)
  let rec baseconv (vars : List term) (tm : term) : IO (Except String thm) := do
    match ← (HolCore.Lib.tryfindM (fun f => f vars tm) (HolCore.Nets.lookup tm basnet)) with
    | .ok th => pure (.ok th)
    | .error _ => (conv_comp THENC HolLight.BINOP_CONV (baseconv vars)) tm
  let finconv :=
    HolLight.GEN_REWRITE_CONV HolLight.DEPTH_CONV [taut] THENC
    HolLight.PURE_REWRITE_CONV [DISJ_ACI]
  pure (fun vars tm => (baseconv vars THENC finconv) tm))
#eval (do let _ ← EXISTS_IN_BSET_CONV [] [[?b. b IN bset (Nox T) /\ T]]; IO.println "<fun>")

#eval phrase 86
-- (* Naive conversion for "minusinf p". *)
-- let MINUSINF_CONV = GEN_REWRITE_CONV TOP_SWEEP_CONV [minusinf];;
unsafe def MINUSINF_CONV : HolCore.Equal.ioconv :=
  HolLight.GEN_REWRITE_CONV HolLight.TOP_SWEEP_CONV [minusinf]
#eval IO.println "<fun>"

#eval phrase 87
-- (* Conversion for "interp s p" where s is a canonical linear form. *)
-- let INTERP_CONV = ...
unsafe def INTERP_CONV : List term → term → IO (Except String thm) :=
  keepE "INTERP_CONV" (do
  let pth_trivial ← prove
   ([[interp x (Nox P) <=> P]])
    (REWRITE_TAC [interp])
  let pth_comp ← prove
   ([[(interp x (And p q) <=> interp x p /\ interp x q) /\
     (interp x (Or p q) <=> interp x p \/ interp x q)]])
    (REWRITE_TAC [interp])
  let (pth_pos, pth_neg) ← CONJ_PAIR (← prove
   ([[((interp x (Lt e)         <=> &0 > x + e) /\
      (interp x (Gt e)         <=> &0 < x + e) /\
      (interp x (Eq e)         <=> (&0 = x + e)) /\
      (interp x (Divides c e)  <=> c divides (x + e))) /\
     ((interp x (Ne e)         <=> ~(&0 = x + e)) /\
      (interp x (Ndivides c e) <=> ~(c divides (x + e))))]])
    (REWRITE_TAC [interp] THEN INT_ARITH_TAC))
  let conv_pos : List term → HolCore.Equal.ioconv := fun vars =>
    HolLight.RAND_CONV (POLYNOMIAL_ADD_CONV vars)
  let conv_neg : List term → HolCore.Equal.ioconv := fun vars =>
    HolLight.RAND_CONV (HolLight.RAND_CONV (POLYNOMIAL_ADD_CONV vars))
  let conv_comp := HolLight.GEN_REWRITE_CONV HolCore.Lib.I [pth_comp]
  let net1 ← (CONJUNCTS pth_trivial).foldrM (fun th net => do
      ExceptT.mk (HolCore.Nets.enter' [] ((← liftExcept (HolCore.Equal.lhand (concl th)),
        (HolCore.Lib.K (HolLight.REWR_CONV th) : List term → HolCore.Equal.ioconv))) net))
      HolCore.Nets.empty_net
  let net2 ← (CONJUNCTS pth_pos).foldrM (fun th net => do
      let cnv : List term → HolCore.Equal.ioconv := HolCore.Lib.K (HolLight.REWR_CONV th)
      ExceptT.mk (HolCore.Nets.enter' [] ((← liftExcept (HolCore.Equal.lhand (concl th)),
        (fun v => cnv v THENC conv_pos v : List term → HolCore.Equal.ioconv))) net))
      net1
  let basnet ← (CONJUNCTS pth_neg).foldrM (fun th net => do
      let cnv : List term → HolCore.Equal.ioconv := HolCore.Lib.K (HolLight.REWR_CONV th)
      ExceptT.mk (HolCore.Nets.enter' [] ((← liftExcept (HolCore.Equal.lhand (concl th)),
        (fun v => cnv v THENC conv_neg v : List term → HolCore.Equal.ioconv))) net))
      net2
  let rec baseconv (vars : List term) (tm : term) : IO (Except String thm) := do
    match ← (HolCore.Lib.tryfindM (fun f => f vars tm) (HolCore.Nets.lookup tm basnet)) with
    | .ok th => pure (.ok th)
    | .error _ => (conv_comp THENC HolLight.BINOP_CONV (baseconv vars)) tm
  pure baseconv)
#eval IO.println "<fun>"

#eval phrase 88
-- (* Expand `?j. &1 <= j /\ j <= &[n] /\ P[j]` cases. *)
-- let EXPAND_INT_CASES_CONV = ...
unsafe def EXPAND_INT_CASES_CONV : term → IO (Except String thm) :=
  keepE "EXPAND_INT_CASES_CONV" (do
  let pth_base ← prove
   ([[(?j. n <= j /\ j <= n /\ P(j)) <=> P(n)]])
    (MESON_TAC [INT_LE_ANTISYM])
  let pth_step ← prove
   ([[(?j. &1 <= j /\ j <= &(SUC n) /\ P(j)) <=>
     (?j. &1 <= j /\ j <= &n /\ P(j)) \/ P(&(SUC n))]])
    (REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM INT_OF_NUM_SUC))] THEN
     REWRITE_TAC [(← ExceptT.mk (INT_ARITH [[x <= y + &1 <=> (x = y + &1) \/ x < y + &1]]))] THEN
     REWRITE_TAC [INT_LT_DISCRETE, INT_LE_RADD] THEN
     MESON_TAC [(← ExceptT.mk (INT_ARITH [[&0 <= x ==> &1 <= x + &1]])), INT_POS, INT_LE_REFL])
  let base_conv := HolLight.REWR_CONV pth_base
  let step_conv :=
    HolLight.BINDER_CONV (HolLight.RAND_CONV (HolLight.LAND_CONV (HolCore.Lib.funpow 2 HolLight.RAND_CONV num_CONV))) THENC
    HolLight.REWR_CONV pth_step THENC
    HolLight.RAND_CONV (HolLight.ONCE_DEPTH_CONV NUM_SUC_CONV)
  let rec conv (tm : term) : IO (Except String thm) := do
    match ← base_conv tm with
    | .ok th => pure (.ok th)
    | .error _ => (step_conv THENC HolLight.LAND_CONV conv) tm
  pure conv)
#eval (do let _ ← EXPAND_INT_CASES_CONV [[?j. &1 <= j /\ j <= &1 /\ j = j]]; IO.println "<fun>")

#eval phrase 89
-- (* Canonicalize "t + c" in all "interp (t + c) P"s assuming t is canonical. *)
-- let CANON_INTERP_ADD = ...
unsafe def CANON_INTERP_ADD : List term → HolCore.Equal.ioconv :=
  let pat := keep "CANON_INTERP_ADD.pat" fun _ =>
    match unsafeIO (HolCore.Parser.parse_term "interp (t + c) P") with | .ok (.ok t) => t | _ => panic! "pat"
  fun vars tm => (do
    match ← Session.net_of_conv pat (HolLight.LAND_CONV (POLYNOMIAL_ADD_CONV vars)) HolCore.Nets.empty_net with
    | .ok net => HolLight.ONCE_DEPTH_CONV (Session.REWRITES_CONV net) tm
    | .error e => pure (.error e))
#eval IO.println "<fun>"

#eval phrase 90
-- (* Conversion to evaluate constant expressions. *)
-- let EVAL_CONSTANT_CONV = ...
unsafe def EVAL_CONSTANT_CONV : term → IO (Except String thm) :=
  keepE "EVAL_CONSTANT_CONV" (do
  let mkEntry (s : String) (c : HolCore.Equal.ioconv) : ExceptT String IO (term × HolCore.Equal.ioconv) := do
    pure ((← ExceptT.mk (HolCore.Parser.parse_term s)), c)
  let mkRew (s : String) : ExceptT String IO (term × HolCore.Equal.ioconv) := do
    let t ← ExceptT.mk (HolCore.Parser.parse_term s)
    let th ← ExceptT.mk (HolLight.REWRITE_CONV [] t)
    pure (t, HolLight.REWR_CONV th)
  let l1 ← (do pure [
    (← mkEntry "x < y" INT_LT_CONV),
    (← mkEntry "x > y" INT_GT_CONV),
    (← mkEntry "x:int = y" INT_EQ_CONV),
    (← mkEntry "x divides y" INT_DIVIDES_CONV)] : ExceptT String IO (List (term × HolCore.Equal.ioconv)))
  let l2 ← (["~F", "~T", "a /\\ T", "T /\\ a", "a /\\ F", "F /\\ a",
             "a \\/ T", "T \\/ a", "a \\/ F", "F \\/ a"].mapM mkRew
            : ExceptT String IO (List (term × HolCore.Equal.ioconv)))
  let net ← (l1 ++ l2).foldrM (fun (pat, cnv) acc => do
      ExceptT.mk (Session.net_of_conv pat cnv acc)) HolCore.Nets.empty_net
  pure (HolLight.DEPTH_CONV (Session.REWRITES_CONV net)))
#eval IO.println "<fun>"

#eval phrase 91
-- (* Basic quantifier elimination conversion. *)
-- let BASIC_COOPER_CONV = ...
unsafe def BASIC_COOPER_CONV : List term → term → IO (Except String thm) :=
  keepE "BASIC_COOPER_CONV" (do
  let p_tm ← ExceptT.mk (HolCore.Parser.parse_term "p:cform")
  let d_tm ← ExceptT.mk (HolCore.Parser.parse_term "d:int")
  let pth_B ← ExceptT.mk (HolLight.SPECL [p_tm, d_tm] MAINTHM_B)
  pure (fun vars tm => ExceptT.run do
    let (_x, _bod) ← liftExcept (dest_exists tm)
    let th1 ← ExceptT.mk ((NORMALIZE_COEFF_CONV vars THENC SHADOW_CONV) tm)
    let p ← liftExcept (do rand (← (do let (_, b) ← dest_exists (← rand (concl th1)); pure b)))
    let th2 ← liftExcept (HolCore.Kernel.INST [(p, p_tm), (← liftExcept (do mk_int_const (← dplcm p)), d_tm)] pth_B)
    let (tm2a, tm2b) ← liftExcept (dest_conj (← liftExcept (HolCore.Equal.lhand (concl th2))))
    let th3 ← do
      let a ← ExceptT.mk (do HolLight.EQT_ELIM (← ExceptT.mk (ALLDIVIDE_CONV tm2a)))
      let b ← ExceptT.mk (do HolLight.EQT_ELIM (← ExceptT.mk (INT_LT_CONV tm2b)))
      HolLight.CONJ a b
    let th4 ← ExceptT.mk (HolLight.TRANS th1 (← ExceptT.mk (HolLight.MP th2 th3)))
    let th5 ← ExceptT.mk (HolLight.CONV_RULE (HolLight.RAND_CONV (HolLight.BINDER_CONV (HolCore.Lib.funpow 2 HolLight.RAND_CONV (HolLight.LAND_CONV
                        MINUSINF_CONV)))) th4)
    let th6 ← ExceptT.mk (HolLight.CONV_RULE (HolLight.RAND_CONV (HolLight.BINDER_CONV (HolCore.Lib.funpow 3 HolLight.RAND_CONV
                        (EXISTS_IN_BSET_CONV vars)))) th5)
    let th7 ← ExceptT.mk (HolLight.CONV_RULE (HolLight.RAND_CONV EXPAND_INT_CASES_CONV) th6)
    let th8 ← ExceptT.mk (HolLight.CONV_RULE (HolLight.RAND_CONV (CANON_INTERP_ADD vars)) th7)
    let th9 ← ExceptT.mk (HolLight.CONV_RULE (HolLight.RAND_CONV (HolLight.ONCE_DEPTH_CONV (INTERP_CONV vars))) th8)
    ExceptT.mk (HolLight.CONV_RULE (HolLight.RAND_CONV EVAL_CONSTANT_CONV) th9)))
#eval IO.println "<fun>"

#eval phrase 92
-- (* NNF transformation that also eliminates negated inequalities. *)
-- let NNF_POSINEQ_CONV = ...
unsafe def NNF_POSINEQ_CONV : List term → HolCore.Equal.ioconv :=
  keepE "NNF_POSINEQ_CONV" (do
  let pth ← prove
   ([[(~(&0 < x) <=> &0 < &1 - x) /\
     (~(&0 > x) <=> &0 < &1 + x)]])
    (REWRITE_TAC [INT_NOT_LT, INT_GT] THEN
     REWRITE_TAC [INT_LT_DISCRETE, INT_GT_DISCRETE] THEN
     INT_ARITH_TAC)
  let pthc1 ← HolLight.CONJUNCT1 pth
  let pthc2 ← HolLight.CONJUNCT2 pth
  let conv1 : List term → HolCore.Equal.ioconv := fun vars =>
    HolLight.REWR_CONV pthc1 THENC
    HolLight.RAND_CONV (POLYNOMIAL_SUB_CONV vars)
  let conv2 : List term → HolCore.Equal.ioconv := fun vars =>
    HolLight.REWR_CONV pthc2 THENC
    HolLight.RAND_CONV (POLYNOMIAL_ADD_CONV vars)
  let pat1 ← ExceptT.mk (HolCore.Parser.parse_term "~(&0 < x)")
  let pat2 ← ExceptT.mk (HolCore.Parser.parse_term "~(&0 > x)")
  let netFinal ← (([ [[~(~ p) <=> p]], [[~(p /\ q) <=> ~p \/ ~q]], [[~(p \/ q) <=> ~p /\ ~q]] ] : List term).foldrM
      (fun t acc => do ExceptT.mk (Session.net_of_conv (← liftExcept (HolCore.Equal.lhand t)) (HolLight.REWR_CONV (← ExceptT.mk (TAUT t))) acc))
      HolCore.Nets.empty_net : ExceptT String IO (HolCore.Nets.net Session.gconv))
  pure (fun vars tm => (do
    let net' ← ExceptT.mk (Session.net_of_conv pat1 (conv1 vars)
                 (← ExceptT.mk (Session.net_of_conv pat2 (conv2 vars) netFinal)))
    ExceptT.mk (HolLight.TOP_SWEEP_CONV (Session.REWRITES_CONV net') tm)).run))
#eval IO.println "<fun>"

#eval phrase 93
-- (* Overall function. *)
-- let COOPER_CONV = ...
unsafe def COOPER_CONV : term → IO (Except String thm) :=
  keepE "COOPER_CONV" (do
  let felim_tm ← ExceptT.mk (HolCore.Parser.parse_term "(!x. P x) <=> ~(?x. ~(P x))")
  let felim_thm ← prove felim_tm (MESON_TAC [])
  let FORALL_ELIM_CONV := HolLight.GEN_REWRITE_CONV HolCore.Lib.I [felim_thm]
  let not_tm ← ExceptT.mk (HolCore.Parser.parse_term "(~)")
  let rec conv (vars : List term) (tm : term) : IO (Except String thm) := ExceptT.run do
    if is_conj tm || is_disj tm then do
      let (lop, r) ← liftExcept (dest_comb tm)
      let (op, l) ← liftExcept (dest_comb lop)
      ExceptT.mk (HolLight.MK_COMB ((← ExceptT.mk (HolLight.AP_TERM op (← ExceptT.mk (conv vars l)))), (← ExceptT.mk (conv vars r))))
    else if is_neg tm then do
      let (l, r) ← liftExcept (dest_comb tm)
      ExceptT.mk (HolLight.AP_TERM l (← ExceptT.mk (conv vars r)))
    else if is_exists tm then do
      let (x, bod) ← liftExcept (dest_exists tm)
      let th1 ← ExceptT.mk (HolLight.MK_EXISTS x (← ExceptT.mk (conv (x :: vars) bod)))
      ExceptT.mk (HolLight.TRANS th1 (← ExceptT.mk (BASIC_COOPER_CONV vars (← liftExcept (rand (concl th1))))))
    else if is_forall tm then do
      let (x, bod) ← liftExcept (dest_forall tm)
      let th1 ← ExceptT.mk (HolLight.AP_TERM not_tm (← ExceptT.mk (conv (x :: vars) bod)))
      let th2 ← ExceptT.mk (HolLight.CONV_RULE (HolLight.RAND_CONV (NNF_POSINEQ_CONV (x :: vars))) th1)
      let th3 ← ExceptT.mk (HolLight.MK_EXISTS x th2)
      let th4 ← ExceptT.mk (HolLight.CONV_RULE (HolLight.RAND_CONV (BASIC_COOPER_CONV vars)) th3)
      let th5 ← ExceptT.mk (HolLight.CONV_RULE (HolLight.RAND_CONV (NNF_POSINEQ_CONV (x :: vars)))
          (← ExceptT.mk (HolLight.AP_TERM not_tm th4)))
      ExceptT.mk (HolLight.TRANS (← ExceptT.mk (FORALL_ELIM_CONV tm)) th5)
    else pure (HolCore.Kernel.REFL tm)
  let init_CONV :=
    PRESIMP_CONV THENC
    HolLight.GEN_REWRITE_CONV HolLight.ONCE_DEPTH_CONV
     [INT_ABS,
      (← ExceptT.mk (INT_ARITH [[max m n = if m <= n then n else m]])),
      (← ExceptT.mk (INT_ARITH [[min m n = if m <= n then m else n]]))] THENC
    CONDS_ELIM_CONV THENC NNF_CONV
  pure (fun tm => ExceptT.run do
    let vars := frees tm
    let th1 ← ExceptT.mk ((init_CONV THENC LINEARIZE_CONV vars) tm)
    let th2 ← ExceptT.mk (HolLight.TRANS th1 (← ExceptT.mk (conv vars (← liftExcept (rand (concl th1))))))
    ExceptT.mk (HolLight.TRANS th2 (← ExceptT.mk (EVAL_CONSTANT_CONV (← liftExcept (rand (concl th2))))))))
#eval (do let _ ← COOPER_CONV [[T]]; IO.println "<fun>")

#eval phrase 94
-- (* Examples from the book. *)
-- time COOPER_CONV `!x y. x < y ==> &2 * x + &1 < &2 * y`;;
#eval (HolCore.Lib.time COOPER_CONV [[!x y. x < y ==> &2 * x + &1 < &2 * y]] : IO (Except String thm))

#eval phrase 95
-- time COOPER_CONV `!x y. ~(&2 * x + &1 = &2 * y)`;;
#eval (HolCore.Lib.time COOPER_CONV [[!x y. ~(&2 * x + &1 = &2 * y)]] : IO (Except String thm))

#eval phrase 96
-- time COOPER_CONV `?x y. x > &0 /\ y >= &0 /\ (&3 * x - &5 * y = &1)`;;
#eval (HolCore.Lib.time COOPER_CONV [[?x y. x > &0 /\ y >= &0 /\ (&3 * x - &5 * y = &1)]] : IO (Except String thm))

#eval phrase 97
-- time COOPER_CONV `?x y z. &4 * x - &6 * y = &1`;;
#eval (HolCore.Lib.time COOPER_CONV [[?x y z. &4 * x - &6 * y = &1]] : IO (Except String thm))

#eval phrase 98
-- time COOPER_CONV `!x. b < x ==> a <= x`;;
#eval (HolCore.Lib.time COOPER_CONV [[!x. b < x ==> a <= x]] : IO (Except String thm))

#eval phrase 99
-- time COOPER_CONV `!x. a < &3 * x ==> b < &3 * x`;;
#eval (HolCore.Lib.time COOPER_CONV [[!x. a < &3 * x ==> b < &3 * x]] : IO (Except String thm))

#eval phrase 100
-- time COOPER_CONV `!x y. x <= y ==> &2 * x + &1 < &2 * y`;;
#eval (HolCore.Lib.time COOPER_CONV [[!x y. x <= y ==> &2 * x + &1 < &2 * y]] : IO (Except String thm))

#eval phrase 101
-- time COOPER_CONV `(?d. y = &65 * d) ==> (?d. y = &5 * d)`;;
#eval (HolCore.Lib.time COOPER_CONV [[(?d. y = &65 * d) ==> (?d. y = &5 * d)]] : IO (Except String thm))

#eval phrase 102
-- time COOPER_CONV `!y. (?d. y = &65 * d) ==> (?d. y = &5 * d)`;;
#eval (HolCore.Lib.time COOPER_CONV [[!y. (?d. y = &65 * d) ==> (?d. y = &5 * d)]] : IO (Except String thm))

#eval phrase 103
-- time COOPER_CONV `!x y. ~(&2 * x + &1 = &2 * y)`;;
#eval (HolCore.Lib.time COOPER_CONV [[!x y. ~(&2 * x + &1 = &2 * y)]] : IO (Except String thm))

#eval phrase 104
-- time COOPER_CONV `!x y z. (&2 * x + &1 = &2 * y) ==> x + y + z > &129`;;
#eval (HolCore.Lib.time COOPER_CONV [[!x y z. (&2 * x + &1 = &2 * y) ==> x + y + z > &129]] : IO (Except String thm))

#eval phrase 105
-- time COOPER_CONV `!x. a < x ==> b < x`;;
#eval (HolCore.Lib.time COOPER_CONV [[!x. a < x ==> b < x]] : IO (Except String thm))

#eval phrase 106
-- time COOPER_CONV `!x. a <= x ==> b < x`;;
#eval (HolCore.Lib.time COOPER_CONV [[!x. a <= x ==> b < x]] : IO (Except String thm))

#eval phrase 107
-- (* Formula examples from Cooper's paper. *)
-- time COOPER_CONV `!a b. ?x. a < &20 * x /\ &20 * x < b`;;
#eval (HolCore.Lib.time COOPER_CONV [[!a b. ?x. a < &20 * x /\ &20 * x < b]] : IO (Except String thm))

#eval phrase 108
-- time COOPER_CONV `?x. a < &20 * x /\ &20 * x < b`;;
#eval (HolCore.Lib.time COOPER_CONV [[?x. a < &20 * x /\ &20 * x < b]] : IO (Except String thm))

#eval phrase 109
-- time COOPER_CONV `!b. ?x. a < &20 * x /\ &20 * x < b`;;
#eval (HolCore.Lib.time COOPER_CONV [[!b. ?x. a < &20 * x /\ &20 * x < b]] : IO (Except String thm))

#eval phrase 110
-- time COOPER_CONV `!a. ?b. a < &4 * b + &3 * a \/ (~(a < b) /\ a > b + &1)`;;
#eval (HolCore.Lib.time COOPER_CONV [[!a. ?b. a < &4 * b + &3 * a \/ (~(a < b) /\ a > b + &1)]] : IO (Except String thm))

#eval phrase 111
-- time COOPER_CONV `?y. !x. x + &5 * y > &1 /\ &13 * x - y > &1 /\ x + &2 < &0`;;
#eval (HolCore.Lib.time COOPER_CONV [[?y. !x. x + &5 * y > &1 /\ &13 * x - y > &1 /\ x + &2 < &0]] : IO (Except String thm))

#eval phrase 112
-- (* More of my own. *)
#eval (HolCore.Lib.time COOPER_CONV [[!x y. x >= &0 /\ y >= &0
                  ==> &12 * x - &8 * y < &0 \/ &12 * x - &8 * y > &2]] : IO (Except String thm))

#eval phrase 113
#eval (HolCore.Lib.time COOPER_CONV [[?x y. &5 * x + &3 * y = &1]] : IO (Except String thm))

#eval phrase 114
#eval (HolCore.Lib.time COOPER_CONV [[?x y. &5 * x + &10 * y = &1]] : IO (Except String thm))

#eval phrase 115
#eval (HolCore.Lib.time COOPER_CONV [[?x y. x >= &0 /\ y >= &0 /\ (&5 * x - &6 * y = &1)]] : IO (Except String thm))

#eval phrase 116
#eval (HolCore.Lib.time COOPER_CONV [[?w x y z. &2 * w + &3 * x + &4 * y + &5 * z = &1]] : IO (Except String thm))

#eval phrase 117
#eval (HolCore.Lib.time COOPER_CONV [[?x y. x >= &0 /\ y >= &0 /\ (&5 * x - &3 * y = &1)]] : IO (Except String thm))

#eval phrase 118
#eval (HolCore.Lib.time COOPER_CONV [[?x y. x >= &0 /\ y >= &0 /\ (&3 * x - &5 * y = &1)]] : IO (Except String thm))

#eval phrase 119
#eval (HolCore.Lib.time COOPER_CONV [[?x y. x >= &0 /\ y >= &0 /\ (&6 * x - &3 * y = &1)]] : IO (Except String thm))

#eval phrase 120
#eval (HolCore.Lib.time COOPER_CONV [[!x y. ~(x = &0) ==> &5 * y < &6 * x \/ &5 * y > &6 * x]] : IO (Except String thm))

#eval phrase 121
#eval (HolCore.Lib.time COOPER_CONV [[!x y. ~(&5 divides x) /\ ~(&6 divides y) ==> ~(&6 * x = &5 * y)]] : IO (Except String thm))

#eval phrase 122
#eval (HolCore.Lib.time COOPER_CONV [[!x y. ~(&5 divides x) ==> ~(&6 * x = &5 * y)]] : IO (Except String thm))

#eval phrase 123
#eval (HolCore.Lib.time COOPER_CONV [[!x y. ~(&6 * x = &5 * y)]] : IO (Except String thm))

#eval phrase 124
#eval (HolCore.Lib.time COOPER_CONV [[!x y. (&6 * x = &5 * y) ==> (?d. y = &3 * d)]] : IO (Except String thm))

#eval phrase 125
#eval (HolCore.Lib.time COOPER_CONV [[(&6 * x = &5 * y) ==> (?d. y = &3 * d)]] : IO (Except String thm))

#eval phrase 126
-- (* Positive variant of the Bezout theorem (see the exercise). *)
#eval (HolCore.Lib.time COOPER_CONV [[!z. z > &7 ==> ?x y. x >= &0 /\ y >= &0 /\ (&3 * x + &5 * y = z)]] : IO (Except String thm))

#eval phrase 127
#eval (HolCore.Lib.time COOPER_CONV [[!z. z > &2 ==> ?x y. x >= &0 /\ y >= &0 /\ (&3 * x + &5 * y = z)]] : IO (Except String thm))

#eval phrase 128
#eval (HolCore.Lib.time COOPER_CONV [[!z. z <= &7 ==>
         ((?x y. x >= &0 /\ y >= &0 /\ (&3 * x + &5 * y = z)) <=>
          ~(?x y. x >= &0 /\ y >= &0 /\ (&3 * x + &5 * y = &7 - z)))]] : IO (Except String thm))

#eval phrase 129
-- (* Basic result about congruences. *)
#eval (HolCore.Lib.time COOPER_CONV [[!x. ~(&2 divides x) /\ &3 divides (x - &1) <=>
                      &12 divides (x - &1) \/ &12 divides (x - &7)]] : IO (Except String thm))

#eval phrase 130
#eval (HolCore.Lib.time COOPER_CONV [[!x. ~(?m. x = &2 * m) /\ (?m. x = &3 * m + &1) <=>
                     (?m. x = &12 * m + &1) \/ (?m. x = &12 * m + &7)]] : IO (Except String thm))

#eval phrase 131
-- (* Something else. *)
#eval (HolCore.Lib.time COOPER_CONV
 [[!x. ~(&2 divides x)
      ==> &4 divides (x - &1) \/
          &8 divides (x - &1) \/
          &8 divides (x - &3) \/
          &6 divides (x - &1) \/
          &14 divides (x - &1) \/
          &14 divides (x - &9) \/
          &14 divides (x - &11) \/
          &24 divides (x - &5) \/
          &24 divides (x - &11)]] : IO (Except String thm))

#eval phrase 132
-- (* Testing fix for an earlier version with negative result from formlcm. *)
#eval (HolCore.Lib.time COOPER_CONV
 [[!a b v_1 v_2 v_3.
    (a + &2 = b) /\ (v_3 = b - a + &1) /\ (v_2 = b - &2) /\ (v_1 = &3) ==> F]] : IO (Except String thm))

#eval phrase 133
-- (* Inspired by the Collatz conjecture. *)
#eval (HolCore.Lib.time COOPER_CONV
 [[?a b. ~(a = &1) /\ ((&2 * b = a) \/ (&2 * b = &3 * a + &1)) /\
              (a = b)]] : IO (Except String thm))

#eval phrase 134
#eval (HolCore.Lib.time COOPER_CONV
 [[?a b. a > &1 /\ b > &1 /\
             ((&2 * b = a) \/ (&2 * b = &3 * a + &1)) /\
             (a = b)]] : IO (Except String thm))

#eval phrase 135
#eval (HolCore.Lib.time COOPER_CONV
 [[?b. a > &1 /\ b > &1 /\
      ((&2 * b = a) \/ (&2 * b = &3 * a + &1)) /\
      ((&2 * a = b) \/ (&2 * a = &3 * b + &1))]] : IO (Except String thm))

#eval phrase 136
-- (*************** These seem to take a long time
-- ... (commented out in HOL Light; see cooper.ml) ...
-- ******************)
-- (* More old examples. *)
#eval (HolCore.Lib.time COOPER_CONV
 [[?x. &5 * x + x + x < x \/
      (y = &7 - x) /\ &33 + z < x /\ x + &1 <= &2 * y \/
      &3 divides &4 * x + z /\ (x + y + z = &7 * z)]] : IO (Except String thm))

#eval phrase 137
#eval (HolCore.Lib.time COOPER_CONV
 [[?x. &5 * x + x + x < x \/
      (y = &7 - x) /\
      &33 + z < x /\
      x + &1 <= &2 * y \/
      &3 divides (&4 * x + z) /\
      (x + y + z = &7 * z)]] : IO (Except String thm))

#eval phrase 138
#eval (HolCore.Lib.time COOPER_CONV
 [[?x. &5 * x + x + x < x \/
      (y = &7 - x) /\
      &33 + z < x /\
      x + &1 <= &2 * y \/
      &3 divides (&4 * x + z) /\
      (x + y + z = &7 * z)]] : IO (Except String thm))

#eval phrase 139
-- (**** This also seems very slow; one quantifier less maybe?
-- ... (commented out in HOL Light; see cooper.ml) ...
-- *****)
#eval (HolCore.Lib.time COOPER_CONV
     [[?x. x + &1 < &2 * y /\
          &3 divides (&4 * x + z) /\
          (&6 * x + y + z = &7 * z)]] : IO (Except String thm))

#eval phrase 140
#eval (HolCore.Lib.time COOPER_CONV
     [[?x. &5 * x + x + x < x \/
          (y = &7 - x) /\
          &33 + z < x /\
          x + &1 < &2 * y \/
          &3 divides (&4 * x + z) /\
          (x + y + z = &7 * z)]] : IO (Except String thm))

#eval phrase 141
-- (* Stamp problem. *)
#eval (HolCore.Lib.time COOPER_CONV [[!x. x >= &8 ==> ?u v. u >= &0 /\ v >= &0 /\
                                         (x = &3 * u + &5 * v)]] : IO (Except String thm))

#eval phrase 142
#eval (HolCore.Lib.time COOPER_CONV [[!x. x >= &10 ==> ?u v. u >= &0 /\ v >= &0 /\
                                         (x = &3 * u + &7 * v)]] : IO (Except String thm))

#eval phrase 143
#eval (HolCore.Lib.time COOPER_CONV [[!x. x >= &30 ==> ?u v. u >= &0 /\ v >= &0 /\
                                         (x = &3 * u + &7 * v)]] : IO (Except String thm))

#eval phrase 144
-- (* Decision procedures in the style of INT_ARITH and ARITH_RULE. *)
-- let INT_COOPER tm = ...
unsafe def INT_COOPER (tm : term) : IO (Except String thm) := ExceptT.run do
  let fvs := frees tm
  let tm' ← liftExcept (HolCore.Bool.list_mk_forall fvs tm)
  HolLight.SPECL fvs (← ExceptT.mk (do HolLight.EQT_ELIM (← ExceptT.mk (COOPER_CONV tm'))))
#eval IO.println "<fun>"

#eval phrase 145
-- let COOPER_RULE tm = ...
unsafe def COOPER_RULE (tm : term) : IO (Except String thm) := ExceptT.run do
  let fvs := frees tm
  let tm' ← liftExcept (HolCore.Bool.list_mk_forall fvs tm)
  let th ← ExceptT.mk ((NUM_TO_INT_CONV THENC COOPER_CONV) tm')
  HolLight.SPECL fvs (← ExceptT.mk (do HolLight.EQT_ELIM th))
#eval IO.println "<fun>"

#eval phrase 146
-- (* Examples. *)
-- time INT_COOPER `abs(x) < &1 ==> (x = &0)`;;
#eval (HolCore.Lib.time INT_COOPER [[abs(x) < &1 ==> (x = &0)]] : IO (Except String thm))

#eval phrase 147
-- time COOPER_RULE `ODD n ==> 2 * n DIV 2 < n`;;
#eval (HolCore.Lib.time COOPER_RULE [[ODD n ==> 2 * n DIV 2 < n]] : IO (Except String thm))

#eval phrase 148
-- time COOPER_RULE `!n. EVEN(n) ==> (2 * n DIV 2 = n)`;;
#eval (HolCore.Lib.time COOPER_RULE [[!n. EVEN(n) ==> (2 * n DIV 2 = n)]] : IO (Except String thm))

#eval phrase 149
-- time COOPER_RULE `!n. ODD n <=> 2 * n DIV 2 < n`;;
#eval (HolCore.Lib.time COOPER_RULE [[!n. ODD n <=> 2 * n DIV 2 < n]] : IO (Except String thm))

#eval phrase 150
-- (**** This seems quite slow ... ****)  (commented out in HOL Light)
-- (*** This one too? ... ***)  (commented out in HOL Light)
-- time COOPER_RULE `!n. n >= 8 ==> ?a b. n = 3 * a + 5 * b`;;
#eval (HolCore.Lib.time COOPER_RULE [[!n. n >= 8 ==> ?a b. n = 3 * a + 5 * b]] : IO (Except String thm))

end HolExamples.Cooper
