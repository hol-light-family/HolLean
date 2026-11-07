/- File: Hol100/Bertrand.lean
Translation of HOL Light's 100/bertrand.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Analysis
import SessionLibrary.Transc
import SessionLibrary.CalcReal
import SessionLibrary.Floor
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Prime SessionLibrary.Analysis SessionLibrary.Floor SessionLibrary.Iter SessionLibrary.Transc SessionLibrary.Pocklington SessionLibrary.CalcReal
namespace Hol100.Bertrand

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
/-- Run an `IO (Except String α)` once, caching under `name` (OCaml's `let`
    evaluates its right-hand side once), for `let` bindings of tuples and lists. -/
private def keepIO {α : Type} [Inhabited α] (name : String) (f : Unit → IO (Except String α)) : α :=
  keep name fun _ =>
    match runIO (f ()) with
    | .ok (.ok v) => v
    | .ok (.error e) => panic! s!"keepIO {name}: {e}"
    | .error e => panic! s!"keepIO {name}: {e}"
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def nc (tm : term) : ExceptT String IO thm := ExceptT.mk (num_CONV tm)
private def nrc (tm : term) : ExceptT String IO thm := ExceptT.mk (NUM_REDUCE_CONV tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)
private def tt (tm : term) : ExceptT String IO thm := ExceptT.mk (TAUT tm)

/- ========================================================================= -/
/- Proof of Bertrand conjecture and weak form of prime number theorem.       -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/prime.ml";;
#eval SessionLibrary.Prime.ensurePrime

#eval phrase 2
-- needs "Library/pocklington.ml";;
#eval SessionLibrary.Pocklington.ensurePocklington

#eval phrase 3
-- needs "Library/analysis.ml";;
#eval SessionLibrary.Analysis.ensureAnalysis

#eval phrase 4
-- needs "Library/transc.ml";;
#eval SessionLibrary.Transc.ensureTransc

#eval phrase 5
-- needs "Library/calc_real.ml";;
#eval SessionLibrary.CalcReal.ensureCalcReal

#eval phrase 6
-- needs "Library/floor.ml";;
#eval SessionLibrary.Floor.ensureFloor

#eval phrase 7
#eval Session.prioritize_real

/- ------------------------------------------------------------------------- -/
/- A ridiculous ommission from the OCaml Num library.                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 8
-- let num_of_float = ...;;  (frexp-based exact conversion of a float)
def num_of_float (x : Float) : ExceptT String IO Rat := do
  let p22 : Float := Float.pow 2.0 22.0
  let q : Nat → Rat := fun k => (2 : Rat) ^ k
  let (y0, n) := x.frExp
  let u0 := (y0 * p22).toUInt64.toNat
  let y1 := p22 * y0 - Float.ofNat u0
  let u1 := (y1 * p22).toUInt64.toNat
  let y2 := p22 * y1 - Float.ofNat u1
  let u2 := (y2 * p22).toUInt64.toNat
  let y3 := p22 * y2 - Float.ofNat u2
  if y3 != 0.0 then throw "num_of_float: inexactness!"
  let pw : Rat := if n ≥ 0 then (2 : Rat) ^ n.toNat else 1 / (2 : Rat) ^ (-n).toNat
  pure (((u0 : Rat) / q 22 + (u1 : Rat) / q 44 + (u2 : Rat) / q 66) * pw)
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Integer truncated square root                                             -/
/- ------------------------------------------------------------------------- -/

#eval phrase 9
def ISQRT : thm := keep "ISQRT" fun _ => new_definition
 [[ISQRT n = @m. m EXP 2 <= n /\ n < (m + 1) EXP 2]]
#eval ISQRT

#eval phrase 10
def ISQRT_WORKS : thm := keep "ISQRT_WORKS" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[~(m + 1 <= m)]])
  prove ([[!n. ISQRT(n) EXP 2 <= n /\ n < (ISQRT(n) + 1) EXP 2]])
   (GEN_TAC THEN REWRITE_TAC [ISQRT] THEN CONV_TAC (pureC SELECT_CONV) THEN
    SUBGOAL_THEN ([[(?m. m EXP 2 <= n) /\ (?a. !m. m EXP 2 <= n ==> m <= a)]]) MP_TAC THENL
     [ALL_TAC,
      ONCE_REWRITE_TAC [num_MAX] THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      MESON_TAC [h1, NOT_LE]] THEN
    CONJ_TAC THENL [EXISTS_TAC ([[0]]) THEN REWRITE_TAC [ARITH, LE_0], ALL_TAC] THEN
    EXISTS_TAC ([[n:num]]) THEN X_GEN_TAC ([[m:num]]) THEN
    MESON_TAC [LE_SQUARE_REFL, EXP_2, LE_TRANS])
  : ExceptT String IO thm).run
#eval ISQRT_WORKS

#eval phrase 11
def ISQRT_0 : thm := keep "ISQRT_0" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[x <= 0 <=> (x = 0)]])
  prove ([[ISQRT 0 = 0]])
   (MP_TAC (← HolLight.SPEC ([[0]]) ISQRT_WORKS) THEN
    SIMP_TAC [h1, EXP_EQ_0, ARITH_EQ])
  : ExceptT String IO thm).run
#eval ISQRT_0

#eval phrase 12
def ISQRT_UNIQUE : thm := keep "ISQRT_UNIQUE" fun _ => (do
  let h1 ← nc (← ExceptT.mk [[2]])
  prove ([[!m n. (ISQRT n = m) <=> m EXP 2 <= n /\ n < (m + 1) EXP 2]])
   (REPEAT GEN_TAC THEN EQ_TAC THEN MP_TAC (← HolLight.SPEC ([[n:num]]) ISQRT_WORKS) THENL
     [MESON_TAC [], ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[(ISQRT n) EXP 2 < (m + 1) EXP 2 /\
                m EXP 2 < (ISQRT n + 1) EXP 2]]) MP_TAC THENL
     [ASM_MESON_TAC [LT_SUC_LE, LE_SUC_LT, LET_TRANS, LTE_TRANS],
      SIMP_TAC [h1, EXP_MONO_LT, NOT_SUC, (← HolLight.GSYM LE_ANTISYM)] THEN ARITH_TAC])
  : ExceptT String IO thm).run
#eval ISQRT_UNIQUE

#eval phrase 13
def ISQRT_SUC : thm := keep "ISQRT_SUC" fun _ => (do
  let h2 ← nc (← ExceptT.mk [[2]])
  let h1 ← ar (← ExceptT.mk [[a <= n /\ n < b /\ ~(SUC n = a) /\ ~(SUC n = b)
      ==> a <= SUC n /\ SUC n < b]])
  prove ([[!n. ISQRT(SUC n) =
       if ?m. SUC n = m EXP 2 then SUC(ISQRT n) else ISQRT n]])
   (GEN_TAC THEN REWRITE_TAC [ISQRT_UNIQUE] THEN COND_CASES_TAC THENL
     [ALL_TAC,
      ASM_MESON_TAC [ISQRT_WORKS, h1]] THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MP_TAC (← HolLight.CONJUNCT2 (← HolLight.SPEC ([[n:num]]) ISQRT_WORKS)) THEN
      REWRITE_TAC [EXP_2, (← HolLight.GSYM ADD1), MULT_CLAUSES, ADD_CLAUSES, LT_SUC] THEN
      ARITH_TAC] THEN
    POP_ASSUM (X_CHOOSE_TAC ([[m:num]])) THEN
    SUBGOAL_THEN ([[m = SUC(ISQRT n)]]) SUBST_ALL_TAC THENL
     [ALL_TAC, ASM_REWRITE_TAC [LE_REFL]] THEN
    SUBGOAL_THEN ([[ISQRT(n) EXP 2 < m EXP 2 /\ m EXP 2 <= SUC(ISQRT n) EXP 2]]) MP_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [h2, EXP_MONO_LE, EXP_MONO_LT, NOT_SUC] THEN
      ARITH_TAC] THEN
    MP_TAC (← HolLight.SPEC ([[n:num]]) ISQRT_WORKS) THEN REWRITE_TAC [ADD1] THEN
    FIRST_X_ASSUM (SUBST1_TAC o HolLight.SYM) THEN REWRITE_TAC [LT_SUC_LE, LE_SUC_LT])
  : ExceptT String IO thm).run
#eval ISQRT_SUC

/- ------------------------------------------------------------------------- -/
/- To allow us to deal with ln(2) numerically using standard conversion.     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 14
def LN_2_COMPOSITION : thm := keep "LN_2_COMPOSITION" fun _ => (do
  prove ([[ln(&2) =
   &7 * ln(&1 + inv(&8)) - &2 * ln(&1 + inv(&24)) - &4 * ln(&1 + inv(&80))]])
   (CONV_TAC (← ExceptT.mk (HolCore.Simp.GEN_SIMPLIFY_CONV Session.B (HolCore.Simp.TOP_DEPTH_SQCONV Session.B)
      (← ExceptT.mk (HolCore.Simp.basic_ss Session.B [])) 4 [(← HolLight.GSYM LN_POW), (← HolLight.GSYM LN_MUL), (← HolLight.GSYM LN_DIV), REAL_POW_LT, real_div,
           SessionLibrary.Analysis.REAL_LT_ADD, REAL_LT_MUL, REAL_LT_INV_EQ, REAL_OF_NUM_LT, ARITH])) THEN
    AP_TERM_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval LN_2_COMPOSITION

/- ------------------------------------------------------------------------- -/
/- Automatically process any ln(n) to allow us to use standard conversions.  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 15
-- let LN_N_CONV = ...;;
def LN_N_CONV_pth : thm := keep "LN_N_CONV_pth" fun _ => (do
  prove ([[x = (&1 + inv(&8)) pow n * (x / (&1 + inv(&8)) pow n)]])
   (CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
    MATCH_MP_TAC REAL_POW_NZ THEN CONV_TAC REAL_RAT_REDUCE_CONV)
  : ExceptT String IO thm).run
def LN_N_CONV_qth : thm := keep "LN_N_CONV_qth" fun _ => (do
  let h2 ← ExceptT.mk (REAL_RAT_REDUCE_CONV (← ExceptT.mk [[&0 < &1 + inv(&8)]]))
  let h1 ← ExceptT.mk (Session.REAL_ARITH3 (← ExceptT.mk [[&1 + (x - &1) = x]]))
  prove ([[&0 < x
     ==> (ln((&1 + inv(&8)) pow n * x / (&1 + inv(&8)) pow n) =
          &n * ln(&1 + inv(&8)) + ln(&1 + (x / (&1 + inv(&8)) pow n - &1)))]])
   (REWRITE_TAC [h1] THEN
    SIMP_TAC [LN_MUL, LN_POW, REAL_LT_DIV, REAL_POW_LT, h2])
  : ExceptT String IO thm).run
def LN_N_CONV (tm0 : term) : IO (Except String thm) := (do
  let ln_tm ← ExceptT.mk [[ln]]
  let x_tm ← ExceptT.mk [[x:real]]
  let n_tm ← ExceptT.mk [[n:num]]
  let (ltm, tm) ← ec (dest_comb tm0)
  if ltm != ln_tm then throw "expected ln(ratconst)"
  let x ← ec (rat_of_term tm)
  let rec dlog (fuel : Nat) (n : Nat) (y : Rat) : Nat :=
    match fuel with
    | 0 => n
    | fuel + 1 => let y' := y + y / 8; if y' < x then dlog fuel (n + 1) y' else n
  let n := dlog 100000 0 1
  let th1 ← HolLight.INST [(← ec (mk_small_numeral (Int.ofNat n)), n_tm), (tm, x_tm)] LN_N_CONV_pth
  let th2 ← HolLight.AP_TERM ltm th1
  let th3 ← HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) LN_N_CONV_qth
    (← ec (HolCore.Kernel.rand (concl th2)))
  let th4 ← HolLight.MP th3 (← HolLight.EQT_ELIM
    (← ExceptT.mk (REAL_RAT_REDUCE_CONV (← ec (HolCore.Equal.lhand (concl th3))))))
  let th5 ← HolLight.TRANS th2 th4
  HolLight.CONV_RULE (HolCore.Lib.funpow 4 HolLight.RAND_CONV REAL_RAT_REDUCE_CONV) th5
  : ExceptT String IO thm).run
#eval (do replay LN_N_CONV_pth; replay LN_N_CONV_qth; IO.println "<fun>" : IO Unit)

/- ------------------------------------------------------------------------- -/
/- Coarser version subtracting off multiples of ln(2) first, then using it.  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 16
-- let LN_N2_CONV = ...;;
def LN_N2_CONV_pth : thm := keep "LN_N2_CONV_pth" fun _ => (do
  prove ([[x = &2 pow n * (x / &2 pow n)]])
   (CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
    MATCH_MP_TAC REAL_POW_NZ THEN CONV_TAC REAL_RAT_REDUCE_CONV)
  : ExceptT String IO thm).run
def LN_N2_CONV_qth : thm := keep "LN_N2_CONV_qth" fun _ => (do
  let h2 ← ExceptT.mk (REAL_RAT_REDUCE_CONV (← ExceptT.mk [[&0 < &2]]))
  let h1 ← ExceptT.mk (Session.REAL_ARITH3 (← ExceptT.mk [[&1 + (x - &1) = x]]))
  prove ([[&0 < x
     ==> (ln(&2 pow n * x / &2 pow n) =
          &n * ln(&2) + ln(&1 + (x / &2 pow n - &1)))]])
   (REWRITE_TAC [h1] THEN
    SIMP_TAC [LN_MUL, LN_POW, REAL_LT_DIV, REAL_POW_LT, h2])
  : ExceptT String IO thm).run
def LN_N2_CONV (tm0 : term) : IO (Except String thm) := (do
  let ln_tm ← ExceptT.mk [[ln]]
  let x_tm ← ExceptT.mk [[x:real]]
  let n_tm ← ExceptT.mk [[n:num]]
  let (ltm, tm) ← ec (dest_comb tm0)
  if ltm != ln_tm then throw "expected ln(ratconst)"
  let x ← ec (rat_of_term tm)
  let rec dlog (fuel : Nat) (n : Nat) (y : Rat) : Nat :=
    match fuel with
    | 0 => n
    | fuel + 1 => let y' := y * 2; if y' < x then dlog fuel (n + 1) y' else n
  let n := dlog 100000 0 1
  let th1 ← HolLight.INST [(← ec (mk_small_numeral (Int.ofNat n)), n_tm), (tm, x_tm)] LN_N2_CONV_pth
  let th2 ← HolLight.AP_TERM ltm th1
  let th3 ← HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) LN_N2_CONV_qth
    (← ec (HolCore.Kernel.rand (concl th2)))
  let th4 ← HolLight.MP th3 (← HolLight.EQT_ELIM
    (← ExceptT.mk (REAL_RAT_REDUCE_CONV (← ec (HolCore.Equal.lhand (concl th3))))))
  let th5 ← HolLight.TRANS th2 th4
  let th6 ← HolLight.CONV_RULE (HolCore.Lib.funpow 4 HolLight.RAND_CONV REAL_RAT_REDUCE_CONV) th5
  let th7 ← HolLight.CONV_RULE (HolCore.Lib.funpow 3 HolLight.RAND_CONV REAL_RAT_REDUCE_CONV) th6
  HolLight.CONV_RULE (HolLight.RAND_CONV (HolLight.ONCE_DEPTH_CONV LN_N_CONV)) th7
  : ExceptT String IO thm).run
#eval (do replay LN_N2_CONV_pth; replay LN_N2_CONV_qth; IO.println "<fun>" : IO Unit)

/- ------------------------------------------------------------------------- -/
/- Lemmas about floor and frac.                                              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 17
def FLOOR_DOUBLE_NUM : thm := keep "FLOOR_DOUBLE_NUM" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[b < a ==> n + a <= c ==> n + b < c]])
  prove ([[!n r d.
        d < 2 /\ 0 < r
        ==> &2 * floor(&n / &r) <= floor(&(2 * n + d) / &r) /\
            floor(&(2 * n + d) / &r) <= &2 * floor(&n / &r) + &1]])
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[floor(&n / &r) = floor((&n + &d / &2) / &r)]]) SUBST1_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_ADD), (← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
      SUBGOAL_THEN ([[&2 * &n + &d = &2 * (&n + &d / &2)]]) SUBST1_TAC THENL
       [SIMP_TAC [REAL_ADD_LDISTRIB, REAL_DIV_LMUL, REAL_OF_NUM_EQ, ARITH_EQ],
        ALL_TAC] THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_ADD_LDISTRIB), (← HolLight.GSYM REAL_MUL_ASSOC), real_div] THEN
      REWRITE_TAC [(← HolLight.GSYM real_div), FLOOR_DOUBLE]] THEN
    CONV_TAC HolLight.SYM_CONV THEN REWRITE_TAC [(← HolLight.GSYM FLOOR_UNIQUE)] THEN
    MP_TAC (← HolLight.SPEC ([[&n / &r]]) FLOOR) THEN SIMP_TAC [] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN EXISTS_TAC ([[&n / &r]]) THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [real_div, REAL_ADD_RDISTRIB, REAL_LE_ADDR] THEN
      SIMP_TAC [SessionLibrary.Analysis.REAL_LE_MUL, SessionLibrary.Analysis.REAL_POS, REAL_LE_INV_EQ],
      ALL_TAC] THEN
    UNDISCH_TAC ([[&n / &r < floor (&n / &r) + &1]]) THEN
    ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_OF_NUM_LT] THEN
    SIMP_TAC [REAL_LT_INTEGERS, FLOOR, INTEGER_CLOSED] THEN
    MATCH_MP_TAC h1 THEN
    ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_MUL_LID, REAL_OF_NUM_LT, ARITH])
  : ExceptT String IO thm).run
#eval FLOOR_DOUBLE_NUM

/- ------------------------------------------------------------------------- -/
/- Range bounds on ln(n!).                                                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 18
def LN_FACT : thm := keep "LN_FACT" fun _ => (do
  prove ([[!n. ln(&(FACT n)) = sum(1,n) (\d. ln(&d))]])
   (INDUCT_TAC THEN REWRITE_TAC [FACT, SessionLibrary.Analysis.sum, LN_1] THEN
    SIMP_TAC [(← HolLight.GSYM REAL_OF_NUM_MUL), LN_MUL, REAL_OF_NUM_LT, FACT_LT, LT_0] THEN
    ASM_REWRITE_TAC [ADD1] THEN REWRITE_TAC [ADD_AC, REAL_ADD_AC])
  : ExceptT String IO thm).run
#eval LN_FACT

#eval phrase 19
def LN_FACT_BOUNDS : thm := keep "LN_FACT_BOUNDS" fun _ => (do
  let h13 ← rr (← ExceptT.mk [[(a + b) - c - (a - c) = b]])
  let h12 ← ar (← ExceptT.mk [[2 + n = SUC(1 + n)]])
  let h11 ← ar (← ExceptT.mk [[~(r = 0) <=> 1 <= r]])
  let h10 ← ar (← ExceptT.mk [[0 < r <=> 1 <= r]])
  let h9 ← rr (← ExceptT.mk [[a < b /\ b < c ==> abs(c - b) <= c - a]])
  let h8 ← nrc (← ExceptT.mk [[0 + 1]])
  let h7 ← rr (← ExceptT.mk [[abs(x - (y - z)) <= a ==> abs(x - (y - (z + &1))) <= &1 + a]])
  let h6 ← rr (← ExceptT.mk [[(a = b + c * &1) <=> (b = a - c)]])
  let h5 ← rr (← ExceptT.mk [[(a - b = c) <=> (a = b + c)]])
  let h4 ← ar (← ExceptT.mk [[SUC(n + 1) = n + 2]])
  let h3 ← ar (← ExceptT.mk [[(n + 1) + 1 = n + 2]])
  let h2 ← rr (← ExceptT.mk [[a < a + &1]])
  let h1 ← rr (← ExceptT.mk [[(n + &1) - n = &1]])
  prove ([[!n. ~(n = 0) ==> abs(ln(&(FACT n)) - (&n * ln(&n) - &n)) <= &1 + ln(&n)]])
   (SUBGOAL_THEN ([[!n. ~(n = 0)
        ==> ?z. &n < z /\ z < &(n + 1) /\
                (&(n + 1) * ln(&(n + 1)) - &n * ln(&n) = ln(z) + &1)]]) MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC (← HolLight.SPECL [([[\x. x * ln(x)]]), ([[\x. ln(x) + &1]]), ([[&n]]), ([[&(n + 1)]])] MVT_ALT) THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_ADD)] THEN
      REWRITE_TAC [h1] THEN
      REWRITE_TAC [REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC [h2] THEN
      X_GEN_TAC ([[x:real]]) THEN STRIP_TAC THEN
      MP_TAC (← HolLight.SPEC ([[x:real]]) (← ExceptT.mk (DIFF_CONV ([[\x. x * ln(x)]])))) THEN
      SIMP_TAC [REAL_MUL_LID, SessionLibrary.Analysis.REAL_MUL_RID, REAL_MUL_LINV, SessionLibrary.Analysis.REAL_LT_IMP_NZ] THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC SessionLibrary.Analysis.REAL_LTE_TRANS THEN
      EXISTS_TAC ([[&n]]) THEN ASM_REWRITE_TAC [REAL_OF_NUM_LT] THEN
      UNDISCH_TAC ([[~(n = 0)]]) THEN ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [RIGHT_IMP_EXISTS_THM, SKOLEM_THM] THEN
    DISCH_THEN (X_CHOOSE_TAC ([[k:num->real]])) THEN
    SUBGOAL_THEN ([[!n. &(n + 1) * ln(&(n + 1)) = sum(1,n) (\i. ln(k i) + &1)]]) MP_TAC THENL
     [INDUCT_TAC THEN REWRITE_TAC [NOT_SUC] THEN
      REWRITE_TAC [SessionLibrary.Analysis.sum, ADD_CLAUSES, LN_1, SessionLibrary.Analysis.REAL_MUL_RZERO] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[n + 1]])) THEN
      REWRITE_TAC [ADD_EQ_0, ARITH_EQ] THEN
      REWRITE_TAC [h3,
                  h4] THEN
      DISCH_THEN (MP_TAC o (HolCore.Lib.last (α := thm)) o HolLight.CONJUNCTS) THEN
      REWRITE_TAC [h5] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [ADD_AC],
      ALL_TAC] THEN
    REWRITE_TAC [SessionLibrary.Analysis.SUM_ADD] THEN
    CONV_TAC (HolLight.LAND_CONV (HolLight.BINDER_CONV (HolLight.RAND_CONV (HolLight.RAND_CONV (HolLight.LAND_CONV (HolLight.LAND_CONV num_CONV)))))) THEN
    REWRITE_TAC [ADD1, SUM_REINDEX, SessionLibrary.Analysis.SUM_CONST] THEN
    ONCE_REWRITE_TAC [h6] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN ([[!n. abs(sum(1,n+1) (\i. ln(&i)) - (&(n + 1) * ln (&(n + 1)) - &(n + 1)))
        <= &1 + ln(&(n + 1))]]) ASSUME_TAC THENL
     [GEN_TAC THEN
      GEN_REWRITE_TAC (HolLight.LAND_CONV o HolCore.Lib.funpow 3 HolLight.RAND_CONV) [(← HolLight.GSYM REAL_OF_NUM_ADD)] THEN
      MATCH_MP_TAC h7 THEN
      FIRST_ASSUM (fun th => HolLight.tactic_of do
        pure (GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV o HolLight.RAND_CONV) [(← HolLight.GSYM th)])) THEN
      SUBGOAL_THEN ([[sum(1,n + 1) (\i. ln (&i)) = sum(1,n) (\i. ln(&(i + 1)))]]) SUBST1_TAC THENL
       [GEN_REWRITE_TAC HolLight.RAND_CONV [SessionLibrary.Analysis.SUM_DIFF] THEN
        REWRITE_TAC [SUM_1, ADD_CLAUSES, LN_1, SessionLibrary.Analysis.REAL_SUB_RZERO] THEN
        GEN_REWRITE_TAC (HolCore.Lib.funpow 3 HolLight.LAND_CONV) [(← HolLight.SYM h8)] THEN
        REWRITE_TAC [SUM_REINDEX] THEN REWRITE_TAC [ADD_AC],
        ALL_TAC] THEN
      REWRITE_TAC [(← HolLight.GSYM SessionLibrary.Analysis.SUM_SUB)] THEN
      MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
      EXISTS_TAC ([[sum(1,n) (\n. abs(ln(&(n + 1)) - ln(k n)))]]) THEN
      REWRITE_TAC [ABS_SUM] THEN
      MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
      EXISTS_TAC ([[sum(1,n) (\i. ln(&(i + 1)) - ln(&i))]]) THEN CONJ_TAC THENL
       [MATCH_MP_TAC SessionLibrary.Analysis.SUM_LE THEN X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN
        REWRITE_TAC [] THEN
        MATCH_MP_TAC h9 THEN
        SUBGOAL_THEN ([[&0 < &r /\ &r < k r /\ k r < &(r + 1)]]) MP_TAC THENL
         [ALL_TAC, MESON_TAC [LN_MONO_LT, REAL_LT_TRANS]] THEN
        ASM_SIMP_TAC [REAL_OF_NUM_LT, h10,
                     h11],
        ALL_TAC] THEN
      REWRITE_TAC [SessionLibrary.Analysis.SUM_SUB] THEN
      REWRITE_TAC [(← HolLight.GSYM (← HolLight.SPECL [([[f:num->real]]), ([[m:num]]), ([[1]])] SUM_REINDEX))] THEN
      ONCE_REWRITE_TAC [SessionLibrary.Analysis.SUM_DIFF] THEN
      REWRITE_TAC [ARITH, SUM_2, SUM_1, LN_1, REAL_ADD_RID] THEN
      ONCE_REWRITE_TAC [h12] THEN
      REWRITE_TAC [SessionLibrary.Analysis.sum, ADD_CLAUSES] THEN
      REWRITE_TAC [ADD_AC] THEN
      REWRITE_TAC [h13, SessionLibrary.Analysis.REAL_LE_REFL],
      ALL_TAC] THEN
    INDUCT_TAC THEN REWRITE_TAC [NOT_SUC] THEN
    ASM_REWRITE_TAC [ADD1, LN_FACT])
  : ExceptT String IO thm).run
#eval LN_FACT_BOUNDS

/- ------------------------------------------------------------------------- -/
/- Some extra number-theoretic odds and ends are useful.                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 20
def primepow : thm := keep "primepow" fun _ => new_definition
 [[primepow q <=> ?p k. 1 <= k /\ prime p /\ (q = p EXP k)]]
#eval primepow

#eval phrase 21
def aprimedivisor : thm := keep "aprimedivisor" fun _ => new_definition
 [[aprimedivisor q = @p. prime p /\ p divides q]]
#eval aprimedivisor

#eval phrase 22
def PRIMEPOW_GE_2 : thm := keep "PRIMEPOW_GE_2" fun _ => (do
  prove ([[!q. primepow q ==> 2 <= q]])
   (REWRITE_TAC [primepow, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [([[q:num]]), ([[p:num]]), ([[k:num]])] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[p:num]]) THEN
    ASM_SIMP_TAC [PRIME_GE_2] THEN GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM EXP_1)] THEN
    REWRITE_TAC [LE_EXP] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [ARITH])
  : ExceptT String IO thm).run
#eval PRIMEPOW_GE_2

#eval phrase 23
def PRIMEPOW_0 : thm := keep "PRIMEPOW_0" fun _ => (do
  let h1 ← nrc (← ExceptT.mk [[2 <= 0]])
  prove ([[~(primepow 0)]])
   (MESON_TAC [h1, PRIMEPOW_GE_2])
  : ExceptT String IO thm).run
#eval PRIMEPOW_0

#eval phrase 24
def APRIMEDIVISOR_PRIMEPOW : thm := keep "APRIMEDIVISOR_PRIMEPOW" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[1 <= k ==> (k = SUC(k - 1))]])
  prove ([[!p k. prime p /\ 1 <= k ==> (aprimedivisor(p EXP k) = p)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [aprimedivisor] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC [] THEN
    X_GEN_TAC ([[q:num]]) THEN
    FIRST_ASSUM (SUBST1_TAC o HolLight.MATCH_MP h1) THEN
    REWRITE_TAC [EXP] THEN
    ASM_MESON_TAC [DIVIDES_REFL, DIVIDES_RMUL, PRIME_DIVEXP, PRIME_DIVPROD,
                  prime, PRIME_1])
  : ExceptT String IO thm).run
#eval APRIMEDIVISOR_PRIMEPOW

#eval phrase 25
def APRIMEDIVISOR : thm := keep "APRIMEDIVISOR" fun _ => (do
  prove ([[!n. ~(n = 1) ==> prime(aprimedivisor n) /\ (aprimedivisor n) divides n]])
   (GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [aprimedivisor] THEN
    CONV_TAC (pureC SELECT_CONV) THEN ASM_SIMP_TAC [PRIME_FACTOR])
  : ExceptT String IO thm).run
#eval APRIMEDIVISOR

#eval phrase 26
def BIG_POWER_LEMMA : thm := keep "BIG_POWER_LEMMA" fun _ => (do
  prove ([[!m n. 2 <= m ==> ?k. n <= m EXP k]])
   (REPEAT STRIP_TAC THEN EXISTS_TAC ([[SUC n]]) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[2 EXP (SUC n)]]) THEN
    ASM_REWRITE_TAC [EXP_MONO_LE, NOT_SUC] THEN
    SPEC_TAC (([[n:num]]), ([[n:num]])) THEN INDUCT_TAC THEN
    REWRITE_TAC [EXP, ARITH] THEN
    UNDISCH_TAC ([[n <= 2 EXP SUC n]]) THEN REWRITE_TAC [EXP] THEN
    MP_TAC (← HolLight.SPECL [([[2:num]]), ([[n:num]])] EXP_EQ_0) THEN
    REWRITE_TAC [ARITH] THEN SPEC_TAC (([[2 EXP n]]), ([[m:num]])) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval BIG_POWER_LEMMA

#eval phrase 27
def PRIME_PRIMEPOW : thm := keep "PRIME_PRIMEPOW" fun _ => (do
  prove ([[!p. prime p ==> primepow p]])
   (MESON_TAC [prime, primepow, LE_REFL, EXP_1])
  : ExceptT String IO thm).run
#eval PRIME_PRIMEPOW

/- ------------------------------------------------------------------------- -/
/- Derive Bezout-type identity by finding gcd.                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 28
-- let rec bezout (m,n) = ...;;
partial def bezout : Rat × Rat → Rat × Rat
  | (m, n) =>
    if m == 0 then (0, 1) else if n == 0 then (1, 0)
    else if m <= n then
      let q := Rat.ofInt (Int.fdiv n.num m.num)   -- quo_num on naturals
      let r := n - q * m                           -- mod_num
      let (x, y) := bezout (m, r)
      (x - q * y, y)
    else let (x, y) := bezout (n, m); (y, x)
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Conversion for "primepow" applied to particular numeral.                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 29
-- let PRIMEPOW_CONV = ...;;
def PRIMEPOW_CONV_pths : thm × thm × thm × thm := keepIO "PRIMEPOW_CONV_pths" fun _ => (do
  let pth0 ← prove ([[primepow 0 <=> F]])
   (REWRITE_TAC [primepow] THEN MESON_TAC [EXP_EQ_0, PRIME_0])
  let pth1 ← prove ([[primepow 1 <=> F]])
   (REWRITE_TAC [primepow] THEN
    MESON_TAC [EXP_EQ_1, PRIME_1, (← ExceptT.mk (NUM_REDUCE_CONV (← ExceptT.mk [[1 <= 0]])))])
  let pth2 ← prove ([[prime p ==> 1 <= k /\ (q = p EXP k) ==> (primepow q <=> T)]])
   (MESON_TAC [primepow])
  let pth3 ← prove ([[(p * x = r * y + 1) /\ ~(p = 1) /\ ~(r = 1) /\ (q = p * r * d)
     ==> (primepow q <=> F)]])
   (    REPEAT STRIP_TAC THEN
    REWRITE_TAC [primepow] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[P:num]]) MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) MP_TAC) THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC (← HolLight.SPEC ([[r:num]]) PRIME_FACTOR) THEN
    MP_TAC (← HolLight.SPEC ([[p:num]]) PRIME_FACTOR) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[P_p:num]]) MP_TAC) THEN
    REWRITE_TAC [divides] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d_p:num]]) SUBST_ALL_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[P_r:num]]) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d_r:num]]) SUBST_ALL_TAC) THEN
    SUBGOAL_THEN ([[P_p divides P /\ P_r divides P]]) ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC ([[k:num]]) THEN
      ASM_MESON_TAC [divides, MULT_AC], ALL_TAC] THEN
    SUBGOAL_THEN ([[(P_p = P) /\ (P_r = P:num)]]) (CONJUNCTS_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC [prime], ALL_TAC] THEN
    ASM_MESON_TAC [DIVIDES_ADD_REVR, divides, MULT_AC, DIVIDES_ONE, prime])
  pure (pth0, pth1, pth2, pth3)
  : ExceptT String IO (thm × thm × thm × thm)).run

def PRIMEPOW_CONV (tm0 : term) : IO (Except String thm) := (do
  let (pth0, pth1, pth2, pth3) := PRIMEPOW_CONV_pths
  let p_tm ← ExceptT.mk [[p:num]]
  let k_tm ← ExceptT.mk [[k:num]]
  let q_tm ← ExceptT.mk [[q:num]]
  let r_tm ← ExceptT.mk [[r:num]]
  let d_tm ← ExceptT.mk [[d:num]]
  let x_tm ← ExceptT.mk [[x:num]]
  let y_tm ← ExceptT.mk [[y:num]]
  let f_tm ← ExceptT.mk [[primepow]]
  let (ptm, tm) ← ec (dest_comb tm0)
  if ptm != f_tm then throw "expected primepow(numeral)"
  let q ← ec (HolCore.Basics.dest_numeral tm)
  if q == 0 then return pth0
  else if q == 1 then return pth1
  match ← SessionLibrary.Pocklington.factor q with
  | [] => throw "internal failure in PRIMEPOW_CONV"
  | [(p, k)] =>
    let th1 ← HolLight.INST [(← ec (mk_numeral q), q_tm), (← ec (mk_numeral p), p_tm),
                             (← ec (mk_numeral k), k_tm)] pth2
    let th2 ← HolLight.MP th1 (← HolLight.EQT_ELIM
      (← ExceptT.mk (PRIME_CONV (← ec (HolCore.Equal.lhand (concl th1))))))
    HolLight.MP th2 (← HolLight.EQT_ELIM
      (← ExceptT.mk (NUM_REDUCE_CONV (← ec (HolCore.Equal.lhand (concl th2))))))
  | (p, _) :: (r, _) :: _ =>
    let d := q / (p * r)
    let (x, y) := bezout (p, r)
    let (p, r, x, y) := if x < 0 then (r, p, y, -x) else (p, r, x, -y)
    let th1 ← HolLight.INST [(← ec (mk_numeral q), q_tm), (← ec (mk_numeral p), p_tm),
                             (← ec (mk_numeral r), r_tm), (← ec (mk_numeral x), x_tm),
                             (← ec (mk_numeral y), y_tm), (← ec (mk_numeral d), d_tm)] pth3
    HolLight.MP th1 (← HolLight.EQT_ELIM
      (← ExceptT.mk (NUM_REDUCE_CONV (← ec (HolCore.Equal.lhand (concl th1))))))
  : ExceptT String IO thm).run
#eval (do replay PRIMEPOW_CONV_pths; IO.println "<fun>" : IO Unit)

/- ------------------------------------------------------------------------- -/
/- Conversion for "aprimedivisor" applied to prime power (only).             -/
/- ------------------------------------------------------------------------- -/

#eval phrase 30
-- let APRIMEDIVISOR_CONV = ...;;
def APRIMEDIVISOR_CONV_pth : thm := keep "APRIMEDIVISOR_CONV_pth" fun _ => (do
  prove ([[prime p ==> 1 <= k /\ (q = p EXP k) ==> (aprimedivisor q = p)]])
   (MESON_TAC [APRIMEDIVISOR_PRIMEPOW])
  : ExceptT String IO thm).run
def APRIMEDIVISOR_CONV (tm0 : term) : IO (Except String thm) := (do
  let p_tm ← ExceptT.mk [[p:num]]
  let k_tm ← ExceptT.mk [[k:num]]
  let q_tm ← ExceptT.mk [[q:num]]
  let a_tm ← ExceptT.mk [[aprimedivisor]]
  let (ptm, tm) ← ec (dest_comb tm0)
  if ptm != a_tm then throw "expected primepow(numeral)"
  let q ← ec (HolCore.Basics.dest_numeral tm)
  if q == 0 then throw "APRIMEDIVISOR_CONV: not a prime power"
  match ← SessionLibrary.Pocklington.factor q with
  | [(p, k)] =>
    let th1 ← HolLight.INST [(← ec (mk_numeral q), q_tm), (← ec (mk_numeral p), p_tm),
                             (← ec (mk_numeral k), k_tm)] APRIMEDIVISOR_CONV_pth
    let th2 ← HolLight.MP th1 (← HolLight.EQT_ELIM
      (← ExceptT.mk (PRIME_CONV (← ec (HolCore.Equal.lhand (concl th1))))))
    HolLight.MP th2 (← HolLight.EQT_ELIM
      (← ExceptT.mk (NUM_REDUCE_CONV (← ec (HolCore.Equal.lhand (concl th2))))))
  | _ => throw "APRIMEDIVISOR_CONV: not a prime power"
  : ExceptT String IO thm).run
#eval (do replay APRIMEDIVISOR_CONV_pth; IO.println "<fun>" : IO Unit)

/- ------------------------------------------------------------------------- -/
/- The Mangoldt function.                                                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 31
def mangoldt : thm := keep "mangoldt" fun _ => new_definition
 [[mangoldt d = if primepow d then ln(&(aprimedivisor d)) else &0]]
#eval mangoldt

#eval phrase 32
def MANGOLDT_POS : thm := keep "MANGOLDT_POS" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[2 <= a ==> 1 <= a]])
  prove ([[!d. &0 <= mangoldt d]])
   (GEN_TAC THEN REWRITE_TAC [mangoldt] THEN
    COND_CASES_TAC THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_LE_REFL] THEN
    ASM_MESON_TAC [APRIMEDIVISOR_PRIMEPOW, h1,
                  PRIME_GE_2, LN_POS, REAL_OF_NUM_LE, primepow])
  : ExceptT String IO thm).run
#eval MANGOLDT_POS

/- ------------------------------------------------------------------------- -/
/- The key lemma.                                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 33
def LN_PRIMEFACT : thm := keep "LN_PRIMEFACT" fun _ => (do
  let h19 ← ar (← ExceptT.mk [[a * b * c = b * a * c:num]])
  let h18 ← ar (← ExceptT.mk [[a + 1 <= b ==> a < b]])
  let h17 ← tt (← ExceptT.mk [[(b ==> a) /\ ~a ==> (a <=> b)]])
  let h16 ← ar (← ExceptT.mk [[1 <= k + 1]])
  let h15 ← ar (← ExceptT.mk [[~(k + 1 <= k)]])
  let h14 ← ar (← ExceptT.mk [[a * b * c = b * a * c:num]])
  let h13 ← ar (← ExceptT.mk [[1 <= k ==> (k = SUC(k - 1))]])
  let h12 ← tt (← ExceptT.mk [[(b ==> a) /\ b ==> (a <=> b)]])
  let h11 ← rr (← ExceptT.mk [[(a = a') /\ (l + b = c) ==> (l + a + b = a' + c)]])
  let h10 ← ar (← ExceptT.mk [[k <= p ==> (1 + p = k + 1 + (p - k))]])
  let h9 ← ar (← ExceptT.mk [[~(1 + m <= d /\ d <= m)]])
  let h8 ← rr (← ExceptT.mk [[(b = &0) ==> (a = a + b)]])
  let h7 ← ar (← ExceptT.mk [[2 <= p ==> 1 <= p]])
  let h6 ← ar (← ExceptT.mk [[1 * y <= x ==> (1 + x = (1 + y) + (x - y))]])
  let h5 ← tt (← ExceptT.mk [[a ==> b ==> c <=> b /\ a ==> c]])
  let h4 ← ar (← ExceptT.mk [[0 < n <=> ~(n = 0)]])
  let h3 ← ar (← ExceptT.mk [[1 < p <=> 2 <= p]])
  let h2 ← ar (← ExceptT.mk [[m < p * m <=> 1 * m < p * m]])
  let h1 ← nrc (← ExceptT.mk [[2 <= 1]])
  prove ([[!n. ~(n = 0)
       ==> (ln(&n) =
            sum(1,n) (\d. if primepow d /\ d divides n
                          then ln(&(aprimedivisor d)) else &0))]])
   (MATCH_MP_TAC num_WF THEN X_GEN_TAC ([[n:num]]) THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC ([[n = 1]]) THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC ([[sum(1,n) (\d. &0)]]) THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC [SessionLibrary.Analysis.SUM_0, LN_1], ALL_TAC] THEN
      MATCH_MP_TAC SessionLibrary.Analysis.SUM_EQ THEN X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN
      REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [PRIMEPOW_GE_2, DIVIDES_LE, h1,
                    LE_TRANS],
      ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP PRIME_FACTOR) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[p:num]]) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [divides] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[m:num]]) SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[m:num]])) THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [MULT_EQ_0, DE_MORGAN_THM]) THEN
    ANTS_TAC THENL
     [ONCE_REWRITE_TAC [h2] THEN
      SIMP_TAC [LT_MULT_RCANCEL, h3] THEN
      ASM_SIMP_TAC [PRIME_GE_2],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
    ASM_SIMP_TAC [LN_MUL, REAL_OF_NUM_LT, h4] THEN
    DISCH_THEN ((fun _ => ALL_TAC)) THEN
    SUBGOAL_THEN ([[?k. 1 <= k /\ (p EXP k) divides (p * m)]]) MP_TAC THENL
     [EXISTS_TAC ([[1]]) THEN SIMP_TAC [EXP_1, DIVIDES_RMUL, DIVIDES_REFL, LE_REFL],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[?k. !j. 1 <= j /\ (p EXP j) divides (p * m) ==> j <= k]]) MP_TAC THENL
     [MP_TAC (← HolLight.SPECL [([[p:num]]), ([[p * m:num]])] BIG_POWER_LEMMA) THEN
      ASM_SIMP_TAC [PRIME_GE_2] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ([[k:num]]) THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP DIVIDES_LE) THEN
      ASM_REWRITE_TAC [MULT_EQ_0] THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN REWRITE_TAC [NOT_LE] THEN
      DISCH_TAC THEN MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC ([[p EXP k]]) THEN
      ASM_REWRITE_TAC [LT_EXP] THEN ASM_SIMP_TAC [PRIME_GE_2],
      ALL_TAC] THEN
    GEN_REWRITE_TAC HolCore.Lib.I [h5] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [num_MAX] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN ([[sum (1,m)
     (\d. if primepow d /\ d divides m then ln (&(aprimedivisor d)) else &0) =
    sum (1,p * m)
     (\d. if primepow d /\ d divides m then ln (&(aprimedivisor d)) else &0)]]) SUBST1_TAC THENL
     [ONCE_REWRITE_TAC [SessionLibrary.Analysis.SUM_DIFF] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN ([[1 + p * m = (1 + m) + (p * m - m)]]) SUBST1_TAC THENL
       [MATCH_MP_TAC h6 THEN
        SIMP_TAC [LE_MULT_RCANCEL] THEN
        ASM_MESON_TAC [PRIME_GE_2, h7],
        ALL_TAC] THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM SUM_TWO)] THEN
      MATCH_MP_TAC h8 THEN
      SUBGOAL_THEN ([[!d. d >= 1 + m
          ==> ((if primepow d /\ d divides m then ln (&(aprimedivisor d))
                else &0) = &0)]]) MP_TAC THENL
       [X_GEN_TAC ([[d:num]]) THEN REWRITE_TAC [GE] THEN DISCH_TAC THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
        ASM_MESON_TAC [DIVIDES_LE, h9],
        ALL_TAC] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP SUM_ZERO) THEN DISCH_THEN MATCH_MP_TAC THEN
      ARITH_TAC,
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [SessionLibrary.Analysis.SUM_DIFF] THEN REWRITE_TAC [SUM_1] THEN
    REWRITE_TAC [PRIMEPOW_0, SessionLibrary.Analysis.REAL_SUB_RZERO] THEN
    SUBGOAL_THEN ([[1 + p * m = p EXP k + 1 + (p * m - p EXP k)]]) SUBST1_TAC THENL
     [MATCH_MP_TAC h10 THEN
      ASM_MESON_TAC [DIVIDES_LE, MULT_EQ_0],
      ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_TWO)] THEN
    MATCH_MP_TAC h11 THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SessionLibrary.Analysis.SUM_EQ THEN
      X_GEN_TAC ([[d:num]]) THEN REWRITE_TAC [ADD_CLAUSES, LE_0] THEN STRIP_TAC THEN
      ASM_CASES_TAC ([[primepow d]]) THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[d divides (p * m) <=> d divides m]]) (fun th => REWRITE_TAC [th]) THEN
      UNDISCH_TAC ([[primepow d]]) THEN REWRITE_TAC [primepow] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[q:num]]) MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[j:num]]) MP_TAC) THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN SUBST_ALL_TAC THEN ASM_CASES_TAC ([[q = p:num]]) THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        MATCH_MP_TAC h12 THEN
        REWRITE_TAC [DIVIDES_LMUL] THEN
        MATCH_MP_TAC DIVIDES_TRANS THEN
        EXISTS_TAC ([[p EXP (k - 1)]]) THEN CONJ_TAC THENL
         [REWRITE_TAC [divides] THEN EXISTS_TAC ([[p EXP ((k - 1) - j)]]) THEN
          REWRITE_TAC [(← HolLight.GSYM EXP_ADD)] THEN AP_TERM_TAC THEN
          UNDISCH_TAC ([[p EXP j < p EXP k]]) THEN ASM_REWRITE_TAC [LT_EXP] THEN
          ARITH_TAC,
          ALL_TAC] THEN
        UNDISCH_TAC ([[p EXP k divides (p * m)]]) THEN
        FIRST_ASSUM ((fun th => GEN_REWRITE_TAC (HolCore.Lib.funpow 2 HolLight.LAND_CONV o HolLight.RAND_CONV) [th]) o HolLight.MATCH_MP h13) THEN
        REWRITE_TAC [divides, EXP] THEN MATCH_MP_TAC MONO_EXISTS THEN
        SIMP_TAC [(← HolLight.GSYM MULT_ASSOC), EQ_MULT_LCANCEL] THEN
        ASM_REWRITE_TAC [],
        ALL_TAC] THEN
      EQ_TAC THEN REWRITE_TAC [DIVIDES_LMUL] THEN
      REWRITE_TAC [divides] THEN DISCH_THEN (X_CHOOSE_THEN ([[r:num]]) MP_TAC) THEN
      DISCH_THEN (fun th => HolLight.tactic_of do
        pure (ASSUME_TAC th THEN
        MP_TAC (← HolLight.AP_TERM ([[(divides) p]]) th))) THEN
      SIMP_TAC [DIVIDES_RMUL, DIVIDES_REFL] THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[p divides (q EXP j) \/ p divides r]]) MP_TAC THENL
       [ASM_MESON_TAC [PRIME_DIVPROD], ALL_TAC] THEN
      DISCH_THEN DISJ_CASES_TAC THENL
       [SUBGOAL_THEN ([[p divides q]]) MP_TAC THENL
         [ASM_MESON_TAC [PRIME_DIVEXP], ALL_TAC] THEN
        ASM_MESON_TAC [prime, PRIME_1],
        ALL_TAC] THEN
      UNDISCH_TAC ([[p * m = q EXP j * r]]) THEN
      UNDISCH_TAC ([[p divides r]]) THEN
      REWRITE_TAC [divides] THEN DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN
      ONCE_REWRITE_TAC [h14] THEN
      SIMP_TAC [EQ_MULT_LCANCEL] THEN ASM_MESON_TAC [],
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT)] THEN REWRITE_TAC [SUM_1] THEN
    REWRITE_TAC [REAL_ADD_ASSOC] THEN BINOP_TAC THENL
     [SUBGOAL_THEN ([[primepow (p EXP k)]]) ASSUME_TAC THENL
       [ASM_MESON_TAC [primepow], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN ([[~((p EXP k) divides m)]]) ASSUME_TAC THENL
       [REWRITE_TAC [divides] THEN
        DISCH_THEN (X_CHOOSE_THEN ([[r:num]]) SUBST_ALL_TAC) THEN
        MP_TAC h15 THEN REWRITE_TAC [] THEN
        FIRST_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC [h16] THEN
        ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [EXP_ADD, EXP_1] THEN
        MESON_TAC [MULT_ASSOC, DIVIDES_REFL, DIVIDES_RMUL],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [REAL_ADD_RID] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      ASM_MESON_TAC [APRIMEDIVISOR_PRIMEPOW],
      ALL_TAC] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.SUM_EQ THEN
    X_GEN_TAC ([[d:num]]) THEN REWRITE_TAC [ADD_CLAUSES, LE_0] THEN STRIP_TAC THEN
    ASM_CASES_TAC ([[primepow d]]) THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[d divides (p * m) <=> d divides m]]) (fun th => REWRITE_TAC [th]) THEN
    UNDISCH_TAC ([[primepow d]]) THEN REWRITE_TAC [primepow] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[q:num]]) MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[j:num]]) MP_TAC) THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_CASES_TAC ([[q = p:num]]) THENL
     [UNDISCH_THEN ([[q = p:num]]) SUBST_ALL_TAC THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      MATCH_MP_TAC h17 THEN
      REWRITE_TAC [DIVIDES_LMUL] THEN DISCH_TAC THEN
      FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP h18) THEN
      REWRITE_TAC [LT_EXP] THEN ASM_SIMP_TAC [PRIME_GE_2, NOT_LT],
      ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN EQ_TAC THEN REWRITE_TAC [DIVIDES_LMUL] THEN
    REWRITE_TAC [divides] THEN DISCH_THEN (X_CHOOSE_THEN ([[r:num]]) MP_TAC) THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
        pure (ASSUME_TAC th THEN
      MP_TAC (← HolLight.AP_TERM ([[(divides) p]]) th))) THEN
    SIMP_TAC [DIVIDES_RMUL, DIVIDES_REFL] THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[p divides (q EXP j) \/ p divides r]]) MP_TAC THENL
     [ASM_MESON_TAC [PRIME_DIVPROD], ALL_TAC] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [SUBGOAL_THEN ([[p divides q]]) MP_TAC THENL
       [ASM_MESON_TAC [PRIME_DIVEXP], ALL_TAC] THEN
      ASM_MESON_TAC [prime, PRIME_1],
      ALL_TAC] THEN
    UNDISCH_TAC ([[p * m = q EXP j * r]]) THEN
    UNDISCH_TAC ([[p divides r]]) THEN
    REWRITE_TAC [divides] THEN DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN
    ONCE_REWRITE_TAC [h19] THEN
    SIMP_TAC [EQ_MULT_LCANCEL] THEN ASM_MESON_TAC [])
  : ExceptT String IO thm).run
#eval LN_PRIMEFACT

/- ------------------------------------------------------------------------- -/
/- The key expansion using the Mangoldt function.                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 34
def MANGOLDT : thm := keep "MANGOLDT" fun _ => (do
  let h16 ← ar (← ExceptT.mk [[t + m * d + 1 = (t + 1) + m * d]])
  let h15 ← nrc (← ExceptT.mk [[2 <= 1]])
  let h14 ← rr (← ExceptT.mk [[(b = &0) ==> (a + b = a)]])
  let h13 ← ar (← ExceptT.mk [[1 <= d ==> (d = 1 + (d - 1))]])
  let h12 ← rr (← ExceptT.mk [[(a + b) - b = a]])
  let h11 ← ar (← ExceptT.mk [[a + b <= c ==> a <= c:num]])
  let h10 ← ar (← ExceptT.mk [[d * q + x < y + 1 + q * d <=> x <= y]])
  let h9 ← ar (← ExceptT.mk [[1 <= d ==> ~(d = 0)]])
  let h8 ← ar (← ExceptT.mk [[1 + x <= y * z ==> x < z * y]])
  let h7 ← rr (← ExceptT.mk [[(b = &0) /\ (a = c) ==> (a + b = c)]])
  let h6 ← ar (← ExceptT.mk [[0 < d <=> 1 <= d]])
  let h5 ← ar (← ExceptT.mk [[1 <= d ==> ~(d = 0)]])
  let h4 ← ar (← ExceptT.mk [[1 <= d /\ 1 + d <= r /\ (r <= d \/ (d = 0)) ==> F]])
  let h3 ← rr (← ExceptT.mk [[(a = a + b) <=> (b = &0)]])
  let h2 ← ar (← ExceptT.mk [[d < n + 1 ==> (n = d + (n - d))]])
  let h1 ← ar (← ExceptT.mk [[~(n = 0) <=> 1 <= n]])
  prove ([[!n. ln(&(FACT n)) = sum(1,n) (\d. mangoldt(d) * floor(&n / &d))]])
   (GEN_TAC THEN REWRITE_TAC [LN_FACT] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[sum(1,n) (\m. sum(1,n) (\d. if primepow d /\ d divides m
                                then ln (&(aprimedivisor d))
                                else &0))]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SessionLibrary.Analysis.SUM_EQ THEN X_GEN_TAC ([[d:num]]) THEN STRIP_TAC THEN
      ASM_SIMP_TAC [LN_PRIMEFACT, h1] THEN
      FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP h2) THEN
      DISCH_THEN (fun th => GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.LAND_CONV o HolLight.RAND_CONV) [th]) THEN
      REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT)] THEN
      REWRITE_TAC [h3] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC ([[sum(1 + d,n - d) (\k. &0)]]) THEN CONJ_TAC THENL
       [ALL_TAC, REWRITE_TAC [SessionLibrary.Analysis.SUM_0]] THEN
      MATCH_MP_TAC SessionLibrary.Analysis.SUM_EQ THEN X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN
      REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [DIVIDES_LE, h4],
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [SessionLibrary.Analysis.SUM_SWAP] THEN MATCH_MP_TAC SessionLibrary.Analysis.SUM_EQ THEN
    X_GEN_TAC ([[d:num]]) THEN STRIP_TAC THEN REWRITE_TAC [] THEN
    REWRITE_TAC [mangoldt] THEN
    ASM_CASES_TAC ([[primepow d]]) THEN ASM_REWRITE_TAC [SessionLibrary.Analysis.SUM_0, SessionLibrary.Analysis.REAL_MUL_LZERO] THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP h5) THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP DIVISION) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[n:num]])) THEN
    MAP_EVERY ABBREV_TAC [([[q = n DIV d]]), ([[r = n MOD d]])] THEN
    DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN ([[floor (&(q * d + r) / &d) = &q]]) SUBST1_TAC THENL
     [ONCE_REWRITE_TAC [(← HolLight.GSYM FLOOR_UNIQUE)] THEN
      REWRITE_TAC [INTEGER_CLOSED] THEN
      ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_LT_LDIV_EQ,
                   REAL_OF_NUM_LT, h6] THEN
      REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_MUL] THEN
      REWRITE_TAC [REAL_OF_NUM_LE, REAL_OF_NUM_LT] THEN
      UNDISCH_TAC ([[r < d:num]]) THEN ARITH_TAC,
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT)] THEN
    MATCH_MP_TAC h7 THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC ([[sum(1 + q * d,r) (\x. &0)]]) THEN
      CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [SessionLibrary.Analysis.SUM_0]] THEN
      MATCH_MP_TAC SessionLibrary.Analysis.SUM_EQ THEN REWRITE_TAC [] THEN
      X_GEN_TAC ([[s:num]]) THEN STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC ([[d divides s]]) THEN REWRITE_TAC [divides] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[t:num]]) SUBST_ALL_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP h8) THEN
      ASM_SIMP_TAC [LT_MULT_RCANCEL, h9] THEN
      REWRITE_TAC [LT_EXISTS] THEN
      DISCH_THEN (X_CHOOSE_THEN ([[e:num]]) SUBST_ALL_TAC) THEN
      UNDISCH_TAC ([[d * (q + SUC e) < r + 1 + q * d]]) THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN DISCH_TAC THEN
      REWRITE_TAC [LEFT_ADD_DISTRIB, MULT_CLAUSES, (← HolLight.GSYM ADD_ASSOC)] THEN
      REWRITE_TAC [h10] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP h11) THEN
      ASM_REWRITE_TAC [NOT_LE],
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [SessionLibrary.Analysis.SUM_DIFF] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_TWO)] THEN
    SIMP_TAC [SUM_1, DIVIDES_0, DIVIDES_LMUL, DIVIDES_REFL] THEN
    REWRITE_TAC [h12] THEN
    REWRITE_TAC [(← HolLight.GSYM SessionLibrary.Analysis.SUM_GROUP)] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[sum(0,q) (\x. ln (&(aprimedivisor d)))]]) THEN CONJ_TAC THENL
     [ALL_TAC, REWRITE_TAC [SessionLibrary.Analysis.SUM_CONST, REAL_MUL_AC]] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.SUM_EQ THEN X_GEN_TAC ([[m:num]]) THEN STRIP_TAC THEN
    REWRITE_TAC [] THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP h13) THEN
    DISCH_THEN (fun th => GEN_REWRITE_TAC (HolCore.Lib.funpow 2 HolLight.LAND_CONV o HolLight.RAND_CONV) [th]) THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT), SUM_1] THEN
    SIMP_TAC [DIVIDES_LMUL, DIVIDES_REFL] THEN
    MATCH_MP_TAC h14 THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[sum(m * d + 1,d - 1) (\x. &0)]]) THEN CONJ_TAC THENL
     [ALL_TAC, REWRITE_TAC [SessionLibrary.Analysis.SUM_0]] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.SUM_EQ THEN X_GEN_TAC ([[s:num]]) THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [LE_EXISTS] THEN
    REWRITE_TAC [] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[t:num]]) SUBST_ALL_TAC) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[~(d divides (t + 1))]]) MP_TAC THENL
     [DISCH_THEN (MP_TAC o HolLight.MATCH_MP DIVIDES_LE) THEN
      UNDISCH_TAC ([[t + m * d + 1 < d - 1 + m * d + 1]]) THEN
      REWRITE_TAC [LT_ADD_RCANCEL] THEN
      UNDISCH_TAC ([[d divides (t + m * d + 1)]]) THEN
      ASM_CASES_TAC ([[t = 0]]) THEN ASM_REWRITE_TAC [ADD_CLAUSES] THENL
       [ASM_MESON_TAC [DIVIDES_REFL, DIVIDES_LMUL, DIVIDES_ADD_REVR,
                      DIVIDES_ONE, PRIMEPOW_GE_2, h15],
        DISCH_TAC THEN ARITH_TAC],
      ALL_TAC] THEN
    UNDISCH_TAC ([[d divides (t + m * d + 1)]]) THEN
    ONCE_REWRITE_TAC [h16] THEN
    MESON_TAC [DIVIDES_REFL, DIVIDES_LMUL, DIVIDES_ADD_REVL])
  : ExceptT String IO thm).run
#eval MANGOLDT

/- ------------------------------------------------------------------------- -/
/- The Chebyshev psi function.                                               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 35
def psi : thm := keep "psi" fun _ => new_definition
 [[psi(n) = sum(1,n) (\d. mangoldt(d))]]
#eval psi

/- ------------------------------------------------------------------------- -/
/- The key bounds on the psi function.                                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 36
def PSI_BOUNDS_LN_FACT : thm := keep "PSI_BOUNDS_LN_FACT" fun _ => (do
  let h17 ← ar (← ExceptT.mk [[0 < r <=> 1 <= r]])
  let h16 ← rr (← ExceptT.mk [[(a = &1) ==> &1 <= a]])
  let h15 ← ar (← ExceptT.mk [[0 < r <=> 1 <= r]])
  let h14 ← rr (← ExceptT.mk [[(b = &0) /\ &1 <= a ==> &1 <= a - &2 * b]])
  let h13 ← rr (← ExceptT.mk [[a = a * &1]])
  let h12 ← ar (← ExceptT.mk [[0 < r <=> 1 <= r]])
  let h11 ← rr (← ExceptT.mk [[m * a - &2 * m * b = m * (a - &2 * b)]])
  let h10 ← ar (← ExceptT.mk [[1 + n <= r ==> ~(r <= n)]])
  let h9 ← ar (← ExceptT.mk [[r < n + 1 <=> r <= n]])
  let h8 ← rr (← ExceptT.mk [[(c = &0) /\ (b = d) ==> ((a + b) - a = c + d)]])
  let h7 ← ar (← ExceptT.mk [[2 * n + d = n + (n + d)]])
  let h6 ← ar (← ExceptT.mk [[0 < r <=> 1 <= r]])
  let h5 ← rr (← ExceptT.mk [[&2 * a <= b /\ b <= &2 * a + &1
      ==> b - &2 * a <= &1]])
  let h4 ← rr (← ExceptT.mk [[m * f - &2 * m * f' = m * (f - &2 * f')]])
  let h3 ← ar (← ExceptT.mk [[1 + n <= r ==> 0 < r]])
  let h2 ← rr (← ExceptT.mk [[(a = a + b) <=> (b = &0)]])
  let h1 ← ar (← ExceptT.mk [[2 * n + d = n + (n + d)]])
  prove ([[!n. ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2))) <= psi(n) /\
       psi(n) - psi(n DIV 2) <= ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2)))]])
   (X_GEN_TAC ([[k:num]]) THEN MP_TAC (← HolLight.SPECL [([[k:num]]), ([[2]])] DIVISION) THEN
    REWRITE_TAC [ARITH_EQ] THEN
    MAP_EVERY ABBREV_TAC [([[n = k DIV 2]]), ([[d = k MOD 2]])] THEN
    POP_ASSUM_LIST ((fun _ => ALL_TAC)) THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
    DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    REWRITE_TAC [psi, MANGOLDT] THEN
    SUBGOAL_THEN ([[sum (1,n) (\d. mangoldt d * floor (&n / &d)) =
    sum (1,2 * n + d) (\d. mangoldt d * floor (&n / &d))]]) SUBST1_TAC THENL
     [REWRITE_TAC [h1] THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT)] THEN
      REWRITE_TAC [h2] THEN
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC ([[sum(1 + n,n + d) (\k. &0)]]) THEN
      CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [SessionLibrary.Analysis.SUM_0]] THEN
      MATCH_MP_TAC SessionLibrary.Analysis.SUM_EQ THEN X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN
      REWRITE_TAC [REAL_ENTIRE] THEN DISJ2_TAC THEN REWRITE_TAC [FLOOR_EQ_0] THEN
      FIRST_ASSUM (ASSUME_TAC o HolLight.MATCH_MP h3) THEN
      ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_LT_LDIV_EQ, REAL_OF_NUM_LT] THEN
      REWRITE_TAC [SessionLibrary.Analysis.REAL_MUL_LZERO, SessionLibrary.Analysis.REAL_POS, REAL_MUL_LID, REAL_OF_NUM_LT] THEN
      UNDISCH_TAC ([[1 + n <= r]]) THEN ARITH_TAC,
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM SUM_CMUL), (← HolLight.GSYM SessionLibrary.Analysis.SUM_SUB)] THEN
      MATCH_MP_TAC SessionLibrary.Analysis.SUM_LE THEN X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN
      REWRITE_TAC [h4] THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.GSYM SessionLibrary.Analysis.REAL_MUL_RID)] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [MANGOLDT_POS] THEN
      MATCH_MP_TAC h5 THEN
      ASM_SIMP_TAC [FLOOR_DOUBLE_NUM, h6],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[sum(1,2 * n + d) (\d. mangoldt d) - sum(1,n) (\d. mangoldt d) =
    sum(1,2 * n + d) (\d. if d <= n then &0 else mangoldt d)]]) SUBST1_TAC THENL
     [REWRITE_TAC [h7] THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT)] THEN
      MATCH_MP_TAC h8 THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC ([[sum(1,n) (\k. &0)]]) THEN CONJ_TAC THENL
         [ALL_TAC, REWRITE_TAC [SessionLibrary.Analysis.SUM_0]] THEN
        MATCH_MP_TAC SessionLibrary.Analysis.SUM_EQ THEN
        SIMP_TAC [h9],
        ALL_TAC] THEN
      MATCH_MP_TAC SessionLibrary.Analysis.SUM_EQ THEN
      SIMP_TAC [h10],
      ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_CMUL), (← HolLight.GSYM SessionLibrary.Analysis.SUM_SUB)] THEN MATCH_MP_TAC SessionLibrary.Analysis.SUM_LE THEN
    X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN REWRITE_TAC [] THEN
    REWRITE_TAC [h11] THEN
    COND_CASES_TAC THENL
     [MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_MUL THEN REWRITE_TAC [MANGOLDT_POS] THEN
      ASM_SIMP_TAC [SessionLibrary.Analysis.REAL_SUB_LE, FLOOR_DOUBLE_NUM, h12],
      ALL_TAC] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [h13] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [MANGOLDT_POS] THEN
    MATCH_MP_TAC h14 THEN
    CONJ_TAC THENL
     [REWRITE_TAC [FLOOR_EQ_0] THEN
      ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_LT_LDIV_EQ, REAL_OF_NUM_LT,
                   h15] THEN
      REWRITE_TAC [SessionLibrary.Analysis.REAL_MUL_LZERO, REAL_MUL_LID, SessionLibrary.Analysis.REAL_POS] THEN
      ASM_REWRITE_TAC [REAL_OF_NUM_LT] THEN ASM_REWRITE_TAC [(← HolLight.GSYM NOT_LE)],
      ALL_TAC] THEN
    MATCH_MP_TAC h16 THEN
    REWRITE_TAC [(← HolLight.GSYM FLOOR_UNIQUE), INTEGER_CLOSED] THEN
    ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_LT_LDIV_EQ, REAL_OF_NUM_LT,
                 h17] THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
    REWRITE_TAC [REAL_OF_NUM_LE, REAL_OF_NUM_LT, REAL_OF_NUM_MUL,
                REAL_OF_NUM_ADD] THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval PSI_BOUNDS_LN_FACT

/- ------------------------------------------------------------------------- -/
/- Map the middle term into multiples of log(n).                             -/
/- ------------------------------------------------------------------------- -/

#eval phrase 37
def LN_FACT_DIFF_BOUNDS : thm := keep "LN_FACT_DIFF_BOUNDS" fun _ => (do
  let h19 ← ar (← ExceptT.mk [[0 < q <=> ~(q = 0)]])
  let h18 ← rr (← ExceptT.mk [[&0 < q ==> &0 < q * &2]])
  let h17 ← rr (← ExceptT.mk [[&0 < q /\ &0 <= r ==> &0 < q * &2 + r]])
  let h16 ← ar (← ExceptT.mk [[0 < q <=> ~(q = 0)]])
  let h15 ← rr (← ExceptT.mk [[l2 + lnn <= (&4 * lnn + &3) - a - b
    <=> a + b + l2 <= &3 * lnn + &3]])
  let h14 ← rr (← ExceptT.mk [[&0 <= x ==> abs(x) <= x]])
  let h13 ← rr (← ExceptT.mk [[abs(b - (a + b)) = abs a]])
  let h12 ← ar (← ExceptT.mk [[r < 2 ==> (r = 0) \/ (r = 1)]])
  let h11 ← rr (← ExceptT.mk [[&0 <= x /\ x <= &1 * y ==> abs(x) <= y]])
  let h10 ← rr (← ExceptT.mk [[x <= a - b - c - d <=> x + b <= a - c - d]])
  let h9 ← rr (← ExceptT.mk [[(q * &2 + r) * l2 - ((q * &2) * (lq + l2) - q * &2 - &2 * (q * lq - q)) =
    r * l2]])
  let h8 ← ar (← ExceptT.mk [[0 < q <=> ~(q = 0)]])
  let h7 ← rr (← ExceptT.mk [[abs(a - (a2 - &2 * a1)) <= b - &2 * b1 - b2
    ==> abs(l2 - a2) <= b2
        ==> abs(l1 - a1) <= b1
            ==> abs((l2 - &2 * l1) - a) <= b]])
  let h6 ← rr (← ExceptT.mk [[!a'. abs((a' - b) - c) <= d - abs(a' - a) ==> abs((a - b) - c) <= d]])
  let h5 ← rr (← ExceptT.mk [[&0 <= x /\ x <= &1 ==> abs(x) <= &1 + &1]])
  let h4 ← rr (← ExceptT.mk [[&2 = &1 + &1]])
  let h3 ← rr (← ExceptT.mk [[x <= &2 ==> x <= &3]])
  let h2 ← nc (← ExceptT.mk [[1]])
  let h1 ← ar (← ExceptT.mk [[r < 2 ==> ((r = 0) <=> ~(r = 1))]])
  prove ([[!n. abs((ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2)))) - &n * ln(&2))
       <= &4 * ln(if n = 0 then &1 else &n) + &3]])
   (REPEAT GEN_TAC THEN ASM_CASES_TAC ([[n = 0]]) THENL
     [ASM_SIMP_TAC [FACT, MULT_CLAUSES, LN_1, DIV_0, ARITH_EQ] THEN
      REWRITE_TAC [SessionLibrary.Analysis.REAL_MUL_LZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV,
      ALL_TAC] THEN
    MP_TAC (← HolLight.SPECL [([[n:num]]), ([[2]])] DIVISION) THEN ASM_REWRITE_TAC [ARITH_EQ] THEN
    MAP_EVERY ABBREV_TAC [([[q = n DIV 2]]), ([[r = n MOD 2]])] THEN
    DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    ASM_CASES_TAC ([[q = 0]]) THENL
     [UNDISCH_TAC ([[~(q * 2 + r = 0)]]) THEN
      ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN
      ASM_SIMP_TAC [h1] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      REWRITE_TAC [h2, FACT, MULT_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [LN_1] THEN
      REWRITE_TAC [SessionLibrary.Analysis.REAL_MUL_RZERO, SessionLibrary.Analysis.REAL_SUB_LZERO, SessionLibrary.Analysis.REAL_SUB_RZERO] THEN
      REWRITE_TAC [SessionLibrary.Analysis.REAL_NEG_0, SessionLibrary.Analysis.REAL_SUB_LZERO, REAL_ADD_LID, REAL_MUL_LID] THEN
      REWRITE_TAC [REAL_ABS_NEG] THEN
      MATCH_MP_TAC h3 THEN
      SUBST1_TAC h4 THEN
      MATCH_MP_TAC h5 THEN
      ASM_SIMP_TAC [LN_POS, LN_LE, REAL_OF_NUM_LE, ARITH, REAL_LE_ADDL],
      ALL_TAC] THEN
    MATCH_MP_TAC h6 THEN
    EXISTS_TAC ([[ln(&(FACT(q * 2)))]]) THEN
    MP_TAC (← HolLight.SPEC ([[q:num]]) LN_FACT_BOUNDS) THEN
    MP_TAC (← HolLight.SPEC ([[q * 2]]) LN_FACT_BOUNDS) THEN
    ASM_REWRITE_TAC [MULT_EQ_0, ARITH_EQ] THEN
    MATCH_MP_TAC h7 THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_ADD), (← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
    ASM_SIMP_TAC [LN_MUL, REAL_OF_NUM_LT, ARITH,
                 h8] THEN
    REWRITE_TAC [h9] THEN
    ONCE_REWRITE_TAC [h10] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[ln(&2) + ln(&q * &2 + &r)]]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC h11 THEN
        SIMP_TAC [LN_POS_LT, SessionLibrary.Analysis.REAL_LT_IMP_LE, SessionLibrary.Analysis.REAL_LE_RMUL_EQ,
                 SessionLibrary.Analysis.REAL_LE_MUL, SessionLibrary.Analysis.REAL_POS, REAL_OF_NUM_LT, ARITH] THEN
        REWRITE_TAC [REAL_OF_NUM_LE] THEN UNDISCH_TAC ([[r < 2]]) THEN ARITH_TAC,
        ALL_TAC] THEN
      FIRST_ASSUM (DISJ_CASES_THEN SUBST1_TAC o HolLight.MATCH_MP h12) THENL
       [REWRITE_TAC [ADD_CLAUSES, SessionLibrary.Analysis.REAL_SUB_REFL, REAL_ADD_RID, REAL_ABS_NUM] THEN
        MATCH_MP_TAC LN_POS THEN
        REWRITE_TAC [REAL_OF_NUM_LE, REAL_OF_NUM_MUL] THEN
        UNDISCH_TAC ([[~(q = 0)]]) THEN ARITH_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [(← HolLight.GSYM ADD1), FACT] THEN
      SIMP_TAC [(← HolLight.GSYM REAL_OF_NUM_MUL), LN_MUL, REAL_OF_NUM_LT,
               FACT_LT, LT_0] THEN
      REWRITE_TAC [h13] THEN
      REWRITE_TAC [ADD1, (← HolLight.GSYM REAL_OF_NUM_SUC), (← HolLight.GSYM REAL_OF_NUM_ADD),
                  (← HolLight.GSYM REAL_OF_NUM_MUL)] THEN
      MATCH_MP_TAC h14 THEN
      MATCH_MP_TAC LN_POS THEN
      REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_MUL, REAL_OF_NUM_LE] THEN
      ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [h15] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[&3 * ln(&q * &2) + &3]]) THEN CONJ_TAC THENL
     [ALL_TAC,
      SIMP_TAC [SessionLibrary.Analysis.REAL_LE_RADD, REAL_LE_LMUL_EQ, REAL_OF_NUM_LT, ARITH] THEN
      ASM_SIMP_TAC [LN_MONO_LE, SessionLibrary.Analysis.REAL_POS, REAL_OF_NUM_LT,
                   h16,
                   h17,
                   h18] THEN
      REWRITE_TAC [REAL_LE_ADDR, SessionLibrary.Analysis.REAL_POS]] THEN
    ASM_SIMP_TAC [LN_MUL, REAL_OF_NUM_LT, ARITH,
                 h19] THEN
    SUBGOAL_THEN ([[&0 <= ln(&2)]]) (fun th => MP_TAC th THEN REAL_ARITH_TAC2) THEN
    MATCH_MP_TAC LN_POS THEN REWRITE_TAC [REAL_OF_NUM_LE, ARITH])
  : ExceptT String IO thm).run
#eval LN_FACT_DIFF_BOUNDS

/- ------------------------------------------------------------------------- -/
/- Hence overall bounds in terms of n * log(2) + constant.                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 38
def PSI_BOUNDS_INDUCT : thm := keep "PSI_BOUNDS_INDUCT" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[m <= a /\ b <= m /\ abs(m - n) <= k
              ==> n - k <= a /\ b <= n + k]])
  prove ([[!n. &n * ln(&2) - (&4 * ln (if n = 0 then &1 else &n) + &3) <= psi(n) /\
       psi(n) - psi(n DIV 2)
       <= &n * ln(&2) + (&4 * ln (if n = 0 then &1 else &n) + &3)]])
   (MESON_TAC [PSI_BOUNDS_LN_FACT, LN_FACT_DIFF_BOUNDS, h1])
  : ExceptT String IO thm).run
#eval PSI_BOUNDS_INDUCT

/- ------------------------------------------------------------------------- -/
/- Evaluation of mangoldt(numeral).                                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 39
-- let MANGOLDT_CONV = GEN_REWRITE_CONV I [mangoldt] THENC ...;;
def MANGOLDT_CONV_1 : HolCore.Equal.ioconv :=
  HolLight.GEN_REWRITE_CONV HolCore.Lib.I [mangoldt] THENC
  HolLight.RATOR_CONV (HolLight.LAND_CONV PRIMEPOW_CONV) THENC
  HolLight.GEN_REWRITE_CONV HolCore.Lib.I [COND_CLAUSES] THENC
  HolLight.TRY_CONV (HolCore.Lib.funpow 2 HolLight.RAND_CONV APRIMEDIVISOR_CONV)
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- More efficient version without two primality tests.                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 40
-- let MANGOLDT_CONV = ... (rebinds MANGOLDT_CONV);;
def MANGOLDT_CONV_pths : thm × thm × thm × thm := keepIO "MANGOLDT_CONV_pths" fun _ => (do
  let pth0 ← prove ([[mangoldt 0 = ln(&1)]])
   (REWRITE_TAC [mangoldt, primepow, LN_1] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC [EXP_EQ_0, PRIME_0])
  let pth1 ← prove ([[mangoldt 1 = ln(&1)]])
   (REWRITE_TAC [mangoldt, primepow, LN_1] THEN COND_CASES_TAC THEN
    ASM_MESON_TAC [EXP_EQ_1, PRIME_1, (← ExceptT.mk (NUM_REDUCE_CONV (← ExceptT.mk [[1 <= 0]])))])
  let pth2 ← prove ([[prime p ==> 1 <= k /\ (q = p EXP k) ==> (mangoldt q = ln(&p))]])
   (SIMP_TAC [mangoldt, APRIMEDIVISOR_PRIMEPOW] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC [primepow])
  let pth3 ← prove ([[(p * x = r * y + 1) /\ ~(p = 1) /\ ~(r = 1) /\ (q = p * r * d)
     ==> (mangoldt q = ln(&1))]])
   (    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[~(primepow q)]])
     (fun th => REWRITE_TAC [LN_1, th, mangoldt]) THEN
    REWRITE_TAC [primepow] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[P:num]]) MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) MP_TAC) THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC (← HolLight.SPEC ([[r:num]]) PRIME_FACTOR) THEN
    MP_TAC (← HolLight.SPEC ([[p:num]]) PRIME_FACTOR) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[P_p:num]]) MP_TAC) THEN
    REWRITE_TAC [divides] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d_p:num]]) SUBST_ALL_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[P_r:num]]) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d_r:num]]) SUBST_ALL_TAC) THEN
    SUBGOAL_THEN ([[P_p divides P /\ P_r divides P]]) ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC ([[k:num]]) THEN
      ASM_MESON_TAC [divides, MULT_AC], ALL_TAC] THEN
    SUBGOAL_THEN ([[(P_p = P) /\ (P_r = P:num)]]) (CONJUNCTS_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC [prime], ALL_TAC] THEN
    ASM_MESON_TAC [DIVIDES_ADD_REVR, divides, MULT_AC, DIVIDES_ONE, prime])
  pure (pth0, pth1, pth2, pth3)
  : ExceptT String IO (thm × thm × thm × thm)).run

def MANGOLDT_CONV (tm0 : term) : IO (Except String thm) := (do
  let (pth0, pth1, pth2, pth3) := MANGOLDT_CONV_pths
  let p_tm ← ExceptT.mk [[p:num]]
  let k_tm ← ExceptT.mk [[k:num]]
  let q_tm ← ExceptT.mk [[q:num]]
  let r_tm ← ExceptT.mk [[r:num]]
  let d_tm ← ExceptT.mk [[d:num]]
  let x_tm ← ExceptT.mk [[x:num]]
  let y_tm ← ExceptT.mk [[y:num]]
  let f_tm ← ExceptT.mk [[mangoldt]]
  let (ptm, tm) ← ec (dest_comb tm0)
  if ptm != f_tm then throw "expected mangoldt(numeral)"
  let q ← ec (HolCore.Basics.dest_numeral tm)
  if q == 0 then return pth0
  else if q == 1 then return pth1
  match ← SessionLibrary.Pocklington.factor q with
  | [] => throw "internal failure in MANGOLDT_CONV"
  | [(p, k)] =>
    let th1 ← HolLight.INST [(← ec (mk_numeral q), q_tm), (← ec (mk_numeral p), p_tm),
                             (← ec (mk_numeral k), k_tm)] pth2
    let th2 ← HolLight.MP th1 (← HolLight.EQT_ELIM
      (← ExceptT.mk (PRIME_CONV (← ec (HolCore.Equal.lhand (concl th1))))))
    HolLight.MP th2 (← HolLight.EQT_ELIM
      (← ExceptT.mk (NUM_REDUCE_CONV (← ec (HolCore.Equal.lhand (concl th2))))))
  | (p, _) :: (r, _) :: _ =>
    let d := q / (p * r)
    let (x, y) := bezout (p, r)
    let (p, r, x, y) := if x < 0 then (r, p, y, -x) else (p, r, x, -y)
    let th1 ← HolLight.INST [(← ec (mk_numeral q), q_tm), (← ec (mk_numeral p), p_tm),
                             (← ec (mk_numeral r), r_tm), (← ec (mk_numeral x), x_tm),
                             (← ec (mk_numeral y), y_tm), (← ec (mk_numeral d), d_tm)] pth3
    HolLight.MP th1 (← HolLight.EQT_ELIM
      (← ExceptT.mk (NUM_REDUCE_CONV (← ec (HolCore.Equal.lhand (concl th1))))))
  : ExceptT String IO thm).run
#eval (do replay MANGOLDT_CONV_pths; IO.println "<fun>" : IO Unit)

/- ------------------------------------------------------------------------- -/
/- Hence an evaluation function for psi, applied to all n <= some N.         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 41
-- let PSI_LIST = ...;;
def PSI_LIST_0 : thm := keep "PSI_LIST_0" fun _ => (do
  prove ([[psi(0) = ln(&1)]])
   (REWRITE_TAC [psi, SessionLibrary.Analysis.sum, LN_1])
  : ExceptT String IO thm).run
def PSI_LIST_SUC : thm := keep "PSI_LIST_SUC" fun _ => (do
  prove ([[psi(SUC n) = psi(n) + mangoldt(SUC n)]])
   (REWRITE_TAC [psi, SessionLibrary.Analysis.sum, ADD1] THEN REWRITE_TAC [ADD_AC])
  : ExceptT String IO thm).run
def PSI_LIST_SIMPER_CONV : HolCore.Equal.ioconv :=
  fun t => do
    SIMP_CONV [REAL_ADD_RID, (← HolLight.GSYM LN_MUL), REAL_OF_NUM_MUL,
               REAL_OF_NUM_LT, ARITH] t
def PSI_LIST : Nat → IO (Except String (List thm))
  | 0 => pure (.ok [PSI_LIST_0])
  | n + 1 => (do
    let n_tm ← ExceptT.mk [[n:num]]
    let ths ← ExceptT.mk (PSI_LIST n)
    let th1 ← HolLight.INST [(← ec (mk_small_numeral (Int.ofNat n)), n_tm)] PSI_LIST_SUC
    let th2 ← HolLight.GEN_REWRITE_RULE (HolLight.RAND_CONV o HolLight.LAND_CONV)
      [← ec (HolCore.Lib.hd ths)] th1
    let th3 ← HolLight.CONV_RULE (HolLight.COMB_CONV (HolCore.Lib.funpow 2 HolLight.RAND_CONV NUM_SUC_CONV)) th2
    let th4 ← HolLight.CONV_RULE (HolCore.Lib.funpow 2 HolLight.RAND_CONV MANGOLDT_CONV) th3
    pure ((← HolLight.CONV_RULE (HolLight.RAND_CONV PSI_LIST_SIMPER_CONV) th4) :: ths)
    : ExceptT String IO (List thm)).run
/-- `PSI_LIST n` as a value (for its uses inside tactics). -/
def PSI_LISTv (n : Nat) : List thm :=
  match runIO (PSI_LIST n) with
  | .ok (.ok l) => l
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
#eval (do replay PSI_LIST_0; replay PSI_LIST_SUC; IO.println "<fun>" : IO Unit)

/- ------------------------------------------------------------------------- -/
/- Run it up to 300.                                                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 42
-- let PSI_LIST_300 = (PSI_LISTv 300);;
def PSI_LIST_300 : List thm := keep "PSI_LIST_300" fun _ => PSI_LISTv 300
#eval printThms PSI_LIST_300

/- ------------------------------------------------------------------------- -/
/- Prove a sharpish linear bound on psi(n) for n <= 128.                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 43
def PSI_UBOUND_128 : thm := keep "PSI_UBOUND_128" fun _ => (do
  let lemma ← prove ([[a <= b /\ l <= a /\ rest ==> l <= a /\ l <= b /\ rest]])
     (MESON_TAC [SessionLibrary.Analysis.REAL_LE_TRANS])
  let tac := HolCore.Lib.time (CONV_TAC (HolLight.LAND_CONV LN_N2_CONV THENC REALCALC_REL_CONV))
  let h2 ← tt (← ExceptT.mk [[T /\ a <=> a]])
  let h1 ← ar (← ExceptT.mk [[n <= 128 <=> n < 129]])
  prove ([[!n. n <= 128 ==> psi(n) <= &133 / &128 * &n]])
   (REWRITE_TAC [h1] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC PSI_LIST_300 THEN
    REWRITE_TAC [LN_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT ((MATCH_MP_TAC lemma THEN
       CONV_TAC (HolLight.LAND_CONV REAL_RAT_REDUCE_CONV) THEN
       GEN_REWRITE_TAC HolCore.Lib.I [h2]) ORELSE
       (CONJ_TAC THENL [tac THEN HolCore.Tactics.NO_TAC, ALL_TAC]) ORELSE tac))
  : ExceptT String IO thm).run
#eval PSI_UBOUND_128

/- ------------------------------------------------------------------------- -/
/- As a multiple of log(2) is often more useful.                             -/
/- ------------------------------------------------------------------------- -/

#eval phrase 44
def PSI_UBOUND_128_LOG : thm := keep "PSI_UBOUND_128_LOG" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[a <= b ==> x <= a ==> x <= b]])
  prove ([[!n. n <= 128 ==> psi(n) <= (&3 / &2 * ln(&2)) * &n]])
   (GEN_TAC THEN DISCH_THEN (MP_TAC o HolLight.MATCH_MP PSI_UBOUND_128) THEN
    MATCH_MP_TAC h1 THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_POS] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV LN_N2_CONV THENC REALCALC_REL_CONV))
  : ExceptT String IO thm).run
#eval PSI_UBOUND_128_LOG

/- ------------------------------------------------------------------------- -/
/- Useful "overpowering" lemma.                                              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 45
def OVERPOWER_LEMMA : thm := keep "OVERPOWER_LEMMA" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[fa <= ga /\ &0 <= d ==> (gx - fx - (ga - fa) = d) ==> fx <= gx]])
  prove ([[!f g d a.
        f(a) <= g(a) /\
        (!x. a <= x ==> ((\x. g(x) - f(x)) diffl (d(x)))(x)) /\
        (!x. a <= x ==> &0 <= d(x))
        ==> !x. a <= x ==> f(x) <= g(x)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[\x:real. g(x) - f(x)]]), ([[d:real->real]]), ([[a:real]]), ([[x:real]])] MVT_ALT) THEN
    UNDISCH_TAC ([[a <= x]]) THEN GEN_REWRITE_TAC HolLight.LAND_CONV [SessionLibrary.Analysis.REAL_LE_LT] THEN
    ASM_CASES_TAC ([[x:real = a]]) THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[z:real]]) MP_TAC) THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC h1 THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_MUL THEN
    ASM_SIMP_TAC [SessionLibrary.Analysis.REAL_SUB_LE, SessionLibrary.Analysis.REAL_LT_IMP_LE])
  : ExceptT String IO thm).run
#eval OVERPOWER_LEMMA

/- ------------------------------------------------------------------------- -/
/- Repeatedly extend range of explicit cases using recurrence.               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 46
-- let DOUBLE_CASES_RULE th = ...;;
def DOUBLE_CASES_RULE (th : thm) : ExceptT String IO thm := do
  let (_, bod) ← ec (HolCore.Basics.dest_forall (concl th))
  let (ant, cons) ← ec (HolCore.Basics.dest_imp bod)
  let m ← ec (HolCore.Basics.dest_numeral (← ec (HolCore.Kernel.rand ant)))
  let ctm ← ec (HolCore.Equal.lhand (← ec (HolCore.Equal.lhand (← ec (HolCore.Kernel.rand cons)))))
  let c ← ec (rat_of_term ctm)
  let fl (r : Rat) : Float := Float.ofInt r.num / Float.ofNat r.den
  let x := fl (m + 1)
  let d := (4.0 * Float.log x + 3.0) / (x * Float.log 2.0)
  let c' := c / 2 + 1 + (HolLibrary.CalcReal.floor_num (← num_of_float (1024.0 * d)) + 2) / 1024
  let c'' := max c c'
  let n_tm ← ExceptT.mk [[n:num]]
  let sf ← ExceptT.mk (HolCore.Basics.subst
    [((← ec (mk_numeral (2 * m))), (← ec (HolCore.Kernel.rand ant))),
     ((← ec (term_of_rat c'')), ctm)])
  let tm ← ec (HolCore.Bool.mk_forall n_tm (← ExceptT.mk (sf bod)))
  let h8 ← rr (← ExceptT.mk [[a <= x ==> inv(&1 + x) <= inv(&1 + a) /\
                 inv(&1 + a) <= b ==> inv(&1 + x) <= b]])
  let h7 ← rr (← ExceptT.mk [[a <= n ==> a - &1 <= n - &1]])
  let h6 ← ar (← ExceptT.mk [[~(n <= b) ==> b + 1 <= n]])
  let h5 ← rr (← ExceptT.mk [[&n = &1 + (&n - &1)]])
  let h4 ← rr (← ExceptT.mk [[logtm <= ((c - a * b) * l2) * n
      ==> (a * l2) * n * b <= (c * l2) * n - logtm]])
  let h3 ← rr (← ExceptT.mk [[a <= b ==> x <= a ==> x <= b]])
  let h2 ← rr (← ExceptT.mk [[pn2 <= ((a - &1) * l2) * n - logtm
      ==> u <= v /\ pn - pn2 <= n * l2 + logtm ==> pn <= (a * l2) * n]])
  let h1 ← rr (← ExceptT.mk [[a <= b ==> x <= a ==> x <= b]])
  prove tm
   (REPEAT STRIP_TAC THEN
      ASM_CASES_TAC (← ec (mk_comb ([[(<=) (n:num)]]) (← ec (mk_numeral m)))) THENL
       [FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP th) THEN
        MATCH_MP_TAC h1 THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC LN_POS THEN CONV_TAC REAL_RAT_REDUCE_CONV,
        ALL_TAC] THEN
      MP_TAC (← HolLight.SPEC ([[n:num]]) PSI_BOUNDS_INDUCT) THEN
      SUBGOAL_THEN ([[~(n = 0)]]) (fun th => REWRITE_TAC [th]) THENL
       [FIRST_ASSUM (UNDISCH_TAC o check HolCore.Basics.is_neg o concl) THEN ARITH_TAC,
        ALL_TAC] THEN
      MATCH_MP_TAC h2 THEN
      MP_TAC (← HolLight.SPEC ([[n DIV 2]]) th) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC [LE_LDIV_EQ, ARITH] THEN
        FIRST_ASSUM (UNDISCH_TAC o check (not o HolCore.Basics.is_neg) o concl) THEN
        ARITH_TAC,
        ALL_TAC] THEN
      MATCH_MP_TAC h3 THEN
      HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        pure (MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
         EXISTS_TAC (← ec (mk_comb (← ec (HolCore.Kernel.rator (← ec (HolCore.Equal.lhand w)))) ([[&n / &2]]))))) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
          MATCH_MP_TAC LN_POS THEN CONV_TAC REAL_RAT_REDUCE_CONV,
          ALL_TAC] THEN
        SIMP_TAC [REAL_LE_RDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
        REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_LE] THEN
        MP_TAC (← HolLight.SPECL [([[n:num]]), ([[2]])] DIVISION) THEN ARITH_TAC,
        ALL_TAC] THEN
      GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [real_div] THEN
      MATCH_MP_TAC h4 THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      SUBST1_TAC h5 THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP h6) THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM REAL_OF_NUM_LE)] THEN
      DISCH_THEN (MP_TAC o HolLight.MATCH_MP h7) THEN
      ABBREV_TAC ([[x = &n - &1]]) THEN
      CONV_TAC (HolLight.LAND_CONV NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV) THEN
      SPEC_TAC (([[x:real]]), ([[x:real]])) THEN POP_ASSUM_LIST ((fun _ => ALL_TAC)) THEN
      MATCH_MP_TAC OVERPOWER_LEMMA THEN
      HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        let th ← ExceptT.mk (DIFF_CONV (← ec (HolCore.Equal.lhand (← ec (HolCore.Kernel.rator (← ec (HolCore.Kernel.rand (← ec (HolCore.Basics.body (← ec (HolCore.Kernel.rand (← ec (HolCore.Equal.lhand (← ec (HolCore.Kernel.rand (← ec (HolCore.Basics.body (← ec (HolCore.Kernel.rand w)))))))))))))))))))
        pure (MP_TAC th)) THEN
      GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.TOP_DEPTH_CONV) [SessionLibrary.Analysis.REAL_MUL_LZERO, REAL_ADD_LID, REAL_ADD_RID,
        SessionLibrary.Analysis.REAL_MUL_RID, REAL_MUL_LID] THEN
      HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        let tm ← ec (mk_abs ([[x:real]]) (← ec (HolCore.Kernel.rand (← ec (HolCore.Kernel.rator (← ec (HolCore.Kernel.rand (← ec (HolCore.Basics.body (← ec (HolCore.Kernel.rand (← ec (HolCore.Equal.lhand w)))))))))))))
        pure (DISCH_TAC THEN EXISTS_TAC tm)) THEN
      CONJ_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [real_sub] THEN
        CONV_TAC (HolLight.ONCE_DEPTH_CONV LN_N2_CONV) THEN
        CONV_TAC REALCALC_REL_CONV,
        ALL_TAC] THEN
      REWRITE_TAC [] THEN CONJ_TAC THENL
       [GEN_TAC THEN
        DISCH_THEN (fun th => FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
        REAL_ARITH_TAC2,
        ALL_TAC] THEN
      X_GEN_TAC ([[x:real]]) THEN DISCH_TAC THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_LE] THEN
      SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ), REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h8) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        POP_ASSUM MP_TAC THEN REAL_ARITH_TAC2,
        ALL_TAC] THEN
      SIMP_TAC [REAL_LE_RDIV_EQ, REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [REAL_MUL_SYM] THEN
      SIMP_TAC [(← HolLight.GSYM REAL_LE_LDIV_EQ), REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV LN_N2_CONV) THEN CONV_TAC REALCALC_REL_CONV)
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Bring it to the self-sustaining point.                                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 47
def PSI_UBOUND_1024_LOG : thm := keep "PSI_UBOUND_1024_LOG" fun _ => (do
  funpowR 3 DOUBLE_CASES_RULE PSI_UBOUND_128_LOG
  : ExceptT String IO thm).run
#eval PSI_UBOUND_1024_LOG

/- ------------------------------------------------------------------------- -/
/- A generic proof of the same kind that we're self-sustaining.              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 48
def PSI_BOUNDS_SUSTAINED_INDUCT : thm := keep "PSI_BOUNDS_SUSTAINED_INDUCT" fun _ => (do
  let h11 ← rr (← ExceptT.mk [[&0 < x ==> &0 < &1 + x]])
  let h10 ← rr (← ExceptT.mk [[a <= x ==> inv(&1 + x) <= inv(&1 + a) /\
               inv(&1 + a) <= b ==> inv(&1 + x) <= b]])
  let h9 ← rr (← ExceptT.mk [[&0 < a ==> a <= x ==> &0 < &1 + x]])
  let h8 ← ar (← ExceptT.mk [[~(n <= b) ==> b + 1 <= n]])
  let h7 ← rr (← ExceptT.mk [[&n = &1 + (&n - &1)]])
  let h6 ← rr (← ExceptT.mk [[d <= c - &1 - c2 <=> c2 + d + &1 <= c]])
  let h5 ← rr (← ExceptT.mk [[logtm <= ((c - a * b) * l2) * n
    ==> (a * l2) * n * b <= (c * l2) * n - logtm]])
  let h4 ← rr (← ExceptT.mk [[a <= b ==> x <= a ==> x <= b]])
  let h3 ← ar (← ExceptT.mk [[n <= 2 * k ==> n < 2 * (k + 1)]])
  let h2 ← rr (← ExceptT.mk [[pn2 <= ((a - &1) * l2) * n - logtm
    ==> u <= v /\ pn - pn2 <= n * l2 + logtm ==> pn <= (a * l2) * n]])
  let h1 ← ar (← ExceptT.mk [[!a. ~(a = 0) /\ ~(n <= a) ==> ~(n = 0)]])
  prove ([[&4 * ln(&1 + &2 pow j) + &3 <= (d * ln(&2)) * (&1 + &2 pow j) /\
   &4 / (&1 + &2 pow j) <= d * ln(&2) /\ &0 <= c /\ c / &2 + d + &1 <= c
   ==> !k. j <= k /\
           (!n. n <= 2 EXP k ==> psi(n) <= (c * ln(&2)) * &n)
           ==> !n. n <= 2 EXP (SUC k) ==> psi(n) <= (c * ln(&2)) * &n]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC ([[n <= 2 EXP k]]) THEN ASM_SIMP_TAC [] THEN
    MP_TAC (← HolLight.SPEC ([[n:num]]) PSI_BOUNDS_INDUCT) THEN
    SUBGOAL_THEN ([[~(n = 0)]]) (fun th => REWRITE_TAC [th]) THENL
     [MATCH_MP_TAC h1 THEN
      EXISTS_TAC ([[2 EXP k]]) THEN ASM_REWRITE_TAC [EXP_EQ_0, ARITH_EQ],
      ALL_TAC] THEN
    MATCH_MP_TAC h2 THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[n DIV 2]])) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [LE_LDIV_EQ, ARITH] THEN
      MATCH_MP_TAC h3 THEN
      ASM_REWRITE_TAC [(← HolLight.GSYM (← HolLight.CONJUNCT2 EXP))],
      ALL_TAC] THEN
    MATCH_MP_TAC h4 THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        pure (MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
       EXISTS_TAC (← ec (mk_comb (← ec (HolCore.Kernel.rator (← ec (HolCore.Equal.lhand w)))) ([[&n / &2]]))))) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_MUL THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC LN_POS THEN CONV_TAC REAL_RAT_REDUCE_CONV,
        ALL_TAC] THEN
      SIMP_TAC [REAL_LE_RDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
      REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_LE] THEN
      MP_TAC (← HolLight.SPECL [([[n:num]]), ([[2]])] DIVISION) THEN ARITH_TAC,
      ALL_TAC] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [real_div] THEN
    MATCH_MP_TAC h5 THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN EXISTS_TAC ([[(d * ln (&2)) * &n]]) THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC [LN_POS, REAL_OF_NUM_LE, ARITH] THEN
      REWRITE_TAC [(← HolLight.GSYM real_div)] THEN
      ASM_REWRITE_TAC [h6]] THEN
    SUBST1_TAC h7 THEN
    SUBGOAL_THEN ([[&2 pow j <= &n - &1]]) MP_TAC THENL
     [MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN EXISTS_TAC ([[&2 pow k]]) THEN CONJ_TAC THENL
       [ASM_SIMP_TAC [REAL_POW_MONO, REAL_OF_NUM_LE, ARITH], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP h8) THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM REAL_OF_NUM_LE)] THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_ADD), (← HolLight.GSYM REAL_OF_NUM_POW)] THEN
      REAL_ARITH_TAC2,
      ALL_TAC] THEN
    ABBREV_TAC ([[x = &n - &1]]) THEN SPEC_TAC (([[x:real]]), ([[x:real]])) THEN
    MATCH_MP_TAC OVERPOWER_LEMMA THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        let th ← ExceptT.mk (DIFF_CONV (← ec (HolCore.Equal.lhand (← ec (HolCore.Kernel.rator (← ec (HolCore.Kernel.rand (← ec (HolCore.Basics.body (← ec (HolCore.Kernel.rand (← ec (HolCore.Equal.lhand (← ec (HolCore.Kernel.rand (← ec (HolCore.Basics.body (← ec (HolCore.Kernel.rand w)))))))))))))))))))
        pure (MP_TAC th)) THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.TOP_DEPTH_CONV) [SessionLibrary.Analysis.REAL_MUL_LZERO, REAL_ADD_LID, REAL_ADD_RID,
      SessionLibrary.Analysis.REAL_MUL_RID, REAL_MUL_LID] THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        let tm ← ec (mk_abs ([[x:real]]) (← ec (HolCore.Kernel.rand (← ec (HolCore.Kernel.rator (← ec (HolCore.Kernel.rand (← ec (HolCore.Basics.body (← ec (HolCore.Kernel.rand (← ec (HolCore.Equal.lhand w)))))))))))))
        pure (DISCH_TAC THEN EXISTS_TAC tm)) THEN
    CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC, ALL_TAC] THEN
    REWRITE_TAC [] THEN CONJ_TAC THENL
     [GEN_TAC THEN
      DISCH_THEN (fun th => FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
      MATCH_MP_TAC h9 THEN
      SIMP_TAC [REAL_POW_LT, REAL_OF_NUM_LT, ARITH],
      ALL_TAC] THEN
    X_GEN_TAC ([[z:real]]) THEN DISCH_TAC THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_LE] THEN
    SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ), REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
    FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h10) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC [SessionLibrary.Analysis.REAL_LE_LADD] THEN
      ASM_SIMP_TAC [REAL_POW_LT, REAL_OF_NUM_LT, ARITH, h11],
      ALL_TAC] THEN
    SIMP_TAC [REAL_LE_RDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [REAL_MUL_SYM] THEN
    ASM_REWRITE_TAC [(← HolLight.GSYM real_div)])
  : ExceptT String IO thm).run
#eval PSI_BOUNDS_SUSTAINED_INDUCT

#eval phrase 49
def PSI_BOUNDS_SUSTAINED : thm := keep "PSI_BOUNDS_SUSTAINED" fun _ => (do
  let lemma ← prove ([[c / &2 + (c / &2 - &1) + &1 <= c]])
     (REWRITE_TAC [(← rr (← ExceptT.mk [[c2 + (c2 - &1) + &1 = &2 * c2]]))] THEN
      SIMP_TAC [REAL_DIV_LMUL, REAL_OF_NUM_EQ, ARITH_EQ, SessionLibrary.Analysis.REAL_LE_REFL])
  let h1 ← ar (← ExceptT.mk [[~(a = 0) /\ m <= a ==> SUC m <= 2 * a]])
  prove ([[(!n. n <= 2 EXP k ==> psi(n) <= (c * ln(&2)) * &n)
   ==> &4 * ln(&1 + &2 pow k) + &3
         <= ((c / &2 - &1) * ln(&2)) * (&1 + &2 pow k) /\
       &4 / (&1 + &2 pow k) <= (c / &2 - &1) * ln(&2) /\ &0 <= c
           ==> !n. psi(n) <= (c * ln(&2)) * &n]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    DISCH_THEN (MP_TAC o HolCore.Lib.C HolLight.CONJ lemma) THEN
    ABBREV_TAC ([[d = c / &2 - &1]]) THEN REWRITE_TAC [(← HolLight.GSYM CONJ_ASSOC)] THEN
    DISCH_THEN (ASSUME_TAC o HolLight.MATCH_MP PSI_BOUNDS_SUSTAINED_INDUCT) THEN
    X_GEN_TAC ([[m:num]]) THEN
    SUBGOAL_THEN ([[?j. m <= 2 EXP j]]) MP_TAC THENL
     [EXISTS_TAC ([[m:num]]) THEN SPEC_TAC (([[m:num]]), ([[m:num]])) THEN
      POP_ASSUM_LIST ((fun _ => ALL_TAC)) THEN INDUCT_TAC THEN REWRITE_TAC [ARITH] THEN
      REWRITE_TAC [EXP] THEN MATCH_MP_TAC h1 THEN
      ASM_REWRITE_TAC [EXP_EQ_0, ARITH_EQ],
      ALL_TAC] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN SPEC_TAC (([[m:num]]), ([[m:num]])) THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN INDUCT_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[2 EXP 0]]) THEN ASM_REWRITE_TAC [] THEN
      ASM_REWRITE_TAC [LE_EXP, ARITH_EQ, LE_0],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[k <= j:num]]) THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    SUBGOAL_THEN ([[2 EXP (SUC j) <= 2 EXP k]]) (fun th => ASM_MESON_TAC [th, LE_TRANS]) THEN
    ASM_REWRITE_TAC [LE_EXP, ARITH] THEN
    UNDISCH_TAC ([[~(k <= j:num)]]) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval PSI_BOUNDS_SUSTAINED

/- ------------------------------------------------------------------------- -/
/- Now apply it and get our reasonable bound.                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 50
def PSI_UBOUND_LOG : thm := keep "PSI_UBOUND_LOG" fun _ => (do
  let h1 ← nrc (← ExceptT.mk [[2 EXP 10]])
  prove ([[!n. psi(n) <= (&4407 / &2048 * ln (&2)) * &n]])
   (MP_TAC PSI_UBOUND_1024_LOG THEN
    SUBST1_TAC (← HolLight.SYM h1) THEN
    DISCH_THEN (MATCH_MP_TAC o HolLight.MATCH_MP PSI_BOUNDS_SUSTAINED) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV LN_N2_CONV) THEN
    CONJ_TAC THEN CONV_TAC REALCALC_REL_CONV)
  : ExceptT String IO thm).run
#eval PSI_UBOUND_LOG

#eval phrase 51
def PSI_UBOUND_3_2 : thm := keep "PSI_UBOUND_3_2" fun _ => (do
  prove ([[!n. psi(n) <= &3 / &2 * &n]])
   (GEN_TAC THEN MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[(&4407 / &2048 * ln (&2)) * &n]]) THEN
    REWRITE_TAC [PSI_UBOUND_LOG] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_POS] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV LN_N2_CONV) THEN
    CONV_TAC REALCALC_REL_CONV)
  : ExceptT String IO thm).run
#eval PSI_UBOUND_3_2

/- ------------------------------------------------------------------------- -/
/- Now get a lower bound.                                                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 52
def PSI_LBOUND_3_5 : thm := keep "PSI_LBOUND_3_5" fun _ => (do
  let lemma ← prove ([[a <= b /\ b <= l /\ rest ==> a <= l /\ b <= l /\ rest]])
     (MESON_TAC [SessionLibrary.Analysis.REAL_LE_TRANS])
  let tac := HolCore.Lib.time (CONV_TAC (HolLight.RAND_CONV LN_N2_CONV THENC REALCALC_REL_CONV))
  let h4 ← rr (← ExceptT.mk [[c <= n * (b - a) ==> a * n <= n * b - c]])
  let h3 ← ar (← ExceptT.mk [[~(n < 300) ==> ~(n = 0)]])
  let h2 ← rr (← ExceptT.mk [[a <= b ==> b <= x ==> a <= x]])
  let h1 ← tt (← ExceptT.mk [[T /\ a <=> a]])
  prove ([[!n. 4 <= n ==> &3 / &5 * &n <= psi(n)]])
   (GEN_TAC THEN ASM_CASES_TAC ([[n < 300]]) THENL
     [POP_ASSUM MP_TAC THEN SPEC_TAC (([[n:num]]), ([[n:num]])) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      REWRITE_TAC PSI_LIST_300 THEN
      REWRITE_TAC [LN_1, ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REPEAT ((MATCH_MP_TAC lemma THEN
         CONV_TAC (HolLight.LAND_CONV REAL_RAT_REDUCE_CONV) THEN
         GEN_REWRITE_TAC HolCore.Lib.I [h1]) ORELSE
         (CONJ_TAC THENL [tac THEN HolCore.Tactics.NO_TAC, ALL_TAC]) ORELSE tac),
      ALL_TAC] THEN
    DISCH_THEN ((fun _ => ALL_TAC)) THEN
    MP_TAC (← HolLight.CONJUNCT1 (← HolLight.SPEC ([[n:num]]) PSI_BOUNDS_INDUCT)) THEN
    MATCH_MP_TAC h2 THEN
    ASM_SIMP_TAC [h3] THEN
    MATCH_MP_TAC h4 THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN EXISTS_TAC ([[&1 / &11 * &n]]) THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_POS] THEN
      REWRITE_TAC [real_sub] THEN CONV_TAC (HolLight.ONCE_DEPTH_CONV LN_N2_CONV) THEN
      CONV_TAC REALCALC_REL_CONV] THEN
    ABBREV_TAC ([[x = &n - &1]]) THEN
    SUBGOAL_THEN ([[&n = &1 + x]]) SUBST1_TAC THENL
     [SessionLibrary.Analysis.EXPAND_TAC "x" THEN REAL_ARITH_TAC2, ALL_TAC] THEN
    SUBGOAL_THEN ([[&299 <= x]]) MP_TAC THENL
     [SessionLibrary.Analysis.EXPAND_TAC "x" THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_LE_SUB_LADD] THEN
      REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_LE, ARITH] THEN
      UNDISCH_TAC ([[~(n < 300)]]) THEN ARITH_TAC,
      ALL_TAC] THEN
    SPEC_TAC (([[x:real]]), ([[x:real]])) THEN POP_ASSUM_LIST ((fun _ => ALL_TAC)) THEN
    MATCH_MP_TAC OVERPOWER_LEMMA THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        let th ← ExceptT.mk (DIFF_CONV (← ec (HolCore.Equal.lhand (← ec (HolCore.Kernel.rator (← ec (HolCore.Kernel.rand (← ec (HolCore.Basics.body (← ec (HolCore.Kernel.rand (← ec (HolCore.Equal.lhand (← ec (HolCore.Kernel.rand (← ec (HolCore.Basics.body (← ec (HolCore.Kernel.rand w)))))))))))))))))))
        pure (MP_TAC th)) THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.TOP_DEPTH_CONV) [SessionLibrary.Analysis.REAL_MUL_LZERO, REAL_ADD_LID, REAL_ADD_RID,
      SessionLibrary.Analysis.REAL_MUL_RID, REAL_MUL_LID] THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        let tm ← ec (mk_abs ([[x:real]]) (← ec (HolCore.Kernel.rand (← ec (HolCore.Kernel.rator (← ec (HolCore.Kernel.rand (← ec (HolCore.Basics.body (← ec (HolCore.Kernel.rand (← ec (HolCore.Equal.lhand w)))))))))))))
        pure (DISCH_TAC THEN EXISTS_TAC tm)) THEN
    CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV LN_N2_CONV) THEN
      CONV_TAC REALCALC_REL_CONV,
      ALL_TAC] THEN
    REWRITE_TAC [] THEN CONJ_TAC THENL
     [GEN_TAC THEN
      DISCH_THEN (fun th => FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
      REAL_ARITH_TAC2,
      ALL_TAC] THEN
    POP_ASSUM_LIST ((fun _ => ALL_TAC)) THEN GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_LE] THEN
    SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ), REAL_OF_NUM_LT, ARITH] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[inv(&1 + &299)]]) THEN CONJ_TAC THENL
     [ALL_TAC, CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval PSI_LBOUND_3_5

/- ========================================================================= -/
/- Now the related theta function.                                           -/
/- ========================================================================= -/

#eval phrase 53
def theta : thm := keep "theta" fun _ => new_definition
 [[theta(n) = sum(1,n) (\p. if prime p then ln(&p) else &0)]]
#eval theta

/- ------------------------------------------------------------------------- -/
/- An optimized rule to give theta(n) for all n <= some N.                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 54
-- let THETA_LIST = ...;;
def THETA_LIST_0 : thm := keep "THETA_LIST_0" fun _ => (do
  prove ([[theta(0) = ln(&1)]])
   (REWRITE_TAC [theta, SessionLibrary.Analysis.sum, LN_1])
  : ExceptT String IO thm).run
def THETA_LIST_SUC : thm := keep "THETA_LIST_SUC" fun _ => (do
  prove ([[theta(SUC n) = theta(n) + (if prime(SUC n) then ln(&(SUC n)) else &0)]])
   (REWRITE_TAC [theta, SessionLibrary.Analysis.sum, ADD1] THEN REWRITE_TAC [ADD_AC])
  : ExceptT String IO thm).run
def THETA_LIST_SIMPER_CONV : HolCore.Equal.ioconv :=
  fun t => do
    (NUM_REDUCE_CONV THENC
     HolLight.ONCE_DEPTH_CONV PRIME_CONV THENC
     HolLight.GEN_REWRITE_CONV HolLight.TOP_DEPTH_CONV
      [COND_CLAUSES, REAL_ADD_LID, REAL_ADD_RID] THENC
     SIMP_CONV [(← HolLight.GSYM LN_MUL), REAL_OF_NUM_MUL, REAL_OF_NUM_LT, ARITH]) t
def THETA_LIST : Nat → IO (Except String (List thm))
  | 0 => pure (.ok [THETA_LIST_0])
  | n + 1 => (do
    let n_tm ← ExceptT.mk [[n:num]]
    let ths ← ExceptT.mk (THETA_LIST n)
    let th1 ← HolLight.INST [(← ec (mk_small_numeral (Int.ofNat n)), n_tm)] THETA_LIST_SUC
    let th2 ← HolLight.GEN_REWRITE_RULE (HolLight.RAND_CONV o HolLight.LAND_CONV)
      [← ec (HolCore.Lib.hd ths)] th1
    pure ((← HolLight.CONV_RULE THETA_LIST_SIMPER_CONV th2) :: ths)
    : ExceptT String IO (List thm)).run
/-- `THETA_LIST n` as a value (for its uses inside tactics). -/
def THETA_LISTv (n : Nat) : List thm :=
  match runIO (THETA_LIST n) with
  | .ok (.ok l) => l
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
#eval (do replay THETA_LIST_0; replay THETA_LIST_SUC; IO.println "<fun>" : IO Unit)

/- ------------------------------------------------------------------------- -/
/- Split up the psi sum to show close relationship with theta.               -/
/- ------------------------------------------------------------------------- -/

#eval phrase 55
def PRIMEPOW_ODD_EVEN : thm := keep "PRIMEPOW_ODD_EVEN" fun _ => (do
  prove ([[!p q j k.
     ~(prime(p) /\ prime(q) /\ 1 <= j /\ (p EXP (2 * j) = q EXP (2 * k + 1)))]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[q divides p]]) ASSUME_TAC THENL
     [MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC ([[2 * j]]) THEN
      UNDISCH_TAC ([[p EXP (2 * j) = q EXP (2 * k + 1)]]) THEN
      REWRITE_TAC [EXP_ADD, EXP_1] THEN
      ASM_MESON_TAC [divides, MULT_SYM],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[q = p:num]]) SUBST_ALL_TAC THENL
     [ASM_MESON_TAC [prime], ALL_TAC] THEN
    UNDISCH_TAC ([[p EXP (2 * j) = p EXP (2 * k + 1)]]) THEN
    REWRITE_TAC [(← HolLight.GSYM LE_ANTISYM)] THEN REWRITE_TAC [LE_EXP] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN
    REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[~(p = 1)]]) (fun th => REWRITE_TAC [th]) THENL
     [ASM_MESON_TAC [PRIME_1], ALL_TAC] THEN
    REWRITE_TAC [LE_ANTISYM] THEN
    DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[EVEN]])) THEN
    REWRITE_TAC [EVEN_ADD, EVEN_MULT, ARITH_EVEN])
  : ExceptT String IO thm).run
#eval PRIMEPOW_ODD_EVEN

#eval phrase 56
def PSI_SPLIT : thm := keep "PSI_SPLIT" fun _ => (do
  let h7 ← ar (← ExceptT.mk [[~(k = 0) ==> 1 <= k]])
  let h6 ← ar (← ExceptT.mk [[(k * 2 + 1 = 1) <=> (k = 0)]])
  let h5 ← ar (← ExceptT.mk [[1 <= j ==> ~(1 = 2 * j + 1)]])
  let h4 ← rr (← ExceptT.mk [[(a = a') /\ (b = &0) /\ (c = &0) ==> (a = a' + b + c)]])
  let h3 ← ar (← ExceptT.mk [[~(k = 0) ==> 1 <= k]])
  let h2 ← ar (← ExceptT.mk [[d < 2 ==> (d = 0) \/ (d = 1)]])
  let h1 ← ar (← ExceptT.mk [[1 <= k ==> 1 <= 2 * k /\ 1 <= 2 * k + 1]])
  prove ([[psi(n) = theta(n) +
            sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                          then ln(&(aprimedivisor d)) else &0) +
            sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                          then ln(&(aprimedivisor d)) else &0)]])
   (REWRITE_TAC [psi, theta, (← HolLight.GSYM SessionLibrary.Analysis.SUM_ADD)] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.SUM_EQ THEN X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN
    REWRITE_TAC [mangoldt, primepow] THEN
    ASM_CASES_TAC ([[?p k. 1 <= k /\ prime p /\ (r = p EXP k)]]) THEN
    ASM_REWRITE_TAC [] THENL
     [ALL_TAC,
      SUBGOAL_THEN ([[~(?p k. 1 <= k /\ prime p /\ (r = p EXP (2 * k))) /\
                  ~(?p k. 1 <= k /\ prime p /\ (r = p EXP (2 * k + 1))) /\
                  ~(prime r)]]) (fun th => REWRITE_TAC [th, REAL_ADD_LID]) THEN
      ASM_MESON_TAC [h1,
                    EXP_1, LE_REFL]] THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN ([[p:num]]) (X_CHOOSE_THEN ([[m:num]]) MP_TAC)) THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC (← HolLight.SPECL [([[m:num]]), ([[2]])] DIVISION) THEN REWRITE_TAC [ARITH_EQ] THEN
    MAP_EVERY ABBREV_TAC [([[k = m DIV 2]]), ([[d = m MOD 2]])] THEN
    DISCH_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    ASM_SIMP_TAC [APRIMEDIVISOR_PRIMEPOW] THEN
    FIRST_ASSUM (DISJ_CASES_THEN SUBST_ALL_TAC o HolLight.MATCH_MP h2) THEN
    ASM_REWRITE_TAC [PRIME_EXP, ADD_EQ_0, MULT_EQ_0, ARITH_EQ] THENL
     [UNDISCH_TAC ([[1 <= k * 2 + 0]]) THEN REWRITE_TAC [ADD_CLAUSES] THEN
      ASM_CASES_TAC ([[k = 0]]) THEN ASM_REWRITE_TAC [ARITH] THEN DISCH_TAC THEN
      SUBGOAL_THEN ([[~(k * 2 = 1)]]) (fun th => REWRITE_TAC [th]) THENL
       [DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[EVEN]])) THEN
        REWRITE_TAC [EVEN_MULT, ARITH_EVEN], ALL_TAC] THEN
      REPEAT (COND_CASES_TAC THEN
             ASM_REWRITE_TAC [REAL_ADD_LID, REAL_ADD_RID]) THEN
      ASM_MESON_TAC [PRIMEPOW_ODD_EVEN, MULT_SYM,
                    h3],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[k = 0]]) THENL
     [MATCH_MP_TAC h4 THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC [ARITH, EXP_1], ALL_TAC] THEN
      CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
       [ASM_MESON_TAC [PRIMEPOW_ODD_EVEN, MULT_SYM], ALL_TAC] THEN
      FIRST_X_ASSUM (X_CHOOSE_THEN ([[q:num]]) MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[j:num]]) MP_TAC) THEN STRIP_TAC THEN
      SUBGOAL_THEN ([[q divides p]]) ASSUME_TAC THENL
       [MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC ([[k * 2 + 1]]) THEN
        UNDISCH_TAC ([[p EXP (k * 2 + 1) = q EXP (2 * j + 1)]]) THEN
        REWRITE_TAC [EXP_ADD, EXP_1] THEN
        ASM_MESON_TAC [divides, MULT_SYM],
        ALL_TAC] THEN
      SUBGOAL_THEN ([[q = p:num]]) SUBST_ALL_TAC THENL
       [ASM_MESON_TAC [prime], ALL_TAC] THEN
      UNDISCH_TAC ([[p EXP (k * 2 + 1) = p EXP (2 * j + 1)]]) THEN
      REWRITE_TAC [(← HolLight.GSYM LE_ANTISYM)] THEN REWRITE_TAC [LE_EXP] THEN
      ASM_CASES_TAC ([[p = 0]]) THENL [ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC ([[p = 1]]) THENL [ASM_MESON_TAC [PRIME_1], ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES] THEN
      REWRITE_TAC [LE_ANTISYM] THEN
      ASM_SIMP_TAC [h5],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [h6, ARITH_EQ] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_ADD_LID, REAL_ADD_RID]) THEN
    ASM_MESON_TAC [PRIMEPOW_ODD_EVEN, MULT_SYM, h7])
  : ExceptT String IO thm).run
#eval PSI_SPLIT

/- ------------------------------------------------------------------------- -/
/- General lemma about sums.                                                 -/
/- ------------------------------------------------------------------------- -/

#eval phrase 57
def SUM_SURJECT : thm := keep "SUM_SURJECT" fun _ => (do
  let h7 ← rr (← ExceptT.mk [[&0 <= x /\ &0 <= y ==> a <= x + a + y]])
  let h6 ← ar (← ExceptT.mk [[m <= s ==> (m + (s - m) = s:num)]])
  let h5 ← rr (← ExceptT.mk [[f <= s'' ==> s <= s' ==> s + f <= s' + s'']])
  let h4 ← ar (← ExceptT.mk [[r < p + SUC q <=> (r = p + q) \/ r < p + q]])
  let h3 ← ar (← ExceptT.mk [[p + q < p + SUC q]])
  let h2 ← ar (← ExceptT.mk [[s < p + q ==> s < p + SUC q]])
  let h1 ← ar (← ExceptT.mk [[~(p <= q /\ q < p + 0)]])
  prove ([[!f i m n p q.
        (!r. m <= r /\ r < m + n ==> &0 <= f(i r)) /\
        (!s. p <= s /\ s < p + q /\ ~(f(s) = &0)
             ==> ?r. m <= r /\ r < m + n /\ (i r = s))
        ==> sum(p,q) f <= sum(m,n) (\r. f(i r))]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[sum(m,n) (\r. if p:num <= i(r) /\ i(r) < p + q
                            then f(i(r)) else &0)]]) THEN
    CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC SessionLibrary.Analysis.SUM_LE THEN X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN
      REWRITE_TAC [] THEN COND_CASES_TAC THEN
      ASM_MESON_TAC [SessionLibrary.Analysis.REAL_LE_REFL, ADD_AC]] THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN
    SPEC_TAC (([[q:num]]), ([[q:num]])) THEN INDUCT_TAC THENL
     [STRIP_TAC THEN REWRITE_TAC [SessionLibrary.Analysis.sum] THEN
      REWRITE_TAC [h1] THEN
      REWRITE_TAC [SessionLibrary.Analysis.SUM_0, SessionLibrary.Analysis.REAL_LE_REFL],
      ALL_TAC] THEN
    DISCH_THEN (fun th => POP_ASSUM MP_TAC THEN STRIP_ASSUME_TAC th) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC [h2],
      ALL_TAC] THEN
    REWRITE_TAC [SessionLibrary.Analysis.sum] THEN
    SUBGOAL_THEN ([[sum(m,n) (\r. if p <= i r /\ i r < p + SUC q then f (i r) else &0) =
    sum(m,n) (\r. if p <= i r /\ i r < p + q then f (i r) else &0) +
    sum(m,n) (\r. if i r = p + q then f(i r) else &0)]]) SUBST1_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM SessionLibrary.Analysis.SUM_ADD)] THEN MATCH_MP_TAC SessionLibrary.Analysis.SUM_EQ THEN
      X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN REWRITE_TAC [] THEN
      ASM_CASES_TAC ([[(i:num->num) r = p + q]]) THEN ASM_REWRITE_TAC [] THENL
       [REWRITE_TAC [LE_ADD, LT_REFL, h3] THEN
        REWRITE_TAC [REAL_ADD_LID, REAL_ADD_RID],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [h4] THEN
      REWRITE_TAC [REAL_ADD_RID],
      ALL_TAC] THEN
    MATCH_MP_TAC h5 THEN
    UNDISCH_TAC ([[!s. p <= s /\ s < p + SUC q /\ ~(f s = &0)
           ==> (?r:num. m <= r /\ r < m + n /\ (i r = s))]]) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[p + q:num]])) THEN
    ASM_CASES_TAC ([[f(p + q:num) = &0]]) THEN ASM_REWRITE_TAC [] THENL
     [MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
      EXISTS_TAC ([[sum(m,n) (\r. &0)]]) THEN CONJ_TAC THENL
       [REWRITE_TAC [SessionLibrary.Analysis.SUM_0, SessionLibrary.Analysis.REAL_LE_REFL], ALL_TAC] THEN
      MATCH_MP_TAC SessionLibrary.Analysis.SUM_LE THEN X_GEN_TAC ([[r:num]]) THEN
      REWRITE_TAC [] THEN COND_CASES_TAC THEN
      REWRITE_TAC [SessionLibrary.Analysis.REAL_LE_REFL] THEN ASM_MESON_TAC [ADD_SYM],
      ALL_TAC] THEN
    ANTS_TAC THENL [ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[s:num]]) STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN ([[n = (s - m) + 1 + ((m + n) - (s + 1))]]) SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [([[m <= s:num]]), ([[s < m + n:num]])] THEN ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT)] THEN
    ASM_SIMP_TAC [SUM_1, h6] THEN
    MATCH_MP_TAC h7 THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
      EXISTS_TAC ([[sum(m,s - m) (\r. &0)]]) THEN CONJ_TAC THENL
       [REWRITE_TAC [SessionLibrary.Analysis.SUM_0, SessionLibrary.Analysis.REAL_LE_REFL], ALL_TAC] THEN
      MATCH_MP_TAC SessionLibrary.Analysis.SUM_LE THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN
      COND_CASES_TAC THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_LE_REFL] THEN
      FIRST_ASSUM (SUBST1_TAC o HolLight.SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY UNDISCH_TAC [([[m <= r:num]]), ([[r < s - m + m:num]]), ([[s < m + n:num]]), ([[m <= s:num]])] THEN
      ARITH_TAC,
      MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
      EXISTS_TAC ([[sum(s + 1,(m + n) - (s + 1)) (\r. &0)]]) THEN CONJ_TAC THENL
       [REWRITE_TAC [SessionLibrary.Analysis.SUM_0, SessionLibrary.Analysis.REAL_LE_REFL], ALL_TAC] THEN
      MATCH_MP_TAC SessionLibrary.Analysis.SUM_LE THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN
      COND_CASES_TAC THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_LE_REFL] THEN
      FIRST_ASSUM (SUBST1_TAC o HolLight.SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY UNDISCH_TAC [([[r < (m + n) - (s + 1) + s + 1:num]]),
         ([[s + 1 <= r]]), ([[s < m + n:num]]), ([[m <= s:num]])] THEN
      ARITH_TAC])
  : ExceptT String IO thm).run
#eval SUM_SURJECT

/- ------------------------------------------------------------------------- -/
/- Apply this to show that one of the residuals is bounded by the other.     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 58
def PSI_RESIDUES_COMPARE_2 : thm := keep "PSI_RESIDUES_COMPARE_2" fun _ => (do
  let h13 ← ar (← ExceptT.mk [[2 <= n ==> ~(n = 1)]])
  let h12 ← tt (← ExceptT.mk [[(b ==> a) ==> ~a ==> b ==> c]])
  let h11 ← ar (← ExceptT.mk [[1 <= k ==> 1 <= 2 * k + 1]])
  let h10 ← ar (← ExceptT.mk [[1 <= k ==> 1 <= 2 * k]])
  let h9 ← ar (← ExceptT.mk [[1 <= k ==> 1 <= 2 * k /\ 1 <= 2 * k + 1]])
  let h8 ← rr (← ExceptT.mk [[b <= c ==> a <= b ==> a <= c]])
  let h7 ← ar (← ExceptT.mk [[1 <= k ==> ~(2 * k = 0)]])
  let h6 ← ar (← ExceptT.mk [[2 <= n <=> ~(n = 0) /\ ~(n = 1)]])
  let h5 ← ar (← ExceptT.mk [[1 <= k ==> 1 <= 2 * k]])
  let h4 ← ar (← ExceptT.mk [[1 <= k ==> 1 <= 2 * k]])
  let h3 ← ar (← ExceptT.mk [[2 <= n ==> 1 <= n]])
  let h2 ← ar (← ExceptT.mk [[1 <= k + 1]])
  let h1 ← ar (← ExceptT.mk [[1 <= k ==> 1 <= 2 * k + 1]])
  prove ([[sum(2,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                 then ln(&(aprimedivisor d)) else &0)
   <= sum(2,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                    then ln(&(aprimedivisor d)) else &0)]])
   (MP_TAC (← HolLight.SPECL [([[\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                    then ln(&(aprimedivisor d)) else &0]]),
      ([[\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP k)
                  then d * (aprimedivisor d) else d]]),
      ([[2]]), ([[n:num]]), ([[2]]), ([[n:num]])] SUM_SURJECT) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN
        ASM_CASES_TAC ([[?p k. 1 <= k /\ prime p /\ (r = p EXP k)]]) THEN
        ASM_REWRITE_TAC [] THENL
         [ALL_TAC,
          COND_CASES_TAC THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_LE_REFL] THEN
          ASM_MESON_TAC [h1]] THEN
        FIRST_X_ASSUM (X_CHOOSE_THEN ([[p:num]]) MP_TAC) THEN
        DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) MP_TAC) THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN SUBST_ALL_TAC THEN
        ASM_SIMP_TAC [APRIMEDIVISOR_PRIMEPOW] THEN
        COND_CASES_TAC THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_LE_REFL] THEN
        SUBGOAL_THEN ([[p EXP k * p = p EXP (k + 1)]]) SUBST1_TAC THENL
         [REWRITE_TAC [EXP_ADD, EXP_1, MULT_AC], ALL_TAC] THEN
        ASM_SIMP_TAC [APRIMEDIVISOR_PRIMEPOW, h2] THEN
        ASM_MESON_TAC [LN_POS, REAL_OF_NUM_LE, PRIME_GE_2, SessionLibrary.Analysis.REAL_LE_REFL,
                      h3],
        ALL_TAC] THEN
      X_GEN_TAC ([[s:num]]) THEN
      ASM_CASES_TAC ([[?p k. 1 <= k /\ prime p /\ (s = p EXP (2 * k + 1))]]) THEN
      ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (X_CHOOSE_THEN ([[p:num]]) MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) MP_TAC) THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      EXISTS_TAC ([[p EXP (2 * k)]]) THEN
      COND_CASES_TAC THENL
       [ALL_TAC, ASM_MESON_TAC [h4]] THEN
      ASM_SIMP_TAC [APRIMEDIVISOR_PRIMEPOW, EXP_ADD, EXP_1,
                   h5] THEN
      CONJ_TAC THENL
       [REWRITE_TAC [h6,
                    EXP_EQ_0, EXP_EQ_1] THEN
        ASM_MESON_TAC [PRIME_1, PRIME_0,
                      h7],
        ALL_TAC] THEN
      MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC ([[p EXP (2 * k + 1)]]) THEN
      ASM_REWRITE_TAC [LE_EXP] THEN
      COND_CASES_TAC THEN UNDISCH_TAC ([[1 <= k]]) THEN ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC h8 THEN
    MATCH_MP_TAC SessionLibrary.Analysis.SUM_LE THEN X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN
    REWRITE_TAC [] THEN
    ASM_CASES_TAC ([[?p k. 1 <= k /\ prime p /\ (r = p EXP k)]]) THEN
    ASM_REWRITE_TAC [] THENL
     [ALL_TAC,
      REPEAT COND_CASES_TAC THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_LE_REFL] THEN
      ASM_MESON_TAC [h9]] THEN
    FIRST_X_ASSUM (CHOOSE_THEN ((fun _ => ALL_TAC))) THEN
    ASM_CASES_TAC ([[?p k. 1 <= k /\ prime p /\ (r = p EXP (2 * k))]]) THEN
    ASM_REWRITE_TAC [] THENL
     [FIRST_X_ASSUM (X_CHOOSE_THEN ([[p:num]]) MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) MP_TAC) THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      ASM_SIMP_TAC [APRIMEDIVISOR_PRIMEPOW,
                   h10] THEN
      SUBGOAL_THEN ([[p EXP (2 * k) * p = p EXP (2 * k + 1)]]) SUBST1_TAC THENL
       [REWRITE_TAC [EXP_ADD, EXP_1, MULT_AC], ALL_TAC] THEN
      COND_CASES_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
      ASM_SIMP_TAC [APRIMEDIVISOR_PRIMEPOW, SessionLibrary.Analysis.REAL_LE_REFL,
                   h11],
      ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_LE_REFL] THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN ([[p:num]]) MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) MP_TAC) THEN
    FIRST_ASSUM (UNDISCH_TAC o check HolCore.Basics.is_neg o concl) THEN
    MATCH_MP_TAC h12 THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [([[p:num]]), ([[k:num]])] THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (← HolLight.SPEC ([[r:num]]) APRIMEDIVISOR) THEN
    ASM_SIMP_TAC [h13] THEN
    ABBREV_TAC ([[q = aprimedivisor r]]) THEN STRIP_TAC THEN
    SUBGOAL_THEN ([[q divides p]]) ASSUME_TAC THENL
     [MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC ([[2 * k + 1]]) THEN
      ASM_MESON_TAC [divides, MULT_SYM],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[q = p:num]]) SUBST_ALL_TAC THENL
     [ASM_MESON_TAC [prime], ALL_TAC] THEN
    UNDISCH_TAC ([[r * p = p EXP (2 * k + 1)]]) THEN
    REWRITE_TAC [EXP_ADD, EXP_1, EQ_MULT_RCANCEL] THEN
    ASM_MESON_TAC [PRIME_0])
  : ExceptT String IO thm).run
#eval PSI_RESIDUES_COMPARE_2

#eval phrase 59
def PSI_RESIDUES_COMPARE : thm := keep "PSI_RESIDUES_COMPARE" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[1 <= k ==> ~(2 * k = 0) /\ ~(2 * k + 1 = 0)]])
  let h2 ← rr (← ExceptT.mk [[b <= d /\ (a = &0) /\ (c = &0) ==> a + b <= c + d]])
  let h1 ← ar (← ExceptT.mk [[~(n = 0) ==> (n = 1 + (n - 1))]])
  prove ([[!n. sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                     then ln(&(aprimedivisor d)) else &0)
       <= sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                        then ln(&(aprimedivisor d)) else &0)]])
   (GEN_TAC THEN
    ASM_CASES_TAC ([[n = 0]]) THEN ASM_REWRITE_TAC [SessionLibrary.Analysis.sum, SessionLibrary.Analysis.REAL_LE_REFL] THEN
    FIRST_ASSUM (SUBST1_TAC o HolLight.MATCH_MP h1) THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT), SUM_1] THEN
    MATCH_MP_TAC h2 THEN
    REWRITE_TAC [PSI_RESIDUES_COMPARE_2, ARITH] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    ASM_MESON_TAC [EXP_EQ_1, PRIME_1, h3])
  : ExceptT String IO thm).run
#eval PSI_RESIDUES_COMPARE

/- ------------------------------------------------------------------------- -/
/- The even residual reduces to the square root case.                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 60
def PSI_SQRT : thm := keep "PSI_SQRT" fun _ => (do
  let h6 ← tt (← ExceptT.mk [[(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)]])
  let h5 ← ar (← ExceptT.mk [[1 + n = SUC n]])
  let h4 ← nc (← ExceptT.mk [[2]])
  let h3 ← ar (← ExceptT.mk [[1 + n = SUC n]])
  let h2 ← nc (← ExceptT.mk [[2]])
  let h1 ← ar (← ExceptT.mk [[1 + n = SUC n]])
  prove ([[!n. psi(ISQRT(n)) =
        sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                      then ln(&(aprimedivisor d)) else &0)]])
   (REWRITE_TAC [psi] THEN INDUCT_TAC THEN
    REWRITE_TAC [ISQRT_0, SessionLibrary.Analysis.sum, ISQRT_SUC] THEN
    ASM_CASES_TAC ([[?m. SUC n = m EXP 2]]) THENL
     [ALL_TAC,
      SUBGOAL_THEN ([[~(?p k. 1 <= k /\ prime p /\ (1 + n = p EXP (2 * k)))]]) ASSUME_TAC THENL
       [ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [EXP_MULT] THEN
        ASM_MESON_TAC [h1],
        ALL_TAC] THEN
      ASM_REWRITE_TAC [REAL_ADD_RID]] THEN
    ASM_REWRITE_TAC [REAL_EQ_ADD_LCANCEL, SessionLibrary.Analysis.sum] THEN
    FIRST_X_ASSUM (X_CHOOSE_TAC ([[m:num]])) THEN
    SUBGOAL_THEN ([[1 + ISQRT n = m]]) SUBST1_TAC THENL
     [SUBGOAL_THEN ([[(1 + ISQRT n) EXP 2 = SUC n]]) MP_TAC THENL
       [ALL_TAC,
        ASM_REWRITE_TAC [h2, (← HolLight.GSYM LE_ANTISYM)] THEN
        REWRITE_TAC [EXP_MONO_LE, EXP_MONO_LT, NOT_SUC]] THEN
      MP_TAC (← HolLight.SPEC ([[n:num]]) ISQRT_SUC) THEN
      COND_CASES_TAC THENL [ALL_TAC, ASM_MESON_TAC []] THEN
      REWRITE_TAC [h3] THEN
      DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
      MP_TAC (← HolLight.SPEC ([[SUC n]]) ISQRT_WORKS) THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [h4, (← HolLight.GSYM LE_ANTISYM)] THEN
      REWRITE_TAC [EXP_MONO_LE, EXP_MONO_LT, NOT_SUC] THEN ARITH_TAC,
      ALL_TAC] THEN
    ASM_REWRITE_TAC [h5] THEN
    REWRITE_TAC [mangoldt, primepow] THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [EXP_MULT] THEN
    REWRITE_TAC [EXP_MONO_EQ, ARITH_EQ] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [aprimedivisor] THEN
    REPEAT AP_TERM_TAC THEN ABS_TAC THEN
    MATCH_MP_TAC h6 THEN
    DISCH_TAC THEN REWRITE_TAC [EXP, EXP_1] THEN
    ASM_SIMP_TAC [PRIME_DIVEXP_EQ, ARITH_EQ])
  : ExceptT String IO thm).run
#eval PSI_SQRT

/- ------------------------------------------------------------------------- -/
/- Hence the main comparison result.                                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 61
def PSI_THETA : thm := keep "PSI_THETA" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[~(p = 0) ==> 1 <= p]])
  let h1 ← ar (← ExceptT.mk [[1 <= k ==> 1 <= 2 * k + 1]])
  prove ([[!n. theta(n) + psi(ISQRT n) <= psi(n) /\
       psi(n) <= theta(n) + &2 * psi(ISQRT n)]])
   (GEN_TAC THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [PSI_SPLIT] THEN
    GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.LAND_CONV) [PSI_SPLIT] THEN
    MP_TAC (← HolLight.SPEC ([[n:num]]) PSI_RESIDUES_COMPARE) THEN
    REWRITE_TAC [(← HolLight.GSYM PSI_SQRT)] THEN
    SIMP_TAC [REAL_MUL_2, (← HolLight.GSYM REAL_ADD_ASSOC), SessionLibrary.Analysis.REAL_LE_LADD, REAL_LE_ADDR] THEN
    DISCH_THEN ((fun _ => ALL_TAC)) THEN
    MATCH_MP_TAC SUM_POS_GEN THEN X_GEN_TAC ([[r:num]]) THEN DISCH_TAC THEN
    REWRITE_TAC [] THEN COND_CASES_TAC THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_LE_REFL] THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN ([[p:num]]) MP_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k:num]]) MP_TAC) THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC [APRIMEDIVISOR_PRIMEPOW,
      h1] THEN
    MATCH_MP_TAC LN_POS THEN REWRITE_TAC [REAL_OF_NUM_LE] THEN
    ASM_MESON_TAC [PRIME_0, h2])
  : ExceptT String IO thm).run
#eval PSI_THETA

/- ------------------------------------------------------------------------- -/
/- A trivial one-way comparison is immediate.                                -/
/- ------------------------------------------------------------------------- -/

#eval phrase 62
def THETA_LE_PSI : thm := keep "THETA_LE_PSI" fun _ => (do
  prove ([[!n. theta(n) <= psi(n)]])
   (GEN_TAC THEN REWRITE_TAC [theta, psi] THEN MATCH_MP_TAC SessionLibrary.Analysis.SUM_LE THEN
    X_GEN_TAC ([[p:num]]) THEN STRIP_TAC THEN
    ASM_CASES_TAC ([[prime p]]) THEN ASM_REWRITE_TAC [MANGOLDT_POS] THEN
    ASM_SIMP_TAC [mangoldt, PRIME_PRIMEPOW] THEN
    SUBGOAL_THEN ([[aprimedivisor p = p]]) (fun th => REWRITE_TAC [th, SessionLibrary.Analysis.REAL_LE_REFL]) THEN
    ASM_MESON_TAC [APRIMEDIVISOR_PRIMEPOW, EXP_1, LE_REFL])
  : ExceptT String IO thm).run
#eval THETA_LE_PSI

/- ------------------------------------------------------------------------- -/
/- A tighter bound on psi on a smaller range, to reduce later case analysis. -/
/- ------------------------------------------------------------------------- -/

#eval phrase 63
def PSI_UBOUND_30 : thm := keep "PSI_UBOUND_30" fun _ => (do
  let lemma ← prove ([[a <= b /\ l <= a /\ rest ==> l <= a /\ l <= b /\ rest]])
     (MESON_TAC [SessionLibrary.Analysis.REAL_LE_TRANS])
  let tac := HolCore.Lib.time (CONV_TAC (HolLight.LAND_CONV LN_N2_CONV THENC REALCALC_REL_CONV))
  let h2 ← tt (← ExceptT.mk [[T /\ a <=> a]])
  let h1 ← ar (← ExceptT.mk [[n <= 30 <=> n < 31]])
  prove ([[!n. n <= 30 ==> psi(n) <= &65 / &64 * &n]])
   (REWRITE_TAC [h1] THEN
    CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC PSI_LIST_300 THEN
    REWRITE_TAC [LN_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT ((MATCH_MP_TAC lemma THEN
       CONV_TAC (HolLight.LAND_CONV REAL_RAT_REDUCE_CONV) THEN
       GEN_REWRITE_TAC HolCore.Lib.I [h2]) ORELSE
       (CONJ_TAC THENL [tac THEN HolCore.Tactics.NO_TAC, ALL_TAC]) ORELSE tac))
  : ExceptT String IO thm).run
#eval PSI_UBOUND_30

/- ------------------------------------------------------------------------- -/
/- Bounds for theta, derived from those for psi.                             -/
/- ------------------------------------------------------------------------- -/

#eval phrase 64
def THETA_UBOUND_3_2 : thm := keep "THETA_UBOUND_3_2" fun _ => (do
  prove ([[!n. theta(n) <= &3 / &2 * &n]])
   (MESON_TAC [SessionLibrary.Analysis.REAL_LE_TRANS, PSI_UBOUND_3_2, THETA_LE_PSI])
  : ExceptT String IO thm).run
#eval THETA_UBOUND_3_2

#eval phrase 65
def THETA_LBOUND_1_2 : thm := keep "THETA_LBOUND_1_2" fun _ => (do
  let lemma ← prove ([[a <= b /\ b <= l /\ rest ==> a <= l /\ b <= l /\ rest]])
     (MESON_TAC [SessionLibrary.Analysis.REAL_LE_TRANS])
  let tac := HolCore.Lib.time (CONV_TAC (HolLight.RAND_CONV LN_N2_CONV THENC REALCALC_REL_CONV))
  let h7 ← rr (← ExceptT.mk [[(a * b) * (a * b) = a * a * b * b]])
  let h6 ← rr (← ExceptT.mk [[d <= (a - b) * n ==> a * n <= ps ==> ps <= th + d ==> b * n <= th]])
  let h5 ← ar (← ExceptT.mk [[5 <= n ==> 4 <= n]])
  let h4 ← tt (← ExceptT.mk [[T /\ a <=> a]])
  let h3 ← rr (← ExceptT.mk [[(a * b) * (a * b) = a * a * b * b]])
  let h2 ← rr (← ExceptT.mk [[d <= (a - b) * n ==> a * n <= ps ==> ps <= th + d ==> b * n <= th]])
  let h1 ← ar (← ExceptT.mk [[n >= 900 ==> 4 <= n]])
  prove ([[!n. 5 <= n ==> &1 / &2 * &n <= theta(n)]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC ([[n >= 900]]) THENL
     [MP_TAC (← HolLight.CONJUNCT2 (← HolLight.SPEC ([[n:num]]) PSI_THETA)) THEN
      MP_TAC (← HolLight.SPEC ([[n:num]]) PSI_LBOUND_3_5) THEN
      ASM_SIMP_TAC [h1] THEN
      MATCH_MP_TAC h2 THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
      SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ), REAL_OF_NUM_LT, ARITH] THEN
      REWRITE_TAC [real_div, (← HolLight.GSYM REAL_MUL_ASSOC)] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
      EXISTS_TAC ([[&3 / &2 * &(ISQRT n)]]) THEN
      REWRITE_TAC [PSI_UBOUND_3_2] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [REAL_MUL_SYM] THEN
      SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ), REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      REWRITE_TAC [real_div, (← HolLight.GSYM REAL_MUL_ASSOC)] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      SUBGOAL_THEN ([[&(ISQRT n) pow 2 <= (&n * &1 / &30) pow 2]]) MP_TAC THENL
       [ALL_TAC,
        ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_NOT_LE] THEN
        DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN
        ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV THEN
        MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_MUL THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_POS] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV] THEN
      MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN EXISTS_TAC ([[&n]]) THEN CONJ_TAC THENL
       [REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_LE, ISQRT_WORKS],
        ALL_TAC] THEN
      REWRITE_TAC [REAL_POW_2, h3] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM SessionLibrary.Analysis.REAL_MUL_RID)] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_POS] THEN
      SIMP_TAC [REAL_MUL_ASSOC, (← HolLight.GSYM REAL_LE_LDIV_EQ),
               REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [REAL_OF_NUM_LE] THEN
      UNDISCH_TAC ([[n >= 900]]) THEN ARITH_TAC,
      ALL_TAC] THEN
    ASM_CASES_TAC ([[n < 413]]) THENL
     [UNDISCH_TAC ([[5 <= n]]) THEN UNDISCH_TAC ([[n < 413]]) THEN
      SPEC_TAC (([[n:num]]), ([[n:num]])) THEN POP_ASSUM_LIST ((fun _ => ALL_TAC)) THEN
      CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC ((THETA_LISTv 412)) THEN
      REWRITE_TAC [LN_1, ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REPEAT ((MATCH_MP_TAC lemma THEN
         CONV_TAC (HolLight.LAND_CONV REAL_RAT_REDUCE_CONV) THEN
         GEN_REWRITE_TAC HolCore.Lib.I [h4]) ORELSE
         (CONJ_TAC THENL [tac THEN HolCore.Tactics.NO_TAC, ALL_TAC]) ORELSE tac),
      ALL_TAC] THEN
    MP_TAC (← HolLight.CONJUNCT2 (← HolLight.SPEC ([[n:num]]) PSI_THETA)) THEN
    MP_TAC (← HolLight.SPEC ([[n:num]]) PSI_LBOUND_3_5) THEN
    ASM_SIMP_TAC [h5] THEN
    MATCH_MP_TAC h6 THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ), REAL_OF_NUM_LT, ARITH] THEN
    REWRITE_TAC [real_div, (← HolLight.GSYM REAL_MUL_ASSOC)] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[&65 / &64 * &(ISQRT n)]]) THEN CONJ_TAC THENL
     [MATCH_MP_TAC PSI_UBOUND_30 THEN
      SUBGOAL_THEN ([[(ISQRT n) EXP (SUC 1) <= 30 EXP (SUC 1)]]) MP_TAC THENL
       [ALL_TAC, REWRITE_TAC [EXP_MONO_LE, NOT_SUC]] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[n:num]]) THEN
      REWRITE_TAC [ARITH, ISQRT_WORKS] THEN
      UNDISCH_TAC ([[~(n >= 900)]]) THEN ARITH_TAC,
      ALL_TAC] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [REAL_MUL_SYM] THEN
    SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ), REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
    REWRITE_TAC [real_div, (← HolLight.GSYM REAL_MUL_ASSOC)] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SUBGOAL_THEN ([[&(ISQRT n) pow 2 <= (&n * &16 / &325) pow 2]]) MP_TAC THENL
     [ALL_TAC,
      ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_NOT_LE] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_MUL THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_POS] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN EXISTS_TAC ([[&n]]) THEN CONJ_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_LE, ISQRT_WORKS],
      ALL_TAC] THEN
    REWRITE_TAC [REAL_POW_2, h7] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM SessionLibrary.Analysis.REAL_MUL_RID)] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_POS] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC [(← HolLight.GSYM REAL_LE_LDIV_EQ),
             REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN EXISTS_TAC ([[&413]]) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [REAL_OF_NUM_LE] THEN
    UNDISCH_TAC ([[~(n < 413)]]) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval THETA_LBOUND_1_2

/- ========================================================================= -/
/- Tighten the bounds on weak PNT to get the Bertrand conjecture.            -/
/- ========================================================================= -/

#eval phrase 66
def FLOOR_POS : thm := keep "FLOOR_POS" fun _ => (do
  prove ([[!x. &0 <= x ==> &0 <= floor x]])
   (GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC ([[x < &1]]) THENL
     [ASM_MESON_TAC [FLOOR_EQ_0, SessionLibrary.Analysis.REAL_LE_REFL], ALL_TAC] THEN
    MP_TAC (← ec (HolCore.Lib.last (HolLight.CONJUNCTS (← HolLight.SPEC ([[x:real]]) FLOOR)))) THEN
    UNDISCH_TAC ([[~(x < &1)]]) THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval FLOOR_POS

#eval phrase 67
def FLOOR_NUM_EXISTS : thm := keep "FLOOR_NUM_EXISTS" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[&0 <= x ==> (abs x = x)]])
  prove ([[!x. &0 <= x ==> ?k. floor x = &k]])
   (REPEAT STRIP_TAC THEN MP_TAC (← HolLight.CONJUNCT1 (← HolLight.SPEC ([[x:real]]) FLOOR)) THEN
    REWRITE_TAC [integer] THEN
    ASM_MESON_TAC [FLOOR_POS, h1])
  : ExceptT String IO thm).run
#eval FLOOR_NUM_EXISTS

#eval phrase 68
def FLOOR_DIV_INTERVAL : thm := keep "FLOOR_DIV_INTERVAL" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[0 < k + 1]])
  let h2 ← ar (← ExceptT.mk [[0 < d <=> ~(d = 0)]])
  let h1 ← ar (← ExceptT.mk [[0 < d <=> ~(d = 0)]])
  prove ([[!n d k. ~(d = 0)
           ==> ((floor(&n / &d) = &k) =
                  if k = 0 then &n < &d
                  else &n / &(k + 1) < &d /\ &d <= &n / &k)]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC ([[k = 0]]) THENL
     [ASM_REWRITE_TAC [FLOOR_EQ_0] THEN
      ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_LT_LDIV_EQ, REAL_OF_NUM_LT,
                   h1] THEN
      ASM_REWRITE_TAC [SessionLibrary.Analysis.REAL_MUL_LZERO, SessionLibrary.Analysis.REAL_POS, REAL_MUL_LID, REAL_OF_NUM_LT],
      ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM FLOOR_UNIQUE), INTEGER_CLOSED] THEN
    ASM_SIMP_TAC [REAL_LE_RDIV_EQ, REAL_LT_LDIV_EQ, REAL_OF_NUM_LT,
                   h2, h3] THEN
    REWRITE_TAC [REAL_MUL_AC, CONJ_ACI, REAL_OF_NUM_ADD])
  : ExceptT String IO thm).run
#eval FLOOR_DIV_INTERVAL

#eval phrase 69
def FLOOR_DIV_EXISTS : thm := keep "FLOOR_DIV_EXISTS" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[0 < k + 1 /\ (~(k = 0) ==> 0 < k)]])
  prove ([[!n d. ~(d = 0)
         ==> ?k. (floor(&n / &d) = &k) /\
                 d * k <= n /\ n < d * (k + 1)]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[?k. floor (&n / &d) = &k]]) MP_TAC THENL
     [ASM_SIMP_TAC [FLOOR_NUM_EXISTS, REAL_LE_DIV, SessionLibrary.Analysis.REAL_POS], ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC ([[k:num]]) THEN SIMP_TAC [] THEN ASM_SIMP_TAC [FLOOR_DIV_INTERVAL] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, LE_0, ADD_CLAUSES, REAL_OF_NUM_LT] THEN
    ASM_SIMP_TAC [REAL_LT_LDIV_EQ, REAL_LE_RDIV_EQ, REAL_OF_NUM_LT,
                 h1] THEN
    REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_LT, REAL_OF_NUM_LE] THEN
    REWRITE_TAC [CONJ_ACI])
  : ExceptT String IO thm).run
#eval FLOOR_DIV_EXISTS

#eval phrase 70
def FLOOR_HALF_INTERVAL : thm := keep "FLOOR_HALF_INTERVAL" fun _ => (do
  let lemma ← prove ([[ODD(k) ==> ~(k = 0)]])
     (MESON_TAC [EVEN, NOT_EVEN])
  let h3 ← ar (← ExceptT.mk [[2 * k1 < (2 * k3 + 1) + 1 /\ 2 * k3 + 1 < 2 * (k1 + 1)
    ==> (k3 = k1)]])
  let h2 ← ar (← ExceptT.mk [[2 * k1 < k2 + 1 /\ k2 < 2 * (k1 + 1)
      ==> (k2 = 2 * k1) \/ (k2 = 2 * k1 + 1)]])
  let h1 ← tt (← ExceptT.mk [[a /\ b /\ c <=> ~(a ==> ~(b /\ c))]])
  prove ([[!n d. ~(d = 0)
         ==> (floor (&n / &d) - &2 * floor (&(n DIV 2) / &d) =
                if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k
                then &1 else &0)]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC ([[n:num]]) o HolLight.MATCH_MP FLOOR_DIV_EXISTS) THEN
    FIRST_ASSUM (MP_TAC o HolLight.SPEC ([[n DIV 2]]) o HolLight.MATCH_MP FLOOR_DIV_EXISTS) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k1:num]]) (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k2:num]]) (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    MAP_EVERY UNDISCH_TAC [([[n DIV 2 < d * (k1 + 1)]]), ([[d * k1 <= n DIV 2]])] THEN
    ONCE_REWRITE_TAC [h1] THEN
    SIMP_TAC [(← HolLight.GSYM NOT_LE), LE_LDIV_EQ, LE_RDIV_EQ, ARITH_EQ, lemma, ADD_EQ_0] THEN
    REWRITE_TAC [NOT_LE, NOT_IMP] THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN ([[d * 2 * k1 < d * (k2 + 1) /\ d * k2 < d * 2 * (k1 + 1)]]) MP_TAC THENL [ASM_MESON_TAC [LET_TRANS, MULT_AC], ALL_TAC] THEN
    ASM_REWRITE_TAC [LT_MULT_LCANCEL] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP h2) THEN
    DISCH_THEN (DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_ADD), (← HolLight.GSYM REAL_OF_NUM_MUL),
                REAL_ADD_SUB, SessionLibrary.Analysis.REAL_SUB_REFL] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_OF_NUM_EQ, ARITH_EQ] THENL
     [ALL_TAC,
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [NOT_EXISTS_THM]) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[2 * k1 + 1]])) THEN
      ASM_REWRITE_TAC [ARITH_ODD, ODD_ADD, ODD_MULT] THEN
      ASM_MESON_TAC [MULT_AC]] THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN ([[k:num]]) MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    REWRITE_TAC [ODD_EXISTS, ADD1] THEN
    DISCH_THEN (X_CHOOSE_THEN ([[k3:num]]) SUBST_ALL_TAC) THEN
    SUBGOAL_THEN ([[d * 2 * k1 < d * ((2 * k3 + 1) + 1) /\
                d * (2 * k3 + 1) < d * 2 * (k1 + 1)]]) MP_TAC THENL [ASM_MESON_TAC [LET_TRANS, MULT_AC], ALL_TAC] THEN
    ASM_REWRITE_TAC [LT_MULT_LCANCEL] THEN
    DISCH_THEN (SUBST_ALL_TAC o HolLight.MATCH_MP h3) THEN
    POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval FLOOR_HALF_INTERVAL

#eval phrase 71
def SUM_EXPAND_LEMMA : thm := keep "SUM_EXPAND_LEMMA" fun _ => (do
  let h17 ← ar (← ExceptT.mk [[2 * j + 1 < 2 * k + 3 /\ 2 * k + 2 < 2 * j + 2 ==> (j = k)]])
  let h16 ← ar (← ExceptT.mk [[a < 1 + b ==> a <= b]])
  let h15 ← ar (← ExceptT.mk [[1 + a <= b ==> a < b]])
  let h14 ← ar (← ExceptT.mk [[SUC(2 * k) = 2 * k + 1]])
  let h13 ← ar (← ExceptT.mk [[SUC(2 * k) + 1 = 2 * k + 2]])
  let h12 ← ar (← ExceptT.mk [[SUC(2 * k) + 1 = 2 * k + 2]])
  let h11 ← ar (← ExceptT.mk [[2 * SUC k + 1 = 2 * k + 3]])
  let h10 ← ar (← ExceptT.mk [[(2 * k + 1) + 1 = SUC(2 * k) + 1]])
  let h9 ← ar (← ExceptT.mk [[n < r <=> 1 + n <= r]])
  let h8 ← ar (← ExceptT.mk [[n <= r <=> n < 1 + r]])
  let h7 ← rr (← ExceptT.mk [[!b. (a - b = d) /\ (b = c) ==> (a - c = d)]])
  let h6 ← rr (← ExceptT.mk [[(s - ss = x + y) ==> (ss = a - ((b + x) + y)) ==> (s = a - b)]])
  let h5 ← ar (← ExceptT.mk [[2 * SUC k = SUC(SUC(2 * k))]])
  let h4 ← ar (← ExceptT.mk [[~(m = 0) ==> m - 2 < m]])
  let h3 ← ar (← ExceptT.mk [[1 + n = SUC n]])
  let h2 ← ar (← ExceptT.mk [[1 + n = SUC n]])
  let h1 ← ar (← ExceptT.mk [[n < n + 1 /\ ~(n + 1 = 0)]])
  prove ([[!n m k. (m + 2 * k = n)
         ==> (sum (1,n DIV (2 * k + 1))
                  (\d. if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k
                       then mangoldt d else &0) =
              sum (1,n) (\d. --(&1) pow (d + 1) * psi (n DIV d)) -
              sum (1,2 * k)
                  (\d. --(&1) pow (d + 1) * psi (n DIV d)))]])
   (GEN_TAC THEN ASM_CASES_TAC ([[n = 0]]) THENL
     [ASM_SIMP_TAC [DIV_0, ADD_EQ_0, ARITH_EQ, SessionLibrary.Analysis.REAL_SUB_REFL, SessionLibrary.Analysis.sum], ALL_TAC] THEN
    MATCH_MP_TAC num_WF THEN X_GEN_TAC ([[m:num]]) THEN ASM_CASES_TAC ([[m = 0]]) THENL
     [DISCH_THEN ((fun _ => ALL_TAC)) THEN ASM_SIMP_TAC [ADD_CLAUSES] THEN
      ASM_SIMP_TAC [DIV_REFL, SUM_1, DIV_1, SessionLibrary.Analysis.REAL_SUB_REFL] THEN
      SUBGOAL_THEN ([[n DIV (n + 1) = 0]]) (fun th => REWRITE_TAC [th, SessionLibrary.Analysis.sum]) THEN
      ASM_MESON_TAC [DIV_EQ_0, h1],
      ALL_TAC] THEN
    ASM_CASES_TAC ([[m = 1]]) THENL
     [DISCH_THEN ((fun _ => ALL_TAC)) THEN ASM_REWRITE_TAC [] THEN
      X_GEN_TAC ([[k:num]]) THEN DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
      REWRITE_TAC [(← HolLight.GSYM ADD1), h2] THEN
      SIMP_TAC [DIV_REFL, NOT_SUC, SessionLibrary.Analysis.sum, SUM_1] THEN
      REWRITE_TAC [REAL_ADD_SUB, mangoldt] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV PRIMEPOW_CONV) THEN
      REWRITE_TAC [COND_ID] THEN CONV_TAC HolLight.SYM_CONV THEN
      REWRITE_TAC [REAL_ENTIRE] THEN DISJ2_TAC THEN
      REWRITE_TAC [h3] THEN
      SIMP_TAC [DIV_REFL, NOT_SUC] THEN REWRITE_TAC (LN_1 :: (PSI_LISTv 1)),
      ALL_TAC] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[m - 2]])) THEN
    ASM_SIMP_TAC [h4] THEN
    DISCH_TAC THEN X_GEN_TAC ([[k:num]]) THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[SUC k]])) THEN ANTS_TAC THENL
     [POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN ARITH_TAC,
      ALL_TAC] THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolCore.Lib.funpow 2 HolLight.RAND_CONV o HolLight.TOP_DEPTH_CONV) [h5, SessionLibrary.Analysis.sum] THEN
    MATCH_MP_TAC h6 THEN
    REWRITE_TAC [REAL_POW_NEG, EVEN_ADD, ARITH_EVEN, EVEN, EVEN_MULT] THEN
    REWRITE_TAC [REAL_POW_ONE, REAL_MUL_LID, REAL_MUL_LNEG] THEN
    GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.ONCE_DEPTH_CONV) [ADD_SYM] THEN
    REWRITE_TAC [psi, (← HolLight.GSYM real_sub)] THEN
    MATCH_MP_TAC h7 THEN
    EXISTS_TAC ([[sum (1,n DIV (SUC (2 * k) + 1))
                  (\d. if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k
                       then mangoldt d else &0)]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_DIFFERENCES_EQ THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIV_MONO2 THEN ARITH_TAC, ALL_TAC] THEN
      X_GEN_TAC ([[r:num]]) THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [NOT_EXISTS_THM]) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC ([[2 * k + 1]])) THEN
      REWRITE_TAC [ODD_ADD, ODD_MULT, ARITH_ODD] THEN
      ASM_REWRITE_TAC [h8] THEN
      ASM_REWRITE_TAC [h9] THEN
      ASM_REWRITE_TAC [h10],
      ALL_TAC] THEN
    MATCH_MP_TAC SUM_MORETERMS_EQ THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIV_MONO2 THEN ARITH_TAC, ALL_TAC] THEN
    X_GEN_TAC ([[r:num]]) THEN
    REWRITE_TAC [h11] THEN
    REWRITE_TAC [h12] THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN ([[oj:num]]) MP_TAC) THEN
    REWRITE_TAC [ODD_EXISTS] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN ([[j:num]]) SUBST1_TAC) THEN
    REWRITE_TAC [h13] THEN
    REWRITE_TAC [h14] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP h15) THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP h16) THEN
    SIMP_TAC [(← HolLight.GSYM NOT_LE), LE_RDIV_EQ, LE_LDIV_EQ, ADD_EQ_0, ARITH_EQ] THEN
    REWRITE_TAC [NOT_LE] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[(2 * j + 1) * r < (2 * k + 3) * r /\
                (2 * k + 2) * r < (2 * j + 2) * r]]) MP_TAC THENL [ASM_MESON_TAC [LET_TRANS], ALL_TAC] THEN
    ASM_REWRITE_TAC [LT_MULT_RCANCEL] THEN
    ASM_CASES_TAC ([[r = 0]]) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (SUBST_ALL_TAC o HolLight.MATCH_MP h17) THEN
    ASM_MESON_TAC [LET_TRANS, LT_REFL, MULT_AC])
  : ExceptT String IO thm).run
#eval SUM_EXPAND_LEMMA

#eval phrase 72
def FACT_EXPAND_PSI : thm := keep "FACT_EXPAND_PSI" fun _ => (do
  let h4 ← ar (← ExceptT.mk [[1 <= d ==> ~(d = 0)]])
  let h3 ← rr (← ExceptT.mk [[m * x - &2 * m * y = m * (x - &2 * y)]])
  let h2 ← rr (← ExceptT.mk [[(b = &0) ==> (a = a + b)]])
  let h1 ← nrc (← ExceptT.mk [[2 = 0]])
  prove ([[!n. ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2))) =
          sum(1,n) (\d. --(&1) pow (d + 1) * psi(n DIV d))]])
   (GEN_TAC THEN REWRITE_TAC [MANGOLDT] THEN
    SUBGOAL_THEN ([[sum (1,n DIV 2) (\d. mangoldt d * floor (&(n DIV 2) / &d)) =
    sum (1,n) (\d. mangoldt d * floor (&(n DIV 2) / &d))]]) SUBST1_TAC THENL
     [SUBGOAL_THEN ([[n = n DIV 2 + (n - n DIV 2)]]) (fun th => GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.LAND_CONV o HolLight.RAND_CONV) [th]) THENL [MESON_TAC [SUB_ADD, DIV_LE, ADD_SYM, h1],
             ALL_TAC] THEN
      REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT)] THEN
      MATCH_MP_TAC h2 THEN
      MATCH_MP_TAC SessionLibrary.Analysis.SUM_EQ_0 THEN X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN
      REWRITE_TAC [REAL_ENTIRE, FLOOR_EQ_0] THEN DISJ2_TAC THEN
      SIMP_TAC [REAL_LE_DIV, SessionLibrary.Analysis.REAL_POS] THEN
      SUBGOAL_THEN ([[0 < r /\ n DIV 2 < r]]) MP_TAC THENL
       [UNDISCH_TAC ([[1 + n DIV 2 <= r]]) THEN ARITH_TAC, ALL_TAC] THEN
      SIMP_TAC [REAL_LT_LDIV_EQ, REAL_OF_NUM_LT, REAL_MUL_LID],
      ALL_TAC] THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_CMUL), (← HolLight.GSYM SessionLibrary.Analysis.SUM_SUB)] THEN
    REWRITE_TAC [h3] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC ([[sum(1,n) (\d. if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k
                  then mangoldt d else &0)]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SessionLibrary.Analysis.SUM_EQ THEN
      X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN REWRITE_TAC [] THEN
      ASM_SIMP_TAC [FLOOR_HALF_INTERVAL, h4] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [SessionLibrary.Analysis.REAL_MUL_RID, SessionLibrary.Analysis.REAL_MUL_RZERO],
      ALL_TAC] THEN
    MP_TAC (← HolLight.SPECL [([[n:num]]), ([[n:num]]), ([[0]])] SUM_EXPAND_LEMMA) THEN
    REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES, SessionLibrary.Analysis.sum, SessionLibrary.Analysis.REAL_SUB_RZERO, DIV_1])
  : ExceptT String IO thm).run
#eval FACT_EXPAND_PSI

/- ------------------------------------------------------------------------- -/
/- Show that we can get bounds by cutting off at odd/even points.            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 73
def PSI_MONO : thm := keep "PSI_MONO" fun _ => (do
  prove ([[!m n. m <= n ==> psi(m) <= psi(n)]])
   (SIMP_TAC [LE_EXISTS, LEFT_IMP_EXISTS_THM, psi] THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT)] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [REAL_LE_ADDR] THEN
    MATCH_MP_TAC SUM_POS_GEN THEN REWRITE_TAC [MANGOLDT_POS])
  : ExceptT String IO thm).run
#eval PSI_MONO

#eval phrase 74
def PSI_POS : thm := keep "PSI_POS" fun _ => (do
  prove ([[!n. &0 <= psi(n)]])
   (SUBGOAL_THEN ([[psi(0) = &0]]) (fun th => MESON_TAC [th, PSI_MONO, LE_0]) THEN
    REWRITE_TAC (LN_1 :: (PSI_LISTv 0)))
  : ExceptT String IO thm).run
#eval PSI_POS

#eval phrase 75
def PSI_EXPANSION_CUTOFF : thm := keep "PSI_EXPANSION_CUTOFF" fun _ => (do
  let h4 ← rr (← ExceptT.mk [[&0 <= a + --b <=> b <= a]])
  let h3 ← rr (← ExceptT.mk [[s1 <= s1' /\ s2' <= s2
    ==> &0 <= a + b /\ &0 <= --c + --d
        ==> s1 <= (s1' + a) + b /\ (s2' + c) + d <= s2]])
  let h2 ← ar (← ExceptT.mk [[SUC(SUC n) + 1 = SUC(SUC(n + 1))]])
  let h1 ← ar (← ExceptT.mk [[2 * SUC n = SUC(SUC(2 * n))]])
  prove ([[!n m p. m <= p
         ==> sum(1,2 * m) (\d. --(&1) pow (d + 1) * psi(n DIV d))
               <= sum(1,2 * p) (\d. --(&1) pow (d + 1) * psi(n DIV d)) /\
             sum(1,2 * p + 1) (\d. --(&1) pow (d + 1) * psi(n DIV d))
               <= sum(1,2 * m + 1) (\d. --(&1) pow (d + 1) * psi(n DIV d))]])
   (GEN_TAC THEN SIMP_TAC [LE_EXISTS, LEFT_IMP_EXISTS_THM] THEN
    GEN_REWRITE_TAC HolLight.BINDER_CONV [SWAP_FORALL_THM] THEN
    SIMP_TAC [LEFT_FORALL_IMP_THM, EXISTS_REFL] THEN
    X_GEN_TAC ([[m:num]]) THEN INDUCT_TAC THEN
    REWRITE_TAC [ADD_CLAUSES, SessionLibrary.Analysis.REAL_LE_REFL] THEN
    REWRITE_TAC [h1,
                h2, SessionLibrary.Analysis.sum] THEN
    FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h3) THEN
    REWRITE_TAC [REAL_POW_NEG, EVEN_ADD, EVEN_MULT, ARITH_EVEN, EVEN] THEN
    REWRITE_TAC [REAL_POW_ONE, REAL_MUL_LID, REAL_MUL_LNEG, SessionLibrary.Analysis.REAL_NEG_NEG] THEN
    REWRITE_TAC [h4] THEN
    CONJ_TAC THEN MATCH_MP_TAC PSI_MONO THEN
    MATCH_MP_TAC DIV_MONO2 THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval PSI_EXPANSION_CUTOFF

#eval phrase 76
def FACT_PSI_BOUND_ODD : thm := keep "FACT_PSI_BOUND_ODD" fun _ => (do
  let h4 ← ar (← ExceptT.mk [[r < 2 <=> (r = 0) \/ (r = 1)]])
  let h3 ← ar (← ExceptT.mk [[1 + n <= r ==> n < r /\ ~(r = 0)]])
  let h2 ← ar (← ExceptT.mk [[~(k <= n) ==> n <= k:num]])
  let h1 ← rr (← ExceptT.mk [[(b = a) ==> a <= b]])
  prove ([[!n k. ODD(k)
         ==> ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2)))
             <= sum(1,k) (\d. --(&1) pow (d + 1) * psi(n DIV d))]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [FACT_EXPAND_PSI] THEN
    ASM_CASES_TAC ([[k <= n:num]]) THENL
     [ALL_TAC,
      MATCH_MP_TAC h1 THEN
      MATCH_MP_TAC SUM_MORETERMS_EQ THEN
      ASM_SIMP_TAC [h2] THEN
      X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN REWRITE_TAC [REAL_ENTIRE] THEN
      DISJ2_TAC THEN SUBGOAL_THEN ([[n DIV r = 0]]) SUBST1_TAC THENL
       [ASM_MESON_TAC [DIV_EQ_0, h3],
        REWRITE_TAC (LN_1 :: (PSI_LISTv 0))]] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [ODD_EXISTS]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[m:num]]) SUBST_ALL_TAC) THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[sum(1,SUC(2 * n DIV 2))
                 (\d. -- &1 pow (d + 1) * psi (n DIV d))]]) THEN
    CONJ_TAC THENL
     [ALL_TAC,
      SUBGOAL_THEN ([[m <= n DIV 2]]) (fun th => SIMP_TAC [th, ADD1, PSI_EXPANSION_CUTOFF]) THEN
      SIMP_TAC [LE_RDIV_EQ, ARITH_EQ] THEN
      POP_ASSUM MP_TAC THEN ARITH_TAC] THEN
    MP_TAC (← HolLight.SPECL [([[n:num]]), ([[2]])] DIVISION) THEN REWRITE_TAC [ARITH_EQ] THEN
    MAP_EVERY ABBREV_TAC [([[q = n DIV 2]]), ([[r = n MOD 2]])] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (fun th => GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.LAND_CONV o HolLight.RAND_CONV) [th]) MP_TAC) THEN
    REWRITE_TAC [h4] THEN
    DISCH_THEN (DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    REWRITE_TAC [ADD1, MULT_AC, SessionLibrary.Analysis.REAL_LE_REFL] THEN
    REWRITE_TAC [(← HolLight.GSYM ADD1), ADD_CLAUSES, SessionLibrary.Analysis.sum, REAL_LE_ADDR] THEN
    REWRITE_TAC [REAL_POW_NEG, EVEN, EVEN_ADD, EVEN_MULT, ARITH_EVEN] THEN
    REWRITE_TAC [REAL_POW_ONE, REAL_MUL_LID, PSI_POS])
  : ExceptT String IO thm).run
#eval FACT_PSI_BOUND_ODD

#eval phrase 77
def FACT_PSI_BOUND_EVEN : thm := keep "FACT_PSI_BOUND_EVEN" fun _ => (do
  let h4 ← ar (← ExceptT.mk [[r < 2 <=> (r = 0) \/ (r = 1)]])
  let h3 ← ar (← ExceptT.mk [[1 + n <= r ==> n < r /\ ~(r = 0)]])
  let h2 ← ar (← ExceptT.mk [[~(k <= n) ==> n <= k:num]])
  let h1 ← rr (← ExceptT.mk [[(a = b) ==> a <= b]])
  prove ([[!n k. EVEN(k)
         ==> sum(1,k) (\d. --(&1) pow (d + 1) * psi(n DIV d))
             <= ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2)))]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [FACT_EXPAND_PSI] THEN
    ASM_CASES_TAC ([[k <= n:num]]) THENL
     [ALL_TAC,
      MATCH_MP_TAC h1 THEN
      MATCH_MP_TAC SUM_MORETERMS_EQ THEN
      ASM_SIMP_TAC [h2] THEN
      X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN REWRITE_TAC [REAL_ENTIRE] THEN
      DISJ2_TAC THEN SUBGOAL_THEN ([[n DIV r = 0]]) SUBST1_TAC THENL
       [ASM_MESON_TAC [DIV_EQ_0, h3],
        REWRITE_TAC (LN_1 :: (PSI_LISTv 0))]] THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [EVEN_EXISTS]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[m:num]]) SUBST_ALL_TAC) THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[sum(1,2 * n DIV 2)
                 (\d. -- &1 pow (d + 1) * psi (n DIV d))]]) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN ([[m <= n DIV 2]]) (fun th => SIMP_TAC [th, ADD1, PSI_EXPANSION_CUTOFF]) THEN
      SIMP_TAC [LE_RDIV_EQ, ARITH_EQ] THEN
      POP_ASSUM MP_TAC THEN ARITH_TAC,
      ALL_TAC] THEN
    MP_TAC (← HolLight.SPECL [([[n:num]]), ([[2]])] DIVISION) THEN REWRITE_TAC [ARITH_EQ] THEN
    MAP_EVERY ABBREV_TAC [([[q = n DIV 2]]), ([[r = n MOD 2]])] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (fun th => GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.LAND_CONV o HolLight.RAND_CONV) [th]) MP_TAC) THEN
    REWRITE_TAC [h4] THEN
    DISCH_THEN (DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    REWRITE_TAC [ADD1, MULT_AC, ADD_CLAUSES, SessionLibrary.Analysis.REAL_LE_REFL] THEN
    REWRITE_TAC [(← HolLight.GSYM ADD1), ADD_CLAUSES, SessionLibrary.Analysis.sum, REAL_LE_ADDR] THEN
    REWRITE_TAC [REAL_POW_NEG, EVEN, EVEN_ADD, EVEN_MULT, ARITH_EVEN] THEN
    REWRITE_TAC [REAL_POW_ONE, REAL_MUL_LID, PSI_POS])
  : ExceptT String IO thm).run
#eval FACT_PSI_BOUND_EVEN

/- ------------------------------------------------------------------------- -/
/- In particular, we will use these.                                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 78
def FACT_PSI_BOUND_2_3 : thm := keep "FACT_PSI_BOUND_2_3" fun _ => (do
  prove ([[!n. psi(n) - psi(n DIV 2)
       <= ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2))) /\
       ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2)))
       <= psi(n) - psi(n DIV 2) + psi(n DIV 3)]])
   (GEN_TAC THEN
    MP_TAC (← HolLight.SPECL [([[n:num]]), ([[2]])] FACT_PSI_BOUND_EVEN) THEN
    MP_TAC (← HolLight.SPECL [([[n:num]]), ([[3]])] FACT_PSI_BOUND_ODD) THEN
    REWRITE_TAC [ARITH] THEN
    CONV_TAC (HolLight.ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
    REWRITE_TAC [ARITH, REAL_ADD_LID, DIV_1] THEN
    REWRITE_TAC [REAL_POW_NEG, ARITH, REAL_POW_ONE, REAL_MUL_LID] THEN
    REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval FACT_PSI_BOUND_2_3

/- ------------------------------------------------------------------------- -/
/- Hence get a good lower bound on psi(n) - psi(n/2).                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 79
def PSI_DOUBLE_LEMMA : thm := keep "PSI_DOUBLE_LEMMA" fun _ => (do
  let h8 ← rr (← ExceptT.mk [[a <= x ==> inv(&1 + x) <= inv(&1 + a) /\
               inv(&1 + a) <= b ==> inv(&1 + x) <= b]])
  let h7 ← rr (← ExceptT.mk [[a <= n ==> a - &1 <= n - &1]])
  let h6 ← ar (← ExceptT.mk [[n >= b ==> b <= n:num]])
  let h5 ← rr (← ExceptT.mk [[&n = &1 + (&n - &1)]])
  let h4 ← ar (← ExceptT.mk [[n >= 1200 ==> ~(n = 0)]])
  let h3 ← rr (← ExceptT.mk [[ltm <= nl2 - a ==> abs(lf - nl2) <= ltm ==> a <= lf]])
  let h2 ← rr (← ExceptT.mk [[a <= b ==> x <= a ==> x <= b]])
  let h1 ← rr (← ExceptT.mk [[b + p3 <= a ==> u <= v /\ a <= p - p2 + p3 ==> b <= p - p2]])
  prove ([[!n. n >= 1200 ==> &n / &6 <= psi(n) - psi(n DIV 2)]])
   (REPEAT STRIP_TAC THEN MP_TAC (← HolLight.SPEC ([[n:num]]) FACT_PSI_BOUND_2_3) THEN
    MATCH_MP_TAC h1 THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[&n / &6 + &n / &2]]) THEN CONJ_TAC THENL
     [REWRITE_TAC [SessionLibrary.Analysis.REAL_LE_LADD] THEN MP_TAC (← HolLight.SPEC ([[n DIV 3]]) PSI_UBOUND_3_2) THEN
      MATCH_MP_TAC h2 THEN
      MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN EXISTS_TAC ([[&3 / &2 * &n / &3]]) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        SIMP_TAC [REAL_LE_RDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
        REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_LE] THEN
        MP_TAC (← HolLight.SPECL [([[n:num]]), ([[3]])] DIVISION) THEN ARITH_TAC,
        ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
        REWRITE_TAC [real_div, (← HolLight.GSYM REAL_MUL_ASSOC)] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_LE_REFL]],
      ALL_TAC] THEN
    MP_TAC (← HolLight.SPEC ([[n:num]]) LN_FACT_DIFF_BOUNDS) THEN
    MATCH_MP_TAC h3 THEN
    ASM_SIMP_TAC [h4] THEN
    REWRITE_TAC [real_div, (← HolLight.GSYM SessionLibrary.Analysis.REAL_SUB_LDISTRIB), (← HolLight.GSYM REAL_ADD_LDISTRIB)] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[&n * &1 / &38]]) THEN CONJ_TAC THENL
     [ALL_TAC,
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_POS] THEN
      SIMP_TAC [SessionLibrary.Analysis.REAL_LE_SUB_LADD] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      CONV_TAC (HolLight.RAND_CONV LN_N2_CONV) THEN CONV_TAC REALCALC_REL_CONV] THEN
    SUBST1_TAC h5 THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.MATCH_MP h6) THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM REAL_OF_NUM_LE)] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP h7) THEN
    ABBREV_TAC ([[x = &n - &1]]) THEN
    CONV_TAC (HolLight.LAND_CONV NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV) THEN
    SPEC_TAC (([[x:real]]), ([[x:real]])) THEN POP_ASSUM_LIST ((fun _ => ALL_TAC)) THEN
    MATCH_MP_TAC OVERPOWER_LEMMA THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        let th ← ExceptT.mk (DIFF_CONV (← ec (HolCore.Equal.lhand (← ec (HolCore.Kernel.rator (← ec (HolCore.Kernel.rand (← ec (HolCore.Basics.body (← ec (HolCore.Kernel.rand (← ec (HolCore.Equal.lhand (← ec (HolCore.Kernel.rand (← ec (HolCore.Basics.body (← ec (HolCore.Kernel.rand w)))))))))))))))))))
        pure (MP_TAC th)) THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.TOP_DEPTH_CONV) [SessionLibrary.Analysis.REAL_MUL_LZERO, REAL_ADD_LID, REAL_ADD_RID,
      SessionLibrary.Analysis.REAL_MUL_RID, REAL_MUL_LID] THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        let tm ← ec (mk_abs ([[x:real]]) (← ec (HolCore.Kernel.rand (← ec (HolCore.Kernel.rator (← ec (HolCore.Kernel.rand (← ec (HolCore.Basics.body (← ec (HolCore.Kernel.rand (← ec (HolCore.Equal.lhand w)))))))))))))
        pure (DISCH_TAC THEN EXISTS_TAC tm)) THEN
    CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [real_sub] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV LN_N2_CONV) THEN
      CONV_TAC REALCALC_REL_CONV,
      ALL_TAC] THEN
    REWRITE_TAC [] THEN CONJ_TAC THENL
     [GEN_TAC THEN
      DISCH_THEN (fun th => FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
      REAL_ARITH_TAC2,
      ALL_TAC] THEN
    X_GEN_TAC ([[x:real]]) THEN DISCH_TAC THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_LE] THEN
    SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ), REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
    FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP h8) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      POP_ASSUM MP_TAC THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval PSI_DOUBLE_LEMMA

/- ------------------------------------------------------------------------- -/
/- Hence show that theta changes (could get a lower bound like n/10).        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 80
def THETA_DOUBLE_LEMMA : thm := keep "THETA_DOUBLE_LEMMA" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[324 * i * i < a ==> (i * 18) * (i * 18) < a]])
  prove ([[!n. n >= 1200 ==> theta(n DIV 2) < theta(n)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.CONJUNCT2 (← HolLight.SPEC ([[n:num]]) PSI_THETA)) THEN
    MP_TAC (← HolLight.CONJUNCT1 (← HolLight.SPEC ([[n DIV 2]]) PSI_THETA)) THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP PSI_DOUBLE_LEMMA) THEN
    MP_TAC (← HolLight.SPEC ([[ISQRT(n DIV 2)]]) PSI_POS) THEN
    SUBGOAL_THEN ([[&2 * psi (ISQRT n) < &n / &6]]) (fun th => MP_TAC th THEN REAL_ARITH_TAC2) THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    SIMP_TAC [(← HolLight.GSYM REAL_LT_RDIV_EQ), REAL_OF_NUM_LT, ARITH] THEN
    REWRITE_TAC [real_div, (← HolLight.GSYM REAL_MUL_ASSOC)] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC ([[&3 / &2 * &(ISQRT n)]]) THEN
    REWRITE_TAC [PSI_UBOUND_3_2] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [REAL_MUL_SYM] THEN
    SIMP_TAC [(← HolLight.GSYM REAL_LT_RDIV_EQ), REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
    REWRITE_TAC [real_div, (← HolLight.GSYM REAL_MUL_ASSOC)] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [real_div, REAL_MUL_LID] THEN
    SIMP_TAC [(← HolLight.GSYM real_div), REAL_LT_RDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
    REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_LT] THEN
    SUBGOAL_THEN ([[(ISQRT n * 18) EXP (SUC 1) < n EXP (SUC 1)]]) MP_TAC THENL
     [ALL_TAC, REWRITE_TAC [EXP_MONO_LT, NOT_SUC]] THEN
    REWRITE_TAC [EXP, EXP_1] THEN
    MATCH_MP_TAC h1 THEN
    MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC ([[324 * n]]) THEN CONJ_TAC THENL
     [REWRITE_TAC [(← HolLight.GSYM EXP_2), ISQRT_WORKS, LE_MULT_LCANCEL],
      REWRITE_TAC [LT_MULT_RCANCEL] THEN POP_ASSUM MP_TAC THEN ARITH_TAC])
  : ExceptT String IO thm).run
#eval THETA_DOUBLE_LEMMA

/- ------------------------------------------------------------------------- -/
/- Hence Bertrand for sufficiently large n.                                  -/
/- ------------------------------------------------------------------------- -/

#eval phrase 81
def BIG_BERTRAND : thm := keep "BIG_BERTRAND" fun _ => (do
  let h3 ← rr (← ExceptT.mk [[(b + a = c) ==> (a = &0) ==> ~(b < c)]])
  let h2 ← ar (← ExceptT.mk [[n + 1 <= r /\ r < n + n + 1 ==> n <= r /\ r <= 2 * n]])
  let h1 ← tt (← ExceptT.mk [[~(a /\ b /\ c) <=> b /\ c ==> ~a]])
  prove ([[!n. n >= 2400 ==> ?p. prime(p) /\ n <= p /\ p <= 2 * n]])
   (REPEAT STRIP_TAC THEN MP_TAC (← HolLight.SPEC ([[2 * n]]) THETA_DOUBLE_LEMMA) THEN
    ANTS_TAC THENL [POP_ASSUM MP_TAC THEN ARITH_TAC, ALL_TAC] THEN
    SIMP_TAC [DIV_MULT, ARITH_EQ] THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN
    REWRITE_TAC [NOT_EXISTS_THM, h1] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN ([[sum(n + 1,n) (\p. if prime p then ln (&p) else &0) = &0]]) MP_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC ([[sum(n + 1,n) (\r. &0)]]) THEN
      CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [SessionLibrary.Analysis.SUM_0]] THEN
      MATCH_MP_TAC SessionLibrary.Analysis.SUM_EQ THEN
      ASM_SIMP_TAC [h2],
      ALL_TAC] THEN
    MATCH_MP_TAC h3 THEN
    REWRITE_TAC [theta] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
    REWRITE_TAC [SUM_SPLIT] THEN
    REWRITE_TAC [MULT_2])
  : ExceptT String IO thm).run
#eval BIG_BERTRAND

/- ------------------------------------------------------------------------- -/
/- Landau trick. Should be automatic but ARITH_RULE is a bit slow.           -/
/- (Direct use of ARITH_RULE takes about 3 minutes on my current laptop.)    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 82
def LANDAU_TRICK : thm := keep "LANDAU_TRICK" fun _ => (do
  let lemma ← tt (← ExceptT.mk [[(p /\ b1 ==> a1) /\ (~b1 ==> a2) ==> p ==> b1 /\ a1 \/ a2]])
  let h1 ← tt (← ExceptT.mk [[a /\ b ==> c <=> a ==> c \/ ~b]])
  prove ([[!n. 0 < n /\ n < 2400
       ==> n <= 2 /\ 2 <= 2 * n \/
           n <= 3 /\ 3 <= 2 * n \/
           n <= 5 /\ 5 <= 2 * n \/
           n <= 7 /\ 7 <= 2 * n \/
           n <= 13 /\ 13 <= 2 * n \/
           n <= 23 /\ 23 <= 2 * n \/
           n <= 43 /\ 43 <= 2 * n \/
           n <= 83 /\ 83 <= 2 * n \/
           n <= 163 /\ 163 <= 2 * n \/
           n <= 317 /\ 317 <= 2 * n \/
           n <= 631 /\ 631 <= 2 * n \/
           n <= 1259 /\ 1259 <= 2 * n \/
           n <= 2503 /\ 2503 <= 2 * n]])
   (GEN_TAC THEN ONCE_REWRITE_TAC [h1] THEN
    REWRITE_TAC [(← HolLight.GSYM DISJ_ASSOC)] THEN
    REPEAT (MATCH_MP_TAC lemma THEN CONJ_TAC THENL [ARITH_TAC, ALL_TAC]) THEN
    ARITH_TAC)
  : ExceptT String IO thm).run
#eval LANDAU_TRICK

/- ------------------------------------------------------------------------- -/
/- Bertrand for all nonzero n using "Landau trick".                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 83
/-- `PRIME_CONV o curry mk_comb `prime` o mk_small_numeral` (used by BERTRAND). -/
private def primeConv (n : Int) : ExceptT String IO thm := do
  ExceptT.mk (PRIME_CONV (← ec (mk_comb (← ExceptT.mk [[prime]]) (← ec (mk_small_numeral n)))))
def BERTRAND : thm := keep "BERTRAND" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[0 < n <=> ~(n = 0)]])
  let h1 ← ar (← ExceptT.mk [[n >= 2400 \/ n < 2400]])
  prove ([[!n. ~(n = 0) ==> ?p. prime p /\ n <= p /\ p <= 2 * n]])
   (REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC h1 THEN
    ASM_SIMP_TAC [BIG_BERTRAND] THEN MP_TAC (← HolLight.SPEC ([[n:num]]) LANDAU_TRICK) THEN
    ASM_REWRITE_TAC [h2] THEN
    STRIP_TAC THEN
    ASM_MESON_TAC (← [2, 3, 5, 7, 13, 23, 43, 83, 163, 317, 631, 1259, 2503].mapM primeConv))
  : ExceptT String IO thm).run
#eval BERTRAND

/- ========================================================================= -/
/- Weak form of the Prime Number Theorem.                                    -/
/- ========================================================================= -/

#eval phrase 84
def pii : thm := keep "pii" fun _ => new_definition
 [[pii(n) = sum(1,n) (\p. if prime(p) then &1 else &0)]]
#eval pii

/- ------------------------------------------------------------------------- -/
/- An optimized rule to give pii(n) for all n <= some N.                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 85
-- let PII_LIST = ...;;
def PII_LIST_0 : thm := keep "PII_LIST_0" fun _ => (do
  prove ([[pii(0) = &0]])
   (REWRITE_TAC [pii, SessionLibrary.Analysis.sum])
  : ExceptT String IO thm).run
def PII_LIST_SUC : thm := keep "PII_LIST_SUC" fun _ => (do
  prove ([[pii(SUC n) = pii(n) + (if prime(SUC n) then &1 else &0)]])
   (REWRITE_TAC [pii, SessionLibrary.Analysis.sum, ADD1] THEN REWRITE_TAC [ADD_AC])
  : ExceptT String IO thm).run
def PII_LIST_SIMPER_CONV : HolCore.Equal.ioconv :=
  NUM_REDUCE_CONV THENC
    HolLight.ONCE_DEPTH_CONV PRIME_CONV THENC
    HolLight.GEN_REWRITE_CONV HolLight.TOP_DEPTH_CONV [COND_CLAUSES] THENC
    REAL_RAT_REDUCE_CONV
def PII_LIST : Nat → IO (Except String (List thm))
  | 0 => pure (.ok [PII_LIST_0])
  | n + 1 => (do
    let n_tm ← ExceptT.mk [[n:num]]
    let ths ← ExceptT.mk (PII_LIST n)
    let th1 ← HolLight.INST [(← ec (mk_small_numeral (Int.ofNat n)), n_tm)] PII_LIST_SUC
    let th2 ← HolLight.GEN_REWRITE_RULE (HolLight.RAND_CONV o HolLight.LAND_CONV)
      [← ec (HolCore.Lib.hd ths)] th1
    pure ((← HolLight.CONV_RULE PII_LIST_SIMPER_CONV th2) :: ths)
    : ExceptT String IO (List thm)).run
/-- `PII_LIST n` as a value (for its uses inside tactics). -/
def PII_LISTv (n : Nat) : List thm :=
  match runIO (PII_LIST n) with
  | .ok (.ok l) => l
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
#eval (do replay PII_LIST_0; replay PII_LIST_SUC; IO.println "<fun>" : IO Unit)

/- ------------------------------------------------------------------------- -/
/- Prove the usual characterization.                                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 86
def PRIMES_FINITE : thm := keep "PRIMES_FINITE" fun _ => (do
  prove ([[!n. FINITE {p | p <= n /\ prime(p)}]])
   (GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC ([[{p | p < SUC n}]]) THEN REWRITE_TAC [FINITE_NUMSEG_LT] THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval PRIMES_FINITE

#eval phrase 87
def PII : thm := keep "PII" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[~(SUC n <= n)]])
  let h1 ← ar (← ExceptT.mk [[1 + n = SUC n]])
  prove ([[!n. pii(n) = &(CARD {p | p <= n /\ prime(p)})]])
   (INDUCT_TAC THENL
     [SUBGOAL_THEN ([[{p | p <= 0 /\ prime p} = {}]]) (fun th => REWRITE_TAC (th :: CARD_CLAUSES :: (PII_LISTv 0))) THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
      MESON_TAC [LE, PRIME_0, NOT_IN_EMPTY],
      ALL_TAC] THEN
    SUBGOAL_THEN ([[{p | p <= SUC n /\ prime p} =
                if prime(SUC n) then (SUC n) INSERT {p | p <= n /\ prime p}
                else {p | p <= n /\ prime p}]]) SUBST1_TAC THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC [EXTENSION, IN_INSERT, IN_ELIM_THM] THEN
      ASM_MESON_TAC [LE],
      ALL_TAC] THEN
    REWRITE_TAC [pii, SessionLibrary.Analysis.sum] THEN REWRITE_TAC [(← HolLight.GSYM pii)] THEN
    REWRITE_TAC [h1] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [REAL_ADD_RID] THEN
    SIMP_TAC [CARD_CLAUSES, PRIMES_FINITE] THEN COND_CASES_TAC THENL
     [RULE_ASSUM_TAC (HolLight.REWRITE_RULE [IN_ELIM_THM]) THEN
      ASM_MESON_TAC [h2],
      REWRITE_TAC [REAL_OF_NUM_SUC]])
  : ExceptT String IO thm).run
#eval PII

/- ------------------------------------------------------------------------- -/
/- One bound is a simple consequence of the one for theta.                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 88
def PII_LBOUND : thm := keep "PII_LBOUND" fun _ => (do
  let h3 ← rr (← ExceptT.mk [[x <= y ==> a <= x ==> a <= y]])
  let h2 ← ar (← ExceptT.mk [[3 <= n ==> (n = 3) \/ (n = 4) \/ 5 <= n]])
  let h1 ← ar (← ExceptT.mk [[3 <= n ==> 1 < n]])
  prove ([[!n. 3 <= n ==> &1 / &2 * (&n / ln(&n)) <= pii(n)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [real_div, REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM real_div), REAL_LE_LDIV_EQ, LN_POS_LT, REAL_OF_NUM_LT,
                 h1] THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [REAL_MUL_SYM] THEN
    FIRST_X_ASSUM (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o HolLight.MATCH_MP h2) THEN
    ASM_REWRITE_TAC ((PII_LISTv 4)) THENL
     [CONV_TAC (HolLight.ONCE_DEPTH_CONV LN_N2_CONV) THEN CONV_TAC REALCALC_REL_CONV,
      CONV_TAC (HolLight.ONCE_DEPTH_CONV LN_N2_CONV) THEN CONV_TAC REALCALC_REL_CONV,
      ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP THETA_LBOUND_1_2) THEN
    MATCH_MP_TAC h3 THEN
    REWRITE_TAC [theta, pii, (← HolLight.GSYM SUM_CMUL)] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.SUM_LE THEN X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN
    REWRITE_TAC [] THEN COND_CASES_TAC THEN
    REWRITE_TAC [SessionLibrary.Analysis.REAL_MUL_RZERO, SessionLibrary.Analysis.REAL_MUL_RID, SessionLibrary.Analysis.REAL_LE_REFL] THEN
    SUBGOAL_THEN ([[&0 < &r /\ &r <= &n]]) (fun th => MESON_TAC [th, LN_MONO_LE, SessionLibrary.Analysis.REAL_LTE_TRANS]) THEN
    REWRITE_TAC [REAL_OF_NUM_LT, REAL_OF_NUM_LE] THEN
    UNDISCH_TAC ([[1 <= r]]) THEN UNDISCH_TAC ([[r < n + 1]]) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval PII_LBOUND

/- ------------------------------------------------------------------------- -/
/- First prove the upper bound for the first 50 numbers, to start with.      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 89
def PII_UBOUND_CASES_50 : thm := keep "PII_UBOUND_CASES_50" fun _ => (do
  let tac := CONV_TAC (HolLight.ONCE_DEPTH_CONV LN_N2_CONV THENC REALCALC_REL_CONV)
  prove ([[!n. n < 50 ==> 3 <= n ==> ln(&n) * pii(n) <= &5 * &n]])
   (CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC ((PII_LISTv 49)) THEN
    SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ), REAL_OF_NUM_LT, ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT (CONJ_TAC THENL [tac THEN HolCore.Tactics.NO_TAC, ALL_TAC]) THEN tac)
  : ExceptT String IO thm).run
#eval PII_UBOUND_CASES_50

/- ------------------------------------------------------------------------- -/
/- An extra trivial pair of lemmas.                                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 90
def THETA_POS : thm := keep "THETA_POS" fun _ => (do
  prove ([[!n. &0 <= theta n]])
   (GEN_TAC THEN REWRITE_TAC [theta] THEN
    MATCH_MP_TAC SUM_POS_GEN THEN
    X_GEN_TAC ([[p:num]]) THEN DISCH_TAC THEN REWRITE_TAC [] THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC [LE_REFL, LN_POS, REAL_OF_NUM_LE])
  : ExceptT String IO thm).run
#eval THETA_POS

#eval phrase 91
def PII_MONO : thm := keep "PII_MONO" fun _ => (do
  prove ([[!m n. m <= n ==> pii(m) <= pii(n)]])
   (SIMP_TAC [LE_EXISTS, LEFT_IMP_EXISTS_THM, pii] THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_SPLIT)] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [REAL_LE_ADDR] THEN
    MATCH_MP_TAC SUM_POS_GEN THEN
    GEN_TAC THEN REWRITE_TAC [] THEN COND_CASES_TAC THEN
    CONV_TAC REAL_RAT_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval PII_MONO

#eval phrase 92
def PII_POS : thm := keep "PII_POS" fun _ => (do
  prove ([[!n. &0 <= pii(n)]])
   (SUBGOAL_THEN ([[pii(0) = &0]]) (fun th => MESON_TAC [th, PII_MONO, LE_0]) THEN
    REWRITE_TAC (LN_1 :: (PII_LISTv 0)))
  : ExceptT String IO thm).run
#eval PII_POS

/- ------------------------------------------------------------------------- -/
/- The induction principle we can use.                                       -/
/- ------------------------------------------------------------------------- -/

#eval phrase 93
def PII_CHANGE : thm := keep "PII_CHANGE" fun _ => (do
  let h3 ← rr (← ExceptT.mk [[a <= n - m ==> &0 <= m ==> a <= n]])
  let h2 ← ar (← ExceptT.mk [[1 <= n <=> ~(n = 0)]])
  let h1 ← rr (← ExceptT.mk [[&0 <= a * (c - b) ==> a * (b - c) <= &0]])
  prove ([[!m n. ~(m = 0) ==> ln(&m) * (pii n - pii m) <= &3 / &2 * &n]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC ([[m <= n:num]]) THENL
     [ALL_TAC,
      MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN EXISTS_TAC ([[&0]]) THEN CONJ_TAC THENL
       [ALL_TAC,
        MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_MUL THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_POS] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV] THEN
      MATCH_MP_TAC h1 THEN
      MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_MUL THEN
      ASM_SIMP_TAC [LN_POS, REAL_OF_NUM_LE, h2] THEN
      REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_LE] THEN MATCH_MP_TAC PII_MONO THEN
      UNDISCH_TAC ([[~(m <= n:num)]]) THEN ARITH_TAC] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[theta n]]) THEN REWRITE_TAC [THETA_UBOUND_3_2] THEN
    MP_TAC (← HolLight.SPEC ([[m:num]]) THETA_POS) THEN
    MATCH_MP_TAC h3 THEN
    FIRST_X_ASSUM (MP_TAC o HolLight.GEN_REWRITE_RULE HolCore.Lib.I [LE_EXISTS]) THEN
    DISCH_THEN (X_CHOOSE_THEN ([[d:num]]) SUBST1_TAC) THEN
    REWRITE_TAC [pii, theta, (← HolLight.GSYM SUM_SPLIT), REAL_ADD_SUB] THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_CMUL)] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.SUM_LE THEN X_GEN_TAC ([[r:num]]) THEN STRIP_TAC THEN
    REWRITE_TAC [] THEN COND_CASES_TAC THEN
    REWRITE_TAC [SessionLibrary.Analysis.REAL_MUL_RZERO, SessionLibrary.Analysis.REAL_LE_REFL, SessionLibrary.Analysis.REAL_MUL_RID] THEN
    SUBGOAL_THEN ([[&0 < &m /\ &m <= &r]]) (fun th => MESON_TAC [th, LN_MONO_LE, SessionLibrary.Analysis.REAL_LTE_TRANS]) THEN
    REWRITE_TAC [REAL_OF_NUM_LT, REAL_OF_NUM_LE] THEN
    UNDISCH_TAC ([[1 + m <= r]]) THEN UNDISCH_TAC ([[~(m = 0)]]) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval PII_CHANGE

#eval phrase 94
def PII_ISQRT_INDUCT : thm := keep "PII_ISQRT_INDUCT" fun _ => (do
  let h8 ← rr (← ExceptT.mk [[&7 <= x ==> &1 <= x]])
  let h7 ← nc (← ExceptT.mk [[2]])
  let h6 ← ar (← ExceptT.mk [[0 < n <=> ~(n = 0)]])
  let h5 ← ar (← ExceptT.mk [[0 < n <=> ~(n = 0)]])
  let h4 ← rr (← ExceptT.mk [[&0 < x ==> &0 < x + &1]])
  let h3 ← rr (← ExceptT.mk [[a - b <= b * (d - &1) ==> a <= b * d]])
  let h2 ← rr (← ExceptT.mk [[&0 <= x ==> &0 < x + &1]])
  let h1 ← rr (← ExceptT.mk [[a * p <= ls * p ==> ls * (p - ps) <= an ==> a * p <= an + ls * ps]])
  prove ([[!n. 50 <= n
       ==> ln(&n) * pii(n)
           <= &9 / &4 * (&3 / &2 * &n + ln(&(ISQRT(n))) * pii(ISQRT(n)))]])
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC HolLight.RAND_CONV [REAL_MUL_SYM] THEN
    SIMP_TAC [(← HolLight.GSYM REAL_LE_LDIV_EQ), REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [real_div] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC [REAL_MUL_ASSOC] THEN
    MP_TAC (← HolLight.SPECL [([[ISQRT n]]), ([[n:num]])] PII_CHANGE) THEN
    SUBGOAL_THEN ([[~(ISQRT n = 0)]]) ASSUME_TAC THENL
     [MP_TAC (← HolLight.SPEC ([[n:num]]) ISQRT_WORKS) THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN SIMP_TAC [ARITH] THEN
      DISCH_TAC THEN UNDISCH_TAC ([[50 <= n]]) THEN ARITH_TAC,
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC h1 THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [PII_POS] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ), REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN EXISTS_TAC ([[ln((&(ISQRT n) + &1) pow 2)]]) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN ([[&0 < &n /\ &n <= (&(ISQRT n) + &1) pow 2]]) (fun th => MESON_TAC [th, SessionLibrary.Analysis.REAL_LTE_TRANS, LN_MONO_LE]) THEN
      REWRITE_TAC [REAL_OF_NUM_ADD, REAL_OF_NUM_POW, REAL_OF_NUM_LE,
                  REAL_OF_NUM_LT] THEN
      SIMP_TAC [ISQRT_WORKS, LT_IMP_LE] THEN
      UNDISCH_TAC ([[50 <= n]]) THEN ARITH_TAC,
      ALL_TAC] THEN
    SIMP_TAC [LN_POW, SessionLibrary.Analysis.REAL_POS, h2] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [REAL_MUL_SYM] THEN
    SIMP_TAC [(← HolLight.GSYM REAL_LE_RDIV_EQ), REAL_OF_NUM_LT, ARITH] THEN
    REWRITE_TAC [real_div, (← HolLight.GSYM REAL_MUL_ASSOC)] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC h3 THEN
    ASM_SIMP_TAC [(← HolLight.GSYM LN_DIV), h4,
                 REAL_OF_NUM_LT, h5] THEN
    REWRITE_TAC [real_div, REAL_ADD_RDISTRIB] THEN
    ASM_SIMP_TAC [SessionLibrary.Analysis.REAL_MUL_RINV, REAL_OF_NUM_EQ, ARITH, REAL_MUL_LID] THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN EXISTS_TAC ([[inv(&(ISQRT n))]]) THEN
    ASM_SIMP_TAC [LN_LE, SessionLibrary.Analysis.REAL_POS, REAL_LE_INV_EQ] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC [real_div, REAL_MUL_LID] THEN REWRITE_TAC [(← HolLight.GSYM real_div)] THEN
    SIMP_TAC [REAL_LE_RDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
    ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM real_div), REAL_LE_LDIV_EQ, REAL_OF_NUM_LT,
                 h6] THEN
    SUBGOAL_THEN ([[&7 <= &(ISQRT n)]]) MP_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_LE] THEN
      SUBGOAL_THEN ([[7 EXP 2 < (ISQRT n + 1) EXP 2]]) MP_TAC THENL
       [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC ([[n:num]]) THEN
        REWRITE_TAC [ISQRT_WORKS] THEN CONV_TAC NUM_REDUCE_CONV THEN
        UNDISCH_TAC ([[50 <= n]]) THEN ARITH_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [h7, EXP_MONO_LT, NOT_SUC] THEN ARITH_TAC,
      ALL_TAC] THEN
    SPEC_TAC (([[&(ISQRT n)]]), ([[x:real]])) THEN
    MATCH_MP_TAC OVERPOWER_LEMMA THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        let th ← ExceptT.mk (DIFF_CONV (← ec (HolCore.Equal.lhand (← ec (HolCore.Kernel.rator (← ec (HolCore.Kernel.rand (← ec (HolCore.Basics.body (← ec (HolCore.Kernel.rand (← ec (HolCore.Equal.lhand (← ec (HolCore.Kernel.rand (← ec (HolCore.Basics.body (← ec (HolCore.Kernel.rand w)))))))))))))))))))
        pure (MP_TAC th)) THEN
    GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.TOP_DEPTH_CONV) [SessionLibrary.Analysis.REAL_MUL_LZERO, REAL_ADD_LID, REAL_ADD_RID,
      SessionLibrary.Analysis.REAL_MUL_RID, REAL_MUL_LID] THEN
    SIMP_TAC [REAL_MUL_LINV, SessionLibrary.Analysis.REAL_LT_IMP_NZ] THEN
    HolCore.Lib.W (fun (_, w) => HolLight.tactic_of do
        let tm ← ec (mk_abs ([[x:real]]) (← ec (HolCore.Kernel.rand (← ec (HolCore.Kernel.rator (← ec (HolCore.Kernel.rand (← ec (HolCore.Basics.body (← ec (HolCore.Kernel.rand (← ec (HolCore.Equal.lhand w)))))))))))))
        pure (DISCH_TAC THEN EXISTS_TAC tm)) THEN
    CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC [real_sub] THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV LN_N2_CONV) THEN
      CONV_TAC REALCALC_REL_CONV,
      ALL_TAC] THEN
    REWRITE_TAC [] THEN CONJ_TAC THENL
     [GEN_TAC THEN
      DISCH_THEN (fun th => FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
      REAL_ARITH_TAC2,
      ALL_TAC] THEN
    X_GEN_TAC ([[x:real]]) THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_RZERO] THEN
    SIMP_TAC [LN_POS, REAL_LE_ADD, SessionLibrary.Analysis.REAL_POS, h8])
  : ExceptT String IO thm).run
#eval PII_ISQRT_INDUCT

/- ------------------------------------------------------------------------- -/
/- Hence a bound by wellfounded induction.                                   -/
/- ------------------------------------------------------------------------- -/

#eval phrase 95
def PII_UBOUND_5 : thm := keep "PII_UBOUND_5" fun _ => (do
  let h8 ← rr (← ExceptT.mk [[i * (a * c) <= n * (d - a * b) ==> a * (b * n + c * i) <= d * n]])
  let h7 ← rr (← ExceptT.mk [[a <= b ==> x <= a ==> x <= b]])
  let h6 ← nc (← ExceptT.mk [[2]])
  let h5 ← ar (← ExceptT.mk [[1 * n < m ==> n < m]])
  let h4 ← ar (← ExceptT.mk [[50 <= n ==> 3 <= n]])
  let h3 ← ar (← ExceptT.mk [[7 <= n ==> 3 <= n]])
  let h2 ← nc (← ExceptT.mk [[2]])
  let h1 ← ar (← ExceptT.mk [[3 <= n ==> 1 < n]])
  prove ([[!n. 3 <= n ==> pii(n) <= &5 * (&n / ln(&n))]])
   (REWRITE_TAC [real_div, REAL_MUL_ASSOC] THEN
    SIMP_TAC [(← HolLight.GSYM real_div), REAL_LE_RDIV_EQ, LN_POS_LT, REAL_OF_NUM_LT,
             h1] THEN
    GEN_REWRITE_TAC (HolLight.BINDER_CONV o HolLight.RAND_CONV o HolLight.LAND_CONV) [REAL_MUL_SYM] THEN
    MATCH_MP_TAC num_WF THEN X_GEN_TAC ([[n:num]]) THEN
    ASM_CASES_TAC ([[n < 50]]) THEN ASM_SIMP_TAC [PII_UBOUND_CASES_50] THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[ISQRT n]])) THEN
    RULE_ASSUM_TAC (HolLight.REWRITE_RULE [NOT_LT]) THEN
    SUBGOAL_THEN ([[7 <= ISQRT n]]) ASSUME_TAC THENL
     [REWRITE_TAC [REAL_OF_NUM_LE] THEN
      SUBGOAL_THEN ([[7 EXP 2 < (ISQRT n + 1) EXP 2]]) MP_TAC THENL
       [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC ([[n:num]]) THEN
        REWRITE_TAC [ISQRT_WORKS] THEN CONV_TAC NUM_REDUCE_CONV THEN
        UNDISCH_TAC ([[50 <= n]]) THEN ARITH_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [h2, EXP_MONO_LT, NOT_SUC] THEN ARITH_TAC,
      ALL_TAC] THEN
    ASM_SIMP_TAC [h3,
                 h4] THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN ([[(ISQRT n) EXP 2 < n EXP 2]]) MP_TAC THENL
       [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC ([[n:num]]) THEN
        REWRITE_TAC [ISQRT_WORKS] THEN REWRITE_TAC [EXP_2] THEN
        MATCH_MP_TAC h5 THEN
        REWRITE_TAC [LT_MULT_RCANCEL] THEN
        UNDISCH_TAC ([[50 <= n]]) THEN ARITH_TAC,
        ALL_TAC] THEN
      REWRITE_TAC [h6, EXP_MONO_LT, NOT_SUC],
      ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP PII_ISQRT_INDUCT) THEN
    MATCH_MP_TAC h7 THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN
    EXISTS_TAC ([[&9 / &4 * (&3 / &2 * &n + &5 * &(ISQRT n))]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REWRITE_TAC [SessionLibrary.Analysis.REAL_LE_LADD],
      ALL_TAC] THEN
    MATCH_MP_TAC h8 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC [(← HolLight.GSYM REAL_LE_LDIV_EQ), REAL_LT_DIV, REAL_OF_NUM_LT, ARITH] THEN
    REWRITE_TAC [real_div, (← HolLight.GSYM REAL_MUL_ASSOC)] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC SessionLibrary.Analysis.REAL_LE_TRANS THEN EXISTS_TAC ([[&(ISQRT n) * &7]]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [SessionLibrary.Analysis.REAL_POS] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV,
      ALL_TAC] THEN
    REWRITE_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC ([[ISQRT n * ISQRT n]]) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC [LE_MULT_LCANCEL],
      REWRITE_TAC [(← HolLight.GSYM EXP_2), ISQRT_WORKS]])
  : ExceptT String IO thm).run
#eval PII_UBOUND_5

-- @@ENSURE BEGIN
/-- Replays this file, once per process (see Common.lean); generated by
    tools/tutorialdiff/ensuregen.py; keep it in step with the `#eval`s above. -/
def ensure : IO Unit := once "Hol100.Bertrand" do
  replay (
          SessionLibrary.Prime.ensurePrime)
  replay (
          SessionLibrary.Pocklington.ensurePocklington)
  replay (
          SessionLibrary.Analysis.ensureAnalysis)
  replay (
          SessionLibrary.Transc.ensureTransc)
  replay (
          SessionLibrary.CalcReal.ensureCalcReal)
  replay (
          SessionLibrary.Floor.ensureFloor)
  replay (
          Session.prioritize_real)
  replay (
          ISQRT)
  replay (
          ISQRT_WORKS)
  replay (
          ISQRT_0)
  replay (
          ISQRT_UNIQUE)
  replay (
          ISQRT_SUC)
  replay (
          LN_2_COMPOSITION)
  replay (
          (do replay LN_N_CONV_pth; replay LN_N_CONV_qth; IO.println "<fun>" : IO Unit))
  replay (
          (do replay LN_N2_CONV_pth; replay LN_N2_CONV_qth; IO.println "<fun>" : IO Unit))
  replay (
          FLOOR_DOUBLE_NUM)
  replay (
          LN_FACT)
  replay (
          LN_FACT_BOUNDS)
  replay (
          primepow)
  replay (
          aprimedivisor)
  replay (
          PRIMEPOW_GE_2)
  replay (
          PRIMEPOW_0)
  replay (
          APRIMEDIVISOR_PRIMEPOW)
  replay (
          APRIMEDIVISOR)
  replay (
          BIG_POWER_LEMMA)
  replay (
          PRIME_PRIMEPOW)
  replay (
          (do replay PRIMEPOW_CONV_pths; IO.println "<fun>" : IO Unit))
  replay (
          (do replay APRIMEDIVISOR_CONV_pth; IO.println "<fun>" : IO Unit))
  replay (
          mangoldt)
  replay (
          MANGOLDT_POS)
  replay (
          LN_PRIMEFACT)
  replay (
          MANGOLDT)
  replay (
          psi)
  replay (
          PSI_BOUNDS_LN_FACT)
  replay (
          LN_FACT_DIFF_BOUNDS)
  replay (
          PSI_BOUNDS_INDUCT)
  replay (
          (do replay MANGOLDT_CONV_pths; IO.println "<fun>" : IO Unit))
  replay (
          (do replay PSI_LIST_0; replay PSI_LIST_SUC; IO.println "<fun>" : IO Unit))
  replay (
          printThms PSI_LIST_300)
  replay (
          PSI_UBOUND_128)
  replay (
          PSI_UBOUND_128_LOG)
  replay (
          OVERPOWER_LEMMA)
  replay (
          PSI_UBOUND_1024_LOG)
  replay (
          PSI_BOUNDS_SUSTAINED_INDUCT)
  replay (
          PSI_BOUNDS_SUSTAINED)
  replay (
          PSI_UBOUND_LOG)
  replay (
          PSI_UBOUND_3_2)
  replay (
          PSI_LBOUND_3_5)
  replay (
          theta)
  replay (
          (do replay THETA_LIST_0; replay THETA_LIST_SUC; IO.println "<fun>" : IO Unit))
  replay (
          PRIMEPOW_ODD_EVEN)
  replay (
          PSI_SPLIT)
  replay (
          SUM_SURJECT)
  replay (
          PSI_RESIDUES_COMPARE_2)
  replay (
          PSI_RESIDUES_COMPARE)
  replay (
          PSI_SQRT)
  replay (
          PSI_THETA)
  replay (
          THETA_LE_PSI)
  replay (
          PSI_UBOUND_30)
  replay (
          THETA_UBOUND_3_2)
  replay (
          THETA_LBOUND_1_2)
  replay (
          FLOOR_POS)
  replay (
          FLOOR_NUM_EXISTS)
  replay (
          FLOOR_DIV_INTERVAL)
  replay (
          FLOOR_DIV_EXISTS)
  replay (
          FLOOR_HALF_INTERVAL)
  replay (
          SUM_EXPAND_LEMMA)
  replay (
          FACT_EXPAND_PSI)
  replay (
          PSI_MONO)
  replay (
          PSI_POS)
  replay (
          PSI_EXPANSION_CUTOFF)
  replay (
          FACT_PSI_BOUND_ODD)
  replay (
          FACT_PSI_BOUND_EVEN)
  replay (
          FACT_PSI_BOUND_2_3)
  replay (
          PSI_DOUBLE_LEMMA)
  replay (
          THETA_DOUBLE_LEMMA)
  replay (
          BIG_BERTRAND)
  replay (
          LANDAU_TRICK)
  replay (
          BERTRAND)
  replay (
          pii)
  replay (
          (do replay PII_LIST_0; replay PII_LIST_SUC; IO.println "<fun>" : IO Unit))
  replay (
          PRIMES_FINITE)
  replay (
          PII)
  replay (
          PII_LBOUND)
  replay (
          PII_UBOUND_CASES_50)
  replay (
          THETA_POS)
  replay (
          PII_MONO)
  replay (
          PII_POS)
  replay (
          PII_CHANGE)
  replay (
          PII_ISQRT_INDUCT)
  replay (
          PII_UBOUND_5)
-- @@ENSURE END

end Hol100.Bertrand
