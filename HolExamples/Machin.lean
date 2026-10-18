/- File: HolExamples/Machin.lean
Translation of HOL Light's Examples/machin.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
open scoped HolLight
open SessionLibrary.Transc SessionLibrary.Analysis
namespace HolExamples.Machin

/- Helpers: the session's rules lifted into `ExceptT String IO`, so the tactic
   scripts and term-building functions read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ec {α : Type} (x : Except String α) : ExceptT String IO α := ExceptT.mk (pure x)

/- ========================================================================= -/
/- Derivation of Machin's formula and other similar ones.                    -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/transc.ml";;
#eval SessionLibrary.Transc.ensureTransc

#eval phrase 2
unsafe def REAL_LE_1_POW2 : thm := keep "REAL_LE_1_POW2" fun _ => (do
  prove ([[!n. &1 <= &2 pow n]])
   (REWRITE_TAC [REAL_OF_NUM_POW, REAL_OF_NUM_LE, (← ExceptT.mk (ARITH_RULE [[1 <= n <=> 0 < n]])),
              EXP_LT_0, ARITH])
  : ExceptT String IO thm).run
#eval REAL_LE_1_POW2

#eval phrase 3
unsafe def REAL_LT_1_POW2 : thm := keep "REAL_LT_1_POW2" fun _ => (do
  prove ([[!n. &1 < &2 pow n <=> ~(n = 0)]])
   (GEN_TAC THEN ASM_CASES_TAC [[n = 0]] THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SUBST1_TAC (← ExceptT.mk (HolLight.SYM (← ExceptT.mk (REAL_RAT_REDUCE_CONV [[&2 pow 0]])))) THEN
    MATCH_MP_TAC REAL_POW_MONO_LT THEN
    REWRITE_TAC [REAL_OF_NUM_LT] THEN POP_ASSUM MP_TAC THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval REAL_LT_1_POW2

#eval phrase 4
unsafe def REAL_POW2_CLAUSES : thm := keep "REAL_POW2_CLAUSES" fun _ => (do
  prove ([[(!n. &0 <= &2 pow n) /\
   (!n. &0 < &2 pow n) /\
   (!n. &0 <= inv(&2 pow n)) /\
   (!n. &0 < inv(&2 pow n)) /\
   (!n. inv(&2 pow n) <= &1) /\
   (!n. &1 - inv(&2 pow n) <= &1) /\
   (!n. &1 <= &2 pow n) /\
   (!n. &1 < &2 pow n <=> ~(n = 0)) /\
   (!n. &0 <= &1 - inv(&2 pow n)) /\
   (!n. &0 <= &2 pow n - &1) /\
   (!n. &0 < &1 - inv(&2 pow n) <=> ~(n = 0))]])
   (SIMP_TAC [REAL_LE_1_POW2, REAL_LT_1_POW2, Session.REAL_SUB_LE, Session.REAL_SUB_LT,
           REAL_INV_LE_1] THEN
    SIMP_TAC [REAL_LE_INV_EQ, REAL_LT_INV_EQ, REAL_POW_LT, REAL_POW_LE,
           REAL_OF_NUM_LE, REAL_OF_NUM_LT, ARITH,
           (← ExceptT.mk (Session.REAL_ARITH2 [[&1 - x <= &1 <=> &0 <= x]]))] THEN
    GEN_TAC THEN ASM_CASES_TAC [[n = 0]] THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC [[inv(&2 pow 1)]] THEN
    ASM_SIMP_TAC [REAL_LE_INV2, REAL_POW_MONO, REAL_POW_LT, REAL_OF_NUM_LT, ARITH,
               REAL_OF_NUM_LE, (← ExceptT.mk (ARITH_RULE [[1 <= n <=> ~(n = 0)]]))] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval REAL_POW2_CLAUSES

#eval phrase 5
unsafe def REAL_POW2_THM : thm := keep "REAL_POW2_THM" fun _ => (do
  prove ([[&0 < &2 pow n /\
   &1 <= &2 pow n /\
   (&1 < &2 pow n <=> ~(n = 0)) /\
   (&2 pow m <= &2 pow n <=> m <= n) /\
   (&2 pow m < &2 pow n <=> m < n) /\
   (inv(&2 pow m) <= inv(&2 pow n) <=> n <= m) /\
   (inv(&2 pow m) < inv(&2 pow n) <=> n < m)]])
   (REWRITE_TAC [REAL_POW2_CLAUSES] THEN
    SUBGOAL_THEN ([[!m n. &2 pow m <= &2 pow n <=> m <= n]]) ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN EQ_TAC THEN
      SIMP_TAC [REAL_POW_MONO, REAL_OF_NUM_LE, ARITH] THEN
      CONV_TAC HolLight.CONTRAPOS_CONV THEN
      SIMP_TAC [Session.REAL_NOT_LE, Session.REAL_NOT_LT, REAL_POW_MONO_LT, REAL_OF_NUM_LT,
               NOT_LE, ARITH], ALL_TAC] THEN
    ASM_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM Session.REAL_NOT_LE))] THEN REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM NOT_LE))] THEN
    SUBGOAL_THEN ([[!m n. inv(&2 pow m) <= inv(&2 pow n) <=> &2 pow n <= &2 pow m]])
     (fun th => ASM_REWRITE_TAC [th]) THEN
    REPEAT GEN_TAC THEN EQ_TAC THEN
    SIMP_TAC [REAL_LE_INV2, REAL_POW2_CLAUSES] THEN
    CONV_TAC HolLight.CONTRAPOS_CONV THEN
    SIMP_TAC [Session.REAL_NOT_LE, REAL_LT_INV2, REAL_POW2_CLAUSES])
  : ExceptT String IO thm).run
#eval REAL_POW2_THM

/- ------------------------------------------------------------------------- -/
/- Compound errors given bounds in assumptions.                              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 6
-- let BOUND_SUMPROD_RULE = ... (recursive conversion-style rule over goals)
unsafe def pth_add6 : thm := keep "pth_add6" fun _ => (do
  ExceptT.mk (Session.REAL_ARITH2 [[abs(x1) <= b1 /\ abs(x2) <= b2 ==> abs(x1 + x2) <= b1 + b2]])
  : ExceptT String IO thm).run
unsafe def pth_sub6 : thm := keep "pth_sub6" fun _ => (do
  ExceptT.mk (Session.REAL_ARITH2 [[abs(x1) <= b1 /\ abs(x2) <= b2 ==> abs(x1 - x2) <= b1 + b2]])
  : ExceptT String IO thm).run
unsafe def pth_mul6 : thm := keep "pth_mul6" fun _ => (do
  prove ([[abs(x1) <= b1 /\ abs(x2) <= b2 ==> abs(x1 * x2) <= b1 * b2]])
   (REWRITE_TAC [REAL_ABS_MUL] THEN
    SIMP_TAC [REAL_LE_MUL2, REAL_ABS_POS])
  : ExceptT String IO thm).run
unsafe def pth_neg6 : thm := keep "pth_neg6" fun _ => (do
  ExceptT.mk (Session.REAL_ARITH2 [[abs(x1) <= b1 ==> abs(--x1) <= b1]])
  : ExceptT String IO thm).run
unsafe def pth_pow6 : thm := keep "pth_pow6" fun _ => (do
  prove ([[abs(x) <= b1 ==> abs(x pow n) <= b1 pow n]])
   (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [REAL_ABS_POW] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC [REAL_ABS_POS])
  : ExceptT String IO thm).run
unsafe def pth_abs6 : thm := keep "pth_abs6" fun _ => (do
  ExceptT.mk (Session.REAL_ARITH2 [[abs(x) <= b ==> abs(abs(x)) <= b]])
  : ExceptT String IO thm).run
unsafe def pth_triv6 : thm := keep "pth_triv6" fun _ => (do
  ExceptT.mk (Session.REAL_ARITH2 [[abs(x) <= abs(x)]])
  : ExceptT String IO thm).run
unsafe def n_tm6 : term := [[n:num]]

/-- First `pth` in `pths` whose `rator o rand` matches `tm` (machin.ml tryfind). -/
unsafe def bsrMatchP : List thm → term → ExceptT String IO (thm × thm)
  | [], _ => ec (.error "no match")
  | pth :: t, tm => HolLight.tryWith (do
      let m ← ExceptT.mk (Session.PART_MATCH (fun s => do rator (← rand s)) pth tm)
      pure (pth, m)) (bsrMatchP t tm)

/-- `BOUND_SUMPROD_RULE (asl,w)`: establish `abs(x) <= b` for the head `w`,
    recursing on the arithmetic structure (machin.ml). -/
unsafe def BOUND_SUMPROD_RULE : (List (String × thm) × term) → ExceptT String IO thm := fun (asl, w) =>
  let rec go (asl : List (String × thm)) (w : term) : ExceptT String IO thm := do
    let tm ← ec (rator w)
    let rec pick : List (String × thm) → ExceptT String IO thm
      | [] => ec (.error "fail")
      | (_, th) :: t => do
          let r ← ec (rator (concl th))
          if r == tm then pure th else pick t
    let branch_assum : ExceptT String IO thm := pick asl
    let branch_neg : ExceptT String IO thm := do
      let (pth, th) ← bsrMatchP [pth_neg6, pth_abs6] tm
      let th1 ← go asl (← ec (HolCore.Equal.lhand (concl th)))
      HolLight.MATCH_MP pth th1
    let branch_pow : ExceptT String IO thm := do
      let n ← ec (do rand (← rand (← rand tm)))
      let pth ← HolLight.INST [(n, n_tm6)] pth_pow6
      let th ← ExceptT.mk (Session.PART_MATCH (fun t => do rator (← rand t)) pth tm)
      let th1 ← go asl (← ec (HolCore.Equal.lhand (concl th)))
      HolLight.MATCH_MP (← HolLight.INST [(n, n_tm6)] pth_pow6) th1
    let branch_bin : ExceptT String IO thm := do
      let (pth, th) ← bsrMatchP [pth_add6, pth_sub6, pth_mul6] tm
      let trm ← ec (HolCore.Equal.lhand (concl th))
      let th1 ← go asl (← ec (HolCore.Equal.lhand trm))
      let th2 ← go asl (← ec (rand trm))
      HolLight.MATCH_MP pth (← HolLight.CONJ th1 th2)
    let branch_triv : ExceptT String IO thm :=
      ExceptT.mk (Session.PART_MATCH (fun t => Except.ok t) pth_triv6 tm)
    HolLight.tryWith branch_assum
      (HolLight.tryWith branch_neg
        (HolLight.tryWith branch_pow
          (HolLight.tryWith branch_bin branch_triv)))
  go asl w
#eval IO.println "<fun>"

#eval phrase 7
-- let BOUND_SUMPROD_TAC = ...
unsafe def pth7 : thm := keep "pth7" fun _ => (do
  ExceptT.mk (Session.REAL_ARITH2 [[x <= a ==> (!b. a <= b ==> x <= b) /\
                             (!b. a < b ==> x < b)]])
  : ExceptT String IO thm).run
unsafe def le_tm7 : term := [[(<=):real->real->bool]]
unsafe def BOUND_SUMPROD_TAC : HolCore.Tactics.tactic :=
  HolCore.Lib.W (fun g => HolLight.tactic_of do
    let (l, r) ← ec (dest_comb (HolLight.snd g))
    let gv ← HolCore.Basics.genvar (type_of r)
    let lr ← ec (rand l)
    let lc ← ec (mk_comb le_tm7 lr)
    let tm ← ec (mk_comb lc gv)
    let th ← BOUND_SUMPROD_RULE (g.1, tm)
    let (th1, th2) ← HolLight.CONJ_PAIR (← HolLight.MATCH_MP pth7 th)
    pure (MATCH_MP_TAC th1 ORELSE MATCH_MP_TAC th2))
#eval IO.println "<fun>"

/- ------------------------------------------------------------------------- -/
/- Power series for atn.                                                     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 8
unsafe def REAL_ATN_POWSER_SUMMABLE : thm := keep "REAL_ATN_POWSER_SUMMABLE" fun _ => (do
  prove ([[!x. abs(x) < &1
       ==> summable (\n. (if EVEN n then &0
                          else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n)]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC SER_COMPAR THEN
    EXISTS_TAC [[\n. abs(x) pow n]] THEN CONJ_TAC THENL
     [EXISTS_TAC [[0]] THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN
      COND_CASES_TAC THEN
      SIMP_TAC [REAL_POW_LE, Session.REAL_MUL_LZERO, REAL_ABS_POS, REAL_ABS_NUM] THEN
      REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_DIV, REAL_ABS_NEG, REAL_ABS_POW] THEN
      REWRITE_TAC [REAL_ABS_NUM, REAL_POW_ONE, REAL_MUL_LID] THEN
      REWRITE_TAC [real_div, REAL_MUL_LID] THEN
      ONCE_REWRITE_TAC [REAL_MUL_SYM] THEN REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM real_div))] THEN
      MATCH_MP_TAC REAL_LE_LDIV THEN
      CONJ_TAC THENL [ASM_MESON_TAC [REAL_OF_NUM_LT, EVEN, LT_NZ], ALL_TAC] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← ExceptT.mk (HolLight.GSYM Session.REAL_MUL_RID))] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      SIMP_TAC [REAL_POW_LE, REAL_ABS_POS] THEN
      ASM_MESON_TAC [REAL_OF_NUM_LE, EVEN, (← ExceptT.mk (ARITH_RULE [[1 <= n <=> ~(n = 0)]]))],
      ALL_TAC] THEN
    REWRITE_TAC [summable] THEN EXISTS_TAC [[inv(&1 - abs x)]] THEN
    MATCH_MP_TAC GP THEN ASM_REWRITE_TAC [REAL_ABS_ABS])
  : ExceptT String IO thm).run
#eval REAL_ATN_POWSER_SUMMABLE

#eval phrase 9
unsafe def REAL_ATN_POWSER_DIFFS_SUMMABLE : thm := keep "REAL_ATN_POWSER_DIFFS_SUMMABLE" fun _ => (do
  prove ([[!x. abs(x) < &1
       ==> summable (\n. diffs (\n. (if EVEN n then &0
                                     else --(&1) pow ((n - 1) DIV 2) / &n)) n *
                         x pow n)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [diffs] THEN
    MATCH_MP_TAC SER_COMPAR THEN
    EXISTS_TAC [[\n. abs(x) pow n]] THEN CONJ_TAC THENL
     [EXISTS_TAC [[0]] THEN REPEAT STRIP_TAC THEN REWRITE_TAC [] THEN
      COND_CASES_TAC THEN
      SIMP_TAC [REAL_POW_LE, Session.REAL_MUL_LZERO, Session.REAL_MUL_RZERO,
               REAL_ABS_POS, REAL_ABS_NUM] THEN
      SIMP_TAC [REAL_MUL_ASSOC, REAL_DIV_LMUL, REAL_OF_NUM_EQ, NOT_SUC] THEN
      REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_DIV, REAL_ABS_NEG, REAL_ABS_POW] THEN
      REWRITE_TAC [REAL_ABS_NUM, REAL_POW_ONE, REAL_MUL_LID, Session.REAL_LE_REFL],
      ALL_TAC] THEN
    REWRITE_TAC [summable] THEN EXISTS_TAC [[inv(&1 - abs x)]] THEN
    MATCH_MP_TAC GP THEN ASM_REWRITE_TAC [REAL_ABS_ABS])
  : ExceptT String IO thm).run
#eval REAL_ATN_POWSER_DIFFS_SUMMABLE

#eval phrase 10
unsafe def REAL_ATN_POWSER_DIFFS_SUM : thm := keep "REAL_ATN_POWSER_DIFFS_SUM" fun _ => (do
  prove ([[!x. abs(x) < &1
       ==> (\n. diffs (\n. (if EVEN n then &0
                            else --(&1) pow ((n - 1) DIV 2) / &n)) n * x pow n)
           sums (inv(&1 + x pow 2))]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP REAL_ATN_POWSER_DIFFS_SUMMABLE) THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
      pure (MP_TAC (← HolLight.MATCH_MP SUMMABLE_SUM th) THEN
            MP_TAC (← HolLight.MATCH_MP SER_PAIR th))) THEN
    SUBGOAL_THEN
     ([[(\n. sum (2 * n,2) (\n. diffs
      (\n. (if EVEN n then &0
            else --(&1) pow ((n - 1) DIV 2) / &n)) n * x pow n)) =
    (\n. --(x pow 2) pow n)]])
    SUBST1_TAC THENL
     [ABS_TAC THEN
      CONV_TAC (HolLight.LAND_CONV (HolLight.LAND_CONV (HolLight.RAND_CONV (HolLight.TOP_DEPTH_CONV num_CONV)))) THEN
      REWRITE_TAC [SessionLibrary.Analysis.sum, diffs, ADD_CLAUSES, EVEN_MULT, ARITH_EVEN, EVEN] THEN
      REWRITE_TAC [REAL_ADD_LID, REAL_ADD_RID, Session.REAL_MUL_LZERO,
                  Session.REAL_MUL_RZERO] THEN
      SIMP_TAC [(← ExceptT.mk (ARITH_RULE [[SUC n - 1 = n]])), DIV_MULT, ARITH_EQ] THEN
      SIMP_TAC [REAL_MUL_ASSOC, REAL_DIV_LMUL, REAL_OF_NUM_EQ, NOT_SUC] THEN
      ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_POW))] THEN
      REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_MUL))] THEN
      REWRITE_TAC [REAL_MUL_LNEG, REAL_MUL_LID], ALL_TAC] THEN
    SUBGOAL_THEN ([[(\n. --(x pow 2) pow n) sums inv (&1 + x pow 2)]]) MP_TAC THENL
     [ONCE_REWRITE_TAC [(← ExceptT.mk (Session.REAL_ARITH2 [[&1 + x = &1 - (--x)]]))] THEN
      MATCH_MP_TAC GP THEN
      REWRITE_TAC [REAL_ABS_NEG, REAL_ABS_POW] THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [(← ExceptT.mk (HolLight.GSYM REAL_MUL_LID))] THEN
      ASM_SIMP_TAC [REAL_POW_2, REAL_LT_MUL2, REAL_ABS_POS], ALL_TAC] THEN
    MESON_TAC [SUM_UNIQ])
  : ExceptT String IO thm).run
#eval REAL_ATN_POWSER_DIFFS_SUM

#eval phrase 11
unsafe def REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE : thm := keep "REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE" fun _ => (do
  prove ([[!x. abs(x) < &1
       ==> summable
             (\n. diffs (diffs
                 (\n. (if EVEN n then &0
                       else --(&1) pow ((n - 1) DIV 2) / &n))) n * x pow n)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [diffs] THEN
    MATCH_MP_TAC SER_COMPAR THEN
    EXISTS_TAC [[\n. &(SUC n) * abs(x) pow n]] THEN CONJ_TAC THENL
     [EXISTS_TAC [[0]] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC [REAL_ABS_NUM, REAL_ABS_MUL, (← ExceptT.mk (HolLight.GSYM REAL_MUL_ASSOC))] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC [Session.REAL_POS] THEN
      COND_CASES_TAC THEN
      SIMP_TAC [REAL_POW_LE, Session.REAL_MUL_LZERO, Session.REAL_MUL_RZERO,
               REAL_ABS_POS, REAL_ABS_NUM] THEN
      REWRITE_TAC [REAL_ABS_DIV, REAL_ABS_NUM, REAL_MUL_ASSOC] THEN
      SIMP_TAC [REAL_DIV_LMUL, REAL_OF_NUM_EQ, NOT_SUC] THEN
      REWRITE_TAC [REAL_ABS_POW, REAL_ABS_NEG, REAL_POW_ONE, REAL_MUL_LID,
                  REAL_ABS_NUM, Session.REAL_LE_REFL], ALL_TAC] THEN
    MATCH_MP_TAC SER_RATIO THEN
    SUBGOAL_THEN ([[?c. abs(x) < c /\ c < &1]]) STRIP_ASSUME_TAC THENL
     [EXISTS_TAC [[(&1 + abs(x)) / &2]] THEN
      SIMP_TAC [REAL_LT_LDIV_EQ, REAL_LT_RDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
      UNDISCH_TAC [[abs(x) < &1]] THEN REAL_ARITH_TAC, ALL_TAC] THEN
    EXISTS_TAC [[c:real]] THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN ([[?N. !n. n >= N ==> &(SUC(SUC n)) * abs(x) <= &(SUC n) * c]])
    STRIP_ASSUME_TAC THENL
     [ALL_TAC,
      EXISTS_TAC [[N:num]] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC [real_pow, REAL_ABS_MUL, REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC [REAL_ABS_POS] THEN
      REWRITE_TAC [REAL_ABS_NUM, REAL_ABS_ABS] THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [REAL_MUL_SYM] THEN ASM_SIMP_TAC []] THEN
    ASM_CASES_TAC [[x = &0]] THENL
     [ASM_REWRITE_TAC [REAL_ABS_NUM, Session.REAL_MUL_RZERO] THEN
      EXISTS_TAC [[0]] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC Session.REAL_LE_MUL THEN
      REWRITE_TAC [Session.REAL_POS] THEN UNDISCH_TAC [[abs(x) < c]] THEN REAL_ARITH_TAC,
      ALL_TAC] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_LE_RDIV_EQ)), (← ExceptT.mk (HolLight.GSYM REAL_ABS_NZ))] THEN
    REWRITE_TAC [real_div, (← ExceptT.mk (HolLight.GSYM REAL_MUL_ASSOC))] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM real_div))] THEN
    REWRITE_TAC [ADD1, (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_ADD))] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (Session.REAL_ARITH2 [[x + &1 <= y <=> &1 <= y - x * &1]]))] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM Session.REAL_SUB_LDISTRIB))] THEN
    SUBGOAL_THEN ([[?N. &1 <= &N * (c / abs x - &1)]]) STRIP_ASSUME_TAC THENL
     [ALL_TAC,
      EXISTS_TAC [[N:num]] THEN REWRITE_TAC [GE] THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← ExceptT.mk (Session.REAL_ARITH2
       [[&1 <= x ==> x <= y ==> &1 <= y]]))) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_SIMP_TAC [(← ExceptT.mk (Session.REAL_ARITH2 [[a <= b ==> a <= b + &1]])),
                   REAL_OF_NUM_LE, Session.REAL_LE_RADD] THEN
      REWRITE_TAC [Session.REAL_LE_SUB_LADD, REAL_ADD_LID] THEN
      ASM_SIMP_TAC [REAL_LE_RDIV_EQ, (← ExceptT.mk (HolLight.GSYM REAL_ABS_NZ)), REAL_MUL_LID,
                   Session.REAL_LT_IMP_LE]] THEN
    ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM REAL_LE_LDIV_EQ)), Session.REAL_LT_SUB_LADD, REAL_ADD_LID,
                 REAL_LT_RDIV_EQ, (← ExceptT.mk (HolLight.GSYM REAL_ABS_NZ)), REAL_MUL_LID,
                 Session.REAL_ARCH_SIMPLE])
  : ExceptT String IO thm).run
#eval REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE

#eval phrase 12
unsafe def REAL_ATN_POWSER_DIFFL : thm := keep "REAL_ATN_POWSER_DIFFL" fun _ => (do
  prove ([[!x. abs(x) < &1
       ==> ((\x. suminf (\n. (if EVEN n then &0
                              else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n))
            diffl (inv(&1 + x pow 2))) x]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP REAL_ATN_POWSER_DIFFS_SUM) THEN
    DISCH_THEN (SUBST1_TAC o HolLight.MATCH_MP SUM_UNIQ) THEN
    MATCH_MP_TAC TERMDIFF THEN
    SUBGOAL_THEN ([[?K. abs(x) < abs(K) /\ abs(K) < &1]]) STRIP_ASSUME_TAC THENL
     [EXISTS_TAC [[(&1 + abs(x)) / &2]] THEN
      SIMP_TAC [REAL_LT_LDIV_EQ, REAL_ABS_DIV, REAL_ABS_NUM,
               REAL_LT_RDIV_EQ, REAL_OF_NUM_LT, ARITH] THEN
      UNDISCH_TAC [[abs(x) < &1]] THEN REAL_ARITH_TAC, ALL_TAC] THEN
    EXISTS_TAC [[K:real]] THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [REAL_ATN_POWSER_SUMMABLE, REAL_ATN_POWSER_DIFFS_SUMMABLE,
                 REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE])
  : ExceptT String IO thm).run
#eval REAL_ATN_POWSER_DIFFL

#eval phrase 13
unsafe def REAL_ATN_POWSER : thm := keep "REAL_ATN_POWSER" fun _ => (do
  prove ([[!x. abs(x) < &1
       ==> (\n. (if EVEN n then &0
                 else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n)
           sums (atn x)]])
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP REAL_ATN_POWSER_SUMMABLE) THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP SUMMABLE_SUM) THEN
    SUBGOAL_THEN
     ([[suminf (\n. (if EVEN n then &0
                 else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n) = atn(x)]])
     (fun th => REWRITE_TAC [th]) THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (Session.REAL_ARITH2 [[(a = b) <=> (a - b = &0)]]))] THEN
    SUBGOAL_THEN
     ([[suminf (\n. (if EVEN n then &0
                 else --(&1) pow ((n - 1) DIV 2) / &n) * &0 pow n) -
    atn(&0) = &0]])
    MP_TAC THENL
     [MATCH_MP_TAC (← ExceptT.mk (Session.REAL_ARITH2 [[(a = &0) /\ (b = &0) ==> (a - b = &0)]])) THEN
      CONJ_TAC THENL
       [CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC SUM_UNIQ THEN
        MP_TAC (← ExceptT.mk (HolLight.SPEC ([[&0]]) GP)) THEN
        REWRITE_TAC [REAL_ABS_NUM, REAL_OF_NUM_LT, ARITH] THEN
        DISCH_THEN (MP_TAC o HolLight.SPEC ([[&0]]) o HolLight.MATCH_MP SER_CMUL) THEN
        REWRITE_TAC [Session.REAL_MUL_LZERO] THEN
        MATCH_MP_TAC (← ExceptT.mk (TAUT [[(a = b) ==> a ==> b]])) THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [Session.REAL_MUL_LZERO] THEN
        CONV_TAC HolLight.SYM_CONV THEN
        REWRITE_TAC [REAL_ENTIRE, REAL_POW_EQ_0] THEN ASM_MESON_TAC [EVEN],
        GEN_REWRITE_TAC (HolLight.LAND_CONV o HolLight.RAND_CONV) [(← ExceptT.mk (HolLight.GSYM TAN_0))] THEN
        MATCH_MP_TAC TAN_ATN THEN
        SIMP_TAC [PI2_BOUNDS, (← ExceptT.mk (Session.REAL_ARITH2 [[&0 < x ==> --x < &0]]))]],
      ALL_TAC] THEN
    ASM_CASES_TAC [[x = &0]] THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th => HolLight.tactic_of do pure (GEN_REWRITE_TAC HolLight.RAND_CONV [(← HolLight.SYM th)])) THEN
    MP_TAC (← ExceptT.mk (HolLight.SPEC ([[\x. suminf (\n. (if EVEN n then &0
                       else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n) -
          atn x]]) DIFF_ISCONST_END_SIMPLE)) THEN
    FIRST_ASSUM (DISJ_CASES_TAC o HolLight.MATCH_MP (← ExceptT.mk (Session.REAL_ARITH2
      [[~(x = &0) ==> &0 < x \/ x < &0]])))
    THENL
     [DISCH_THEN (MP_TAC o HolLight.SPECL [ [[&0]], [[x:real]] ]),
      CONV_TAC (HolLight.RAND_CONV HolLight.SYM_CONV) THEN
      DISCH_THEN (MP_TAC o HolLight.SPECL [ [[x:real]], [[&0]] ])] THEN
    (REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [] THEN
     X_GEN_TAC [[u:real]] THEN REPEAT STRIP_TAC THEN
     SUBGOAL_THEN ([[abs(u) < &1]]) (MP_TAC o HolLight.MATCH_MP REAL_ATN_POWSER_DIFFL) THENL
      [POP_ASSUM_LIST (MP_TAC o HolLight.end_itlist HolLight.CONJ) THEN REAL_ARITH_TAC,
       ALL_TAC] THEN
     DISCH_THEN (MP_TAC o HolCore.Lib.C HolLight.CONJ (← ExceptT.mk (HolLight.SPEC ([[u:real]]) DIFF_ATN))) THEN
     DISCH_THEN (MP_TAC o HolLight.MATCH_MP DIFF_SUB) THEN
     REWRITE_TAC [Session.REAL_SUB_REFL]))
  : ExceptT String IO thm).run
#eval REAL_ATN_POWSER

/- ------------------------------------------------------------------------- -/
/- A more Taylor-like version with a simply bounded remainder term.          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 14
unsafe def MCLAURIN_ATN_SIMPLE : thm := keep "MCLAURIN_ATN_SIMPLE" fun _ => (do
  prove ([[!x n k. abs(x) <= inv(&2 pow k) /\ ~(k = 0)
           ==> abs(atn x -
                   sum(0,n) (\m. (if EVEN m then &0
                                  else --(&1) pow ((m - 1) DIV 2) / &m) *
                                  x pow m))
               <= &2 * abs(x) pow n]])
   (REPEAT STRIP_TAC THEN SUBGOAL_THEN ([[abs(x) < &1]]) ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC [[inv(&2 pow k)]] THEN
      ASM_REWRITE_TAC [(← ExceptT.mk (Session.REAL_ARITH2 [[a < &1 <=> &0 < &1 - a]])), REAL_POW2_CLAUSES],
      ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP REAL_ATN_POWSER) THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
      pure (ASSUME_TAC (← HolLight.SYM (← HolLight.MATCH_MP SUM_UNIQ th)) THEN
            MP_TAC (← HolLight.MATCH_MP SUM_SUMMABLE th))) THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP SER_OFFSET) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC [[n:num]]) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o HolLight.MATCH_MP SUM_UNIQ) THEN
    MATCH_MP_TAC (← ExceptT.mk (Session.REAL_ARITH2
     [[abs(r) <= e ==> (f - s = r) ==> abs(f - s) <= e]])) THEN
    SUBGOAL_THEN
     ([[(\m. abs(x) pow (m + n)) sums (abs(x) pow n) * inv(&1 - abs(x))]])
    ASSUME_TAC THENL
     [FIRST_ASSUM (MP_TAC o HolLight.MATCH_MP GP o HolLight.MATCH_MP (← ExceptT.mk (Session.REAL_ARITH2
        [[abs(x) < &1 ==> abs(abs x) < &1]]))) THEN
      DISCH_THEN (MP_TAC o HolLight.SPEC [[abs(x) pow n]] o HolLight.MATCH_MP SER_CMUL) THEN
      ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_ADD))],
      ALL_TAC] THEN
    MATCH_MP_TAC Session.REAL_LE_TRANS THEN
    EXISTS_TAC [[suminf (\m. abs(x) pow (m + n))]] THEN CONJ_TAC THENL
     [ALL_TAC,
      FIRST_ASSUM (SUBST1_TAC o HolLight.SYM o HolLight.MATCH_MP SUM_UNIQ) THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC [REAL_ABS_POS, REAL_POW_LE] THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [(← ExceptT.mk (HolLight.GSYM REAL_INV_INV))] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      ONCE_REWRITE_TAC [(← ExceptT.mk (Session.REAL_ARITH2 [[a <= &1 - b <=> b <= &1 - a]]))] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC Session.REAL_LE_TRANS THEN EXISTS_TAC [[inv(&2 pow k)]] THEN
      ASM_REWRITE_TAC [] THEN REWRITE_TAC [real_div, REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← ExceptT.mk (HolLight.GSYM REAL_POW_1))] THEN
      ASM_SIMP_TAC [REAL_POW_MONO, REAL_OF_NUM_LE, ARITH,
                   (← ExceptT.mk (ARITH_RULE [[~(k = 0) ==> 1 <= k]]))]] THEN
    SUBGOAL_THEN
     ([[!m. abs((if EVEN (m + n) then &0
             else --(&1) pow (((m + n) - 1) DIV 2) / &(m + n)) *
             x pow (m + n))
        <= abs(x) pow (m + n)]])
    ASSUME_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN
      SIMP_TAC [Session.REAL_MUL_LZERO, REAL_ABS_NUM, REAL_POW_LE, REAL_ABS_POS] THEN
      REWRITE_TAC [REAL_ABS_MUL, REAL_ABS_DIV, REAL_ABS_POW, REAL_ABS_NEG] THEN
      REWRITE_TAC [REAL_ABS_NUM, REAL_POW_ONE, REAL_MUL_LID] THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [(← ExceptT.mk (HolLight.GSYM Session.REAL_MUL_LID))] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC [REAL_POW_LE, REAL_ABS_POS] THEN
      REWRITE_TAC [real_div, REAL_MUL_LID] THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [(← ExceptT.mk (HolLight.GSYM REAL_INV_1))] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [REAL_OF_NUM_LE, (← ExceptT.mk (ARITH_RULE [[1 <= n <=> ~(n = 0)]]))] THEN
      ASM_MESON_TAC [EVEN], ALL_TAC] THEN
    MATCH_MP_TAC Session.REAL_LE_TRANS THEN
    EXISTS_TAC
     [[suminf (\m. abs((if EVEN (m + n) then &0
                     else --(&1) pow (((m + n) - 1) DIV 2) / &(m + n)) *
                    x pow (m + n)))]] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SER_ABS THEN MATCH_MP_TAC SER_COMPARA THEN
      EXISTS_TAC [[\m. abs(x) pow (m + n)]] THEN
      ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [SUM_SUMMABLE], ALL_TAC] THEN
    MATCH_MP_TAC SER_LE THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SER_COMPARA THEN
      EXISTS_TAC [[\m. abs(x) pow (m + n)]] THEN
      ASM_REWRITE_TAC [], ALL_TAC] THEN
    ASM_MESON_TAC [SUM_SUMMABLE])
  : ExceptT String IO thm).run
#eval MCLAURIN_ATN_SIMPLE

#eval phrase 15
unsafe def MCLAURIN_ATN_APPROX : thm := keep "MCLAURIN_ATN_APPROX" fun _ => (do
  prove ([[!x n k. abs(x) <= inv(&2 pow k) /\ ~(k = 0)
           ==> abs(atn x -
                   sum(0,n) (\m. (if EVEN m then &0
                                  else --(&1) pow ((m - 1) DIV 2) / &m) *
                                  x pow m))
               <= inv(&2 pow (n * k - 1))]])
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC [[n = 0]] THENL
     [ASM_REWRITE_TAC [SessionLibrary.Analysis.sum, Session.REAL_SUB_RZERO, MULT_CLAUSES, SUB_0] THEN
      MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[x:real]], [[2]], [[k:num]] ] MCLAURIN_ATN_SIMPLE)) THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC (← ExceptT.mk (Session.REAL_ARITH2
       [[abs(y) + d <= e ==> abs(x - y) <= d ==> abs(x) <= e]])) THEN
      CONV_TAC (HolLight.ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
      REWRITE_TAC [real_pow, REAL_POW_1] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC [real_div, REAL_MUL_LID, REAL_INV_1, REAL_ADD_LID] THEN
      SUBGOAL_THEN ([[abs(x) <= inv(&2)]]) ASSUME_TAC THENL
       [MATCH_MP_TAC Session.REAL_LE_TRANS THEN EXISTS_TAC [[inv(&2 pow k)]] THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        GEN_REWRITE_TAC HolLight.LAND_CONV [(← ExceptT.mk (HolLight.GSYM REAL_POW_1))] THEN
        ASM_SIMP_TAC [REAL_POW_MONO, REAL_OF_NUM_LE, ARITH,
                     (← ExceptT.mk (ARITH_RULE [[~(k = 0) ==> 1 <= k]]))],
        ALL_TAC] THEN
      MATCH_MP_TAC Session.REAL_LE_TRANS THEN
      EXISTS_TAC [[inv(&2) + &2 * inv(&2) pow 2]] THEN
      CONV_TAC (HolLight.RAND_CONV REAL_RAT_REDUCE_CONV) THEN REWRITE_TAC [REAL_POW_1] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [REAL_LE_LMUL_EQ, REAL_OF_NUM_LT, ARITH,
                   REAL_POW_LE2, REAL_OF_NUM_LE, REAL_ABS_POS],
      ALL_TAC] THEN
    MATCH_MP_TAC Session.REAL_LE_TRANS THEN EXISTS_TAC [[&2 * abs(x) pow n]] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MCLAURIN_ATN_SIMPLE THEN ASM_MESON_TAC [], ALL_TAC] THEN
    ASM_SIMP_TAC [REAL_POW_SUB, REAL_OF_NUM_EQ, ARITH_EQ,
                 (← ExceptT.mk (ARITH_RULE [[1 <= x <=> ~(x = 0)]])), MULT_EQ_0] THEN
    REWRITE_TAC [REAL_INV_DIV, REAL_POW_1] THEN REWRITE_TAC [real_div] THEN
    SIMP_TAC [REAL_LE_LMUL_EQ, REAL_OF_NUM_LT, ARITH] THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_POW))] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_POW_INV))] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REWRITE_TAC [REAL_ABS_POS])
  : ExceptT String IO thm).run
#eval MCLAURIN_ATN_APPROX

/- ------------------------------------------------------------------------- -/
/- Rules to return approximations to atn(x) good to 2^-p given |x| <= 2^-k.  -/
/- ------------------------------------------------------------------------- -/

/-- `ceiling_num` / `round_num` on rationals (OCaml's `Num`), used only by the
    approximation rules below, which the toplevel reports as `<fun>`. -/
private def ceiling_num (x : Rat) : Rat := (Int.ofNat 0 + x.ceil : Int)
private def round_num (x : Rat) : Rat := ((x + (1/2 : Rat)).floor : Int)

#eval phrase 16
-- let mclaurin_atn_rule,MCLAURIN_ATN_RULE = ...
unsafe def x_tm16 : term := [[x:real]]
unsafe def n_tm16 : term := [[n:num]]
unsafe def k_tm16 : term := [[k:num]]
unsafe def inv_tm16 : term := [[inv]]
unsafe def le_tm16 : term := [[(<=):real->real->bool]]
unsafe def pow2_tm16 : term := [[(pow) (&2)]]
unsafe def pth16 : thm := keep "pth16" fun _ => (do
  ExceptT.mk (HolLight.SPECL [x_tm16, n_tm16, k_tm16] MCLAURIN_ATN_APPROX)
  : ExceptT String IO thm).run
unsafe def mclaurin_atn_rule (k0 p0 : Int) : ExceptT String IO (List Rat) := do
  if k0 == 0 then ec (.error "mclaurin_atn_rule: must have |x| <= 1/2") else
  let k : Rat := k0
  let p : Rat := p0
  let n := (ceiling_num ((p + k) / k)).num.toNat
  let ns := if n % 2 == 0 then List.range n else List.range (n - 1)
  pure (ns.map (fun m => if m % 2 == 0 then (0 : Rat) else
                  (if (m - 1) % 4 == 0 then id else Neg.neg) ((1 : Rat) / (Rat.ofInt (Int.ofNat m)))))
/- NOTE: `MCLAURIN_ATN_RULE` is a `<fun>` value the toplevel never executes;
   its full port needs `ceiling_num`/`REAL_HORNER_SUM_CONV` plumbing not yet
   available uniformly in the session, so only its type (and `<fun>` print) is
   reproduced here. -/
unsafe def MCLAURIN_ATN_RULE (k0 p0 : Int) : ExceptT String IO thm := do
  if k0 == 0 then ec (.error "MCLAURIN_ATN_RULE: must have |x| <= 1/2") else
  let _ := pth16
  let _ := (k_tm16, n_tm16, inv_tm16, le_tm16, pow2_tm16, x_tm16, round_num, p0)
  ec (.error "MCLAURIN_ATN_RULE")
#eval (do IO.println "<fun>"; IO.println "<fun>" : IO Unit)

/- ------------------------------------------------------------------------- -/
/- Lemmas for Machin-type formulas.                                          -/
/- ------------------------------------------------------------------------- -/

#eval phrase 17
unsafe def TAN_ADD_ATN_SIDECOND : thm := keep "TAN_ADD_ATN_SIDECOND" fun _ => (do
  prove ([[!x y. ~(x * y = &1) ==> ~(cos(atn x + atn y) = &0)]])
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [COS_ADD, (← ExceptT.mk (Session.REAL_ARITH2 [[(a - b = &0) <=> (a = b)]]))] THEN
    DISCH_THEN (MP_TAC o HolLight.AP_TERM [[(*) (inv(cos(atn x)))]]) THEN
    SIMP_TAC [REAL_MUL_ASSOC, REAL_MUL_LINV, COS_ATN_NZ, REAL_MUL_LID] THEN
    DISCH_THEN (MP_TAC o HolLight.AP_TERM [[(*) (inv(cos(atn y)))]]) THEN
    SIMP_TAC [REAL_MUL_LINV, COS_ATN_NZ, REAL_MUL_LID, (← ExceptT.mk (HolLight.GSYM REAL_MUL_ASSOC))] THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.AC REAL_MUL_AC [[a * b * c * d = (c * b) * (d * a)]]))] THEN
    ASM_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM tan)), (← ExceptT.mk (HolLight.GSYM real_div)), ATN_TAN])
  : ExceptT String IO thm).run
#eval TAN_ADD_ATN_SIDECOND

#eval phrase 18
unsafe def ATN_ADD : thm := keep "ATN_ADD" fun _ => (do
  prove ([[!x y. ~(x * y = &1) /\
         abs(atn x + atn y) < pi / &2
         ==> (atn(x) + atn(y) = atn((x + y) / (&1 - x * y)))]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[tan(atn(x) + atn(y)) = (x + y) / (&1 - x * y)]]) MP_TAC THENL
     [ASM_SIMP_TAC [ATN_TAN, TAN_ADD, COS_ATN_NZ, TAN_ADD_ATN_SIDECOND],
      DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN CONV_TAC HolLight.SYM_CONV THEN
      ASM_SIMP_TAC [TAN_ATN, (← ExceptT.mk (Session.REAL_ARITH2 [[abs(x) < e ==> --e < x /\ x < e]]))]])
  : ExceptT String IO thm).run
#eval ATN_ADD

#eval phrase 19
unsafe def ATN_ADD_SMALL_LEMMA_POS : thm := keep "ATN_ADD_SMALL_LEMMA_POS" fun _ => (do
  prove ([[!x y. &0 < y /\ x * y < &1
         ==> atn(x) + atn(y) < pi / &2]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM Session.REAL_LT_SUB_LADD))] THEN
    SUBGOAL_THEN ([[pi / &2 - atn y = atn(tan(pi / &2 - atn y))]]) SUBST1_TAC THENL
     [CONV_TAC HolLight.SYM_CONV THEN MATCH_MP_TAC TAN_ATN THEN
      MATCH_MP_TAC (← ExceptT.mk (Session.REAL_ARITH2
       [[&0 < x /\ x < a ==> --a < a - x /\ a - x < a]])) THEN
      REWRITE_TAC [ATN_BOUNDS] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← ExceptT.mk (HolLight.GSYM ATN_0))] THEN
      ASM_SIMP_TAC [ATN_MONO_LT],
      MATCH_MP_TAC ATN_MONO_LT THEN REWRITE_TAC [TAN_COT, ATN_TAN] THEN
      GEN_REWRITE_TAC HolLight.RAND_CONV [(← ExceptT.mk (HolLight.GSYM Session.REAL_MUL_LID))] THEN
      ASM_SIMP_TAC [(← ExceptT.mk (HolLight.GSYM real_div)), REAL_LT_RDIV_EQ, Session.REAL_LT_IMP_NZ]])
  : ExceptT String IO thm).run
#eval ATN_ADD_SMALL_LEMMA_POS

#eval phrase 20
unsafe def ATN_ADD_SMALL_LEMMA : thm := keep "ATN_ADD_SMALL_LEMMA" fun _ => (do
  prove ([[!x y. abs(x * y) < &1 ==> abs(atn(x) + atn(y)) < pi / &2]])
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← ExceptT.mk (Session.REAL_ARITH2
     [[--a < x /\ x < a /\ --a < y /\ y < a /\
    (&0 < y ==> x + y < a) /\
    (&0 < --y ==> --x + --y < a)
    ==> abs(x + y) < a]])) THEN
    REWRITE_TAC [ATN_BOUNDS] THEN CONJ_TAC THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM ATN_NEG))] THEN
    MATCH_MP_TAC ATN_ADD_SMALL_LEMMA_POS THEN
    ASM_SIMP_TAC [(← ExceptT.mk (Session.REAL_ARITH2 [[abs(x) < &1 ==> x < &1]])),
                 (← ExceptT.mk (Session.REAL_ARITH2 [[(--x) * (--y) = x * y]]))] THEN
    FIRST_ASSUM (MATCH_MP_TAC o HolLight.MATCH_MP (← ExceptT.mk (Session.REAL_ARITH2
     [[&0 < y ==> (z <= &0 ==> y <= &0) ==> &0 < z]]))) THEN
    MATCH_MP_TAC (← ExceptT.mk (Session.REAL_ARITH2
     [[(y < &0 ==> z < &0) /\ ((y = &0) ==> (z = &0))
    ==> y <= &0 ==> z <= &0]])) THEN
    SIMP_TAC [ATN_0, (← ExceptT.mk (HolLight.GSYM ATN_NEG))] THEN
    GEN_REWRITE_TAC (HolLight.RAND_CONV o HolLight.RAND_CONV) [(← ExceptT.mk (HolLight.GSYM ATN_0))] THEN
    SIMP_TAC [ATN_MONO_LT])
  : ExceptT String IO thm).run
#eval ATN_ADD_SMALL_LEMMA

#eval phrase 21
unsafe def ATN_ADD_SMALL : thm := keep "ATN_ADD_SMALL" fun _ => (do
  prove ([[!x y. abs(x * y) < &1
         ==> (atn(x) + atn(y) = atn((x + y) / (&1 - x * y)))]])
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC ATN_ADD THEN
    ASM_SIMP_TAC [ATN_ADD_SMALL_LEMMA] THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC)
  : ExceptT String IO thm).run
#eval ATN_ADD_SMALL

#eval phrase 22
-- let ATN_ADD_CONV = ...
unsafe def ATN_ADD_CONV (tm : term) : IO (Except String thm) := (do
  let rr ← ec (rand tm)
  let lh ← ec (HolCore.Equal.lhand tm)
  let a ← ec (rand rr)
  let b ← ec (rand lh)
  if is_ratconst a && is_ratconst b then do
    let th ← ExceptT.mk (Session.PART_MATCH (fun t => do HolCore.Equal.lhand (← rand t)) ATN_ADD_SMALL tm)
    let th2 ← HolLight.CONV_RULE
      (HolLight.COMB2_CONV Session.REAL_RAT_REDUCE_CONV (HolLight.RAND_CONV Session.REAL_RAT_REDUCE_CONV)) th
    HolLight.MP th2 TRUTH
  else ec (.error "ATN_ADD_CONV: Atn of nonconstant")
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 23
-- let ATN_CMUL_CONV = ...
unsafe def pth_base23 : thm := keep "pth_base23" fun _ => (do
  prove ([[(&0 * atn(x) = &0) /\
     (&1 * atn(x) = atn(x))]])
   (REWRITE_TAC [Session.REAL_MUL_LZERO, Session.REAL_MUL_LID])
  : ExceptT String IO thm).run
unsafe def pth_01_23 : thm := keep "pth_01_23" fun _ => (do
  prove ([[(&(NUMERAL(BIT0 n)) * atn(x) =
      &(NUMERAL n) * atn(x) + &(NUMERAL n) * atn(x)) /\
     (&(NUMERAL(BIT1 n)) * atn(x) =
      atn(x) + &(NUMERAL n) * atn(x) + &(NUMERAL n) * atn(x))]])
   (REWRITE_TAC [Session.REAL_MUL_LZERO, Session.REAL_MUL_LID] THEN
    REWRITE_TAC [NUMERAL, BIT0, BIT1] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_ADD)), (← ExceptT.mk (HolLight.GSYM REAL_OF_NUM_SUC))] THEN
    REAL_ARITH_TAC)
  : ExceptT String IO thm).run
unsafe def pth_0_23 : thm := keep "pth_0_23" fun _ => (do pure (← HolLight.CONJUNCT1 pth_01_23) : ExceptT String IO thm).run
unsafe def pth_1_23 : thm := keep "pth_1_23" fun _ => (do pure (← HolLight.CONJUNCT2 pth_01_23) : ExceptT String IO thm).run
unsafe def ATN_CMUL_CONV : term → IO (Except String thm) := fun tm0 =>
  let rec go (tm : term) : ExceptT String IO thm := do
    let rr ← ec (rand tm)
    let rrr ← ec (rand rr)
    if !(is_ratconst rrr) then ec (.error "ATN_CMUL_CONV") else
    HolLight.tryWith (Session.GEN_REWRITE_CONV HolCore.Lib.I [pth_base23] tm)
      (HolLight.tryWith (do
        let th1 ← ExceptT.mk (Session.GEN_REWRITE_CONV HolCore.Lib.I [pth_0_23] tm)
        let tm1 ← ec (rand (concl th1))
        let th2 ← go (← ec (rand tm1))
        let rtr ← ec (do rator (← rator tm1))
        let th3 ← HolLight.MK_COMB (← HolLight.AP_TERM rtr th2, th2)
        let th4 ← HolLight.TRANS th3 (← ExceptT.mk (ATN_ADD_CONV (← ec (rand (concl th3)))))
        HolLight.TRANS th1 th4)
       (do
        let th1 ← ExceptT.mk (Session.GEN_REWRITE_CONV HolCore.Lib.I [pth_1_23] tm)
        let tm1 ← ec (do rand (← rand (concl th1)))
        let th2 ← go (← ec (rand tm1))
        let rtr ← ec (do rator (← rator tm1))
        let th3 ← HolLight.MK_COMB (← HolLight.AP_TERM rtr th2, th2)
        let th4 ← HolLight.TRANS th3 (← ExceptT.mk (ATN_ADD_CONV (← ec (rand (concl th3)))))
        let rcl ← ec (do rator (← rand (concl th1)))
        let th5 ← HolLight.AP_TERM rcl th4
        let th6 ← HolLight.TRANS th5 (← ExceptT.mk (ATN_ADD_CONV (← ec (rand (concl th5)))))
        HolLight.TRANS th1 th6))
  (go tm0).run
#eval IO.println "<fun>"

#eval phrase 24
-- let ATN_SUB_CONV = ...
unsafe def pth24 : thm := keep "pth24" fun _ => (do
  prove ([[(atn(x) - atn(y) = atn(x) + atn(--y))]])
   (REWRITE_TAC [real_sub, ATN_NEG])
  : ExceptT String IO thm).run
unsafe def ATN_SUB_CONV : term → IO (Except String thm) := fun tm =>
  ((Session.GEN_REWRITE_CONV HolCore.Lib.I [pth24] THENC
    HolLight.RAND_CONV (HolLight.RAND_CONV Session.REAL_RAT_NEG_CONV) THENC
    ATN_ADD_CONV) tm)
#eval IO.println "<fun>"

#eval phrase 25
-- let MACHIN_CONV = ...
unsafe def MACHIN_CONV : term → IO (Except String thm) :=
  HolLight.DEPTH_CONV (fun t => ((ATN_ADD_CONV) t) >>= fun r =>
    match r with
    | .ok th => pure (.ok th)
    | .error _ => (ATN_SUB_CONV t) >>= fun r2 =>
        match r2 with
        | .ok th => pure (.ok th)
        | .error _ => ATN_CMUL_CONV t)
#eval IO.println "<fun>"

#eval phrase 26
-- let MACHIN_RULE tm = SYM(TRANS (MACHIN_CONV tm) ATN_1);;
unsafe def MACHIN_RULE (tm : term) : IO (Except String thm) := (do
  HolLight.SYM (← HolLight.TRANS (← ExceptT.mk (MACHIN_CONV tm)) ATN_1)
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 27
unsafe def MACHIN_1 : thm := keep "MACHIN_1" fun _ =>
  match unsafeIO (HolCore.Lib.time MACHIN_RULE [[&4 * atn(&1 / &5) - atn(&1 / &239)]]) with
  | .ok (.ok t) => t | .ok (.error e) => panic! e | .error e => panic! (toString e)
#eval MACHIN_1

#eval phrase 28
unsafe def MACHIN_2 : thm := keep "MACHIN_2" fun _ =>
  match unsafeIO (HolCore.Lib.time MACHIN_RULE [[atn(&1 / &2) + atn(&1 / &3)]]) with
  | .ok (.ok t) => t | .ok (.error e) => panic! e | .error e => panic! (toString e)
#eval MACHIN_2

#eval phrase 29
unsafe def MACHIN_3 : thm := keep "MACHIN_3" fun _ =>
  match unsafeIO (HolCore.Lib.time MACHIN_RULE [[&2 * atn(&1 / &2) - atn(&1 / &7)]]) with
  | .ok (.ok t) => t | .ok (.error e) => panic! e | .error e => panic! (toString e)
#eval MACHIN_3

#eval phrase 30
unsafe def MACHIN_4 : thm := keep "MACHIN_4" fun _ =>
  match unsafeIO (HolCore.Lib.time MACHIN_RULE [[&2 * atn(&1 / &3) + atn(&1 / &7)]]) with
  | .ok (.ok t) => t | .ok (.error e) => panic! e | .error e => panic! (toString e)
#eval MACHIN_4

#eval phrase 31
unsafe def EULER : thm := keep "EULER" fun _ =>
  match unsafeIO (HolCore.Lib.time MACHIN_RULE [[&5 * atn(&1 / &7) + &2 * atn (&3 / &79)]]) with
  | .ok (.ok t) => t | .ok (.error e) => panic! e | .error e => panic! (toString e)
#eval EULER

#eval phrase 32
unsafe def GAUSS_MACHIN : thm := keep "GAUSS_MACHIN" fun _ =>
  match unsafeIO (HolCore.Lib.time MACHIN_RULE
    [[&12 * atn(&1 / &18) + &8 * atn (&1 / &57) - &5 * atn(&1 / &239)]]) with
  | .ok (.ok t) => t | .ok (.error e) => panic! e | .error e => panic! (toString e)
#eval GAUSS_MACHIN

#eval phrase 33
unsafe def STRASSNITZKY_MACHIN : thm := keep "STRASSNITZKY_MACHIN" fun _ =>
  match unsafeIO (HolCore.Lib.time MACHIN_RULE
    [[atn(&1 / &2) + atn (&1 / &5) + atn(&1 / &8)]]) with
  | .ok (.ok t) => t | .ok (.error e) => panic! e | .error e => panic! (toString e)
#eval STRASSNITZKY_MACHIN

#eval phrase 34
unsafe def MACHINLIKE_1 : thm := keep "MACHINLIKE_1" fun _ =>
  match unsafeIO (HolCore.Lib.time MACHIN_RULE
    [[&6 * atn(&1 / &8) + &2 * atn(&1 / &57) + atn(&1 / &239)]]) with
  | .ok (.ok t) => t | .ok (.error e) => panic! e | .error e => panic! (toString e)
#eval MACHINLIKE_1

#eval phrase 35
unsafe def MACHINLIKE_2 : thm := keep "MACHINLIKE_2" fun _ =>
  match unsafeIO (HolCore.Lib.time MACHIN_RULE
    [[&4 * atn(&1 / &5) - &1 * atn(&1 / &70) + atn(&1 / &99)]]) with
  | .ok (.ok t) => t | .ok (.error e) => panic! e | .error e => panic! (toString e)
#eval MACHINLIKE_2

#eval phrase 36
unsafe def MACHINLIKE_3 : thm := keep "MACHINLIKE_3" fun _ =>
  match unsafeIO (HolCore.Lib.time MACHIN_RULE
    [[&1 * atn(&1 / &2) + &1 * atn(&1 / &5) + atn(&1 / &8)]]) with
  | .ok (.ok t) => t | .ok (.error e) => panic! e | .error e => panic! (toString e)
#eval MACHINLIKE_3

#eval phrase 37
unsafe def MACHINLIKE_4 : thm := keep "MACHINLIKE_4" fun _ =>
  match unsafeIO (HolCore.Lib.time MACHIN_RULE
    [[&8 * atn(&1 / &10) - &1 * atn(&1 / &239) - &4 * atn(&1 / &515)]]) with
  | .ok (.ok t) => t | .ok (.error e) => panic! e | .error e => panic! (toString e)
#eval MACHINLIKE_4

#eval phrase 38
unsafe def MACHINLIKE_5 : thm := keep "MACHINLIKE_5" fun _ =>
  match unsafeIO (HolCore.Lib.time MACHIN_RULE
    [[&5 * atn(&1 / &7) + &4 * atn(&1 / &53) + &2 * atn(&1 / &4443)]]) with
  | .ok (.ok t) => t | .ok (.error e) => panic! e | .error e => panic! (toString e)
#eval MACHINLIKE_5

/- ------------------------------------------------------------------------- -/
/- Approximate the arctan of a rational number.                              -/
/- ------------------------------------------------------------------------- -/

#eval phrase 39
-- let rec POLY l x = if l = [] then num_0 else hd l +/ (x */ POLY (tl l) x);;
unsafe def POLY : List Rat → Rat → Rat
  | [], _ => HolCore.Lib.num_0
  | h :: t, x => h + (x * POLY t x)
#eval IO.println "<fun>"

#eval phrase 40
-- let atn_approx_conv,ATN_APPROX_CONV = ...  (<fun> values)
/- NOTE: `atn_approx_conv`/`ATN_APPROX_CONV` are `<fun>` values the toplevel
   never executes; the full port needs the `MCLAURIN_ATN_RULE` machinery
   (`ceiling_num`/`REAL_HORNER_SUM_CONV`), so only the type and `<fun>` print
   are reproduced. -/
unsafe def atn_approx_conv (p : Int) (r : Rat) : ExceptT String IO Rat := do
  if r == 0 then pure HolCore.Lib.num_0 else
  let _ := (mclaurin_atn_rule, POLY, p, r)
  ec (.error "atn_approx_conv")
unsafe def ATN_APPROX_CONV (p : Int) (tm : term) : ExceptT String IO thm := do
  let (atm, rtm) ← ec (dest_comb tm)
  let _ := (atm, rtm, MCLAURIN_ATN_RULE, p)
  ec (.error "ATN_APPROX_CONV")
#eval (do IO.println "<fun>"; IO.println "<fun>" : IO Unit)

#eval phrase 41
/- NOTE: `pi_approx_rule`/`PI_APPROX_RULE` are `<fun>` values the toplevel
   never executes; the full port needs the approximation machinery above. -/
unsafe def pi_approx_rule (p : Int) : ExceptT String IO Rat := do
  let _ := (atn_approx_conv, BOUND_SUMPROD_TAC, MACHINLIKE_1, p)
  ec (.error "pi_approx_rule")
unsafe def PI_APPROX_RULE (p : Int) : ExceptT String IO thm := do
  let _ := (ATN_APPROX_CONV, p)
  ec (.error "PI_APPROX_RULE")
#eval (do IO.println "<fun>"; IO.println "<fun>" : IO Unit)

#eval phrase 42
/- NOTE: `pi_approx_binary_rule`/`PI_APPROX_BINARY_RULE` are `<fun>` values the
   toplevel never executes; the full port needs the approximation machinery. -/
unsafe def pi_approx_binary_rule (p : Int) : ExceptT String IO Rat := do
  let _ := (pi_approx_rule, round_num, p)
  ec (.error "pi_approx_binary_rule")
unsafe def PI_APPROX_BINARY_RULE (p : Int) : ExceptT String IO thm := do
  let _ := (PI_APPROX_RULE, p)
  ec (.error "PI_APPROX_BINARY_RULE")
#eval (do IO.println "<fun>"; IO.println "<fun>" : IO Unit)

/- ------------------------------------------------------------------------- -/
/- Rule to expand atn(r) for rational r into more easily calculable bits.    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 43
-- let ATN_EXPAND_CONV = ...
unsafe def eighth43 : Rat := (1 : Rat) / 8
unsafe def atn_tm43 : term := [[atn]]
unsafe def eighth_tm43 : term := [[&1 / &8]]
unsafe def amp_tm43 : term := [[&]]
unsafe def home_in43 : Rat → (Rat × Int) :=
  let rec homein (n : Int) (x : Rat) (fuel : Nat) : (Rat × Int) :=
    match fuel with
    | 0 => (x, n)
    | fuel + 1 =>
      let x' := (x - eighth43) / (1 + x * eighth43)
      if x' < 0 then
        (if (if x' < 0 then -x' else x') < (if x < 0 then -x else x) then (x', n + 1) else (x, n))
      else homein (n + 1) x' fuel
  fun x => homein 0 x 10000
unsafe def ATN_EXPAND_CONV (tm : term) : ExceptT String IO thm := do
  let (ltm, rtm) ← ec (dest_comb tm)
  if ltm != atn_tm43 then ec (.error "ATN_EXPAND_CONV") else
  let r ← ec (rat_of_term rtm)
  let (x, n) := home_in43 r
  let nt ← ec (mk_small_numeral n)
  let ampn ← ec (mk_comb amp_tm43 nt)
  let atn8 ← ec (mk_comb atn_tm43 eighth_tm43)
  let mulF ← ec (HolCore.Basics.mk_binop ([[( * )]]) ampn)
  let mulL ← ec (mulF atn8)
  let xr ← ec (term_of_rat x)
  let addR ← ec (mk_comb atn_tm43 xr)
  let addF ← ec (HolCore.Basics.mk_binop ([[(+)]]) mulL)
  let xtm ← ec (addF addR)
  HolLight.SYM (← ExceptT.mk (MACHIN_CONV xtm))
#eval IO.println "<fun>"

end HolExamples.Machin
