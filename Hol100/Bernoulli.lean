/- File: Hol100/Bernoulli.lean
Translation of HOL Light's 100/bernoulli.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import Hol100.Common
import SessionLibrary.Binomial
import SessionLibrary.Analysis
import SessionLibrary.Transc
open HolCore.Kernel Session HolLight.Syntax HolExamples Hol100
open SessionLibrary.Binomial SessionLibrary.Analysis SessionLibrary.Transc
namespace Hol100.Bernoulli

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)
private def ar (tm : term) : ExceptT String IO thm := ExceptT.mk (ARITH_RULE tm)
private def rf (tm : term) : ExceptT String IO thm := ExceptT.mk (REAL_FIELD tm)
private def rr (tm : term) : ExceptT String IO thm := ExceptT.mk (Session.REAL_ARITH3 tm)

/- ========================================================================= -/
/- Bernoulli numbers and polynomials; sum of kth powers.                     -/
/- ========================================================================= -/

#eval phrase 1
-- needs "Library/binomial.ml";;
#eval SessionLibrary.Binomial.ensureBinomial

#eval phrase 2
-- needs "Library/analysis.ml";;
#eval SessionLibrary.Analysis.ensureAnalysis

#eval phrase 3
-- needs "Library/transc.ml";;
#eval SessionLibrary.Transc.ensureTransc

#eval phrase 4
#eval Session.prioritize_real

/- ------------------------------------------------------------------------- -/
/- A couple of basic lemmas about new-style sums.                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 5
def SUM_DIFFS : thm := keep "SUM_DIFFS" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[~((n + 1) + 1 <= n + 1)]])
  let h2 ← ar (← ExceptT.mk [[m <= SUC n + 1 <=> m <= n + 1 \/ m = SUC n + 1]])
  let h1 ← ar (← ExceptT.mk [[m <= 0 + 1 <=> m = 0 \/ m = 1]])
  prove ([[!a m n. m <= n + 1 ==> sum(m..n) (\i. a(i + 1) - a(i)) = a(n + 1) - a(m)]])
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [SUM_CLAUSES_NUMSEG] THENL
     [REWRITE_TAC [h1] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [ARITH, ADD_CLAUSES, SessionLibrary.Analysis.REAL_SUB_REFL],
      SIMP_TAC [h2] THEN
      STRIP_TAC THEN ASM_SIMP_TAC [ADD1] THENL [REAL_ARITH_TAC2, ALL_TAC] THEN
      REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_REFL, h3] THEN
      MATCH_MP_TAC SUM_TRIV_NUMSEG THEN ARITH_TAC])
  : ExceptT String IO thm).run
#eval SUM_DIFFS

#eval phrase 6
def DIFF_SUM : thm := keep "DIFF_SUM" fun _ => (do
  let h2 ← ar (← ExceptT.mk [[k <= b ==> k <= SUC b]])
  let h1 ← ar (← ExceptT.mk [[~(a <= SUC b) ==> b < a]])
  prove ([[!f f' a b.
        (!k. a <= k /\ k <= b ==> ((\x. f x k) diffl f'(k)) x)
        ==> ((\x. sum(a..b) (f x)) diffl (sum(a..b) f')) x]])
   (REPLICATE_TAC 3 GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [SUM_CLAUSES_NUMSEG] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [ARITH, DIFF_CONST, SUM_TRIV_NUMSEG,
                 h1] THEN
    DISCH_TAC THEN MATCH_MP_TAC DIFF_ADD THEN
    ASM_SIMP_TAC [LE_REFL, h2])
  : ExceptT String IO thm).run
#eval DIFF_SUM

/- ------------------------------------------------------------------------- -/
/- Bernoulli numbers.                                                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 7
def bernoulli : thm := keep "bernoulli" fun _ => define
 [[(bernoulli 0 = &1) /\
  (!n. bernoulli(SUC n) =
       --sum(0..n) (\j. &(binom(n + 2,j)) * bernoulli j) / (&n + &2))]]
#eval bernoulli

/- ------------------------------------------------------------------------- -/
/- A slightly tidier-looking form of the recurrence.                         -/
/- ------------------------------------------------------------------------- -/

#eval phrase 8
def BERNOULLI : thm := keep "BERNOULLI" fun _ => (do
  let h4 ← ar (← ExceptT.mk [[~(n = n + 1)]])
  let h3 ← rf (← ExceptT.mk [[x = &n + &2 ==> s + x * --s / (&n + &2) = &0]])
  let h2 ← ar (← ExceptT.mk [[SUC(SUC n) = n + 2]])
  let h1 ← ar (← ExceptT.mk [[n < SUC n]])
  prove ([[!n. sum(0..n) (\j. &(binom(n + 1,j)) * bernoulli j) =
       if n = 0 then &1 else &0]])
   (INDUCT_TAC THEN
    REWRITE_TAC [bernoulli, SUM_CLAUSES_NUMSEG, (← HolLight.GSYM ADD1), ADD_CLAUSES, binom,
                REAL_MUL_LID, LE_0, NOT_SUC] THEN
    SIMP_TAC [BINOM_LT, h1, BINOM_REFL, REAL_ADD_LID] THEN
    REWRITE_TAC [ADD_CLAUSES] THEN REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_ADD)] THEN
    REWRITE_TAC [h2] THEN
    MATCH_MP_TAC h3 THEN
    REWRITE_TAC [ADD1, BINOM_TOP_STEP_REAL, h4] THEN
    REWRITE_TAC [BINOM_REFL] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval BERNOULLI

/- ------------------------------------------------------------------------- -/
/- Bernoulli polynomials.                                                    -/
/- ------------------------------------------------------------------------- -/

#eval phrase 9
def bernpoly : thm := keep "bernpoly" fun _ => new_definition
 [[bernpoly n x = sum(0..n) (\k. &(binom(n,k)) * bernoulli k * x pow (n - k))]]
#eval bernpoly

/- ------------------------------------------------------------------------- -/
/- The key derivative recurrence.                                            -/
/- ------------------------------------------------------------------------- -/

#eval phrase 10
def DIFF_BERNPOLY : thm := keep "DIFF_BERNPOLY" fun _ => (do
  let h3 ← ar (← ExceptT.mk [[k <= n ==> k <= n + 1]])
  let h2 ← ar (← ExceptT.mk [[k <= n ==> (n + 1) - k - 1 = n - k]])
  let h1 ← ar (← ExceptT.mk [[k <= n ==> ~(k = n + 1)]])
  prove ([[!n x. ((bernpoly (SUC n)) diffl (&(SUC n) * bernpoly n x)) x]])
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (HolLight.RATOR_CONV o HolLight.LAND_CONV) [(← HolLight.GSYM ETA_AX)] THEN
    REWRITE_TAC [bernpoly, SUM_CLAUSES_NUMSEG, LE_0] THEN
    GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM REAL_ADD_RID)] THEN
    MATCH_MP_TAC DIFF_ADD THEN REWRITE_TAC [SUB_REFL, real_pow, DIFF_CONST] THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_LMUL)] THEN MATCH_MP_TAC DIFF_SUM THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [ADD1, BINOM_TOP_STEP_REAL] THEN
    DIFF_TAC THEN ASM_SIMP_TAC [h1] THEN
    REWRITE_TAC [SessionLibrary.Analysis.REAL_MUL_LZERO, REAL_ADD_LID] THEN
    ASM_SIMP_TAC [h2] THEN
    ASM_SIMP_TAC [(← HolLight.GSYM REAL_OF_NUM_SUB), h3] THEN
    UNDISCH_TAC ([[k <= n:num]]) THEN
    REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_ADD), (← HolLight.GSYM REAL_OF_NUM_LE)] THEN
    ABBREV_TAC ([[z = x pow (n - k)]]) THEN CONV_TAC REAL_FIELD)
  : ExceptT String IO thm).run
#eval DIFF_BERNPOLY

/- ------------------------------------------------------------------------- -/
/- Hence the key stepping recurrence.                                        -/
/- ------------------------------------------------------------------------- -/

#eval phrase 11
def INTEGRALS_EQ : thm := keep "INTEGRALS_EQ" fun _ => (do
  prove ([[!f g. (!x. ((\x. f(x) - g(x)) diffl &0) x) /\ f(&0) = g(&0)
         ==> !x. f(x) = g(x)]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← HolLight.SPECL [([[\x:real. f(x) - g(x)]]), ([[x:real]]), ([[&0]])] DIFF_ISCONST_ALL) THEN
    ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC2)
  : ExceptT String IO thm).run
#eval INTEGRALS_EQ

#eval phrase 12
def RECURRENCE_BERNPOLY : thm := keep "RECURRENCE_BERNPOLY" fun _ => (do
  let h1 ← ar (← ExceptT.mk [[i <= n ==> SUC n - i = SUC(n - i)]])
  prove ([[!n x. bernpoly n (x + &1) - bernpoly n x = &n * x pow (n - 1)]])
   (INDUCT_TAC THENL
     [REWRITE_TAC [bernpoly, SUM_SING_NUMSEG, SessionLibrary.Analysis.REAL_SUB_REFL, SUB_REFL,
                  real_pow, SessionLibrary.Analysis.REAL_MUL_LZERO],
      ALL_TAC] THEN
    MATCH_MP_TAC INTEGRALS_EQ THEN CONJ_TAC THENL
     [X_GEN_TAC ([[x:real]]) THEN FIRST_X_ASSUM (MP_TAC o HolLight.SPEC ([[x:real]])) THEN
      ONCE_REWRITE_TAC [(← HolLight.GSYM SessionLibrary.Analysis.REAL_SUB_0)] THEN
      DISCH_THEN (MP_TAC o HolLight.AP_TERM ([[(*) (&(SUC n))]])) THEN
      REWRITE_TAC [SessionLibrary.Analysis.REAL_MUL_RZERO] THEN DISCH_THEN (SUBST1_TAC o HolLight.SYM) THEN
      REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_LDISTRIB] THEN
      REPEAT (MATCH_MP_TAC DIFF_SUB THEN CONJ_TAC) THEN
      SIMP_TAC [SessionLibrary.Analysis.SUC_SUB1, DIFF_CMUL, DIFF_POW, DIFF_BERNPOLY, ETA_AX] THEN
      GEN_REWRITE_TAC HolLight.LAND_CONV [(← HolLight.GSYM SessionLibrary.Analysis.REAL_MUL_RID)] THEN
      MATCH_MP_TAC DIFF_CHAIN THEN REWRITE_TAC [DIFF_BERNPOLY] THEN
      DIFF_TAC THEN REAL_ARITH_TAC2,
      ALL_TAC] THEN
    REWRITE_TAC [bernpoly, (← HolLight.GSYM SUM_SUB_NUMSEG)] THEN
    REWRITE_TAC [REAL_ADD_LID, REAL_POW_ONE, (← HolLight.GSYM SessionLibrary.Analysis.REAL_SUB_LDISTRIB)] THEN
    REWRITE_TAC [SUM_CLAUSES_NUMSEG, LE_0, SUB_REFL, real_pow] THEN
    REWRITE_TAC [SessionLibrary.Analysis.REAL_SUB_REFL, SessionLibrary.Analysis.REAL_MUL_RZERO, REAL_ADD_RID] THEN
    SIMP_TAC [h1] THEN
    REWRITE_TAC [real_pow, SessionLibrary.Analysis.REAL_MUL_LZERO, SessionLibrary.Analysis.REAL_SUB_RZERO, SessionLibrary.Analysis.REAL_MUL_RID] THEN
    REWRITE_TAC [BERNOULLI, ADD1] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [ARITH, real_pow, REAL_MUL_LID] THEN
    CONV_TAC HolLight.SYM_CONV THEN REWRITE_TAC [REAL_ENTIRE, REAL_POW_EQ_0] THEN
    ASM_REWRITE_TAC [ADD_SUB])
  : ExceptT String IO thm).run
#eval RECURRENCE_BERNPOLY

/- ------------------------------------------------------------------------- -/
/- Hence we get the main result.                                             -/
/- ------------------------------------------------------------------------- -/

#eval phrase 13
def SUM_OF_POWERS : thm := keep "SUM_OF_POWERS" fun _ => (do
  let h1 ← rr (← ExceptT.mk [[&0 < &n + &1]])
  prove ([[!n. sum(0..n) (\k. &k pow m) =
        (bernpoly(SUC m) (&n + &1) - bernpoly(SUC m) (&0)) / (&m + &1)]])
   (GEN_TAC THEN ASM_SIMP_TAC [REAL_EQ_RDIV_EQ, h1] THEN
    ONCE_REWRITE_TAC [(← HolLight.GSYM REAL_MUL_SYM)] THEN
    REWRITE_TAC [(← HolLight.GSYM SUM_LMUL)] THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC ([[sum(0..n) (\i. bernpoly (SUC m) (&(i + 1)) - bernpoly (SUC m) (&i))]]) THEN
    CONJ_TAC THENL
     [REWRITE_TAC [RECURRENCE_BERNPOLY, (← HolLight.GSYM REAL_OF_NUM_ADD)] THEN
      REWRITE_TAC [(← HolLight.GSYM REAL_OF_NUM_SUC), SessionLibrary.Analysis.SUC_SUB1],
      SIMP_TAC [SUM_DIFFS, LE_0] THEN REWRITE_TAC [REAL_OF_NUM_ADD]])
  : ExceptT String IO thm).run
#eval SUM_OF_POWERS

/- ------------------------------------------------------------------------- -/
/- Now explicit computations of the various terms on specific instances.     -/
/- ------------------------------------------------------------------------- -/

#eval phrase 14
-- let SUM_CONV = ...;;
def SUM_CONV_pth : thm := keep "SUM_CONV_pth" fun _ => (do
  prove ([[sum(0..0) f = f 0 /\ sum(0..SUC n) f = sum(0..n) f + f(SUC n)]])
   (SIMP_TAC [SUM_CLAUSES_NUMSEG, LE_0])
  : ExceptT String IO thm).run
partial def SUM_CONV (tm : term) : IO (Except String thm) := (do
  let econv_0 := HolLight.GEN_REWRITE_CONV HolCore.Lib.I [← HolLight.CONJUNCT1 SUM_CONV_pth]
  let econv_1 := HolLight.GEN_REWRITE_CONV HolCore.Lib.I [← HolLight.CONJUNCT2 SUM_CONV_pth]
  ExceptT.mk ((econv_0 ORELSEC
     (HolLight.LAND_CONV (HolLight.RAND_CONV num_CONV) THENC econv_1 THENC
      HolLight.COMB2_CONV (HolLight.RAND_CONV SUM_CONV) (HolLight.RAND_CONV NUM_SUC_CONV))) tm)
  : ExceptT String IO thm).run
#eval (do replay SUM_CONV_pth; IO.println "<fun>" : IO Unit)

#eval phrase 15
-- let BINOM_CONV = ...;;
def BINOM_CONV_pth : thm := keep "BINOM_CONV_pth" fun _ => (do
  prove ([[a * b * x = FACT c ==> x = (FACT c) DIV (a * b)]])
   (REPEAT STRIP_TAC THEN CONV_TAC HolLight.SYM_CONV THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC ([[0]]) THEN CONJ_TAC THENL
     [POP_ASSUM MP_TAC THEN ARITH_TAC,
      POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [(← HolLight.GSYM CONTRAPOS_THM)] THEN
      SIMP_TAC [LT_NZ, MULT_ASSOC, MULT_CLAUSES] THEN
      MESON_TAC [LT_NZ, FACT_LT]])
  : ExceptT String IO thm).run
def BINOM_CONV (tm : term) : IO (Except String thm) := (do
  let binom_tm ← ExceptT.mk [[binom]]
  let (bop, lr) ← ec (dest_comb tm)
  if bop != binom_tm then throw "BINOM_CONV"
  let (l, r) ← ec (dest_pair lr)
  let n ← ec (HolCore.Basics.dest_numeral l)
  let k ← ec (HolCore.Basics.dest_numeral r)
  if n < k then
    let th ← HolLight.SPECL [l, r] BINOM_LT
    HolLight.MP th (← HolLight.EQT_ELIM (← ExceptT.mk (NUM_LT_CONV (← ec (HolCore.Equal.lhand (concl th))))))
  else
    let d := n - k
    let th1 ← HolLight.MATCH_MP BINOM_CONV_pth (← HolLight.SPECL [← ec (mk_numeral d), r] BINOM_FACT)
    HolLight.CONV_RULE NUM_REDUCE_CONV th1
  : ExceptT String IO thm).run
#eval (do replay BINOM_CONV_pth; IO.println "<fun>" : IO Unit)

#eval phrase 16
-- let BERNOULLIS = ...;;
partial def BERNOULLIS (n : Int) : IO (Except String (List thm)) := (do
  let (th_0, th_1) ← HolLight.CONJ_PAIR bernoulli
  let b_tm ← ExceptT.mk [[bernoulli]]
  let conv_1 := HolLight.GEN_REWRITE_CONV HolCore.Lib.I [th_1]
  if n <= 0 then return [th_0]
  let bths ← ExceptT.mk (BERNOULLIS (n - 1))
  let tm ← ec (mk_comb b_tm (← ec (mk_small_numeral n)))
  let th ← ExceptT.mk ((HolLight.RAND_CONV num_CONV THENC conv_1 THENC
     HolLight.LAND_CONV (HolLight.RAND_CONV SUM_CONV) THENC
     HolLight.ONCE_DEPTH_CONV HolLight.BETA_CONV THENC
     HolLight.DEPTH_CONV (NUM_RED_CONV ORELSEC BINOM_CONV) THENC
     HolLight.GEN_REWRITE_CONV HolLight.ONCE_DEPTH_CONV bths THENC
     REAL_RAT_REDUCE_CONV) tm)
  return th :: bths
  : ExceptT String IO (List thm)).run
#eval IO.println "<fun>"

#eval phrase 17
-- let BERNOULLI_CONV = ...;;
def BERNOULLI_CONV (tm : term) : IO (Except String thm) := (do
  let b_tm ← ExceptT.mk [[bernoulli]]
  let (op, n) ← ec (dest_comb tm)
  if op != b_tm || !(is_numeral n) then throw "BERNOULLI_CONV"
  ec (HolCore.Lib.hd (← ExceptT.mk (BERNOULLIS (← ec (dest_small_numeral n)))))
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 18
-- let BERNPOLY_CONV = ...;;
def BERNPOLY_CONV (tm : term) : IO (Except String thm) := (do
  let conv_1 := HolLight.REWR_CONV bernpoly THENC SUM_CONV THENC
    HolLight.TOP_DEPTH_CONV HolLight.BETA_CONV THENC NUM_REDUCE_CONV
  let conv_3 := HolLight.ONCE_DEPTH_CONV BINOM_CONV THENC REAL_POLY_CONV
  let n ← ec (dest_small_numeral (← ec (HolCore.Equal.lhand tm)))
  let conv_2 := HolLight.GEN_REWRITE_CONV HolLight.ONCE_DEPTH_CONV (← ExceptT.mk (BERNOULLIS n))
  ExceptT.mk ((conv_1 THENC conv_2 THENC conv_3) tm)
  : ExceptT String IO thm).run
#eval IO.println "<fun>"

#eval phrase 19
-- let SOP_CONV = ...;;
def SOP_CONV_pth : thm := keep "SOP_CONV_pth" fun _ => (do
  prove ([[sum(0..n) (\k. &k pow m) =
        (\p. (p(&n + &1) - p(&0)) / (&m + &1))
        (\x. bernpoly (SUC m) x)]])
   (REWRITE_TAC [SUM_OF_POWERS])
  : ExceptT String IO thm).run
def SOP_CONV : HolCore.Equal.ioconv :=
  HolLight.REWR_CONV SOP_CONV_pth THENC
  HolLight.RAND_CONV (HolLight.ABS_CONV (HolLight.LAND_CONV NUM_SUC_CONV THENC BERNPOLY_CONV)) THENC
  HolLight.TOP_DEPTH_CONV HolLight.BETA_CONV THENC
  REAL_POLY_CONV
#eval (do replay SOP_CONV_pth; IO.println "<fun>" : IO Unit)

#eval phrase 20
-- let SOP_NUM_CONV = ...;;
def SOP_NUM_CONV_pth : thm := keep "SOP_NUM_CONV_pth" fun _ => (do
  prove ([[sum(0..n) (\k. &k pow p) = &m ==> nsum(0..n) (\k. k EXP p) = m]])
   (REWRITE_TAC [REAL_OF_NUM_POW, (← HolLight.GSYM REAL_OF_NUM_SUM_NUMSEG),
                REAL_OF_NUM_EQ])
  : ExceptT String IO thm).run
def SOP_NUM_CONV (tm : term) : IO (Except String thm) := (do
  let th1 ← HolLight.PART_MATCH (HolCore.Equal.lhs o HolCore.Kernel.rand) SOP_NUM_CONV_pth tm
  let th2 ← ExceptT.mk (SOP_CONV (← ec (HolCore.Equal.lhs (← ec (HolCore.Equal.lhand (concl th1))))))
  HolLight.MATCH_MP th1 th2
  : ExceptT String IO thm).run
#eval (do replay SOP_NUM_CONV_pth; IO.println "<fun>" : IO Unit)

/- ------------------------------------------------------------------------- -/
/- The example Bernoulli bragged about.                                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 21
-- time SOP_NUM_CONV `nsum(0..1000) (\k. k EXP 10)`;;
#eval try_ (HolCore.Lib.time SOP_NUM_CONV [[nsum(0..1000) (\k. k EXP 10)]]) HolCore.Printer.string_of_thm

/- ------------------------------------------------------------------------- -/
/- The general formulas for moderate powers.                                 -/
/- ------------------------------------------------------------------------- -/

#eval phrase 22
-- time SOP_CONV `sum(0..n) (\k. &k pow 0)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 0)]]) HolCore.Printer.string_of_thm

#eval phrase 23
-- time SOP_CONV `sum(0..n) (\k. &k pow 1)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 1)]]) HolCore.Printer.string_of_thm

#eval phrase 24
-- time SOP_CONV `sum(0..n) (\k. &k pow 2)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 2)]]) HolCore.Printer.string_of_thm

#eval phrase 25
-- time SOP_CONV `sum(0..n) (\k. &k pow 3)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 3)]]) HolCore.Printer.string_of_thm

#eval phrase 26
-- time SOP_CONV `sum(0..n) (\k. &k pow 4)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 4)]]) HolCore.Printer.string_of_thm

#eval phrase 27
-- time SOP_CONV `sum(0..n) (\k. &k pow 5)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 5)]]) HolCore.Printer.string_of_thm

#eval phrase 28
-- time SOP_CONV `sum(0..n) (\k. &k pow 6)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 6)]]) HolCore.Printer.string_of_thm

#eval phrase 29
-- time SOP_CONV `sum(0..n) (\k. &k pow 7)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 7)]]) HolCore.Printer.string_of_thm

#eval phrase 30
-- time SOP_CONV `sum(0..n) (\k. &k pow 8)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 8)]]) HolCore.Printer.string_of_thm

#eval phrase 31
-- time SOP_CONV `sum(0..n) (\k. &k pow 9)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 9)]]) HolCore.Printer.string_of_thm

#eval phrase 32
-- time SOP_CONV `sum(0..n) (\k. &k pow 10)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 10)]]) HolCore.Printer.string_of_thm

#eval phrase 33
-- time SOP_CONV `sum(0..n) (\k. &k pow 11)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 11)]]) HolCore.Printer.string_of_thm

#eval phrase 34
-- time SOP_CONV `sum(0..n) (\k. &k pow 12)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 12)]]) HolCore.Printer.string_of_thm

#eval phrase 35
-- time SOP_CONV `sum(0..n) (\k. &k pow 13)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 13)]]) HolCore.Printer.string_of_thm

#eval phrase 36
-- time SOP_CONV `sum(0..n) (\k. &k pow 14)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 14)]]) HolCore.Printer.string_of_thm

#eval phrase 37
-- time SOP_CONV `sum(0..n) (\k. &k pow 15)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 15)]]) HolCore.Printer.string_of_thm

#eval phrase 38
-- time SOP_CONV `sum(0..n) (\k. &k pow 16)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 16)]]) HolCore.Printer.string_of_thm

#eval phrase 39
-- time SOP_CONV `sum(0..n) (\k. &k pow 17)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 17)]]) HolCore.Printer.string_of_thm

#eval phrase 40
-- time SOP_CONV `sum(0..n) (\k. &k pow 18)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 18)]]) HolCore.Printer.string_of_thm

#eval phrase 41
-- time SOP_CONV `sum(0..n) (\k. &k pow 19)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 19)]]) HolCore.Printer.string_of_thm

#eval phrase 42
-- time SOP_CONV `sum(0..n) (\k. &k pow 20)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 20)]]) HolCore.Printer.string_of_thm

#eval phrase 43
-- time SOP_CONV `sum(0..n) (\k. &k pow 21)`;;
#eval try_ (HolCore.Lib.time SOP_CONV [[sum(0..n) (\k. &k pow 21)]]) HolCore.Printer.string_of_thm

end Hol100.Bernoulli
