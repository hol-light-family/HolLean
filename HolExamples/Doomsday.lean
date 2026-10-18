/- File: HolExamples/Doomsday.lean
Translation of HOL Light's Examples/doomsday.ml, phrase by phrase.
Part of the Lean4 translation of HOL Light by Chris Walton 2026.
-/
import HolExamples.Common
open HolCore.Kernel Session HolLight.Syntax HolExamples
open scoped HolLight
namespace HolExamples.Doomsday

/- The session's `prove` lifted into `ExceptT String IO`, so tactic scripts
   read as the OCaml does. -/
private unsafe def prove (g : term) (tac : HolCore.Tactics.tactic) : ExceptT String IO thm :=
  ExceptT.mk (Session.prove g tac)

/- Run an `ExceptT String IO thm`, panicking with HOL Light's message on
   failure (as the OCaml toplevel would raise). -/
private unsafe def runThm (m : ExceptT String IO thm) : thm :=
  match unsafeIO m.run with
  | .ok (.ok t) => t
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)

/- ========================================================================= -/
/- Formalization of Conway's Doomsday Algorithm by Claude Opus 4.6           -/
/- ========================================================================= -/

/- ========================================================================= -/
/- Part 1: Calendar primitives                                               -/
/- ========================================================================= -/

/- ------------------------------------------------------------------------- -/
/- Leap year: a year is a leap year iff it is divisible by 4 but not 100,    -/
/- or divisible by 400.                                                      -/
/- ------------------------------------------------------------------------- -/

#eval phrase 1
unsafe def leap_year : thm := keep "leap_year" fun _ => new_definition
 [[leap_year y <=> (4 divides y /\ ~(100 divides y)) \/ 400 divides y]]
#eval leap_year

#eval phrase 2
-- Equivalent characterization using MOD
unsafe def LEAP_YEAR_MOD : thm := keep "LEAP_YEAR_MOD" fun _ => (do
  prove ([[!y. leap_year y <=>
       y MOD 4 = 0 /\ ~(y MOD 100 = 0) \/ y MOD 400 = 0]])
   (GEN_TAC THEN REWRITE_TAC [leap_year, DIVIDES_MOD])
  : ExceptT String IO thm).run
#eval LEAP_YEAR_MOD

#eval phrase 3
/- ------------------------------------------------------------------------- -/
/- Days in each month                                                        -/
/- ------------------------------------------------------------------------- -/
unsafe def days_in_month : thm := keep "days_in_month" fun _ => new_definition
 [[days_in_month y m =
    if m = 1 then 31
    else if m = 2 then (if leap_year y then 29 else 28)
    else if m = 3 then 31
    else if m = 4 then 30
    else if m = 5 then 31
    else if m = 6 then 30
    else if m = 7 then 31
    else if m = 8 then 31
    else if m = 9 then 30
    else if m = 10 then 31
    else if m = 11 then 30
    else if m = 12 then 31
    else 0]]
#eval days_in_month

#eval phrase 4
/- ------------------------------------------------------------------------- -/
/- Days in a year                                                            -/
/- ------------------------------------------------------------------------- -/
unsafe def days_in_year : thm := keep "days_in_year" fun _ => new_definition
 [[days_in_year y = if leap_year y then 366 else 365]]
#eval days_in_year

#eval phrase 5
/- ------------------------------------------------------------------------- -/
/- Valid date predicate                                                      -/
/- ------------------------------------------------------------------------- -/
unsafe def valid_date : thm := keep "valid_date" fun _ => new_definition
 [[valid_date (y,m,d) <=>
    1 <= m /\ m <= 12 /\ 1 <= d /\ d <= days_in_month y m]]
#eval valid_date

#eval phrase 6
/- ------------------------------------------------------------------------- -/
/- Concrete leap year evaluations                                            -/
/- ------------------------------------------------------------------------- -/
unsafe def LEAP_YEAR_2000 : thm := keep "LEAP_YEAR_2000" fun _ => (do
  prove ([[leap_year 2000]])
   (REWRITE_TAC [LEAP_YEAR_MOD] THEN CONV_TAC NUM_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval LEAP_YEAR_2000

#eval phrase 7
unsafe def NOT_LEAP_YEAR_1900 : thm := keep "NOT_LEAP_YEAR_1900" fun _ => (do
  prove ([[~(leap_year 1900)]])
   (REWRITE_TAC [LEAP_YEAR_MOD] THEN CONV_TAC NUM_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval NOT_LEAP_YEAR_1900

#eval phrase 8
unsafe def LEAP_YEAR_2024 : thm := keep "LEAP_YEAR_2024" fun _ => (do
  prove ([[leap_year 2024]])
   (REWRITE_TAC [LEAP_YEAR_MOD] THEN CONV_TAC NUM_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval LEAP_YEAR_2024

#eval phrase 9
unsafe def NOT_LEAP_YEAR_2023 : thm := keep "NOT_LEAP_YEAR_2023" fun _ => (do
  prove ([[~(leap_year 2023)]])
   (REWRITE_TAC [LEAP_YEAR_MOD] THEN CONV_TAC NUM_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval NOT_LEAP_YEAR_2023

#eval phrase 10
unsafe def NOT_LEAP_YEAR_2100 : thm := keep "NOT_LEAP_YEAR_2100" fun _ => (do
  prove ([[~(leap_year 2100)]])
   (REWRITE_TAC [LEAP_YEAR_MOD] THEN CONV_TAC NUM_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval NOT_LEAP_YEAR_2100

#eval phrase 11
unsafe def LEAP_YEAR_2400 : thm := keep "LEAP_YEAR_2400" fun _ => (do
  prove ([[leap_year 2400]])
   (REWRITE_TAC [LEAP_YEAR_MOD] THEN CONV_TAC NUM_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval LEAP_YEAR_2400

#eval phrase 12
-- Useful tactic for 12-month case splits
unsafe def MONTH_CASES_TAC : HolCore.Tactics.tactic :=
  GEN_TAC THEN REWRITE_TAC [IMP_CONJ_ALT, ARITH_RULE [[n <= 12 <=> n < 13]]] THEN
  CONV_TAC EXPAND_CASES_CONV
#eval IO.println "<fun>"

#eval phrase 13
-- Days in month bounds
unsafe def DAYS_IN_MONTH_POS : thm := keep "DAYS_IN_MONTH_POS" fun _ => (do
  prove ([[!y m. 1 <= m /\ m <= 12 ==> 1 <= days_in_month y m]])
   (MONTH_CASES_TAC THEN
    REWRITE_TAC [days_in_month] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval DAYS_IN_MONTH_POS

#eval phrase 14
unsafe def DAYS_IN_MONTH_UPPER : thm := keep "DAYS_IN_MONTH_UPPER" fun _ => (do
  prove ([[!y m. days_in_month y m <= 31]])
   (REPEAT GEN_TAC THEN REWRITE_TAC [days_in_month] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval DAYS_IN_MONTH_UPPER

#eval phrase 15
/- ========================================================================= -/
/- Part 2: Day counting                                                      -/
/- ========================================================================= -/

/- ------------------------------------------------------------------------- -/
/- Cumulative days before a given month within a year                        -/
/- ------------------------------------------------------------------------- -/
unsafe def cumdays_before : thm := keep "cumdays_before" fun _ => new_definition
 [[cumdays_before y m =
    if m <= 1 then 0
    else if m = 2 then 31
    else if m = 3 then (if leap_year y then 60 else 59)
    else if m = 4 then (if leap_year y then 91 else 90)
    else if m = 5 then (if leap_year y then 121 else 120)
    else if m = 6 then (if leap_year y then 152 else 151)
    else if m = 7 then (if leap_year y then 182 else 181)
    else if m = 8 then (if leap_year y then 213 else 212)
    else if m = 9 then (if leap_year y then 244 else 243)
    else if m = 10 then (if leap_year y then 274 else 273)
    else if m = 11 then (if leap_year y then 305 else 304)
    else if m = 12 then (if leap_year y then 335 else 334)
    else (if leap_year y then 366 else 365)]]
#eval cumdays_before

#eval phrase 16
/- ------------------------------------------------------------------------- -/
/- Day of year: ordinal day number within a year (January 1 = 1)             -/
/- ------------------------------------------------------------------------- -/
unsafe def day_of_year : thm := keep "day_of_year" fun _ => new_definition
 [[day_of_year y m d = cumdays_before y m + d]]
#eval day_of_year

#eval phrase 17
-- Cumdays_before is consistent with days_in_month: each step adds one
unsafe def CUMDAYS_BEFORE_STEP : thm := keep "CUMDAYS_BEFORE_STEP" fun _ => (do
  prove ([[!y m. 1 <= m /\ m <= 12 ==>
         cumdays_before y (m + 1) = cumdays_before y m + days_in_month y m]])
   (MONTH_CASES_TAC THEN REWRITE_TAC [cumdays_before, days_in_month] THEN
    ARITH_TAC)
  : ExceptT String IO thm).run
#eval CUMDAYS_BEFORE_STEP

#eval phrase 18
-- Days in year equals sum of all monthly days
unsafe def DAYS_IN_YEAR_SUM : thm := keep "DAYS_IN_YEAR_SUM" fun _ => (do
  prove ([[!y. days_in_year y = cumdays_before y 13]])
   (GEN_TAC THEN REWRITE_TAC [days_in_year, cumdays_before] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    COND_CASES_TAC THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval DAYS_IN_YEAR_SUM

#eval phrase 19
/- ------------------------------------------------------------------------- -/
/- Cumulative days: total days from year 0 to start of year y                -/
/- ------------------------------------------------------------------------- -/
unsafe def cumulative_days : thm := keep "cumulative_days" fun _ => Session.define
 [[cumulative_days 0 = 0 /\
  cumulative_days (SUC y) = cumulative_days y + days_in_year y]]
#eval cumulative_days

#eval phrase 20
/- ------------------------------------------------------------------------- -/
/- Day number: absolute day count from epoch                                 -/
/- ------------------------------------------------------------------------- -/
unsafe def day_number : thm := keep "day_number" fun _ => new_definition
 [[day_number y m d = cumulative_days y + day_of_year y m d]]
#eval day_number

#eval phrase 21
/- ------------------------------------------------------------------------- -/
/- Day of week: 0=Sun, 1=Mon, 2=Tue, 3=Wed, 4=Thu, 5=Fri, 6=Sat              -/
/- Epoch calibration: +5 makes Jan 1, year 0 = Saturday (6)                  -/
/- ------------------------------------------------------------------------- -/
unsafe def day_of_week : thm := keep "day_of_week" fun _ => new_definition
 [[day_of_week y m d = (day_number y m d + 5) MOD 7]]
#eval day_of_week

#eval phrase 22
/- ========================================================================= -/
/- Part 3: Doomsday algorithm definitions                                    -/
/- ========================================================================= -/

/- ------------------------------------------------------------------------- -/
/- Doomsday dates: the day of the month that is a "doomsday" for each        -/
/- month. These all fall on the same day of the week within any given year.  -/
/- ------------------------------------------------------------------------- -/
unsafe def doomsday_date : thm := keep "doomsday_date" fun _ => new_definition
 [[doomsday_date y m =
    if m = 1 then (if leap_year y then 4 else 3)
    else if m = 2 then (if leap_year y then 29 else 28)
    else if m = 3 then 7
    else if m = 4 then 4
    else if m = 5 then 9
    else if m = 6 then 6
    else if m = 7 then 11
    else if m = 8 then 8
    else if m = 9 then 5
    else if m = 10 then 10
    else if m = 11 then 7
    else 12]]
#eval doomsday_date

#eval phrase 23
/- ------------------------------------------------------------------------- -/
/- Century anchor: the doomsday for the first year of each century           -/
/- ------------------------------------------------------------------------- -/
unsafe def century_anchor : thm := keep "century_anchor" fun _ => new_definition
 [[century_anchor c = (5 * (c MOD 4) + 2) MOD 7]]
#eval century_anchor

#eval phrase 24
/- ------------------------------------------------------------------------- -/
/- The Doomsday algorithm: computes the day of the week for the doomsday     -/
/- of any year.                                                              -/
/- ------------------------------------------------------------------------- -/
unsafe def doomsday : thm := keep "doomsday" fun _ => new_definition
 [[doomsday y =
    (century_anchor (y DIV 100) + y MOD 100 + (y MOD 100) DIV 4) MOD 7]]
#eval doomsday

#eval phrase 25
/- ========================================================================= -/
/- Part 4: Key lemmas and main correctness proof                             -/
/- ========================================================================= -/

/- ------------------------------------------------------------------------- -/
/- All doomsday dates are valid                                              -/
/- ------------------------------------------------------------------------- -/
unsafe def VALID_DOOMSDAY : thm := keep "VALID_DOOMSDAY" fun _ => (do
  prove ([[!y m. 1 <= m /\ m <= 12 ==> valid_date(y, m, doomsday_date y m)]])
   (MONTH_CASES_TAC THEN
    REWRITE_TAC [valid_date, doomsday_date, days_in_month] THEN
    ARITH_TAC)
  : ExceptT String IO thm).run
#eval VALID_DOOMSDAY

#eval phrase 26
/- ------------------------------------------------------------------------- -/
/- Helper: equal MOD propagates through addition                             -/
/- ------------------------------------------------------------------------- -/
unsafe def MOD_ADD_EQ_COMPAT : thm := keep "MOD_ADD_EQ_COMPAT" fun _ => (do
  prove ([[!a b c n. a MOD n = b MOD n ==> (c + a) MOD n = (c + b) MOD n]])
   (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM MOD_ADD_MOD))] THEN
    ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval MOD_ADD_EQ_COMPAT

#eval phrase 27
/- ------------------------------------------------------------------------- -/
/- Reference doomsday: the day-of-week value computed from cumulative_days   -/
/- ------------------------------------------------------------------------- -/
unsafe def year_doomsday : thm := keep "year_doomsday" fun _ => new_definition
 [[year_doomsday y = (cumulative_days y + (if leap_year y then 2 else 1)) MOD 7]]
#eval year_doomsday

#eval phrase 28
-- year_doomsday equals day_of_week of any doomsday date
unsafe def YEAR_DOOMSDAY_EQ_DOW : thm := keep "YEAR_DOOMSDAY_EQ_DOW" fun _ => (do
  prove ([[!y m. 1 <= m /\ m <= 12 ==>
         day_of_week y m (doomsday_date y m) = year_doomsday y]])
   (MONTH_CASES_TAC THEN
    REWRITE_TAC [day_of_week, day_number, year_doomsday, day_of_year] THEN
    REWRITE_TAC [cumdays_before, doomsday_date] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM ADD_ASSOC))] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM MOD_ADD_MOD))] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval YEAR_DOOMSDAY_EQ_DOW

#eval phrase 29
/- ------------------------------------------------------------------------- -/
/- Corollary: all doomsday dates in a year fall on the same weekday          -/
/- ------------------------------------------------------------------------- -/
unsafe def DOOMSDAY_SAME_WEEKDAY : thm := keep "DOOMSDAY_SAME_WEEKDAY" fun _ => (do
  prove ([[!y m1 m2. 1 <= m1 /\ m1 <= 12 /\ 1 <= m2 /\ m2 <= 12 ==>
             day_of_week y m1 (doomsday_date y m1) =
             day_of_week y m2 (doomsday_date y m2)]])
   (MESON_TAC [YEAR_DOOMSDAY_EQ_DOW])
  : ExceptT String IO thm).run
#eval DOOMSDAY_SAME_WEEKDAY

#eval phrase 30
/- ========================================================================= -/
/- Part 5: Main correctness theorem -- year_doomsday y = doomsday y          -/
/- ========================================================================= -/

/- The proof strategy: decompose y = 100*c + t where t < 100.                -/
/- Show doomsday and year_doomsday satisfy the same recurrence within a      -/
/- century, then verify agreement at century boundaries using 400-year       -/
/- periodicity.                                                              -/

/- ------------------------------------------------------------------------- -/
/- Year-to-year step for year_doomsday (mod 7 shift)                         -/
/- ------------------------------------------------------------------------- -/
unsafe def CUMULATIVE_DAYS_SUC : thm := keep "CUMULATIVE_DAYS_SUC" fun _ => (do
  prove ([[!y. cumulative_days (SUC y) = cumulative_days y + days_in_year y]])
   (REWRITE_TAC [cumulative_days])
  : ExceptT String IO thm).run
#eval CUMULATIVE_DAYS_SUC

#eval phrase 31
/- ------------------------------------------------------------------------- -/
/- The main theorem: year_doomsday y = doomsday y                            -/
/-                                                                           -/
/- We prove this by strong induction on y, verifying base cases and          -/
/- showing the formula is preserved across year boundaries.                  -/
/- ------------------------------------------------------------------------- -/

/- First, prove it for years 0-399 computationally.                          -/
/- We do this by proving the formula for each year in a 400-year block       -/
/- matches the year_doomsday value.                                          -/

/- Key lemma: leap year structure within a century -/
/- For years 100*c + t where 0 < t < 100: leap_year iff 4 | t -/
unsafe def LEAP_YEAR_IN_CENTURY : thm := keep "LEAP_YEAR_IN_CENTURY" fun _ => (do
  prove ([[!c t. 0 < t /\ t < 100 ==> (leap_year (100 * c + t) <=> t MOD 4 = 0)]])
   (REPEAT STRIP_TAC THEN REWRITE_TAC [LEAP_YEAR_MOD] THEN
    ASM_SIMP_TAC [MOD_MULT_ADD, LE_1, MOD_LT] THEN
    REWRITE_TAC [(← ExceptT.mk (ARITH_RULE [[100 * c = 4 * (25 * c)]])), MOD_MULT_ADD] THEN
    REWRITE_TAC [MULT_ASSOC, ARITH, (← ExceptT.mk (TAUT [[(p \/ q <=> p) <=> q ==> p]]))] THEN
    REWRITE_TAC [(← ExceptT.mk (HolLight.GSYM DIVIDES_MOD))] THEN MATCH_MP_TAC (← ExceptT.mk (NUMBER_RULE
     [[f divides fh /\ f divides h ==> fh divides h * c + t ==> f divides t]])) THEN
    REWRITE_TAC [DIVIDES_MOD] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval LEAP_YEAR_IN_CENTURY

#eval phrase 32
/- ------------------------------------------------------------------------- -/
/- Recurrence for year_doomsday                                              -/
/- ------------------------------------------------------------------------- -/
unsafe def YEAR_DOOMSDAY_STEP : thm := keep "YEAR_DOOMSDAY_STEP" fun _ => (do
  prove ([[!y. year_doomsday(SUC y) =
       (year_doomsday y + (if leap_year(SUC y) then 2 else 1)) MOD 7]])
   (GEN_TAC THEN
    REWRITE_TAC [year_doomsday, CUMULATIVE_DAYS_SUC, days_in_year] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    COND_CASES_TAC THEN REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    REPEAT (MATCH_MP_TAC MOD_ADD_EQ_COMPAT) THEN
    CONV_TAC NUM_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval YEAR_DOOMSDAY_STEP

#eval phrase 33
/- ------------------------------------------------------------------------- -/
/- Within-century step for the doomsday formula                              -/
/- For 0 < t < 100: doomsday increments by the same leap offset              -/
/- ------------------------------------------------------------------------- -/
unsafe def DOOMSDAY_STEP : thm := keep "DOOMSDAY_STEP" fun _ => (do
  prove ([[!c t. t < 99 ==>
         doomsday(100 * c + SUC t) =
         (doomsday(100 * c + t) + (if SUC t MOD 4 = 0 then 2 else 1)) MOD 7]])
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [doomsday, century_anchor] THEN
    SUBGOAL_THEN ([[SUC t < 100 /\ t < 100]]) STRIP_ASSUME_TAC THENL
    [ASM_ARITH_TAC, ALL_TAC] THEN
    ASM_SIMP_TAC [DIV_MULT_ADD, MOD_MULT_ADD, (← ExceptT.mk (ARITH_RULE [[~(100 = 0)]])),
                 DIV_LT, MOD_LT, ADD_CLAUSES] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval DOOMSDAY_STEP

#eval phrase 34
/- ------------------------------------------------------------------------- -/
/- Within a century: if the base case matches, the entire century matches    -/
/- ------------------------------------------------------------------------- -/
unsafe def WITHIN_CENTURY : thm := keep "WITHIN_CENTURY" fun _ => (do
  prove ([[!c. year_doomsday(100 * c) = doomsday(100 * c) ==>
       !t. t < 100 ==> year_doomsday(100 * c + t) = doomsday(100 * c + t)]])
   (GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
    [REWRITE_TAC [ADD_CLAUSES] THEN ASM_REWRITE_TAC [],
     DISCH_TAC THEN
     SUBGOAL_THEN ([[year_doomsday(100 * c + t) = doomsday(100 * c + t)]])
       ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC, ALL_TAC] THEN
     SUBGOAL_THEN ([[100 * c + SUC t = SUC(100 * c + t)]]) SUBST1_TAC THENL
     [ARITH_TAC, ALL_TAC] THEN
     ASM_REWRITE_TAC [YEAR_DOOMSDAY_STEP] THEN
     SUBGOAL_THEN ([[SUC(100 * c + t) = 100 * c + SUC t]]) SUBST1_TAC THENL
     [ARITH_TAC, ALL_TAC] THEN
     SUBGOAL_THEN ([[t < 99]]) ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
     ASM_SIMP_TAC [DOOMSDAY_STEP] THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[c:num]], [[SUC t]] ] LEAP_YEAR_IN_CENTURY)) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC, DISCH_TAC THEN ASM_REWRITE_TAC []]])
  : ExceptT String IO thm).run
#eval WITHIN_CENTURY

#eval phrase 35
/- ------------------------------------------------------------------------- -/
/- Century base cases: computed iteratively using the recurrence             -/
/- ------------------------------------------------------------------------- -/
unsafe def YEAR_DOOMSDAY_0 : thm := keep "YEAR_DOOMSDAY_0" fun _ => (do
  prove ([[year_doomsday 0 = 2]])
   (REWRITE_TAC [year_doomsday, cumulative_days, LEAP_YEAR_MOD] THEN
    CONV_TAC NUM_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval YEAR_DOOMSDAY_0

#eval phrase 36
unsafe def DOOMSDAY_0 : thm := keep "DOOMSDAY_0" fun _ => (do
  prove ([[doomsday 0 = 2]])
   (REWRITE_TAC [doomsday, century_anchor] THEN CONV_TAC NUM_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval DOOMSDAY_0

#eval phrase 37
-- Iterative computation of year_doomsday at century boundaries
unsafe def compute_year_doomsday (n : Int) : thm :=
  let rec go (k : Int) (th : thm) : thm :=
    if k >= n then th
    else
      let th' : thm := runThm (do
        let k_tm ← ExceptT.mk (pure (mk_small_numeral k))
        let step_th ← ExceptT.mk (HolLight.SPEC k_tm YEAR_DOOMSDAY_STEP)
        HolLight.CONV_RULE (
          HolLight.LAND_CONV (HolLight.RAND_CONV NUM_SUC_CONV) THENC
          HolLight.RAND_CONV (
            HolLight.ONCE_DEPTH_CONV NUM_SUC_CONV THENC
            Session.REWRITE_CONV [th, LEAP_YEAR_MOD] THENC
            NUM_REDUCE_CONV)) step_th)
      go (k + 1) th'
  go 0 YEAR_DOOMSDAY_0
#eval IO.println "<fun>"

#eval phrase 38
unsafe def YEAR_DOOMSDAY_100 : thm := keep "YEAR_DOOMSDAY_100" fun _ => compute_year_doomsday 100
#eval YEAR_DOOMSDAY_100

#eval phrase 39
unsafe def YEAR_DOOMSDAY_200 : thm := keep "YEAR_DOOMSDAY_200" fun _ => compute_year_doomsday 200
#eval YEAR_DOOMSDAY_200

#eval phrase 40
unsafe def YEAR_DOOMSDAY_300 : thm := keep "YEAR_DOOMSDAY_300" fun _ => compute_year_doomsday 300
#eval YEAR_DOOMSDAY_300

#eval phrase 41
unsafe def YEAR_DOOMSDAY_400 : thm := keep "YEAR_DOOMSDAY_400" fun _ => compute_year_doomsday 400
#eval YEAR_DOOMSDAY_400

#eval phrase 42
-- Doomsday algorithm values at century boundaries
unsafe def DOOMSDAY_100 : thm := keep "DOOMSDAY_100" fun _ => (do
  prove ([[doomsday 100 = 0]])
   (REWRITE_TAC [doomsday, century_anchor] THEN CONV_TAC NUM_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval DOOMSDAY_100

#eval phrase 43
unsafe def DOOMSDAY_200 : thm := keep "DOOMSDAY_200" fun _ => (do
  prove ([[doomsday 200 = 5]])
   (REWRITE_TAC [doomsday, century_anchor] THEN CONV_TAC NUM_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval DOOMSDAY_200

#eval phrase 44
unsafe def DOOMSDAY_300 : thm := keep "DOOMSDAY_300" fun _ => (do
  prove ([[doomsday 300 = 3]])
   (REWRITE_TAC [doomsday, century_anchor] THEN CONV_TAC NUM_REDUCE_CONV)
  : ExceptT String IO thm).run
#eval DOOMSDAY_300

#eval phrase 45
/- ------------------------------------------------------------------------- -/
/- 400-year periodicity for both doomsday and year_doomsday                  -/
/- ------------------------------------------------------------------------- -/
unsafe def LEAP_YEAR_400_PERIOD : thm := keep "LEAP_YEAR_400_PERIOD" fun _ => (do
  prove ([[!y. leap_year(y + 400) <=> leap_year y]])
   (GEN_TAC THEN REWRITE_TAC [LEAP_YEAR_MOD] THEN
    REWRITE_TAC [(← ExceptT.mk (ARITH_RULE [[y + 400 = y + 4 * 100]])), MOD_MULT_ADD] THEN
    REWRITE_TAC [(← ExceptT.mk (ARITH_RULE [[4 * 100 = 400 * 1]])), MOD_MULT_ADD])
  : ExceptT String IO thm).run
#eval LEAP_YEAR_400_PERIOD

#eval phrase 46
unsafe def DOOMSDAY_400_PERIOD : thm := keep "DOOMSDAY_400_PERIOD" fun _ => (do
  prove ([[!y. doomsday(y + 400) = doomsday y]])
   (GEN_TAC THEN REWRITE_TAC [doomsday, century_anchor] THEN
    REWRITE_TAC [(← ExceptT.mk (ARITH_RULE [[y + 400 = 100 * 4 + y]])), MOD_MULT_ADD] THEN
    SIMP_TAC [DIV_MULT_ADD, (← ExceptT.mk (ARITH_RULE [[~(100 = 0)]]))] THEN
    REWRITE_TAC [(← ExceptT.mk (ARITH_RULE [[4 + y = 4 * 1 + y]])), MOD_MULT_ADD])
  : ExceptT String IO thm).run
#eval DOOMSDAY_400_PERIOD

#eval phrase 47
unsafe def YEAR_DOOMSDAY_400_PERIOD : thm := keep "YEAR_DOOMSDAY_400_PERIOD" fun _ => (do
  prove ([[!y. year_doomsday(y + 400) = year_doomsday y]])
   (INDUCT_TAC THENL
    [REWRITE_TAC [ADD_CLAUSES, YEAR_DOOMSDAY_400, YEAR_DOOMSDAY_0],
     REWRITE_TAC [(← ExceptT.mk (ARITH_RULE [[SUC y + 400 = SUC(y + 400)]]))] THEN
     REWRITE_TAC [YEAR_DOOMSDAY_STEP] THEN
     SUBGOAL_THEN ([[leap_year(SUC(y + 400)) <=> leap_year(SUC y)]]) SUBST1_TAC THENL
     [REWRITE_TAC [(← ExceptT.mk (ARITH_RULE [[SUC(y + 400) = SUC y + 400]]))] THEN
      REWRITE_TAC [LEAP_YEAR_400_PERIOD],
      ASM_REWRITE_TAC []]])
  : ExceptT String IO thm).run
#eval YEAR_DOOMSDAY_400_PERIOD

#eval phrase 48
/- ------------------------------------------------------------------------- -/
/- Century base case for all c: year_doomsday(100*c) = doomsday(100*c)       -/
/- ------------------------------------------------------------------------- -/
unsafe def CENTURY_BASE_ALL : thm := keep "CENTURY_BASE_ALL" fun _ => (do
  prove ([[!c. year_doomsday(100 * c) = doomsday(100 * c)]])
   (GEN_TAC THEN
    MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[c:num]], [[4]] ] DIVISION)) THEN ANTS_TAC THENL
    [ARITH_TAC, ALL_TAC] THEN
    ABBREV_TAC [[q = c DIV 4]] THEN ABBREV_TAC [[r = c MOD 4]] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN ([[100 * c = 400 * q + 100 * r]]) SUBST1_TAC THENL
    [ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN
    SUBGOAL_THEN ([[r < 4]]) MP_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    SPEC_TAC ([[r:num]], [[r:num]]) THEN SPEC_TAC ([[q:num]], [[q:num]]) THEN
    INDUCT_TAC THENL
    [REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC [YEAR_DOOMSDAY_0, YEAR_DOOMSDAY_100, YEAR_DOOMSDAY_200,
                  YEAR_DOOMSDAY_300, DOOMSDAY_0, DOOMSDAY_100, DOOMSDAY_200,
                  DOOMSDAY_300],
     REPEAT STRIP_TAC THEN
     REWRITE_TAC [(← ExceptT.mk (ARITH_RULE [[400 * SUC q + x = (400 * q + x) + 400]]))] THEN
     REWRITE_TAC [YEAR_DOOMSDAY_400_PERIOD, DOOMSDAY_400_PERIOD] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC []])
  : ExceptT String IO thm).run
#eval CENTURY_BASE_ALL

#eval phrase 49
/- ========================================================================= -/
/- THE MAIN THEOREM: year_doomsday y = doomsday y for all y                  -/
/- ========================================================================= -/
unsafe def YEAR_DOOMSDAY_EQ_DOOMSDAY : thm := keep "YEAR_DOOMSDAY_EQ_DOOMSDAY" fun _ => (do
  prove ([[!y. year_doomsday y = doomsday y]])
   (GEN_TAC THEN
    MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[y:num]], [[100]] ] DIVISION)) THEN ANTS_TAC THENL
    [ARITH_TAC, ALL_TAC] THEN
    ABBREV_TAC [[c = y DIV 100]] THEN ABBREV_TAC [[t = y MOD 100]] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN ([[y = 100 * c + t]]) SUBST1_TAC THENL
    [ASM_ARITH_TAC, ALL_TAC] THEN
    MP_TAC (← ExceptT.mk (HolLight.SPEC ([[c:num]]) WITHIN_CENTURY)) THEN
    DISCH_THEN (fun th => HolLight.tactic_of do
      pure (MP_TAC (← HolLight.MP th (← ExceptT.mk (HolLight.SPEC ([[c:num]]) CENTURY_BASE_ALL))))) THEN
    DISCH_THEN (MP_TAC o HolLight.SPEC ([[t:num]])) THEN ASM_REWRITE_TAC [])
  : ExceptT String IO thm).run
#eval YEAR_DOOMSDAY_EQ_DOOMSDAY

#eval phrase 50
/- ========================================================================= -/
/- DOOMSDAY_CORRECT: The Doomsday algorithm gives the correct day of week    -/
/- for the doomsday date in every month of every year.                       -/
/- ========================================================================= -/
unsafe def DOOMSDAY_CORRECT : thm := keep "DOOMSDAY_CORRECT" fun _ => (do
  prove ([[!y m. 1 <= m /\ m <= 12 ==>
         day_of_week y m (doomsday_date y m) = doomsday y]])
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[y:num]], [[m:num]] ] YEAR_DOOMSDAY_EQ_DOW)) THEN
    ASM_REWRITE_TAC [YEAR_DOOMSDAY_EQ_DOOMSDAY])
  : ExceptT String IO thm).run
#eval DOOMSDAY_CORRECT

#eval phrase 51
/- ========================================================================= -/
/- Part 6: Corollaries and applications                                      -/
/- ========================================================================= -/

/- ------------------------------------------------------------------------- -/
/- Day-of-week shift: adding days shifts the weekday                         -/
/- ------------------------------------------------------------------------- -/
unsafe def DOW_SHIFT : thm := keep "DOW_SHIFT" fun _ => (do
  prove ([[!y m d1 d2. day_of_week y m (d1 + d2) = (day_of_week y m d1 + d2) MOD 7]])
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [day_of_week, day_number, day_of_year] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval DOW_SHIFT

#eval phrase 52
/- ------------------------------------------------------------------------- -/
/- Day-of-week from doomsday: for any date on or after the doomsday date     -/
/- ------------------------------------------------------------------------- -/
unsafe def DOW_FROM_DOOMSDAY : thm := keep "DOW_FROM_DOOMSDAY" fun _ => (do
  prove ([[!y m d. 1 <= m /\ m <= 12 /\ doomsday_date y m <= d ==>
           day_of_week y m d = (doomsday y + d - doomsday_date y m) MOD 7]])
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN ([[d = doomsday_date y m + (d - doomsday_date y m)]])
    SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [DOW_SHIFT] THEN
    ASM_SIMP_TAC [DOOMSDAY_CORRECT] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC)
  : ExceptT String IO thm).run
#eval DOW_FROM_DOOMSDAY

#eval phrase 53
/- ------------------------------------------------------------------------- -/
/- Cumulative days 400-year periodicity (mod 7)                              -/
/- ------------------------------------------------------------------------- -/
unsafe def compute_cumdays (n : Int) : thm :=
  let rec go (k : Int) (th : thm) : thm :=
    if k >= n then th
    else
      let th' : thm := runThm (do
        let k_tm ← ExceptT.mk (pure (mk_small_numeral k))
        let step_th ← ExceptT.mk (HolLight.SPEC k_tm CUMULATIVE_DAYS_SUC)
        HolLight.CONV_RULE (
          HolLight.LAND_CONV (HolLight.RAND_CONV NUM_SUC_CONV) THENC
          HolLight.RAND_CONV (
            HolLight.ONCE_DEPTH_CONV NUM_SUC_CONV THENC
            Session.REWRITE_CONV [th, days_in_year, LEAP_YEAR_MOD] THENC
            NUM_REDUCE_CONV)) step_th)
      go (k + 1) th'
  go 0 (runThm (HolLight.CONJUNCT1 cumulative_days))
#eval IO.println "<fun>"

#eval phrase 54
unsafe def CUMDAYS_400 : thm := keep "CUMDAYS_400" fun _ => compute_cumdays 400
#eval CUMDAYS_400

#eval phrase 55
unsafe def CUMULATIVE_DAYS_400_MOD7 : thm := keep "CUMULATIVE_DAYS_400_MOD7" fun _ => (do
  prove ([[!y. cumulative_days(y + 400) MOD 7 = cumulative_days y MOD 7]])
   (INDUCT_TAC THENL
    [REWRITE_TAC [ADD_CLAUSES, CUMDAYS_400, cumulative_days] THEN
     CONV_TAC NUM_REDUCE_CONV,
     REWRITE_TAC [(← ExceptT.mk (ARITH_RULE [[SUC y + 400 = SUC(y + 400)]]))] THEN
     REWRITE_TAC [CUMULATIVE_DAYS_SUC, days_in_year] THEN
     SUBGOAL_THEN ([[leap_year(y + 400) <=> leap_year y]])
       (fun th => REWRITE_TAC [th]) THENL
     [REWRITE_TAC [LEAP_YEAR_400_PERIOD], ALL_TAC] THEN
     COND_CASES_TAC THEN REWRITE_TAC [] THEN
     CONV_TAC MOD_DOWN_CONV THEN
     ONCE_REWRITE_TAC [ADD_SYM] THEN
     MATCH_MP_TAC MOD_ADD_EQ_COMPAT THEN
     ASM_REWRITE_TAC []])
  : ExceptT String IO thm).run
#eval CUMULATIVE_DAYS_400_MOD7

#eval phrase 56
/- ------------------------------------------------------------------------- -/
/- 400-year periodicity for the full day_of_week function                    -/
/- ------------------------------------------------------------------------- -/
unsafe def DAY_OF_WEEK_400_PERIOD : thm := keep "DAY_OF_WEEK_400_PERIOD" fun _ => (do
  prove ([[!y m d. day_of_week (y + 400) m d = day_of_week y m d]])
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [day_of_week, day_number, day_of_year] THEN
    SUBGOAL_THEN ([[cumdays_before (y + 400) m = cumdays_before y m]])
    SUBST1_TAC THENL
     [REWRITE_TAC [cumdays_before, LEAP_YEAR_400_PERIOD], ALL_TAC] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    MATCH_MP_TAC MOD_ADD_EQ_COMPAT THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    MATCH_MP_TAC MOD_ADD_EQ_COMPAT THEN
    REWRITE_TAC [CUMULATIVE_DAYS_400_MOD7])
  : ExceptT String IO thm).run
#eval DAY_OF_WEEK_400_PERIOD

#eval phrase 57
/- ========================================================================= -/
/- Part 7: Full doomsday algorithm for any date                              -/
/- ========================================================================= -/

/- ------------------------------------------------------------------------- -/
/- Day-of-week is periodic with period 7 in the day argument                 -/
/- ------------------------------------------------------------------------- -/
unsafe def DOW_PERIOD : thm := keep "DOW_PERIOD" fun _ => (do
  prove ([[!y m d k. day_of_week y m (d + 7 * k) = day_of_week y m d]])
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [day_of_week, day_number, day_of_year] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    MATCH_MP_TAC MOD_ADD_EQ_COMPAT THEN
    ONCE_REWRITE_TAC [(← ExceptT.mk (ARITH_RULE
      [[c + b + d + 7 * k = 7 * k + (c + b + d)]]))] THEN
    REWRITE_TAC [MOD_MULT_ADD])
  : ExceptT String IO thm).run
#eval DOW_PERIOD

#eval phrase 58
/- ------------------------------------------------------------------------- -/
/- Doomsday date bounds: all doomsday dates are between 1 and 29             -/
/- ------------------------------------------------------------------------- -/
unsafe def DOOMSDAY_DATE_BOUND : thm := keep "DOOMSDAY_DATE_BOUND" fun _ => (do
  prove ([[!y m. 1 <= m /\ m <= 12 ==>
         1 <= doomsday_date y m /\ doomsday_date y m <= 29]])
   (MONTH_CASES_TAC THEN REWRITE_TAC [doomsday_date] THEN ARITH_TAC)
  : ExceptT String IO thm).run
#eval DOOMSDAY_DATE_BOUND

#eval phrase 59
/- ------------------------------------------------------------------------- -/
/- The full doomsday algorithm: computes day of week for any valid date.     -/
/-                                                                           -/
/- Conway's mental process:                                                  -/
/-   1. Compute the year's doomsday from century anchor + year offset        -/
/-   2. Look up the doomsday date for the month (4/4, 6/6, 8/8, etc.)        -/
/-   3. Count the offset from the doomsday date to the target day            -/
/-   4. Add that offset (mod 7) to the year's doomsday                       -/
/-                                                                           -/
/- The +35 (= 5*7) is a safety offset to avoid natural number underflow      -/
/- when the target day is before the doomsday date in the month.             -/
/- ------------------------------------------------------------------------- -/
unsafe def doomsday_algorithm : thm := keep "doomsday_algorithm" fun _ => new_definition
 [[doomsday_algorithm y m d =
    (doomsday y + d + 35 - doomsday_date y m) MOD 7]]
#eval doomsday_algorithm

#eval phrase 60
/- ------------------------------------------------------------------------- -/
/- THE FULL CORRECTNESS THEOREM: the doomsday algorithm computes the         -/
/- correct day of the week for every valid Gregorian date.                   -/
/- ------------------------------------------------------------------------- -/
unsafe def DOOMSDAY_ALGORITHM_CORRECT : thm := keep "DOOMSDAY_ALGORITHM_CORRECT" fun _ => (do
  prove ([[!y m d. valid_date(y,m,d) ==>
           doomsday_algorithm y m d = day_of_week y m d]])
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [doomsday_algorithm] THEN
    SUBGOAL_THEN ([[day_of_week y m d = day_of_week y m (d + 35)]]) SUBST1_TAC THENL
    [ONCE_REWRITE_TAC [(← ExceptT.mk (ARITH_RULE [[d + 35 = d + 7 * 5]]))] THEN
     REWRITE_TAC [DOW_PERIOD], ALL_TAC] THEN
    MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[y:num]], [[m:num]], [[d + 35]] ] DOW_FROM_DOOMSDAY)) THEN
    ANTS_TAC THENL
    [RULE_ASSUM_TAC (REWRITE_RULE [valid_date]) THEN
     MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[y:num]], [[m:num]] ] DOOMSDAY_DATE_BOUND)) THEN
     ASM_ARITH_TAC,
     DISCH_THEN SUBST1_TAC THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN
     MP_TAC (← ExceptT.mk (HolLight.SPECL [ [[y:num]], [[m:num]] ] DOOMSDAY_DATE_BOUND)) THEN
     RULE_ASSUM_TAC (REWRITE_RULE [valid_date]) THEN
     ASM_ARITH_TAC])
  : ExceptT String IO thm).run
#eval DOOMSDAY_ALGORITHM_CORRECT

#eval phrase 61
/- ========================================================================= -/
/- Part 8: Enumerated day type with named output and evaluation              -/
/- ========================================================================= -/
unsafe def day_INDUCT_day_RECURSION : thm × thm := keep "day_types" fun _ =>
  match unsafeIO (define_type
    "day = Sunday | Monday | Tuesday | Wednesday | Thursday | Friday | Saturday") with
  | .ok (.ok p) => p
  | .ok (.error e) => panic! e
  | .error e => panic! (toString e)
unsafe def day_INDUCT : thm := day_INDUCT_day_RECURSION.1
unsafe def day_RECURSION : thm := day_INDUCT_day_RECURSION.2
#eval (do IO.println (← HolCore.Printer.string_of_thm day_INDUCT)
          IO.println (← HolCore.Printer.string_of_thm day_RECURSION) : IO Unit)

#eval phrase 62
/- Conway's names:
 * Noneday Oneday Twosday Treblesday Foursday Fiveday Sixturday
 -/
unsafe def dayname : thm := keep "dayname" fun _ => new_definition
 [[dayname n = if n = 0 then Sunday
              else if n = 1 then Monday
              else if n = 2 then Tuesday
              else if n = 3 then Wednesday
              else if n = 4 then Thursday
              else if n = 5 then Friday
              else Saturday]]
#eval dayname

#eval phrase 63
unsafe def doomsday_day : thm := keep "doomsday_day" fun _ => new_definition
 [[doomsday_day y m d = dayname(doomsday_algorithm y m d)]]
#eval doomsday_day

#eval phrase 64
unsafe def DOOMSDAY_DAY_CORRECT : thm := keep "DOOMSDAY_DAY_CORRECT" fun _ => (do
  prove ([[!y m d. valid_date(y,m,d)
           ==> doomsday_day y m d = dayname(day_of_week y m d)]])
   (REWRITE_TAC [doomsday_day] THEN
    MESON_TAC [DOOMSDAY_ALGORITHM_CORRECT])
  : ExceptT String IO thm).run
#eval DOOMSDAY_DAY_CORRECT

#eval phrase 65
/- ------------------------------------------------------------------------- -/
/- Evaluation conversion for doomsday_day.                                   -/
/- Usage: DOOMSDAY_DAY_CONV `doomsday_day 1966 12 14`                        -/
/-   |- doomsday_day 1966 12 14 = Wednesday                                  -/
/- ------------------------------------------------------------------------- -/
unsafe def DOOMSDAY_DAY_CONV : term → IO (Except String thm) :=
  let csE : IO (Except String HolMath.Compute.compset) := do
    match ← Session.bool_compset with
    | .error e => return .error e
    | .ok cs =>
      match ← Session.set_skip cs ([[COND:bool->num->num->num]]) (some 1) with
      | .error e => return .error e
      | .ok _ =>
      match ← Session.set_skip cs ([[COND:bool->day->day->day]]) (some 1) with
      | .error e => return .error e
      | .ok _ =>
      match ← HolMath.CalcNum.num_red_conv_list
          NUM_SUC_CONV NUM_PRE_CONV NUM_FACT_CONV NUM_LT_CONV NUM_LE_CONV
          NUM_GT_CONV NUM_GE_CONV NUM_EQ_CONV NUM_EVEN_CONV NUM_ODD_CONV
          NUM_ADD_CONV NUM_SUB_CONV NUM_MULT_CONV NUM_EXP_CONV NUM_DIV_CONV
          NUM_MOD_CONV NUM_MAX_CONV NUM_MIN_CONV with
      | .error e => return .error e
      | .ok redList =>
      match ← HolMath.CalcNum.num_compute_add_convs redList Session.add_conv cs with
      | .error e => return .error e
      | .ok _ =>
      match ← Session.add_thms [doomsday_day, doomsday_algorithm, doomsday, century_anchor,
                    doomsday_date, LEAP_YEAR_MOD, dayname] cs with
      | .error e => return .error e
      | .ok _ => return .ok cs
  fun tm => do
    match ← csE with
    | .error e => return .error e
    | .ok cs => Session.WEAK_CBV_CONV cs tm
#eval IO.println "<fun>"

#eval phrase 66
/- ------------------------------------------------------------------------- -/
/- Famous dates with named days                                              -/
/- ------------------------------------------------------------------------- -/
unsafe def DAY_1776_7_4 : thm := keep "DAY_1776_7_4" fun _ => (do
  prove ([[doomsday_day 1776 7 4 = Thursday]])
   (CONV_TAC DOOMSDAY_DAY_CONV)
  : ExceptT String IO thm).run
#eval DAY_1776_7_4

#eval phrase 67
unsafe def DAY_1969_7_20 : thm := keep "DAY_1969_7_20" fun _ => (do
  prove ([[doomsday_day 1969 7 20 = Sunday]])
   (CONV_TAC DOOMSDAY_DAY_CONV)
  : ExceptT String IO thm).run
#eval DAY_1969_7_20

#eval phrase 68
unsafe def DAY_1989_11_9 : thm := keep "DAY_1989_11_9" fun _ => (do
  prove ([[doomsday_day 1989 11 9 = Thursday]])
   (CONV_TAC DOOMSDAY_DAY_CONV)
  : ExceptT String IO thm).run
#eval DAY_1989_11_9

#eval phrase 69
unsafe def DAY_2000_1_1 : thm := keep "DAY_2000_1_1" fun _ => (do
  prove ([[doomsday_day 2000 1 1 = Saturday]])
   (CONV_TAC DOOMSDAY_DAY_CONV)
  : ExceptT String IO thm).run
#eval DAY_2000_1_1

#eval phrase 70
unsafe def DAY_2026_3_26 : thm := keep "DAY_2026_3_26" fun _ => (do
  prove ([[doomsday_day 2026 3 26 = Thursday]])
   (CONV_TAC DOOMSDAY_DAY_CONV)
  : ExceptT String IO thm).run
#eval DAY_2026_3_26

#eval phrase 71
unsafe def DAY_1966_12_14 : thm := keep "DAY_1966_12_14" fun _ => (do
  prove ([[doomsday_day 1966 12 14 = Wednesday]])
   (CONV_TAC DOOMSDAY_DAY_CONV)
  : ExceptT String IO thm).run
#eval DAY_1966_12_14

#eval phrase 72
unsafe def DAY_2005_03_25 : thm := keep "DAY_2005_03_25" fun _ => (do
  prove ([[doomsday_day 2005 03 25 = Friday]])
   (CONV_TAC DOOMSDAY_DAY_CONV)
  : ExceptT String IO thm).run
#eval DAY_2005_03_25

end HolExamples.Doomsday
