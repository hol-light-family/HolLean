/- File: Arith.lean
Natural number arithmetic.
John Harrison, University of Cambridge Computer Laboratory
Original (c) Copyright, University of Cambridge 1998
Original (c) Copyright, John Harrison 1998-2007
Original (c) Copyright, Marco Maggesi 2015
Original (c) Copyright, Andrea Gabrielli, Marco Maggesi 2017-2018
Original (c) Copyright, Mario Carneiro 2020
Lean4 translation by Chris Walton 2026 -/

import HolCore.Bool
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics
import HolCore.Itab
import HolCore.Simp
import HolCore.Parser
import HolCore.Printer
import HolCore.Theorems
import HolCore.IndDefs
import HolCore.Classic
import HolCore.Canon
import HolCore.Meson
import HolMath.Nums
import HolMath.Recursion
import HolMath.Base

namespace HolMath.Arith

/- ---------------------------------------------------------------------- -/
/- Note: all the following proofs are intuitionistic and intensional,     -/
/- except for the least number principle num_WOP.                         -/
/- (And except the arith rewrites at the end; these could be done that    -/
/- way but they use the conditional anyway.) In fact, one could very      -/
/- easily write a "decider" returning P \/ ~P for quantifier-free P.      -/
/- ---------------------------------------------------------------------- -/

/-- Register `arith.ml`'s infix operators (run before any arithmetic term is
    parsed). -/
def setupArithInfixes : IO Unit := do
  HolCore.Printer.parse_as_infix ("<", (12, "right"))
  HolCore.Printer.parse_as_infix ("<=", (12, "right"))
  HolCore.Printer.parse_as_infix (">", (12, "right"))
  HolCore.Printer.parse_as_infix (">=", (12, "right"))
  HolCore.Printer.parse_as_infix ("+", (16, "right"))
  HolCore.Printer.parse_as_infix ("-", (18, "left"))
  HolCore.Printer.parse_as_infix ("*", (20, "right"))
  HolCore.Printer.parse_as_infix ("EXP", (24, "left"))
  HolCore.Printer.parse_as_infix ("DIV", (22, "left"))
  HolCore.Printer.parse_as_infix ("MOD", (22, "left"))

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/-- The `arith.ml` theorems, part 1: PRE, addition, and the bitwise numeral
    representation. -/
structure ArithThms1 where
  PRE              : thm
  ADD              : thm
  ADD_0            : thm
  ADD_SUC          : thm
  ADD_CLAUSES      : thm
  ADD_SYM          : thm
  ADD_ASSOC        : thm
  ADD_AC           : thm
  ADD_EQ_0         : thm
  EQ_ADD_LCANCEL   : thm
  EQ_ADD_RCANCEL   : thm
  EQ_ADD_LCANCEL_0 : thm
  EQ_ADD_RCANCEL_0 : thm
  BIT0             : thm
  BIT1             : thm
  BIT0_THM         : thm
  BIT1_THM         : thm
  ONE              : thm
  TWO              : thm
  ADD1             : thm
  deriving Inhabited

@[nospecialize]
def setupArith1 [HolBase] (N : HolMath.Nums.NumsThms)
    (MESON_TAC : List thm → tactic)
    (new_recursive_definition' : thm → term → IO (Except String thm)) :
    ExceptT String IO ArithThms1 := do
  let new_recursive_definition (ax : thm) (s : String) : ExceptT String IO thm := do
    new_recursive_definition' ax (← q s)
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { num_RECURSION, NOT_SUC, SUC_INJ, BIT0_DEF, BIT1_DEF, NUMERAL, .. } := N

  /- The predecessor function. -/

  let PRE ← new_recursive_definition num_RECURSION
   r"(PRE 0 = 0) /\
  (!n. PRE (SUC n) = n)"

  /- Addition. -/

  let ADD ← new_recursive_definition num_RECURSION
   r"(!n. 0 + n = n) /\
  (!m n. (SUC m) + n = SUC(m + n))"

  let ADD_0 ← prove
   r"!m. m + 0 = m"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [ADD])

  let ADD_SUC ← prove
   r"!m n. m + (SUC n) = SUC(m + n)"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [ADD])

  let ADD_CLAUSES ← prove
   r"(!n. 0 + n = n) /\
   (!m. m + 0 = m) /\
   (!m n. (SUC m) + n = SUC(m + n)) /\
   (!m n. m + (SUC n) = SUC(m + n))"
   (REWRITE_TAC [ADD, ADD_0, ADD_SUC])

  let ADD_SYM ← prove
   r"!m n. m + n = n + m"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES])

  let ADD_ASSOC ← prove
   r"!m n p. m + (n + p) = (m + n) + p"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES])

  let ADD_AC ← prove
   r"(m + n = n + m) /\
   ((m + n) + p = m + (n + p)) /\
   (m + (n + p) = n + (m + p))"
   (MESON_TAC [ADD_ASSOC, ADD_SYM])

  let ADD_EQ_0 ← prove
   r"!m n. (m + n = 0) <=> (m = 0) /\ (n = 0)"
   (REPEAT INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, NOT_SUC])

  let EQ_ADD_LCANCEL ← prove
   r"!m n p. (m + n = m + p) <=> (n = p)"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES, SUC_INJ])

  let EQ_ADD_RCANCEL ← prove
   r"!m n p. (m + p = n + p) <=> (m = n)"
   (ONCE_REWRITE_TAC [ADD_SYM] THEN MATCH_ACCEPT_TAC EQ_ADD_LCANCEL)

  let EQ_ADD_LCANCEL_0 ← prove
   r"!m n. (m + n = m) <=> (n = 0)"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES, SUC_INJ])

  let EQ_ADD_RCANCEL_0 ← prove
   r"!m n. (m + n = n) <=> (m = 0)"
   (ONCE_REWRITE_TAC [ADD_SYM] THEN MATCH_ACCEPT_TAC EQ_ADD_LCANCEL_0)

  /- Now define "bitwise" binary representation of numerals. -/

  let BIT0 ← prove
   r"!n. BIT0 n = n + n"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [BIT0_DEF, ADD_CLAUSES])

  let BIT1 ← prove
   r"!n. BIT1 n = SUC(n + n)"
   (REWRITE_TAC [BIT1_DEF, BIT0])

  let BIT0_THM ← prove
   r"!n. NUMERAL (BIT0 n) = NUMERAL n + NUMERAL n"
   (REWRITE_TAC [NUMERAL, BIT0])

  let BIT1_THM ← prove
   r"!n. NUMERAL (BIT1 n) = SUC(NUMERAL n + NUMERAL n)"
   (REWRITE_TAC [NUMERAL, BIT1])

  /- Following is handy before num_CONV arrives. -/

  let ONE ← prove
   r"1 = SUC 0"
   (REWRITE_TAC [BIT1, ← REWRITE_RULE [NUMERAL] ADD_CLAUSES, NUMERAL])

  let TWO ← prove
   r"2 = SUC 1"
   (REWRITE_TAC [BIT0, BIT1, ← REWRITE_RULE [NUMERAL] ADD_CLAUSES, NUMERAL])

  /- One immediate consequence. -/

  let ADD1 ← prove
   r"!m. SUC m = m + 1"
   (REWRITE_TAC [BIT1_THM, ADD_CLAUSES])

  return {
    PRE, ADD, ADD_0, ADD_SUC, ADD_CLAUSES, ADD_SYM, ADD_ASSOC, ADD_AC,
    ADD_EQ_0, EQ_ADD_LCANCEL, EQ_ADD_RCANCEL, EQ_ADD_LCANCEL_0,
    EQ_ADD_RCANCEL_0, BIT0, BIT1, BIT0_THM, BIT1_THM, ONE, TWO, ADD1 }

/-- The `arith.ml` theorems, part 2: multiplication, exponentiation, the
    recursively-defined orderings, and MAX/MIN with their step and base
    cases. -/
structure ArithThms2 where
  MULT             : thm
  MULT_0           : thm
  MULT_SUC         : thm
  MULT_CLAUSES     : thm
  MULT_SYM         : thm
  LEFT_ADD_DISTRIB : thm
  RIGHT_ADD_DISTRIB : thm
  MULT_ASSOC       : thm
  MULT_AC          : thm
  MULT_EQ_0        : thm
  EQ_MULT_LCANCEL  : thm
  EQ_MULT_RCANCEL  : thm
  MULT_2           : thm
  MULT_EQ_1        : thm
  EXP              : thm
  EXP_EQ_0         : thm
  EXP_EQ_1         : thm
  EXP_ZERO         : thm
  EXP_ADD          : thm
  EXP_ONE          : thm
  EXP_1            : thm
  EXP_2            : thm
  MULT_EXP         : thm
  EXP_MULT         : thm
  EXP_EXP          : thm
  LE               : thm
  LT               : thm
  GE               : thm
  GT               : thm
  MAX              : thm
  MIN              : thm
  LE_SUC_LT        : thm
  LT_SUC_LE        : thm
  LE_SUC           : thm
  LT_SUC           : thm
  LE_0             : thm
  LT_0             : thm
  deriving Inhabited

@[nospecialize]
def setupArith2 [HolBase] (N : HolMath.Nums.NumsThms)
    (new_definition' : term → IO (Except String thm))
    (A1 : ArithThms1)
    (MESON_TAC : List thm → tactic)
    (new_recursive_definition' : thm → term → IO (Except String thm)) :
    ExceptT String IO ArithThms2 := do
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let new_recursive_definition (ax : thm) (s : String) : ExceptT String IO thm := do
    new_recursive_definition' ax (← q s)
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { num_RECURSION, NOT_SUC, SUC_INJ, .. } := N
  let { DISJ_SYM, .. } := HolBase.T
  let { ADD, ADD_CLAUSES, ADD_SYM, ADD_ASSOC, ADD_EQ_0, EQ_ADD_LCANCEL,
        BIT0_THM, BIT1_THM, ONE, .. } := A1

  /- Multiplication. -/

  let MULT ← new_recursive_definition num_RECURSION
   r"(!n. 0 * n = 0) /\
  (!m n. (SUC m) * n = (m * n) + n)"

  let MULT_0 ← prove
   r"!m. m * 0 = 0"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [MULT, ADD_CLAUSES])

  let MULT_SUC ← prove
   r"!m n. m * (SUC n) = m + (m * n)"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [MULT, ADD_CLAUSES, ADD_ASSOC])

  let MULT_CLAUSES ← prove
   r"(!n. 0 * n = 0) /\
   (!m. m * 0 = 0) /\
   (!n. 1 * n = n) /\
   (!m. m * 1 = m) /\
   (!m n. (SUC m) * n = (m * n) + n) /\
   (!m n. m * (SUC n) = m + (m * n))"
   (REWRITE_TAC [BIT1_THM, MULT, MULT_0, MULT_SUC, ADD_CLAUSES])

  let MULT_SYM ← prove
   r"!m n. m * n = n * m"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES, ← EQT_INTRO (← SPEC_ALL ADD_SYM)])

  let LEFT_ADD_DISTRIB ← prove
   r"!m n p. m * (n + p) = (m * n) + (m * p)"
   (GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ADD, MULT_CLAUSES, ADD_ASSOC])

  let RIGHT_ADD_DISTRIB ← prove
   r"!m n p. (m + n) * p = (m * p) + (n * p)"
   (ONCE_REWRITE_TAC [MULT_SYM] THEN MATCH_ACCEPT_TAC LEFT_ADD_DISTRIB)

  let MULT_ASSOC ← prove
   r"!m n p. m * (n * p) = (m * n) * p"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES, RIGHT_ADD_DISTRIB])

  let MULT_AC ← prove
   r"(m * n = n * m) /\
   ((m * n) * p = m * (n * p)) /\
   (m * (n * p) = n * (m * p))"
   (MESON_TAC [MULT_ASSOC, MULT_SYM])

  let MULT_EQ_0 ← prove
   r"!m n. (m * n = 0) <=> (m = 0) \/ (n = 0)"
   (REPEAT INDUCT_TAC THEN REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES, NOT_SUC])

  let EQ_MULT_LCANCEL ← prove
   r"!m n p. (m * n = m * p) <=> (m = 0) \/ (n = p)"
   (INDUCT_TAC THEN REWRITE_TAC [MULT_CLAUSES, NOT_SUC] THEN
    REPEAT INDUCT_TAC THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES, ← GSYM NOT_SUC, NOT_SUC] THEN
    ASM_REWRITE_TAC [SUC_INJ, ← GSYM ADD_ASSOC, EQ_ADD_LCANCEL])

  let EQ_MULT_RCANCEL ← prove
   r"!m n p. (m * p = n * p) <=> (m = n) \/ (p = 0)"
   (ONCE_REWRITE_TAC [MULT_SYM, DISJ_SYM] THEN MATCH_ACCEPT_TAC EQ_MULT_LCANCEL)

  let MULT_2 ← prove
   r"!n. 2 * n = n + n"
   (GEN_TAC THEN REWRITE_TAC [BIT0_THM, MULT_CLAUSES, RIGHT_ADD_DISTRIB])

  let MULT_EQ_1 ← prove
   r"!m n. (m * n = 1) <=> (m = 1) /\ (n = 1)"
   (INDUCT_TAC THEN INDUCT_TAC THEN REWRITE_TAC
      [MULT_CLAUSES, ADD_CLAUSES, BIT0_THM, BIT1_THM, ← GSYM NOT_SUC] THEN
    REWRITE_TAC [SUC_INJ, ADD_EQ_0, MULT_EQ_0] THEN
    CONV_TAC (fun t => (TAUT t).run))

  /- Exponentiation. -/

  let EXP ← new_recursive_definition num_RECURSION
   r"(!m. m EXP 0 = 1) /\
  (!m n. m EXP (SUC n) = m * (m EXP n))"

  let EXP_EQ_0 ← prove
   r"!m n. (m EXP n = 0) <=> (m = 0) /\ ~(n = 0)"
   (REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC
      [BIT1_THM, NOT_SUC, NOT_SUC, EXP, MULT_CLAUSES, ADD_CLAUSES, ADD_EQ_0])

  let EXP_EQ_1 ← prove
   r"!x n. x EXP n = 1 <=> x = 1 \/ n = 0"
   (GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [EXP, MULT_EQ_1, NOT_SUC] THEN
    CONV_TAC (fun t => (TAUT t).run))

  let EXP_ZERO ← prove
   r"!n. 0 EXP n = if n = 0 then 1 else 0"
   (GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [EXP_EQ_0, EXP_EQ_1])

  let EXP_ADD ← prove
   r"!m n p. m EXP (n + p) = (m EXP n) * (m EXP p)"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [EXP, ADD_CLAUSES, MULT_CLAUSES, MULT_AC])

  let EXP_ONE ← prove
   r"!n. 1 EXP n = 1"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [EXP, MULT_CLAUSES])

  let EXP_1 ← prove
   r"!n. n EXP 1 = n"
   (REWRITE_TAC [ONE, EXP, MULT_CLAUSES, ADD_CLAUSES])

  let EXP_2 ← prove
   r"!n. n EXP 2 = n * n"
   (REWRITE_TAC [BIT0_THM, BIT1_THM, EXP, EXP_ADD, MULT_CLAUSES, ADD_CLAUSES])

  let MULT_EXP ← prove
   r"!p m n. (m * n) EXP p = m EXP p * n EXP p"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [EXP, MULT_CLAUSES, MULT_AC])

  let EXP_MULT ← prove
   r"!m n p. m EXP (n * p) = (m EXP n) EXP p"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [EXP_ADD, EXP, MULT_CLAUSES] THENL
     [CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
      INDUCT_TAC THEN ASM_REWRITE_TAC [EXP, MULT_CLAUSES],
      REWRITE_TAC [MULT_EXP] THEN MATCH_ACCEPT_TAC MULT_SYM])

  let EXP_EXP ← prove
   r"!x m n. (x EXP m) EXP n = x EXP (m * n)"
   (REWRITE_TAC [EXP_MULT])

  /- Define the orderings recursively too. -/

  let LE ← new_recursive_definition num_RECURSION
   r"(!m. (m <= 0) <=> (m = 0)) /\
  (!m n. (m <= SUC n) <=> (m = SUC n) \/ (m <= n))"

  let LT ← new_recursive_definition num_RECURSION
   r"(!m. (m < 0) <=> F) /\
  (!m n. (m < SUC n) <=> (m = n) \/ (m < n))"

  let GE ← new_definition
   r"m >= n <=> n <= m"

  let GT ← new_definition
   r"m > n <=> n < m"

  /- Maximum and minimum of natural numbers. -/

  let MAX ← new_definition
   r"!m n. MAX m n = if m <= n then n else m"

  let MIN ← new_definition
   r"!m n. MIN m n = if m <= n then m else n"

  /- Step cases. -/

  let LE_SUC_LT ← prove
   r"!m n. (SUC m <= n) <=> (m < n)"
   (GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [LE, LT, NOT_SUC, SUC_INJ])

  let LT_SUC_LE ← prove
   r"!m n. (m < SUC n) <=> (m <= n)"
   (GEN_TAC THEN INDUCT_TAC THEN ONCE_REWRITE_TAC [LT, LE] THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [LT])

  let LE_SUC ← prove
   r"!m n. (SUC m <= SUC n) <=> (m <= n)"
   (REWRITE_TAC [LE_SUC_LT, LT_SUC_LE])

  let LT_SUC ← prove
   r"!m n. (SUC m < SUC n) <=> (m < n)"
   (REWRITE_TAC [LT_SUC_LE, LE_SUC_LT])

  /- Base cases. -/

  let LE_0 ← prove
   r"!n. 0 <= n"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [LE])

  let LT_0 ← prove
   r"!n. 0 < SUC n"
   (REWRITE_TAC [LT_SUC_LE, LE_0])

  return {
    MULT, MULT_0, MULT_SUC, MULT_CLAUSES, MULT_SYM, LEFT_ADD_DISTRIB,
    RIGHT_ADD_DISTRIB, MULT_ASSOC, MULT_AC, MULT_EQ_0, EQ_MULT_LCANCEL,
    EQ_MULT_RCANCEL, MULT_2, MULT_EQ_1, EXP, EXP_EQ_0, EXP_EQ_1, EXP_ZERO,
    EXP_ADD, EXP_ONE, EXP_1, EXP_2, MULT_EXP, EXP_MULT, EXP_EXP, LE, LT, GE,
    GT, MAX, MIN, LE_SUC_LT, LT_SUC_LE, LE_SUC, LT_SUC, LE_0, LT_0 }

/-- The `arith.ml` theorems, part 3: reflexivity, antisymmetry, transitivity,
    totality, the relationships between orderings, and the "0 < n" shuffling
    lemmas. -/
structure ArithThms3 where
  LE_REFL      : thm
  LT_REFL      : thm
  LT_IMP_NE    : thm
  LE_ANTISYM   : thm
  LT_ANTISYM   : thm
  LET_ANTISYM  : thm
  LTE_ANTISYM  : thm
  LE_TRANS     : thm
  LT_TRANS     : thm
  LET_TRANS    : thm
  LTE_TRANS    : thm
  LE_CASES     : thm
  LT_CASES     : thm
  LET_CASES    : thm
  LTE_CASES    : thm
  LE_LT        : thm
  LT_LE        : thm
  NOT_LE       : thm
  NOT_LT       : thm
  LT_IMP_LE    : thm
  EQ_IMP_LE    : thm
  LT_NZ        : thm
  LE_1         : thm
  deriving Inhabited

@[nospecialize]
def setupArith3 [HolBase] (N : HolMath.Nums.NumsThms)
    (A1 : ArithThms1) (A2 : ArithThms2)
    (MESON_TAC : List thm → tactic) :
    ExceptT String IO ArithThms3 := do
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { NOT_SUC, SUC_INJ, .. } := N
  let { CONJ_SYM, DISJ_SYM, EQ_SYM_EQ, .. } := HolBase.T
  let { ONE, .. } := A1
  let { LE, LT, LE_SUC_LT, LT_SUC_LE, LE_SUC, LT_SUC, LE_0, LT_0, .. } := A2

  /- Reflexivity. -/

  let LE_REFL ← prove
   r"!n. n <= n"
   (INDUCT_TAC THEN REWRITE_TAC [LE])

  let LT_REFL ← prove
   r"!n. ~(n < n)"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [LT_SUC] THEN REWRITE_TAC [LT])

  let LT_IMP_NE ← prove
   r"!m n:num. m < n ==> ~(m = n)"
   (MESON_TAC [LT_REFL])

  /- Antisymmetry. -/

  let LE_ANTISYM ← prove
   r"!m n. (m <= n /\ n <= m) <=> (m = n)"
   (REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [LE_SUC, SUC_INJ] THEN
    REWRITE_TAC [LE, NOT_SUC, ← GSYM NOT_SUC])

  let LT_ANTISYM ← prove
   r"!m n. ~(m < n /\ n < m)"
   (REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [LT_SUC] THEN REWRITE_TAC [LT])

  let LET_ANTISYM ← prove
   r"!m n. ~(m <= n /\ n < m)"
   (REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [LE_SUC, LT_SUC] THEN
    REWRITE_TAC [LE, LT, NOT_SUC])

  let LTE_ANTISYM ← prove
   r"!m n. ~(m < n /\ n <= m)"
   (ONCE_REWRITE_TAC [CONJ_SYM] THEN REWRITE_TAC [LET_ANTISYM])

  /- Transitivity. -/

  let LE_TRANS ← prove
   r"!m n p. m <= n /\ n <= p ==> m <= p"
   (REPEAT INDUCT_TAC THEN
    ASM_REWRITE_TAC [LE_SUC, LE_0] THEN REWRITE_TAC [LE, NOT_SUC])

  let LT_TRANS ← prove
   r"!m n p. m < n /\ n < p ==> m < p"
   (REPEAT INDUCT_TAC THEN
    ASM_REWRITE_TAC [LT_SUC, LT_0] THEN REWRITE_TAC [LT, NOT_SUC])

  let LET_TRANS ← prove
   r"!m n p. m <= n /\ n < p ==> m < p"
   (REPEAT INDUCT_TAC THEN
    ASM_REWRITE_TAC [LE_SUC, LT_SUC, LT_0] THEN REWRITE_TAC [LT, LE, NOT_SUC])

  let LTE_TRANS ← prove
   r"!m n p. m < n /\ n <= p ==> m < p"
   (REPEAT INDUCT_TAC THEN
    ASM_REWRITE_TAC [LE_SUC, LT_SUC, LT_0] THEN REWRITE_TAC [LT, LE, NOT_SUC])

  /- Totality. -/

  -- `W(W (curry SPEC_TAC) o hd o frees o snd)`.
  let SPEC_FIRST_FREE_TAC : tactic :=
    W (fun g => tactic_of do
      let v ← liftExcept (hd (frees (snd g)))
      pure (SPEC_TAC (v, v)))

  let LE_CASES ← prove
   r"!m n. m <= n \/ n <= m"
   (REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [LE_0, LE_SUC])

  let LT_CASES ← prove
   r"!m n. (m < n) \/ (n < m) \/ (m = n)"
   (REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [LT_SUC, SUC_INJ] THEN
    REWRITE_TAC [LT, NOT_SUC, ← GSYM NOT_SUC] THEN
    SPEC_FIRST_FREE_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC [LT_0])

  let LET_CASES ← prove
   r"!m n. m <= n \/ n < m"
   (REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [LE_SUC_LT, LT_SUC_LE, LE_0])

  let LTE_CASES ← prove
   r"!m n. m < n \/ n <= m"
   (ONCE_REWRITE_TAC [DISJ_SYM] THEN MATCH_ACCEPT_TAC LET_CASES)

  /- Relationship between orderings. -/

  let LE_LT ← prove
   r"!m n. (m <= n) <=> (m < n) \/ (m = n)"
   (REPEAT INDUCT_TAC THEN
    ASM_REWRITE_TAC [LE_SUC, LT_SUC, SUC_INJ, LE_0, LT_0] THEN
    REWRITE_TAC [LE, LT])

  let LT_LE ← prove
   r"!m n. (m < n) <=> (m <= n) /\ ~(m = n)"
   (REWRITE_TAC [LE_LT] THEN REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST_ALL_TAC THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC [LT_REFL],
      DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC []])

  let NOT_LE ← prove
   r"!m n. ~(m <= n) <=> (n < m)"
   (REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [LE_SUC, LT_SUC] THEN
    REWRITE_TAC [LE, LT, NOT_SUC, ← GSYM NOT_SUC, LE_0] THEN
    SPEC_FIRST_FREE_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC [LT_0])

  let NOT_LT ← prove
   r"!m n. ~(m < n) <=> n <= m"
   (REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [LE_SUC, LT_SUC] THEN
    REWRITE_TAC [LE, LT, NOT_SUC, ← GSYM NOT_SUC, LE_0] THEN
    SPEC_FIRST_FREE_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC [LT_0])

  let LT_IMP_LE ← prove
   r"!m n. m < n ==> m <= n"
   (REWRITE_TAC [LT_LE] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [])

  let EQ_IMP_LE ← prove
   r"!m n. (m = n) ==> m <= n"
   (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [LE_REFL])

  /- Often useful to shuffle between different versions of "0 < n". -/

  let LT_NZ ← prove
   r"!n. 0 < n <=> ~(n = 0)"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [NOT_SUC, LT, EQ_SYM_EQ] THEN
    CONV_TAC (fun t => (TAUT t).run))

  let LE_1 ← prove
   r"(!n. ~(n = 0) ==> 0 < n) /\
   (!n. ~(n = 0) ==> 1 <= n) /\
   (!n. 0 < n ==> ~(n = 0)) /\
   (!n. 0 < n ==> 1 <= n) /\
   (!n. 1 <= n ==> 0 < n) /\
   (!n. 1 <= n ==> ~(n = 0))"
   (REWRITE_TAC [LT_NZ, ← GSYM NOT_LT, ONE, LT])

  return {
    LE_REFL, LT_REFL, LT_IMP_NE, LE_ANTISYM, LT_ANTISYM, LET_ANTISYM,
    LTE_ANTISYM, LE_TRANS, LT_TRANS, LET_TRANS, LTE_TRANS, LE_CASES, LT_CASES,
    LET_CASES, LTE_CASES, LE_LT, LT_LE, NOT_LE, NOT_LT, LT_IMP_LE, EQ_IMP_LE,
    LT_NZ, LE_1 }

/-- The `arith.ml` theorems, part 4: the existential characterizations of the
    orderings, their interaction with addition and multiplication, the "without
    loss of generality" lemmas, well-founded/least-number principles, and the
    variant induction schemes. -/
structure ArithThms4 where
  LE_EXISTS          : thm
  LT_EXISTS          : thm
  LE_ADD             : thm
  LE_ADDR            : thm
  LT_ADD             : thm
  LT_ADDR            : thm
  LE_ADD_LCANCEL     : thm
  LE_ADD_RCANCEL     : thm
  LT_ADD_LCANCEL     : thm
  LT_ADD_RCANCEL     : thm
  LE_ADD2            : thm
  LET_ADD2           : thm
  LTE_ADD2           : thm
  LT_ADD2            : thm
  LT_MULT            : thm
  LE_MULT2           : thm
  LT_LMULT           : thm
  LE_MULT_LCANCEL    : thm
  LE_MULT_RCANCEL    : thm
  LT_MULT_LCANCEL    : thm
  LT_MULT_RCANCEL    : thm
  LT_MULT2           : thm
  LE_SQUARE_REFL     : thm
  LT_POW2_REFL       : thm
  WLOG_LE            : thm
  WLOG_LT            : thm
  WLOG_LE_3          : thm
  num_WF             : thm
  num_WOP            : thm
  num_MAX            : thm
  LE_INDUCT          : thm
  num_INDUCTION_DOWN : thm
  deriving Inhabited

@[nospecialize]
def setupArith4 [HolBase] (N : HolMath.Nums.NumsThms)
    (A1 : ArithThms1) (A2 : ArithThms2) (A3 : ArithThms3)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic)
    (MESON' : List thm → term → IO (Except String thm)) :
    ExceptT String IO ArithThms4 := do
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { NOT_SUC, SUC_INJ, num_INDUCTION, .. } := N
  let { CONJ_SYM, DISJ_SYM, IMP_CONJ, RIGHT_EXISTS_AND_THM, EXISTS_REFL,
        LEFT_IMP_EXISTS_THM, BETA_THM, .. } := HolBase.T
  let { NOT_EXISTS_THM, .. } := HolBase.C
  let { ADD_CLAUSES, ADD_SYM, ADD_ASSOC, ADD_AC, ADD_EQ_0, EQ_ADD_LCANCEL, ONE,
        TWO, ADD1, .. } := A1
  let { MULT_CLAUSES, MULT_SYM, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB,
        EQ_MULT_LCANCEL, MULT_2, EXP, EXP_EQ_0, LE, LT, LE_SUC_LT, LE_SUC,
        LT_SUC, LE_0, LT_0, .. } := A2
  let { LE_REFL, LT_REFL, LET_TRANS, LE_CASES, LT_CASES, LTE_CASES, LT_LE,
        NOT_LE, LT_IMP_LE, LE_1, .. } := A3

  /- Relate the orderings to arithmetic operations. -/

  let LE_EXISTS ← prove
   r"!m n. (m <= n) <=> (?d. n = m + d)"
   (GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [LE] THENL
     [REWRITE_TAC [← CONV_RULE (LAND_CONV SYM_CONV) (← SPEC_ALL ADD_EQ_0)] THEN
      REWRITE_TAC [RIGHT_EXISTS_AND_THM, EXISTS_REFL],
      EQ_TAC THENL
       [DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
         [EXISTS_TAC (← q r"0") THEN REWRITE_TAC [ADD_CLAUSES],
          DISCH_THEN (X_CHOOSE_THEN (← q r"d:num") SUBST1_TAC) THEN
          EXISTS_TAC (← q r"SUC d") THEN REWRITE_TAC [ADD_CLAUSES]],
        ONCE_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
        INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, SUC_INJ] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [] THEN DISJ2_TAC THEN
        REWRITE_TAC [EQ_ADD_LCANCEL, ← GSYM EXISTS_REFL]]])

  let LT_EXISTS ← prove
   r"!m n. (m < n) <=> (?d. n = m + SUC d)"
   (GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [LT, ADD_CLAUSES, ← GSYM NOT_SUC] THEN
    ASM_REWRITE_TAC [SUC_INJ] THEN EQ_TAC THENL
     [DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
       [EXISTS_TAC (← q r"0") THEN REWRITE_TAC [ADD_CLAUSES],
        DISCH_THEN (X_CHOOSE_THEN (← q r"d:num") SUBST1_TAC) THEN
        EXISTS_TAC (← q r"SUC d") THEN REWRITE_TAC [ADD_CLAUSES]],
      ONCE_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, SUC_INJ] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [] THEN DISJ2_TAC THEN
      REWRITE_TAC [SUC_INJ, EQ_ADD_LCANCEL, ← GSYM EXISTS_REFL]])

  /- Interaction with addition. -/

  let LE_ADD ← prove
   r"!m n. m <= m + n"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [LE, ADD_CLAUSES, LE_REFL])

  let LE_ADDR ← prove
   r"!m n. n <= m + n"
   (ONCE_REWRITE_TAC [ADD_SYM] THEN MATCH_ACCEPT_TAC LE_ADD)

  let LT_ADD ← prove
   r"!m n. (m < m + n) <=> (0 < n)"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES, LT_SUC])

  let LT_ADDR ← prove
   r"!m n. (n < m + n) <=> (0 < m)"
   (ONCE_REWRITE_TAC [ADD_SYM] THEN MATCH_ACCEPT_TAC LT_ADD)

  let LE_ADD_LCANCEL ← prove
   r"!m n p. (m + n) <= (m + p) <=> n <= p"
   (REWRITE_TAC [LE_EXISTS, ← GSYM ADD_ASSOC, EQ_ADD_LCANCEL])

  let LE_ADD_RCANCEL ← prove
   r"!m n p. (m + p) <= (n + p) <=> (m <= n)"
   (ONCE_REWRITE_TAC [ADD_SYM] THEN MATCH_ACCEPT_TAC LE_ADD_LCANCEL)

  let LT_ADD_LCANCEL ← prove
   r"!m n p. (m + n) < (m + p) <=> n < p"
   (REWRITE_TAC [LT_EXISTS, ← GSYM ADD_ASSOC, EQ_ADD_LCANCEL, SUC_INJ])

  let LT_ADD_RCANCEL ← prove
   r"!m n p. (m + p) < (n + p) <=> (m < n)"
   (ONCE_REWRITE_TAC [ADD_SYM] THEN MATCH_ACCEPT_TAC LT_ADD_LCANCEL)

  let LE_ADD2 ← prove
   r"!m n p q. m <= p /\ n <= q ==> m + n <= p + q"
   (REPEAT GEN_TAC THEN REWRITE_TAC [LE_EXISTS] THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (X_CHOOSE_TAC (← q r"a:num")) (X_CHOOSE_TAC (← q r"b:num"))) THEN
    EXISTS_TAC (← q r"a + b") THEN ASM_REWRITE_TAC [ADD_AC])

  let LET_ADD2 ← prove
   r"!m n p q. m <= p /\ n < q ==> m + n < p + q"
   (REPEAT GEN_TAC THEN REWRITE_TAC [LE_EXISTS, LT_EXISTS] THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (X_CHOOSE_TAC (← q r"a:num")) (X_CHOOSE_TAC (← q r"b:num"))) THEN
    EXISTS_TAC (← q r"a + b") THEN ASM_REWRITE_TAC [SUC_INJ, ADD_CLAUSES, ADD_AC])

  let LTE_ADD2 ← prove
   r"!m n p q. m < p /\ n <= q ==> m + n < p + q"
   (ONCE_REWRITE_TAC [ADD_SYM, CONJ_SYM] THEN
    MATCH_ACCEPT_TAC LET_ADD2)

  let LT_ADD2 ← prove
   r"!m n p q. m < p /\ n < q ==> m + n < p + q"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC LTE_ADD2 THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LT_IMP_LE THEN
    ASM_REWRITE_TAC [])

  /- And multiplication. -/

  let LT_MULT ← prove
   r"!m n. (0 < m * n) <=> (0 < m) /\ (0 < n)"
   (REPEAT INDUCT_TAC THEN REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES, LT_0])

  let LE_MULT2 ← prove
   r"!m n p q. m <= n /\ p <= q ==> m * p <= n * q"
   (REPEAT GEN_TAC THEN REWRITE_TAC [LE_EXISTS] THEN
    DISCH_THEN (CONJUNCTS_THEN2
      (X_CHOOSE_TAC (← q r"a:num")) (X_CHOOSE_TAC (← q r"b:num"))) THEN
    EXISTS_TAC (← q r"a * p + m * b + a * b") THEN
    ASM_REWRITE_TAC [LEFT_ADD_DISTRIB] THEN
    REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, ADD_ASSOC])

  let LT_LMULT ← prove
   r"!m n p. ~(m = 0) /\ n < p ==> m * n < m * p"
   (REPEAT GEN_TAC THEN REWRITE_TAC [LT_LE] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC [LE_REFL],
      ASM_REWRITE_TAC [EQ_MULT_LCANCEL]])

  let mc4 ← liftExcept (match (CONJUNCTS MULT_CLAUSES)[4]? with
    | some t => .ok t | none => .error "el")

  let LE_MULT_LCANCEL ← prove
   r"!m n p. (m * n) <= (m * p) <=> (m = 0) \/ n <= p"
   (REPEAT INDUCT_TAC THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES, LE_REFL, LE_0, NOT_SUC] THEN
    REWRITE_TAC [LE_SUC] THEN
    REWRITE_TAC [LE, LE_ADD_LCANCEL, ← GSYM ADD_ASSOC] THEN
    ASM_REWRITE_TAC [← GSYM mc4, NOT_SUC])

  let LE_MULT_RCANCEL ← prove
   r"!m n p. (m * p) <= (n * p) <=> (m <= n) \/ (p = 0)"
   (ONCE_REWRITE_TAC [MULT_SYM, DISJ_SYM] THEN
    MATCH_ACCEPT_TAC LE_MULT_LCANCEL)

  let LT_MULT_LCANCEL ← prove
   r"!m n p. (m * n) < (m * p) <=> ~(m = 0) /\ n < p"
   (REPEAT INDUCT_TAC THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES, LT_REFL, LT_0, NOT_SUC] THEN
    REWRITE_TAC [LT_SUC] THEN
    REWRITE_TAC [LT, LT_ADD_LCANCEL, ← GSYM ADD_ASSOC] THEN
    ASM_REWRITE_TAC [← GSYM mc4, NOT_SUC])

  let LT_MULT_RCANCEL ← prove
   r"!m n p. (m * p) < (n * p) <=> (m < n) /\ ~(p = 0)"
   (ONCE_REWRITE_TAC [MULT_SYM, CONJ_SYM] THEN
    MATCH_ACCEPT_TAC LT_MULT_LCANCEL)

  let LT_MULT2 ← prove
   r"!m n p q. m < n /\ p < q ==> m * p < n * q"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC (← q r"n * p") THEN
    ASM_SIMP_TAC [LE_MULT_RCANCEL, LT_IMP_LE, LT_MULT_LCANCEL] THEN
    UNDISCH_TAC (← q r"m < n") THEN CONV_TAC CONTRAPOS_CONV THEN SIMP_TAC [LT])

  let LE_SQUARE_REFL ← prove
   r"!n. n <= n * n"
   (INDUCT_TAC THEN REWRITE_TAC [MULT_CLAUSES, LE_0, LE_ADDR])

  let LT_POW2_REFL ← prove
   r"!n. n < 2 EXP n"
   (INDUCT_TAC THEN REWRITE_TAC [EXP] THEN REWRITE_TAC [MULT_2, ADD1] THEN
    REWRITE_TAC [ONE, LT] THEN MATCH_MP_TAC LTE_ADD2 THEN
    ASM_REWRITE_TAC [LE_SUC_LT, TWO] THEN
    MESON_TAC [EXP_EQ_0, LE_1, NOT_SUC])

  /- Useful "without loss of generality" lemmas. -/

  let WLOG_LE ← prove
   r"(!m n. P m n <=> P n m) /\ (!m n. m <= n ==> P m n) ==> !m n. P m n"
   (MESON_TAC [LE_CASES])

  let WLOG_LT ← prove
   r"(!m. P m m) /\ (!m n. P m n <=> P n m) /\ (!m n. m < n ==> P m n)
   ==> !m y. P m y"
   (MESON_TAC [LT_CASES])

  let WLOG_LE_3 ← prove
   r"!P. (!x y z. P x y z ==> P y x z /\ P x z y) /\
       (!x y z. x <= y /\ y <= z ==> P x y z)
       ==> !x y z. P x y z"
   (MESON_TAC [LE_CASES])

  /- Existence of least and greatest elements of (finite) set. -/

  let num_WF ← prove
   r"!P. (!n. (!m. m < n ==> P m) ==> P n) ==> !n. P n"
   (GEN_TAC THEN MP_TAC (← SPEC (← q r"\n. !m. m < n ==> P m") num_INDUCTION) THEN
    REWRITE_TAC [LT, BETA_THM] THEN MESON_TAC [LT])

  let num_WOP ← prove
   r"!P. (?n. P n) <=> (?n. P(n) /\ !m. m < n ==> ~P(m))"
   (GEN_TAC THEN EQ_TAC THENL [ALL_TAC, MESON_TAC []] THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [NOT_EXISTS_THM] THEN
    DISCH_TAC THEN MATCH_MP_TAC num_WF THEN ASM_MESON_TAC [])

  let num_MAX ← prove
   r"!P. (?x. P x) /\ (?M. !x. P x ==> x <= M) <=>
       ?m. P m /\ (!x. P x ==> x <= m)"
   (GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"a:num")) MP_TAC) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"m:num") MP_TAC o ONCE_REWRITE_RULE [num_WOP]) THEN
      DISCH_THEN (fun th => tactic_of do pure (EXISTS_TAC (← q r"m:num") THEN MP_TAC th)) THEN
      REWRITE_TAC [← TAUT (← q r"(a /\ b ==> c /\ a) <=> (a /\ b ==> c)")] THEN
      SPEC_TAC (← q r"m:num", ← q r"m:num") THEN INDUCT_TAC THENL
       [REWRITE_TAC [LE, LT] THEN DISCH_THEN (IMP_RES_THEN SUBST_ALL_TAC) THEN
        POP_ASSUM ACCEPT_TAC,
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC (← q r"m:num"))) THEN
        REWRITE_TAC [LT] THEN CONV_TAC CONTRAPOS_CONV THEN
        DISCH_TAC THEN REWRITE_TAC [] THEN X_GEN_TAC (← q r"p:num") THEN
        FIRST_ASSUM (MP_TAC o SPEC (← q r"p:num")) THEN REWRITE_TAC [LE] THEN
        ASM_CASES_TAC (← q r"p = SUC m") THEN ASM_REWRITE_TAC []],
      REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"m:num") THEN ASM_REWRITE_TAC []])

  /- Other variants of induction. -/

  let LE_INDUCT ← prove
   r"!P. (!m:num. P m m) /\
       (!m n. m <= n /\ P m n ==> P m (SUC n))
       ==> (!m n. m <= n ==> P m n)"
   (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, ← MESON [LE_EXISTS]
      (← q r"(!m n:num. m <= n ==> R m n) <=> (!m d. R m (m + d))")] THEN
    REPEAT DISCH_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_SIMP_TAC [ADD_CLAUSES])

  let num_INDUCTION_DOWN ← prove
   r"!(P:num->bool) m.
        (!n. m <= n ==> P n) /\
        (!n. n < m /\ P(n + 1) ==> P n)
        ==> !n. P n"
   (← do
    let t3 ← TAUT (← q r"~(~p /\ q) <=> q ==> p")
    let t2 ← TAUT (← q r"~p ==> q <=> ~q ==> p")
    let t1 ← TAUT (← q r"q /\ ~r ==> (p /\ q <=> r) ==> ~p")
    let m1 ← MESON [] (← q r"(!x. P x) <=> ~(?x. ~P x)")
    pure
     (REWRITE_TAC [← GSYM ADD1] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC [m1] THEN
      W (MP_TAC o PART_MATCH (lhand o lhand) num_MAX o rand o snd) THEN
      MATCH_MP_TAC t1 THEN
      ONCE_REWRITE_TAC [t2] THEN
      REWRITE_TAC [NOT_EXISTS_THM, t3, NOT_LE] THEN
      ASM_MESON_TAC [LTE_CASES, LT, LT_IMP_LE]))

  return {
    LE_EXISTS, LT_EXISTS, LE_ADD, LE_ADDR, LT_ADD, LT_ADDR, LE_ADD_LCANCEL,
    LE_ADD_RCANCEL, LT_ADD_LCANCEL, LT_ADD_RCANCEL, LE_ADD2, LET_ADD2,
    LTE_ADD2, LT_ADD2, LT_MULT, LE_MULT2, LT_LMULT, LE_MULT_LCANCEL,
    LE_MULT_RCANCEL, LT_MULT_LCANCEL, LT_MULT_RCANCEL, LT_MULT2,
    LE_SQUARE_REFL, LT_POW2_REFL, WLOG_LE, WLOG_LT, WLOG_LE_3, num_WF, num_WOP,
    num_MAX, LE_INDUCT, num_INDUCTION_DOWN }

/-- The `arith.ml` theorems, part 5: oddness and evenness (recursively),
    cutoff subtraction (recursively), and the factorial function. -/
structure ArithThms5 where
  EVEN                 : thm
  ODD                  : thm
  NOT_EVEN             : thm
  NOT_ODD              : thm
  EVEN_OR_ODD          : thm
  EVEN_AND_ODD         : thm
  EVEN_ADD             : thm
  EVEN_MULT            : thm
  EVEN_EXP             : thm
  ODD_ADD              : thm
  ODD_MULT             : thm
  ODD_EXP              : thm
  EVEN_DOUBLE          : thm
  ODD_DOUBLE           : thm
  EVEN_EXISTS_LEMMA    : thm
  EVEN_EXISTS          : thm
  ODD_EXISTS           : thm
  EVEN_ODD_DECOMPOSITION : thm
  SUB                  : thm
  SUB_0                : thm
  SUB_PRESUC           : thm
  SUB_SUC              : thm
  SUB_REFL             : thm
  ADD_SUB              : thm
  ADD_SUB2             : thm
  SUB_EQ_0             : thm
  ADD_SUBR2            : thm
  ADD_SUBR             : thm
  SUB_ADD              : thm
  SUB_ADD_LCANCEL      : thm
  SUB_ADD_RCANCEL      : thm
  LEFT_SUB_DISTRIB     : thm
  RIGHT_SUB_DISTRIB    : thm
  SUC_SUB1             : thm
  EVEN_SUB             : thm
  ODD_SUB              : thm
  FACT                 : thm
  FACT_LT              : thm
  FACT_LE              : thm
  FACT_NZ              : thm
  FACT_MONO            : thm
  deriving Inhabited

@[nospecialize]
def setupArith5 [HolBase] (N : HolMath.Nums.NumsThms)
    (A1 : ArithThms1) (A2 : ArithThms2) (A3 : ArithThms3) (A4 : ArithThms4)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic)
    (new_recursive_definition' : thm → term → IO (Except String thm)) :
    ExceptT String IO ArithThms5 := do
  let new_recursive_definition (ax : thm) (s : String) : ExceptT String IO thm := do
    new_recursive_definition' ax (← q s)
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { num_RECURSION, NOT_SUC, .. } := N
  let { DISJ_SYM, SWAP_EXISTS_THM, MONO_EXISTS, .. } := HolBase.T
  let { DE_MORGAN_THM, .. } := HolBase.C
  let { PRE, ADD_CLAUSES, ADD_SYM, BIT0_THM, BIT1_THM, ONE, TWO, .. } := A1
  let { MULT_CLAUSES, MULT_SYM, LEFT_ADD_DISTRIB, MULT_ASSOC, MULT_EQ_0,
        MULT_2, EXP, EXP_EQ_0, LE, LT, LE_SUC_LT, LE_SUC, LE_0, LT_0, .. } := A2
  let { LE_REFL, LE_TRANS, LE_CASES, NOT_LE, LT_NZ, .. } := A3
  let { LE_EXISTS, LE_ADD, LT_MULT, LE_MULT_LCANCEL, LE_MULT_RCANCEL,
        LT_MULT_RCANCEL, num_WF, .. } := A4

  /- Oddness and evenness (recursively rather than inductively!) -/

  let EVEN ← new_recursive_definition num_RECURSION
   r"(EVEN 0 <=> T) /\
   (!n. EVEN (SUC n) <=> ~(EVEN n))"

  let ODD ← new_recursive_definition num_RECURSION
   r"(ODD 0 <=> F) /\
   (!n. ODD (SUC n) <=> ~(ODD n))"

  let NOT_EVEN ← prove
   r"!n. ~(EVEN n) <=> ODD n"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [EVEN, ODD])

  let NOT_ODD ← prove
   r"!n. ~(ODD n) <=> EVEN n"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [EVEN, ODD])

  let EVEN_OR_ODD ← prove
   r"!n. EVEN n \/ ODD n"
   (INDUCT_TAC THEN REWRITE_TAC [EVEN, ODD, NOT_EVEN, NOT_ODD] THEN
    ONCE_REWRITE_TAC [DISJ_SYM] THEN ASM_REWRITE_TAC [])

  let EVEN_AND_ODD ← prove
   r"!n. ~(EVEN n /\ ODD n)"
   (REWRITE_TAC [← GSYM NOT_EVEN, ← ITAUT (← q r"~(p /\ ~p)")])

  let EVEN_ADD ← prove
   r"!m n. EVEN(m + n) <=> (EVEN m <=> EVEN n)"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [EVEN, ADD_CLAUSES] THEN
    X_GEN_TAC (← q r"p:num") THEN
    DISJ_CASES_THEN MP_TAC (← SPEC (← q r"n:num") EVEN_OR_ODD) THEN
    DISJ_CASES_THEN MP_TAC (← SPEC (← q r"p:num") EVEN_OR_ODD) THEN
    REWRITE_TAC [← GSYM NOT_EVEN] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [])

  let EVEN_MULT ← prove
   r"!m n. EVEN(m * n) <=> EVEN(m) \/ EVEN(n)"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES, EVEN_ADD, EVEN] THEN
    X_GEN_TAC (← q r"p:num") THEN
    DISJ_CASES_THEN MP_TAC (← SPEC (← q r"n:num") EVEN_OR_ODD) THEN
    DISJ_CASES_THEN MP_TAC (← SPEC (← q r"p:num") EVEN_OR_ODD) THEN
    REWRITE_TAC [← GSYM NOT_EVEN] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [])

  let EVEN_EXP ← prove
   r"!m n. EVEN(m EXP n) <=> EVEN(m) /\ ~(n = 0)"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [EVEN, EXP, ONE, EVEN_MULT, NOT_SUC] THEN
    CONV_TAC (fun t => (ITAUT t).run))

  let ODD_ADD ← prove
   r"!m n. ODD(m + n) <=> ~(ODD m <=> ODD n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM NOT_EVEN, EVEN_ADD] THEN
    CONV_TAC (fun t => (ITAUT t).run))

  let ODD_MULT ← prove
   r"!m n. ODD(m * n) <=> ODD(m) /\ ODD(n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM NOT_EVEN, EVEN_MULT] THEN
    CONV_TAC (fun t => (ITAUT t).run))

  let ODD_EXP ← prove
   r"!m n. ODD(m EXP n) <=> ODD(m) \/ (n = 0)"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [ODD, EXP, ONE, ODD_MULT, NOT_SUC] THEN
    CONV_TAC (fun t => (ITAUT t).run))

  let EVEN_DOUBLE ← prove
   r"!n. EVEN(2 * n)"
   (GEN_TAC THEN REWRITE_TAC [EVEN_MULT] THEN DISJ1_TAC THEN
    PURE_REWRITE_TAC [BIT0_THM, BIT1_THM] THEN REWRITE_TAC [EVEN, EVEN_ADD])

  let ODD_DOUBLE ← prove
   r"!n. ODD(SUC(2 * n))"
   (REWRITE_TAC [ODD] THEN REWRITE_TAC [NOT_ODD, EVEN_DOUBLE])

  let EVEN_EXISTS_LEMMA ← prove
   r"!n. (EVEN n ==> ?m. n = 2 * m) /\
       (~EVEN n ==> ?m. n = SUC(2 * m))"
   (INDUCT_TAC THEN REWRITE_TAC [EVEN] THENL
     [EXISTS_TAC (← q r"0") THEN REWRITE_TAC [MULT_CLAUSES],
      POP_ASSUM STRIP_ASSUME_TAC THEN CONJ_TAC THEN
      DISCH_THEN (ANTE_RES_THEN (X_CHOOSE_TAC (← q r"m:num"))) THENL
       [EXISTS_TAC (← q r"SUC m") THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [MULT_2] THEN REWRITE_TAC [ADD_CLAUSES],
        EXISTS_TAC (← q r"m:num") THEN ASM_REWRITE_TAC []]])

  let EVEN_EXISTS ← prove
   r"!n. EVEN n <=> ?m. n = 2 * m"
   (GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [MATCH_MP_TAC (← CONJUNCT1 (← SPEC_ALL EVEN_EXISTS_LEMMA)) THEN ASM_REWRITE_TAC [],
      POP_ASSUM (CHOOSE_THEN SUBST1_TAC) THEN REWRITE_TAC [EVEN_DOUBLE]])

  let ODD_EXISTS ← prove
   r"!n. ODD n <=> ?m. n = SUC(2 * m)"
   (GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [MATCH_MP_TAC (← CONJUNCT2 (← SPEC_ALL EVEN_EXISTS_LEMMA)) THEN
      ASM_REWRITE_TAC [NOT_EVEN],
      POP_ASSUM (CHOOSE_THEN SUBST1_TAC) THEN REWRITE_TAC [ODD_DOUBLE]])

  let mc3 ← liftExcept (match (CONJUNCTS MULT_CLAUSES)[2]? with
    | some t => .ok t | none => .error "el")

  let EVEN_ODD_DECOMPOSITION ← prove
   r"!n. (?k m. ODD m /\ (n = 2 EXP k * m)) <=> ~(n = 0)"
   (MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
    DISJ_CASES_TAC (← SPEC (← q r"n:num") EVEN_OR_ODD) THENL
     [ALL_TAC, ASM_MESON_TAC [ODD, EXP, MULT_CLAUSES]] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"m:num") SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"m:num")) THEN
    ASM_CASES_TAC (← q r"m = 0") THEN ASM_REWRITE_TAC [MULT_EQ_0] THENL
     [REWRITE_TAC [MULT_CLAUSES, LT] THEN
      CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
      REWRITE_TAC [EXP_EQ_0, MULT_EQ_0, TWO, NOT_SUC] THEN MESON_TAC [ODD],
      ALL_TAC] THEN
    ANTS_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [← GSYM mc3] THEN
      ASM_REWRITE_TAC [LT_MULT_RCANCEL, TWO, LT],
      ALL_TAC] THEN
    REWRITE_TAC [TWO, NOT_SUC] THEN REWRITE_TAC [← GSYM TWO] THEN
    ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"p:num") THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"k:num") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"SUC k") THEN ASM_REWRITE_TAC [EXP, MULT_ASSOC])

  /- Cutoff subtraction, also defined recursively. (Not the HOL88 defn.) -/

  let SUB ← new_recursive_definition num_RECURSION
   r"(!m. m - 0 = m) /\
  (!m n. m - (SUC n) = PRE(m - n))"

  let SUB_0 ← prove
   r"!m. (0 - m = 0) /\ (m - 0 = m)"
   (REWRITE_TAC [SUB] THEN INDUCT_TAC THEN ASM_REWRITE_TAC [SUB, PRE])

  let SUB_PRESUC ← prove
   r"!m n. PRE(SUC m - n) = m - n"
   (GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [SUB, PRE])

  let SUB_SUC ← prove
   r"!m n. SUC m - SUC n = m - n"
   (REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [SUB, PRE, SUB_PRESUC])

  let SUB_REFL ← prove
   r"!n. n - n = 0"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [SUB_SUC, SUB_0])

  let ADD_SUB ← prove
   r"!m n. (m + n) - n = m"
   (GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES, SUB_SUC, SUB_0])

  let ADD_SUB2 ← prove
   r"!m n. (m + n) - m = n"
   (ONCE_REWRITE_TAC [ADD_SYM] THEN MATCH_ACCEPT_TAC ADD_SUB)

  let SUB_EQ_0 ← prove
   r"!m n. (m - n = 0) <=> m <= n"
   (REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC [SUB_SUC, LE_SUC, SUB_0] THEN
    REWRITE_TAC [LE, LE_0])

  let ADD_SUBR2 ← prove
   r"!m n. m - (m + n) = 0"
   (REWRITE_TAC [SUB_EQ_0, LE_ADD])

  let ADD_SUBR ← prove
   r"!m n. n - (m + n) = 0"
   (ONCE_REWRITE_TAC [ADD_SYM] THEN MATCH_ACCEPT_TAC ADD_SUBR2)

  let SUB_ADD ← prove
   r"!m n. n <= m ==> ((m - n) + n = m)"
   (REWRITE_TAC [LE_EXISTS] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [← ONCE_REWRITE_RULE [ADD_SYM] ADD_SUB] THEN
    MATCH_ACCEPT_TAC ADD_SYM)

  let SUB_ADD_LCANCEL ← prove
   r"!m n p. (m + n) - (m + p) = n - p"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES, SUB_0, SUB_SUC])

  let SUB_ADD_RCANCEL ← prove
   r"!m n p. (m + p) - (n + p) = m - n"
   (ONCE_REWRITE_TAC [ADD_SYM] THEN MATCH_ACCEPT_TAC SUB_ADD_LCANCEL)

  let LEFT_SUB_DISTRIB ← prove
   r"!m n p. m * (n - p) = m * n - m * p"
   (REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
    DISJ_CASES_TAC (← SPECL [← q r"n:num", ← q r"p:num"] LE_CASES) THENL
     [FIRST_ASSUM (fun th => tactic_of do pure (
        REWRITE_TAC [← REWRITE_RULE [← GSYM SUB_EQ_0] th])) THEN
      ASM_REWRITE_TAC [MULT_CLAUSES, SUB_EQ_0, LE_MULT_LCANCEL],
      POP_ASSUM (CHOOSE_THEN SUBST1_TAC o REWRITE_RULE [LE_EXISTS]) THEN
      REWRITE_TAC [LEFT_ADD_DISTRIB] THEN
      REWRITE_TAC [← ONCE_REWRITE_RULE [ADD_SYM] ADD_SUB]])

  let RIGHT_SUB_DISTRIB ← prove
   r"!m n p. (m - n) * p = m * p - n * p"
   (ONCE_REWRITE_TAC [MULT_SYM] THEN MATCH_ACCEPT_TAC LEFT_SUB_DISTRIB)

  let SUC_SUB1 ← prove
   r"!n. SUC n - 1 = n"
   (REWRITE_TAC [ONE, SUB_SUC, SUB_0])

  let EVEN_SUB ← prove
   r"!m n. EVEN(m - n) <=> m <= n \/ (EVEN(m) <=> EVEN(n))"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"m <= n:num") THENL
     [ASM_MESON_TAC [SUB_EQ_0, EVEN], ALL_TAC] THEN
    DISJ_CASES_TAC (← SPECL [← q r"m:num", ← q r"n:num"] LE_CASES) THEN ASM_SIMP_TAC [] THEN
    FIRST_ASSUM (MP_TAC o AP_TERM (← q r"EVEN") o MATCH_MP SUB_ADD) THEN
    ASM_MESON_TAC [EVEN_ADD])

  let ODD_SUB ← prove
   r"!m n. ODD(m - n) <=> n < m /\ ~(ODD m <=> ODD n)"
   (REWRITE_TAC [← GSYM NOT_EVEN, EVEN_SUB, DE_MORGAN_THM, NOT_LE] THEN
    CONV_TAC (fun t => (TAUT t).run))

  /- The factorial function. -/

  let FACT ← new_recursive_definition num_RECURSION
   r"(FACT 0 = 1) /\
   (!n. FACT (SUC n) = (SUC n) * FACT(n))"

  let FACT_LT ← prove
   r"!n. 0 < FACT n"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [FACT, LT_MULT] THEN
    REWRITE_TAC [ONE, LT_0])

  let FACT_LE ← prove
   r"!n. 1 <= FACT n"
   (REWRITE_TAC [ONE, LE_SUC_LT, FACT_LT])

  let FACT_NZ ← prove
   r"!n. ~(FACT n = 0)"
   (REWRITE_TAC [← GSYM LT_NZ, FACT_LT])

  let FACT_MONO ← prove
   r"!m n. m <= n ==> FACT m <= FACT n"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:num") SUBST1_TAC o REWRITE_RULE [LE_EXISTS]) THEN
    SPEC_TAC (← q r"d:num", ← q r"d:num") THEN
    INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, LE_REFL] THEN
    REWRITE_TAC [FACT] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"FACT(m + d)") THEN
    ASM_REWRITE_TAC [] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM mc3] THEN
    REWRITE_TAC [LE_MULT_RCANCEL] THEN
    REWRITE_TAC [ONE, LE_SUC, LE_0])

  return {
    EVEN, ODD, NOT_EVEN, NOT_ODD, EVEN_OR_ODD, EVEN_AND_ODD, EVEN_ADD,
    EVEN_MULT, EVEN_EXP, ODD_ADD, ODD_MULT, ODD_EXP, EVEN_DOUBLE, ODD_DOUBLE,
    EVEN_EXISTS_LEMMA, EVEN_EXISTS, ODD_EXISTS, EVEN_ODD_DECOMPOSITION, SUB,
    SUB_0, SUB_PRESUC, SUB_SUC, SUB_REFL, ADD_SUB, ADD_SUB2, SUB_EQ_0,
    ADD_SUBR2, ADD_SUBR, SUB_ADD, SUB_ADD_LCANCEL, SUB_ADD_RCANCEL,
    LEFT_SUB_DISTRIB, RIGHT_SUB_DISTRIB, SUC_SUB1, EVEN_SUB, ODD_SUB, FACT,
    FACT_LT, FACT_LE, FACT_NZ, FACT_MONO }

/-- The `arith.ml` theorems, part 6: more complicated theorems about
    exponentiation (`EXP_LT_0`, `LT_EXP`, `LE_EXP`, `EQ_EXP`, and the
    monotonicity lemmas). -/
structure ArithThms6 where
  EXP_LT_0        : thm
  LT_EXP          : thm
  LE_EXP          : thm
  EQ_EXP          : thm
  EXP_MONO_LE_IMP : thm
  EXP_MONO_LT_IMP : thm
  EXP_MONO_LE     : thm
  EXP_MONO_LT     : thm
  EXP_MONO_EQ     : thm
  deriving Inhabited

@[nospecialize]
def setupArith6 [HolBase] (N : HolMath.Nums.NumsThms)
    (A1 : ArithThms1) (A2 : ArithThms2) (A3 : ArithThms3) (A4 : ArithThms4)
    (ASM_MESON_TAC : List thm → tactic) :
    ExceptT String IO ArithThms6 := do
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { NOT_SUC, .. } := N
  let { RIGHT_FORALL_IMP_THM, .. } := HolBase.T
  let { DE_MORGAN_THM, .. } := HolBase.C
  let { ADD_CLAUSES, ONE, TWO, .. } := A1
  let { MULT_CLAUSES, MULT_ASSOC, MULT_2, EXP, EXP_EQ_0, EXP_ONE, LE, LT, LT_0, .. } := A2
  let { LE_REFL, LT_REFL, LE_ANTISYM, LE_TRANS, LET_TRANS, LTE_TRANS, NOT_LE,
        NOT_LT, LT_IMP_LE, .. } := A3
  let { LE_EXISTS, LT_EXISTS, LT_ADD, LE_MULT2, LE_MULT_LCANCEL,
        LE_MULT_RCANCEL, LT_MULT_RCANCEL, .. } := A4

  /- More complicated theorems about exponential. -/

  let EXP_LT_0 ← prove
   r"!n x. 0 < x EXP n <=> ~(x = 0) \/ (n = 0)"
   (REWRITE_TAC [← GSYM NOT_LE, LE, EXP_EQ_0, DE_MORGAN_THM])

  let LT_EXP ← prove
   r"!x m n. x EXP m < x EXP n <=> 2 <= x /\ m < n \/
                                 (x = 0) /\ ~(m = 0) /\ (n = 0)"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"x = 0") THEN ASM_REWRITE_TAC [] THENL
     [REWRITE_TAC [← GSYM NOT_LT, TWO, ONE, LT] THEN
      SPEC_TAC (← q r"n:num", ← q r"n:num") THEN INDUCT_TAC THEN
      REWRITE_TAC [EXP, NOT_SUC, MULT_CLAUSES, LT] THEN
      SPEC_TAC (← q r"m:num", ← q r"m:num") THEN INDUCT_TAC THEN
      REWRITE_TAC [EXP, MULT_CLAUSES, NOT_SUC, LT_REFL, LT] THEN
      REWRITE_TAC [ONE, LT_0], ALL_TAC] THEN
    EQ_TAC THENL
     [CONV_TAC CONTRAPOS_CONV THEN
      REWRITE_TAC [NOT_LT, DE_MORGAN_THM, NOT_LE] THEN
      REWRITE_TAC [TWO, ONE, LT] THEN
      ASM_REWRITE_TAC [← SYM ONE] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [EXP_ONE, LE_REFL] THEN
      FIRST_ASSUM (X_CHOOSE_THEN (← q r"d:num") SUBST1_TAC o
        REWRITE_RULE [LE_EXISTS]) THEN
      SPEC_TAC (← q r"d:num", ← q r"d:num") THEN INDUCT_TAC THEN
      REWRITE_TAC [ADD_CLAUSES, EXP, LE_REFL] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"1 * x EXP (n + d)") THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC [MULT_CLAUSES],
        REWRITE_TAC [LE_MULT_RCANCEL] THEN
        DISJ1_TAC THEN UNDISCH_TAC (← q r"~(x = 0)") THEN
        CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [NOT_LE] THEN
        REWRITE_TAC [ONE, LT]],
      STRIP_TAC THEN
      FIRST_ASSUM (X_CHOOSE_THEN (← q r"d:num") SUBST1_TAC o
        REWRITE_RULE [LT_EXISTS]) THEN
      SPEC_TAC (← q r"d:num", ← q r"d:num") THEN INDUCT_TAC THEN
      REWRITE_TAC [ADD_CLAUSES, EXP] THENL
       [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC (← q r"2 * x EXP m") THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC [MULT_2, LT_ADD, EXP_LT_0],
          ASM_REWRITE_TAC [LE_MULT_RCANCEL]],
        MATCH_MP_TAC LTE_TRANS THEN
        EXISTS_TAC (← q r"x EXP (m + SUC d)") THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [ADD_CLAUSES, EXP, MULT_ASSOC, LE_MULT_RCANCEL] THEN
        DISJ1_TAC THEN MATCH_MP_TAC LE_TRANS THEN
        EXISTS_TAC (← q r"x * 1") THEN CONJ_TAC THENL
         [REWRITE_TAC [MULT_CLAUSES, LE_REFL],
          REWRITE_TAC [LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
          UNDISCH_TAC (← q r"~(x = 0)") THEN
          CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [NOT_LE] THEN
          REWRITE_TAC [ONE, LT]]]])

  let LE_EXP ← prove
   r"!x m n. x EXP m <= x EXP n <=>
           if x = 0 then (m = 0) ==> (n = 0)
           else (x = 1) \/ m <= n"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM NOT_LT, LT_EXP, DE_MORGAN_THM] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [TWO, LT, ONE] THEN
    CONV_TAC (fun t => (do EQT_INTRO (← TAUT t)).run))

  let EQ_EXP ← prove
   r"!x m n. x EXP m = x EXP n <=>
           if x = 0 then (m = 0 <=> n = 0)
           else (x = 1) \/ m = n"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM LE_ANTISYM, LE_EXP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [LE_EXP] THEN
    REWRITE_TAC [← GSYM LE_ANTISYM] THEN CONV_TAC (fun t => (TAUT t).run))

  let EXP_MONO_LE_IMP ← prove
   r"!x y n. x <= y ==> x EXP n <= y EXP n"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    INDUCT_TAC THEN ASM_SIMP_TAC [LE_MULT2, EXP, LE_REFL])

  let EXP_MONO_LT_IMP ← prove
   r"!x y n. x < y /\ ~(n = 0) ==> x EXP n < y EXP n"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [NOT_SUC, EXP] THEN
    DISCH_TAC THEN MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC (← q r"x * y EXP n") THEN
    ASM_SIMP_TAC [LT_IMP_LE, LE_MULT_LCANCEL, LT_MULT_RCANCEL, EXP_MONO_LE_IMP,
                  EXP_EQ_0] THEN
    ASM_MESON_TAC [← CONJUNCT1 LT])

  let EXP_MONO_LE ← prove
   r"!x y n. x EXP n <= y EXP n <=> x <= y \/ n = 0"
   (REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC [EXP, LE_REFL, EXP_MONO_LE_IMP] THEN
    ASM_MESON_TAC [NOT_LE, EXP_MONO_LT_IMP])

  let EXP_MONO_LT ← prove
   r"!x y n. x EXP n < y EXP n <=> x < y /\ ~(n = 0)"
   (REWRITE_TAC [← GSYM NOT_LE, EXP_MONO_LE, DE_MORGAN_THM])

  let EXP_MONO_EQ ← prove
   r"!x y n. x EXP n = y EXP n <=> x = y \/ n = 0"
   (REWRITE_TAC [← GSYM LE_ANTISYM, EXP_MONO_LE] THEN CONV_TAC (fun t => (TAUT t).run))

  return {
    EXP_LT_0, LT_EXP, LE_EXP, EQ_EXP, EXP_MONO_LE_IMP, EXP_MONO_LT_IMP,
    EXP_MONO_LE, EXP_MONO_LT, EXP_MONO_EQ }

/-- The `arith.ml` theorems, part 7 (first part of "Division and modulus, via
    existence proof of their basic property"): `DIV` and `MOD` are introduced
    by an existence proof (`DIVMOD_EXIST_0`) plus `new_specification`
    (`DIVISION_0`), followed by their basic and uniqueness properties. -/
structure ArithThms7 where
  DIVMOD_EXIST     : thm
  DIVMOD_EXIST_0   : thm
  DIVISION_0       : thm
  DIVISION         : thm
  DIV_ZERO         : thm
  MOD_ZERO         : thm
  DIVISION_SIMP    : thm
  EQ_DIVMOD        : thm
  MOD_LT_EQ        : thm
  MOD_LT_EQ_LT     : thm
  DIVMOD_UNIQ_LEMMA : thm
  DIVMOD_UNIQ      : thm
  MOD_UNIQ         : thm
  DIV_UNIQ         : thm
  DIV_0            : thm
  MOD_0            : thm
  DIV_MULT         : thm
  MOD_MULT         : thm
  MOD_LT           : thm
  MOD_EQ_SELF      : thm
  MOD_CASES        : thm
  MOD_ADD_CASES    : thm
  MOD_EQ           : thm
  DIV_LE           : thm
  DIV_MUL_LE       : thm
  MOD_LE_TWICE     : thm
  DIV_1            : thm
  MOD_1            : thm
  DIV_LT           : thm
  MOD_MOD          : thm
  MOD_MOD_REFL     : thm
  MOD_MOD_LE       : thm
  MOD_EVEN_2       : thm
  DIV_MULT2        : thm
  MOD_MULT2        : thm
  MOD_EXISTS       : thm
  LE_RDIV_EQ       : thm
  RDIV_LT_EQ       : thm
  LE_LDIV_EQ       : thm
  LDIV_LT_EQ       : thm
  LE_LDIV          : thm
  DIV_MONO         : thm
  DIV_MONO_LT      : thm
  DIV_EQ_0         : thm
  MOD_DIV_EQ_0     : thm
  MOD_EQ_0         : thm
  DIV_EQ_SELF      : thm
  MOD_REFL         : thm
  deriving Inhabited

@[nospecialize]
def setupArith7 [HolBase] (N : HolMath.Nums.NumsThms)
    (A1 : ArithThms1) (A2 : ArithThms2) (A3 : ArithThms3) (A4 : ArithThms4)
    (A5 : ArithThms5)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic)
    (MESON' : List thm → term → IO (Except String thm))
    (IMP_REWRITE_TAC : List thm → tactic)
    (new_specification' : List String → thm → IO (Except String thm)) :
    ExceptT String IO ArithThms7 := do
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let new_specification (ns : List String) (th : thm) : ExceptT String IO thm :=
    new_specification' ns th
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { NOT_SUC, .. } := N
  let { RIGHT_EXISTS_AND_THM, EXISTS_REFL, LEFT_IMP_EXISTS_THM, AND_FORALL_THM,
        RIGHT_AND_EXISTS_THM, .. } := HolBase.T
  let { NOT_FORALL_THM, NOT_IMP, SKOLEM_THM, .. } := HolBase.C
  let { ADD_CLAUSES, ADD_SYM, ADD_ASSOC, ADD_AC, EQ_ADD_LCANCEL,
        EQ_ADD_RCANCEL, ONE, ADD1, .. } := A1
  let { MULT_CLAUSES, MULT_SYM, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_AC,
        MULT_EQ_0, EQ_MULT_LCANCEL, EQ_MULT_RCANCEL, MULT_2, LE, LT, LE_SUC_LT,
        LT_SUC_LE, LE_0, .. } := A2
  let { LE_REFL, LT_IMP_NE, LE_TRANS, LET_TRANS, LTE_TRANS, LE_CASES, NOT_LE,
        NOT_LT, LT_IMP_LE, LT_NZ, LE_1, .. } := A3
  let { LE_EXISTS, LE_ADD, LT_ADD, LT_ADDR, LE_ADD_RCANCEL, LT_ADD_LCANCEL,
        LT_ADD_RCANCEL, LE_ADD2, LT_ADD2, LE_MULT_LCANCEL, LT_MULT_LCANCEL,
        LT_MULT_RCANCEL, num_WOP, .. } := A4
  let { EVEN_EXISTS, SUB_ADD, .. } := A5

  /- Division and modulus, via existence proof of their basic property. -/

  let DIVMOD_EXIST ← prove
   r"!m n. ~(n = 0) ==> ?q r. (m = q * n + r) /\ r < n"
   (REPEAT STRIP_TAC THEN MP_TAC (← SPEC (← q r"\r. ?q. m = q * n + r") num_WOP) THEN
    BETA_TAC THEN DISCH_THEN (MP_TAC o (fun (th : thm) => (do pure (← EQ_IMP_RULE th).1 : ExceptT String IO thm))) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    DISCH_THEN (MP_TAC o SPECL [← q r"m:num", ← q r"0"]) THEN
    REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"r:num") MP_TAC) THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC (← q r"q:num")) MP_TAC) THEN
    DISCH_THEN (fun th => tactic_of do pure (
      MAP_EVERY EXISTS_TAC [← q r"q:num", ← q r"r:num"] THEN MP_TAC th)) THEN
    CONV_TAC CONTRAPOS_CONV THEN ASM_REWRITE_TAC [NOT_LT] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:num") SUBST_ALL_TAC o
      REWRITE_RULE [LE_EXISTS]) THEN
    REWRITE_TAC [NOT_FORALL_THM] THEN EXISTS_TAC (← q r"d:num") THEN
    REWRITE_TAC [NOT_IMP, RIGHT_AND_EXISTS_THM] THEN
    EXISTS_TAC (← q r"q + 1") THEN REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
    REWRITE_TAC [MULT_CLAUSES, ADD_ASSOC, LT_ADDR] THEN
    ASM_REWRITE_TAC [← GSYM NOT_LE, LE])

  let DIVMOD_EXIST_0 ← prove
   r"!m n. ?q r. if n = 0 then q = 0 /\ r = m
               else m = q * n + r /\ r < n"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_SIMP_TAC [DIVMOD_EXIST, RIGHT_EXISTS_AND_THM, EXISTS_REFL])

  let DIVISION_0 ← new_specification ["DIV", "MOD"]
    (← REWRITE_RULE [SKOLEM_THM] DIVMOD_EXIST_0)

  let DIVISION ← prove
   r"!m n. ~(n = 0) ==> (m = m DIV n * n + m MOD n) /\ m MOD n < n"
   (MESON_TAC [DIVISION_0])

  let DIV_ZERO ← prove
   r"!n. n DIV 0 = 0"
   (MESON_TAC [DIVISION_0])

  let MOD_ZERO ← prove
   r"!n. n MOD 0 = n"
   (MESON_TAC [DIVISION_0])

  let DIVISION_SIMP ← prove
   r"(!m n. m DIV n * n + m MOD n = m) /\
   (!m n. n * m DIV n + m MOD n = m)"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_SIMP_TAC [DIV_ZERO, MOD_ZERO, MULT_CLAUSES, ADD_CLAUSES] THEN
    ASM_MESON_TAC [DIVISION, MULT_SYM])

  let EQ_DIVMOD ← prove
   r"!p m n. m DIV p = n DIV p /\ m MOD p = n MOD p <=> m = n"
   (MESON_TAC [DIVISION_SIMP])

  let MOD_LT_EQ ← prove
   r"!m n. m MOD n < n <=> ~(n = 0)"
   (MESON_TAC [DIVISION, LE_1, ← CONJUNCT1 LT])

  let MOD_LT_EQ_LT ← prove
   r"!m n. m MOD n < n <=> 0 < n"
   (MESON_TAC [DIVISION, LE_1, ← CONJUNCT1 LT])

  let DIVMOD_UNIQ_LEMMA ← prove
   r"!m n q1 r1 q2 r2. ((m = q1 * n + r1) /\ r1 < n) /\
                     ((m = q2 * n + r2) /\ r2 < n)
                     ==> (q1 = q2) /\ (r1 = r2)"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"r1:num = r2") MP_TAC THENL
     [UNDISCH_TAC (← q r"m = q2 * n + r2") THEN
      ASM_REWRITE_TAC [] THEN
      DISJ_CASES_THEN MP_TAC (← SPECL [← q r"q1:num", ← q r"q2:num"] LE_CASES) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"d:num") SUBST1_TAC o REWRITE_RULE [LE_EXISTS]) THEN
      REWRITE_TAC [RIGHT_ADD_DISTRIB, ← GSYM ADD_ASSOC, EQ_ADD_LCANCEL] THENL
       [DISCH_TAC THEN UNDISCH_TAC (← q r"r1 < n"),
        DISCH_THEN (ASSUME_TAC o SYM) THEN UNDISCH_TAC (← q r"r2 < n")] THEN
      ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
      SPEC_TAC (← q r"d:num", ← q r"d:num") THEN INDUCT_TAC THEN
      REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES,
        ← GSYM NOT_LE, LE_ADD, ← GSYM ADD_ASSOC],
      DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC [] THEN
      CONV_TAC SYM_CONV THEN
      UNDISCH_TAC (← q r"m = q1 * n + r2") THEN
      ASM_REWRITE_TAC [EQ_ADD_RCANCEL, EQ_MULT_RCANCEL] THEN
      REPEAT (UNDISCH_TAC (← q r"r2 < n")) THEN
      ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [← GSYM NOT_LE, LE_0]])

  let DIVMOD_UNIQ ← prove
   r"!m n q r. (m = q * n + r) /\ r < n ==> (m DIV n = q) /\ (m MOD n = r)"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC o GSYM) THEN
    MATCH_MP_TAC DIVMOD_UNIQ_LEMMA THEN
    MAP_EVERY EXISTS_TAC [← q r"m:num", ← q r"n:num"] THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC DIVISION THEN
    DISCH_TAC THEN UNDISCH_TAC (← q r"r < n") THEN
    ASM_REWRITE_TAC [← GSYM NOT_LE, LE_0])

  let MOD_UNIQ ← prove
   r"!m n q r. (m = q * n + r) /\ r < n ==> (m MOD n = r)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP DIVMOD_UNIQ th])))

  let DIV_UNIQ ← prove
   r"!m n q r. (m = q * n + r) /\ r < n ==> (m DIV n = q)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP DIVMOD_UNIQ th])))

  let (DIV_0, MOD_0) ← CONJ_PAIR (← prove
   r"(!n. 0 DIV n = 0) /\ (!n. 0 MOD n = 0)"
   (REWRITE_TAC [AND_FORALL_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [DIV_ZERO, MOD_ZERO] THEN
    MATCH_MP_TAC DIVMOD_UNIQ THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES, LT_NZ]))

  let (DIV_MULT, MOD_MULT) ← CONJ_PAIR (← prove
   r"(!m n. ~(m = 0) ==> (m * n) DIV m = n) /\
   (!m n. (m * n) MOD m = 0)"
   (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"m = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES, MOD_0] THEN
    MATCH_MP_TAC DIVMOD_UNIQ THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES, MULT_AC, LT_NZ]))

  let MOD_LT ← prove
   r"!m n. m < n ==> m MOD n = m"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN
    EXISTS_TAC (← q r"0") THEN ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES])

  let MOD_EQ_SELF ← prove
   r"!m n. m MOD n = m <=> n = 0 \/ m < n"
   (MESON_TAC [MOD_ZERO, MOD_LT, DIVISION, LE_1])

  let MOD_CASES ← prove
   r"!n p. n < 2 * p ==> n MOD p = if n < p then n else n - p"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [MOD_LT] THEN
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC (← q r"1") THEN
    RULE_ASSUM_TAC (REWRITE_RULE [NOT_LT]) THEN CONJ_TAC THENL
     [REWRITE_TAC [MULT_CLAUSES] THEN ASM_MESON_TAC [SUB_ADD, ADD_SYM],
      ASM_MESON_TAC [LT_ADD_RCANCEL, SUB_ADD, MULT_2, LT_ADD2]])

  let MOD_ADD_CASES ← prove
   r"!m n p.
        m < p /\ n < p
        ==> (m + n) MOD p = if m + n < p then m + n else (m + n) - p"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_CASES THEN
    REWRITE_TAC [MULT_2] THEN ASM_MESON_TAC [LT_ADD2])

  let MOD_EQ ← prove
   r"!m n p q. m = n + q * p ==> m MOD p = n MOD p"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"p = 0") THENL
     [ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN
      DISCH_THEN SUBST1_TAC THEN REFL_TAC,
      DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC MOD_UNIQ THEN
      EXISTS_TAC (← q r"q + n DIV p") THEN
      POP_ASSUM (MP_TAC o MATCH_MP DIVISION) THEN
      DISCH_THEN (STRIP_ASSUME_TAC o GSYM o SPEC (← q r"n:num")) THEN
      ASM_REWRITE_TAC [RIGHT_ADD_DISTRIB, ← GSYM ADD_ASSOC] THEN
      MATCH_ACCEPT_TAC ADD_SYM])

  let DIV_LE ← prove
   r"!m n. m DIV n <= m"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [DIV_ZERO, LE_0] THEN
    FIRST_ASSUM (fun th => tactic_of do pure (
      GEN_REWRITE_TAC RAND_CONV [← MATCH_MP DIVISION th])) THEN
    UNDISCH_TAC (← q r"~(n = 0)") THEN SPEC_TAC (← q r"n:num", ← q r"n:num") THEN
    INDUCT_TAC THEN REWRITE_TAC [MULT_CLAUSES, ← GSYM ADD_ASSOC, LE_ADD])

  let DIV_MUL_LE ← prove
   r"!m n. n * (m DIV n) <= m"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, LE_0] THEN
    POP_ASSUM (MP_TAC o SPEC (← q r"m:num") o MATCH_MP DIVISION) THEN
    DISCH_THEN (fun th => tactic_of do pure (
      GEN_REWRITE_TAC RAND_CONV [← CONJUNCT1 th])) THEN
    REWRITE_TAC [LE_ADD, MULT_AC])

  let MOD_LE_TWICE ← prove
   r"!m n. 0 < m /\ m <= n ==> 2 * n MOD m <= n"
   (← do
    let m1 ← MESON [LT_ADD_RCANCEL]
     (← q r"n - m:num < m <=> (n - m) + m < m + m")
    pure
     (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"2 * m <= n") THENL
       [TRANS_TAC LE_TRANS (← q r"2 * m") THEN
        ASM_SIMP_TAC [LE_MULT_LCANCEL, DIVISION, LT_IMP_LE, LE_1],
        RULE_ASSUM_TAC (REWRITE_RULE [NOT_LE])] THEN
      TRANS_TAC LE_TRANS (← q r"m + n MOD m") THEN
      ASM_SIMP_TAC [MULT_2, LE_ADD_RCANCEL, DIVISION, LT_IMP_LE, LE_1] THEN
      ONCE_REWRITE_TAC [ADD_SYM] THEN
      SUBGOAL_THEN (← q r"n MOD m = n - m")
       (fun th => ASM_SIMP_TAC [LE_REFL, SUB_ADD, th]) THEN
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC (← q r"1") THEN
      ONCE_REWRITE_TAC [ADD_SYM] THEN ASM_SIMP_TAC [MULT_CLAUSES, SUB_ADD] THEN
      ONCE_REWRITE_TAC [m1] THEN
      ASM_SIMP_TAC [← GSYM MULT_2, SUB_ADD]))

  let (DIV_1, MOD_1) ← CONJ_PAIR (← prove
   r"(!n. n DIV 1 = n) /\ (!n. n MOD 1 = 0)"
   (SIMP_TAC [AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC DIVMOD_UNIQ THEN
    REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN REWRITE_TAC [ONE, LT]))

  let DIV_LT ← prove
   r"!m n. m < n ==> m DIV n = 0"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC (← q r"m:num") THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES])

  let MOD_MOD ← prove
   r"!m n p. (m MOD (n * p)) MOD n = m MOD n"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"p = 0") THEN ASM_REWRITE_TAC [MOD_ZERO, MULT_CLAUSES] THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [MOD_ZERO, MULT_CLAUSES] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_EQ THEN
    EXISTS_TAC (← q r"m DIV (n * p) * p") THEN
    MP_TAC (← SPECL [← q r"m:num", ← q r"n * p:num"] DIVISION) THEN
    ASM_REWRITE_TAC [MULT_EQ_0, MULT_AC, ADD_AC] THEN
    DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← GSYM th])))

  let MOD_MOD_REFL ← prove
   r"!m n. (m MOD n) MOD n = m MOD n"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [MOD_ZERO] THEN
    MP_TAC (← SPECL [← q r"m:num", ← q r"n:num", ← q r"1"] MOD_MOD) THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, MULT_EQ_0] THEN
    REWRITE_TAC [ONE, NOT_SUC])

  let MOD_MOD_LE ← prove
   r"!m n p. ~(n = 0) /\ n <= p ==> (m MOD n) MOD p = m MOD n"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_LT THEN
    ASM_MESON_TAC [DIVISION, LTE_TRANS])

  let MOD_EVEN_2 ← prove
   r"!m n. EVEN n ==> m MOD n MOD 2 = m MOD 2"
   (SIMP_TAC [EVEN_EXISTS, LEFT_IMP_EXISTS_THM, MOD_MOD])

  let DIV_MULT2 ← prove
   r"!m n p. ~(m = 0) ==> ((m * n) DIV (m * p) = n DIV p)"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"p = 0") THEN
    ASM_REWRITE_TAC [DIV_ZERO, MULT_CLAUSES] THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC (← q r"m * (n MOD p)") THEN
    ASM_SIMP_TAC [LT_MULT_LCANCEL, DIVISION] THEN
    ONCE_REWRITE_TAC [← AC MULT_AC (← q r"a * b * c:num = b * a * c")] THEN
    REWRITE_TAC [← GSYM LEFT_ADD_DISTRIB, EQ_MULT_LCANCEL] THEN
    ASM_SIMP_TAC [← GSYM DIVISION])

  let MOD_MULT2 ← prove
   r"!m n p. (m * n) MOD (m * p) = m * n MOD p"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"p = 0") THEN
    ASM_REWRITE_TAC [MOD_ZERO, MULT_CLAUSES] THEN ASM_CASES_TAC (← q r"m = 0") THEN
    ASM_REWRITE_TAC [MOD_ZERO, MULT_CLAUSES] THEN
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC (← q r"n DIV p") THEN
    ASM_SIMP_TAC [LT_MULT_LCANCEL, DIVISION] THEN
    ONCE_REWRITE_TAC [← AC MULT_AC (← q r"a * b * c:num = b * a * c")] THEN
    REWRITE_TAC [← GSYM LEFT_ADD_DISTRIB, EQ_MULT_LCANCEL] THEN
    ASM_SIMP_TAC [← GSYM DIVISION])

  let MOD_EXISTS ← prove
   r"!m n. (?q. m = n * q) <=> if n = 0 then (m = 0) else (m MOD n = 0)"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC [MOD_MULT] THEN
    EXISTS_TAC (← q r"m DIV n") THEN
    SUBGOAL_THEN (← q r"m = (m DIV n) * n + m MOD n")
     (fun th => GEN_REWRITE_TAC LAND_CONV [th]) THENL
     [ASM_MESON_TAC [DIVISION], ASM_REWRITE_TAC [ADD_CLAUSES, MULT_AC]])

  let LE_RDIV_EQ ← prove
   r"!a b n. ~(a = 0) ==> (n <= b DIV a <=> a * n <= b)"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"a * (b DIV a)") THEN
      ASM_REWRITE_TAC [DIV_MUL_LE, LE_MULT_LCANCEL],
      SUBGOAL_THEN (← q r"a * n < a * (b DIV a + 1)") MP_TAC THENL
       [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC (← q r"(b DIV a) * a + b MOD a") THEN
        CONJ_TAC THENL [ASM_MESON_TAC [DIVISION], ALL_TAC] THEN
        SIMP_TAC [LEFT_ADD_DISTRIB, MULT_SYM, MULT_CLAUSES, LT_ADD_LCANCEL] THEN
        ASM_MESON_TAC [DIVISION],
        ASM_REWRITE_TAC [LT_MULT_LCANCEL, ← GSYM ADD1, LT_SUC_LE]]])

  let RDIV_LT_EQ ← prove
   r"!a b n. ~(a = 0) ==> (b DIV a < n <=> b < a * n)"
   (SIMP_TAC [← GSYM NOT_LE, LE_RDIV_EQ])

  let LE_LDIV_EQ ← prove
   r"!a b n. ~(a = 0) ==> (b DIV a <= n <=> b < a * (n + 1))"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM NOT_LT] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [← GSYM LE_SUC_LT] THEN
    ASM_SIMP_TAC [LE_RDIV_EQ] THEN REWRITE_TAC [NOT_LT, NOT_LE, ADD1])

  let LDIV_LT_EQ ← prove
   r"!a b n. ~(a = 0) ==> (n < b DIV a <=> a * (n + 1) <= b)"
   (SIMP_TAC [← GSYM NOT_LE, LE_LDIV_EQ])

  let LE_LDIV ← prove
   r"!a b n. ~(a = 0) /\ b <= a * n ==> b DIV a <= n"
   (SIMP_TAC [LE_LDIV_EQ, LEFT_ADD_DISTRIB, MULT_CLAUSES] THEN
    MESON_TAC [LT_ADD, LT_NZ, LET_TRANS])

  let DIV_MONO ← prove
   r"!m n p. m <= n ==> m DIV p <= n DIV p"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"p = 0") THEN
    ASM_REWRITE_TAC [DIV_ZERO, LE_REFL] THEN
    MATCH_MP_TAC (← MESON [LE_REFL] (← q r"(!k:num. k <= a ==> k <= b) ==> a <= b")) THEN
    ASM_SIMP_TAC [LE_RDIV_EQ] THEN ASM_MESON_TAC [LE_TRANS])

  let DIV_MONO_LT ← prove
   r"!m n p. ~(p = 0) /\ m + p <= n ==> m DIV p < n DIV p"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC (← MESON [ADD1, LE_SUC_LT, LE_REFL]
     (← q r"(!k:num. k <= a ==> k + 1 <= b) ==> a < b")) THEN
    ASM_SIMP_TAC [LE_RDIV_EQ, LEFT_ADD_DISTRIB, MULT_CLAUSES] THEN
    ASM_MESON_TAC [LE_REFL, LE_TRANS, LE_ADD2, ADD_SYM])

  let DIV_EQ_0 ← prove
   r"!m n. ~(n = 0) ==> ((m DIV n = 0) <=> m < n)"
   (REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [FIRST_ASSUM (SUBST1_TAC o CONJUNCT1 o SPEC (← q r"m:num") o MATCH_MP DIVISION) THEN
      ASM_SIMP_TAC [MULT_CLAUSES, ADD_CLAUSES, DIVISION],
      MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC (← q r"m:num") THEN
      ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES]])

  let MOD_DIV_EQ_0 ← prove
   r"!m n. ~(n = 0) ==> (m MOD n) DIV n = 0"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (fun th => IMP_REWRITE_TAC [th, DIV_EQ_0, MOD_LT_EQ]))

  let MOD_EQ_0 ← prove
   r"!m n. (m MOD n = 0) <=> ?q. m = q * n"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, MOD_ZERO] THEN
    REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [FIRST_ASSUM (SUBST1_TAC o CONJUNCT1 o SPEC (← q r"m:num") o MATCH_MP DIVISION) THEN
      ASM_SIMP_TAC [MULT_CLAUSES, ADD_CLAUSES, DIVISION] THEN MESON_TAC [],
      MATCH_MP_TAC MOD_UNIQ THEN ASM_SIMP_TAC [ADD_CLAUSES, MULT_AC] THEN
      ASM_MESON_TAC [NOT_LE, ← CONJUNCT1 LE]])

  let mc3 ← liftExcept (match (CONJUNCTS MULT_CLAUSES)[2]? with
    | some t => .ok t | none => .error "el")

  let DIV_EQ_SELF ← prove
   r"!m n. m DIV n = m <=> m = 0 \/ n = 1"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"m = 0") THEN ASM_REWRITE_TAC [DIV_0] THEN
    ASM_CASES_TAC (← q r"n = 1") THEN ASM_REWRITE_TAC [DIV_1] THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [DIV_ZERO] THEN
    MATCH_MP_TAC LT_IMP_NE THEN ASM_SIMP_TAC [RDIV_LT_EQ] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM mc3] THEN
    ASM_REWRITE_TAC [LT_MULT_RCANCEL] THEN
    REWRITE_TAC [← GSYM NOT_LE, ONE, LE] THEN ASM_REWRITE_TAC [← GSYM ONE])

  let MOD_REFL ← prove
   r"!n. n MOD n = 0"
   (SIMP_TAC [MOD_EQ_0] THEN MESON_TAC [MULT_CLAUSES])

  return {
    DIVMOD_EXIST, DIVMOD_EXIST_0, DIVISION_0, DIVISION, DIV_ZERO, MOD_ZERO,
    DIVISION_SIMP, EQ_DIVMOD, MOD_LT_EQ, MOD_LT_EQ_LT, DIVMOD_UNIQ_LEMMA,
    DIVMOD_UNIQ, MOD_UNIQ, DIV_UNIQ, DIV_0, MOD_0, DIV_MULT, MOD_MULT, MOD_LT,
    MOD_EQ_SELF, MOD_CASES, MOD_ADD_CASES, MOD_EQ, DIV_LE, DIV_MUL_LE,
    MOD_LE_TWICE, DIV_1, MOD_1, DIV_LT, MOD_MOD, MOD_MOD_REFL, MOD_MOD_LE,
    MOD_EVEN_2, DIV_MULT2, MOD_MULT2, MOD_EXISTS, LE_RDIV_EQ, RDIV_LT_EQ,
    LE_LDIV_EQ, LDIV_LT_EQ, LE_LDIV, DIV_MONO, DIV_MONO_LT, DIV_EQ_0,
    MOD_DIV_EQ_0, MOD_EQ_0, DIV_EQ_SELF, MOD_REFL }

/-- The `arith.ml` theorems, part 8 (continuation of "Division and modulus"):
    from `EVEN_MOD` through `EXISTS_MOD_THM` (arith.ml lines 1402-1672). -/
structure ArithThms8 where
  EVEN_MOD          : thm
  ODD_MOD           : thm
  MOD_2_CASES       : thm
  EVEN_MOD_EVEN     : thm
  ODD_MOD_EVEN      : thm
  HALF_DOUBLE       : thm
  DOUBLE_HALF       : thm
  MOD_MULT_RMOD     : thm
  MOD_MULT_LMOD     : thm
  MOD_MULT_MOD2     : thm
  MOD_EXP_MOD       : thm
  MOD_MULT_ADD      : thm
  DIV_MULT_ADD      : thm
  MOD_ADD_MOD       : thm
  DIV_ADD_MOD       : thm
  MOD_ADD_EQ_EQ     : thm
  DIV_ADD_EQ_EQ     : thm
  DIV_ADD_EQ        : thm
  MOD_ADD_EQ        : thm
  DIV_REFL          : thm
  MOD_LE            : thm
  DIV_MONO2         : thm
  DIV_LE_EXCLUSION  : thm
  DIV_EQ_EXCLUSION  : thm
  MULT_DIV_LE       : thm
  DIV_DIV           : thm
  DIV_MOD           : thm
  MOD_MULT_MOD      : thm
  MOD_MOD_EXP_MIN   : thm
  DIV_EXP           : thm
  MOD_EXP           : thm
  FORALL_LT_MOD_THM : thm
  FORALL_MOD_THM    : thm
  EXISTS_LT_MOD_THM : thm
  EXISTS_MOD_THM    : thm
  deriving Inhabited

@[nospecialize]
def setupArith8 [HolBase] (N : HolMath.Nums.NumsThms)
    (A1 : ArithThms1) (A2 : ArithThms2) (A3 : ArithThms3) (A4 : ArithThms4)
    (A5 : ArithThms5) (A6 : ArithThms6) (A7 : ArithThms7)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic)
    (MESON' : List thm → term → IO (Except String thm))
    (METIS_TAC : List thm → tactic) (ASM_METIS_TAC : List thm → tactic) :
    ExceptT String IO ArithThms8 := do
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { NOT_SUC, .. } := N
  let { EQ_SYM_EQ, EQ_TRANS, LEFT_IMP_EXISTS_THM, AND_FORALL_THM, MONO_IMP, .. } := HolBase.T
  let { DE_MORGAN_THM, .. } := HolBase.C
  let { ADD_CLAUSES, ADD_SYM, ADD_ASSOC, ADD_AC, EQ_ADD_LCANCEL,
        EQ_ADD_RCANCEL, ONE, TWO, ADD1, .. } := A1
  let { MULT_CLAUSES, MULT_SYM, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB,
        MULT_ASSOC, MULT_AC, MULT_EQ_0, EQ_MULT_LCANCEL, EQ_MULT_RCANCEL, EXP,
        EXP_EQ_0, EXP_ZERO, EXP_ADD, EXP_ONE, LE, LT, MIN, LT_SUC_LE, LE_0,
        LT_0, .. } := A2
  let { LE_REFL, LE_ANTISYM, LE_TRANS, LET_TRANS, LTE_TRANS, LE_CASES, NOT_LE,
        NOT_LT, .. } := A3
  let { LE_EXISTS, LE_ADD, LE_ADD_RCANCEL, LE_MULT_LCANCEL, LE_MULT_RCANCEL,
        LT_MULT_RCANCEL, .. } := A4
  let { NOT_EVEN, NOT_ODD, EVEN_EXISTS, SUB_ADD, .. } := A5
  let { EXP_LT_0, LT_EXP, LE_EXP, .. } := A6
  let { DIVISION, DIV_ZERO, MOD_ZERO, DIVISION_SIMP, MOD_LT_EQ, DIVMOD_UNIQ,
        MOD_UNIQ, DIV_UNIQ, DIV_0, MOD_0, DIV_MULT, MOD_LT, MOD_EQ_SELF,
        MOD_EQ, MOD_1, MOD_MOD, MOD_EVEN_2, LE_RDIV_EQ, MOD_EQ_0, .. } := A7

  let EVEN_MOD ← prove
   r"!n. EVEN(n) <=> n MOD 2 = 0"
   (REWRITE_TAC [EVEN_EXISTS, MOD_EQ_0] THEN MESON_TAC [MULT_SYM])

  let ODD_MOD ← prove
   r"!n. ODD(n) <=> n MOD 2 = 1"
   (GEN_TAC THEN REWRITE_TAC [← GSYM NOT_EVEN, EVEN_MOD] THEN
    SUBGOAL_THEN (← q r"n MOD 2 < 2") MP_TAC THENL
     [SIMP_TAC [DIVISION, TWO, NOT_SUC], ALL_TAC] THEN
    SPEC_TAC (← q r"n MOD 2", ← q r"n:num") THEN
    REWRITE_TAC [TWO, ONE, LT] THEN MESON_TAC [NOT_SUC])

  let MOD_2_CASES ← prove
   r"!n. n MOD 2 = if EVEN n then 0 else 1"
   (MESON_TAC [EVEN_MOD, ODD_MOD, NOT_ODD])

  let EVEN_MOD_EVEN ← prove
   r"!m n. EVEN n ==> (EVEN(m MOD n) <=> EVEN m)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [EVEN_MOD] THEN
    ASM_SIMP_TAC [MOD_EVEN_2])

  let ODD_MOD_EVEN ← prove
   r"!m n. EVEN n ==> (ODD(m MOD n) <=> ODD m)"
   (SIMP_TAC [← GSYM NOT_EVEN, EVEN_MOD_EVEN])

  let HALF_DOUBLE ← prove
   r"(!n. (2 * n) DIV 2 = n) /\ (!n. (n * 2) DIV 2 = n)"
   (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
    SIMP_TAC [DIV_MULT, TWO, NOT_SUC])

  let DOUBLE_HALF ← prove
   r"(!n. EVEN n ==> 2 * n DIV 2 = n) /\
   (!n. EVEN n ==> n DIV 2 * 2 = n)"
   (SIMP_TAC [EVEN_EXISTS, LEFT_IMP_EXISTS_THM, HALF_DOUBLE] THEN
    REWRITE_TAC [MULT_SYM])

  let MOD_MULT_RMOD ← prove
   r"!m n p. (m * (p MOD n)) MOD n = (m * p) MOD n"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [MOD_ZERO] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_EQ THEN EXISTS_TAC (← q r"m * p DIV n") THEN
    REWRITE_TAC [← GSYM MULT_ASSOC, ← GSYM LEFT_ADD_DISTRIB] THEN
    REWRITE_TAC [EQ_MULT_LCANCEL] THEN DISJ2_TAC THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN ASM_SIMP_TAC [DIVISION])

  let MOD_MULT_LMOD ← prove
   r"!m n p. ((m MOD n) * p) MOD n = (m * p) MOD n"
   (ONCE_REWRITE_TAC [MULT_SYM] THEN SIMP_TAC [MOD_MULT_RMOD])

  let MOD_MULT_MOD2 ← prove
   r"!m n p. ((m MOD n) * (p MOD n)) MOD n = (m * p) MOD n"
   (SIMP_TAC [MOD_MULT_RMOD, MOD_MULT_LMOD])

  let MOD_EXP_MOD ← prove
   r"!m n p. ((m MOD n) EXP p) MOD n = (m EXP p) MOD n"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [MOD_ZERO] THEN SPEC_TAC (← q r"p:num", ← q r"p:num") THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC [EXP] THEN ASM_SIMP_TAC [MOD_MULT_LMOD] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"(m * ((m MOD n) EXP p) MOD n) MOD n") THEN CONJ_TAC THENL
     [ALL_TAC, ASM_REWRITE_TAC []] THEN
    ASM_SIMP_TAC [MOD_MULT_RMOD])

  let MOD_MULT_ADD ← prove
   r"(!m n p. (m * n + p) MOD n = p MOD n) /\
   (!m n p. (n * m + p) MOD n = p MOD n) /\
   (!m n p. (p + m * n) MOD n = p MOD n) /\
   (!m n p. (p + n * m) MOD n = p MOD n)"
   (MATCH_MP_TAC (← TAUT (← q r"(p ==> q) /\ p ==> p /\ q")) THEN
    CONJ_TAC THENL [SIMP_TAC [MULT_AC, ADD_AC], REPEAT GEN_TAC] THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC (← q r"m + p DIV n") THEN
    ASM_SIMP_TAC [RIGHT_ADD_DISTRIB, ← GSYM ADD_ASSOC, EQ_ADD_LCANCEL, DIVISION])

  let DIV_MULT_ADD ← prove
   r"(!a b n. ~(n = 0) ==> (a * n + b) DIV n = a + b DIV n) /\
   (!a b n. ~(n = 0) ==> (n * a + b) DIV n = a + b DIV n) /\
   (!a b n. ~(n = 0) ==> (b + a * n) DIV n = b DIV n + a) /\
   (!a b n. ~(n = 0) ==> (b + n * a) DIV n = b DIV n + a)"
   (MATCH_MP_TAC (← TAUT (← q r"(p ==> q) /\ p ==> p /\ q")) THEN
    CONJ_TAC THENL [SIMP_TAC [MULT_AC, ADD_AC], REPEAT STRIP_TAC] THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC (← q r"b MOD n") THEN
    REWRITE_TAC [RIGHT_ADD_DISTRIB, ← GSYM ADD_ASSOC] THEN
    ASM_MESON_TAC [DIVISION])

  let MOD_ADD_MOD ← prove
   r"!a b n. (a MOD n + b MOD n) MOD n = (a + b) MOD n"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [MOD_ZERO] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_EQ THEN
    EXISTS_TAC (← q r"a DIV n + b DIV n") THEN REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
    ONCE_REWRITE_TAC [← AC ADD_AC (← q r"(a + b) + (c + d) = (c + a) + (d + b)")] THEN
    BINOP_TAC THEN ASM_SIMP_TAC [DIVISION])

  let DIV_ADD_MOD ← prove
   r"!a b n. ~(n = 0)
           ==> (((a + b) MOD n = a MOD n + b MOD n) <=>
                ((a + b) DIV n = a DIV n + b DIV n))"
   (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP DIVISION) THEN
    DISCH_THEN (fun th => tactic_of do pure (MAP_EVERY (MP_TAC o CONJUNCT1 o C SPEC th)
      [← q r"a + b:num", ← q r"a:num", ← q r"b:num"])) THEN
    DISCH_THEN (fun th1 => DISCH_THEN (fun th2 => tactic_of do pure (
      MP_TAC (← MK_COMB (← AP_TERM (← q r"(+)") th2, th1))))) THEN
    DISCH_THEN (fun th => GEN_REWRITE_TAC (funpow 2 LAND_CONV) [th]) THEN
    ONCE_REWRITE_TAC [← AC ADD_AC (← q r"(a + b) + c + d = (a + c) + (b + d)")] THEN
    REWRITE_TAC [← GSYM RIGHT_ADD_DISTRIB] THEN
    DISCH_THEN (fun th => EQ_TAC THEN DISCH_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC [EQ_ADD_RCANCEL, EQ_ADD_LCANCEL, EQ_MULT_RCANCEL] THEN
    REWRITE_TAC [EQ_SYM_EQ])

  let MOD_ADD_EQ_EQ ← prove
   r"!n x y. (x + y) MOD n = x MOD n + y MOD n <=>
           n = 0 \/ x MOD n + y MOD n < n"
   (MESON_TAC [MOD_ZERO, MOD_EQ_SELF, MOD_ADD_MOD])

  let DIV_ADD_EQ_EQ ← prove
   r"!n x y. (x + y) DIV n = x DIV n + y DIV n <=>
           n = 0 \/ x MOD n + y MOD n < n"
   (METIS_TAC [DIV_ZERO, ADD_CLAUSES, DIV_ADD_MOD, MOD_ADD_EQ_EQ])

  let DIV_ADD_EQ ← prove
   r"!n x y. x MOD n + y MOD n < n ==> (x + y) DIV n = x DIV n + y DIV n"
   (SIMP_TAC [DIV_ADD_EQ_EQ])

  let MOD_ADD_EQ ← prove
   r"!n x y. x MOD n + y MOD n < n ==> (x + y) MOD n = x MOD n + y MOD n"
   (SIMP_TAC [MOD_ADD_EQ_EQ])

  let DIV_REFL ← prove
   r"!n. ~(n = 0) ==> (n DIV n = 1)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
    EXISTS_TAC (← q r"0") THEN REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES] THEN
    POP_ASSUM MP_TAC THEN SPEC_TAC (← q r"n:num", ← q r"n:num") THEN
    INDUCT_TAC THEN REWRITE_TAC [LT_0])

  let MOD_LE ← prove
   r"!m n. m MOD n <= m"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [MOD_ZERO, LE_REFL] THEN FIRST_ASSUM
    (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV
     [← MATCH_MP DIVISION th])) THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN REWRITE_TAC [LE_ADD])

  let DIV_MONO2 ← prove
   r"!m n p. ~(p = 0) /\ p <= m ==> n DIV m <= n DIV p"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [LE_RDIV_EQ] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"m * n DIV m") THEN
    ASM_REWRITE_TAC [LE_MULT_RCANCEL] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"m:num"] DIVISION) THEN ASM_MESON_TAC [LE_ADD, LE])

  let DIV_LE_EXCLUSION ← prove
   r"!a b c d. ~(b = 0) /\ b * c < (a + 1) * d ==> c DIV d <= a DIV b"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"d = 0") THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, LT] THEN STRIP_TAC THEN
    MATCH_MP_TAC (← MESON [LE_REFL] (← q r"(!k:num. k <= a ==> k <= b) ==> a <= b")) THEN
    X_GEN_TAC (← q r"k:num") THEN
    SUBGOAL_THEN (← q r"b * d * k <= b * c ==> (b * k) * d < (a + 1) * d") MP_TAC THENL
     [ASM_MESON_TAC [LET_TRANS, MULT_AC], ALL_TAC] THEN
    MATCH_MP_TAC MONO_IMP THEN
    ASM_SIMP_TAC [LE_MULT_LCANCEL, LT_MULT_RCANCEL, LE_RDIV_EQ] THEN
    REWRITE_TAC [← GSYM ADD1, LT_SUC_LE])

  let DIV_EQ_EXCLUSION ← prove
   r"!a b c d.
        b * c < (a + 1) * d /\ a * d < (c + 1) * b ==> (a DIV b = c DIV d)"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"b = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES, LT] THEN
    ASM_CASES_TAC (← q r"d = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES, LT] THEN
    ASM_MESON_TAC [MULT_SYM, LE_ANTISYM, DIV_LE_EXCLUSION])

  let MULT_DIV_LE ← prove
   r"!m n p. m * (n DIV p) <= (m * n) DIV p"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"p = 0") THEN
    ASM_REWRITE_TAC [LE_REFL, DIV_ZERO, MULT_CLAUSES] THEN
    ASM_SIMP_TAC [LE_RDIV_EQ] THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"n:num") o MATCH_MP DIVISION) THEN
    DISCH_THEN (fun th => tactic_of do pure (
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← CONJUNCT1 th])) THEN
    REWRITE_TAC [LEFT_ADD_DISTRIB] THEN REWRITE_TAC [MULT_AC, LE_ADD])

  let DIV_DIV ← prove
   r"!m n p. (m DIV n) DIV p = m DIV (n * p)"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"p = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES, DIV_ZERO] THEN
    ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [DIV_0, MULT_CLAUSES, DIV_ZERO] THEN
    REWRITE_TAC [MULT_EQ_0, DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (← MESON [LE_ANTISYM] (← q r"(!k. k <= m <=> k <= n) ==> m = n")) THEN
    ASM_SIMP_TAC [LE_RDIV_EQ, MULT_EQ_0, MULT_ASSOC])

  let DIV_MOD ← prove
   r"!m n p. (m DIV n) MOD p = (m MOD (n * p)) DIV n"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"p = 0") THEN ASM_REWRITE_TAC [MOD_ZERO, MULT_CLAUSES] THEN
    ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [MOD_0, MULT_CLAUSES, DIV_ZERO] THEN
    MATCH_MP_TAC (← MESON [LE_ANTISYM] (← q r"(!k. k <= m <=> k <= n) ==> m = n")) THEN
    X_GEN_TAC (← q r"k:num") THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q r"k + p * ((m DIV n) DIV p) <= (m DIV n)") THEN CONJ_TAC THENL
     [MP_TAC (← SPECL [← q r"m DIV n", ← q r"p:num"] DIVISION) THEN ASM_REWRITE_TAC [],
      MP_TAC (← SPECL [← q r"m:num", ← q r"n * p:num"] DIVISION) THEN
      ASM_SIMP_TAC [LE_RDIV_EQ, MULT_EQ_0, DIV_DIV, LEFT_ADD_DISTRIB]] THEN
    REWRITE_TAC [MULT_AC] THEN MESON_TAC [ADD_SYM, MULT_SYM, LE_ADD_RCANCEL])

  let MOD_MULT_MOD ← prove
   r"!m n p. m MOD (n * p) = n * (m DIV n) MOD p + m MOD n"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, MOD_ZERO, ADD_CLAUSES] THEN
    ASM_CASES_TAC (← q r"p = 0") THENL
     [ASM_REWRITE_TAC [MULT_CLAUSES, MOD_ZERO] THEN
      ASM_METIS_TAC [DIVISION, MULT_SYM],
      ALL_TAC] THEN
    MATCH_MP_TAC (← MESON [EQ_ADD_LCANCEL] (← q r"(?a. a + x = a + y) ==> x = y")) THEN
    EXISTS_TAC (← q r"m DIV n DIV p * n * p") THEN
    REWRITE_TAC [DIVISION_SIMP, DIV_DIV] THEN
    REWRITE_TAC [← AC MULT_AC (← q r"d * n * p = n * (d * p)")] THEN
    REWRITE_TAC [← GSYM LEFT_ADD_DISTRIB, ADD_ASSOC, ← GSYM DIV_DIV] THEN
    REWRITE_TAC [DIVISION_SIMP])

  let MOD_MOD_EXP_MIN ← prove
   r"!x p m n. x MOD (p EXP m) MOD (p EXP n) = x MOD (p EXP (MIN m n))"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"p = 0") THENL
     [ASM_REWRITE_TAC [EXP_ZERO, MIN] THEN ASM_CASES_TAC (← q r"m = 0") THEN
      ASM_REWRITE_TAC [MOD_ZERO, MOD_1, MOD_0, LE_0] THEN
      ASM_CASES_TAC (← q r"m:num <= n") THEN ASM_REWRITE_TAC [] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [LE],
      REWRITE_TAC [MIN]] THEN
     ASM_CASES_TAC (← q r"m:num <= n") THEN ASM_REWRITE_TAC [] THENL
     [FIRST_X_ASSUM (CHOOSE_THEN SUBST1_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
      MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC (← q r"p EXP m") THEN
      ASM_SIMP_TAC [DIVISION, EXP_EQ_0, LE_EXP, LE_ADD],
      SUBGOAL_THEN (← q r"?d. m = n + d") (CHOOSE_THEN SUBST1_TAC) THENL
       [ASM_MESON_TAC [LE_CASES, LE_EXISTS],
        ASM_SIMP_TAC [EXP_ADD, MOD_MOD, MULT_EQ_0, EXP_EQ_0]]])

  let (DIV_EXP, MOD_EXP) ← CONJ_PAIR (← prove
   r"(!m n p. ~(m = 0)
            ==> (m EXP n) DIV (m EXP p) =
                if p <= n then m EXP (n - p)
                else if m = 1 then 1 else 0) /\
   (!m n p. ~(m = 0)
            ==> (m EXP n) MOD (m EXP p) =
                if p <= n \/ m = 1 then 0 else m EXP n)"
   (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"m = 0") THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC DIVMOD_UNIQ THEN
    ASM_CASES_TAC (← q r"p:num <= n") THEN
    ASM_SIMP_TAC [← GSYM EXP_ADD, EXP_LT_0, SUB_ADD, ADD_CLAUSES] THEN
    ASM_CASES_TAC (← q r"m = 1") THEN
    ASM_REWRITE_TAC [EXP_ONE, ADD_CLAUSES, MULT_CLAUSES, LT_EXP] THEN
    REWRITE_TAC [LT, ← GSYM NOT_LT, ONE, TWO] THEN
    ASM_REWRITE_TAC [← SYM ONE, ← GSYM NOT_LE]))

  let FORALL_LT_MOD_THM ← prove
   r"!P n. (!a. a < n ==> P a) <=> n = 0 \/ !a. P(a MOD n)"
   (MESON_TAC [LT, MOD_EQ_SELF, MOD_LT_EQ])

  let FORALL_MOD_THM ← prove
   r"!P n. ~(n = 0) ==> ((!a. P(a MOD n)) <=> (!a. a < n ==> P a))"
   (SIMP_TAC [FORALL_LT_MOD_THM])

  let EXISTS_LT_MOD_THM ← prove
   r"!P n. (?a. a < n /\ P a) <=> ~(n = 0) /\ ?a. P(a MOD n)"
   (MESON_TAC [LT, MOD_EQ_SELF, MOD_LT_EQ])

  let EXISTS_MOD_THM ← prove
   r"!P n. ~(n = 0) ==> ((?a. P(a MOD n)) <=> (?a. a < n /\ P a))"
   (SIMP_TAC [EXISTS_LT_MOD_THM])

  return {
    EVEN_MOD, ODD_MOD, MOD_2_CASES, EVEN_MOD_EVEN, ODD_MOD_EVEN, HALF_DOUBLE,
    DOUBLE_HALF, MOD_MULT_RMOD, MOD_MULT_LMOD, MOD_MULT_MOD2, MOD_EXP_MOD,
    MOD_MULT_ADD, DIV_MULT_ADD, MOD_ADD_MOD, DIV_ADD_MOD, MOD_ADD_EQ_EQ,
    DIV_ADD_EQ_EQ, DIV_ADD_EQ, MOD_ADD_EQ, DIV_REFL, MOD_LE, DIV_MONO2,
    DIV_LE_EXCLUSION, DIV_EQ_EXCLUSION, MULT_DIV_LE, DIV_DIV, DIV_MOD,
    MOD_MULT_MOD, MOD_MOD_EXP_MIN, DIV_EXP, MOD_EXP, FORALL_LT_MOD_THM,
    FORALL_MOD_THM, EXISTS_LT_MOD_THM, EXISTS_MOD_THM }

/-- The `arith.ml` theorems, part 9 (arith.ml lines 1672-1904): the cutoff
    subtraction / predecessor / DIV / MOD elimination theorems, the `minimal`
    binder and its lemmas, the transitive-relation stepwise lemmas, and the two
    forms of Dependent Choice. -/
structure ArithThms9 where
  PRE_ELIM_THM             : thm
  PRE_ELIM_THM'            : thm
  SUB_ELIM_THM             : thm
  SUB_ELIM_THM'            : thm
  DIVMOD_ELIM_THM          : thm
  DIVMOD_ELIM_THM'         : thm
  minimal                  : thm
  MINIMAL                  : thm
  MINIMAL_UNIQUE           : thm
  LE_MINIMAL               : thm
  MINIMAL_LE               : thm
  MINIMAL_UBOUND           : thm
  MINIMAL_LBOUND           : thm
  MINIMAL_MONO             : thm
  TRANSITIVE_STEPWISE_LT_EQ : thm
  TRANSITIVE_STEPWISE_LT   : thm
  TRANSITIVE_STEPWISE_LE_EQ : thm
  TRANSITIVE_STEPWISE_LE   : thm
  DEPENDENT_CHOICE_FIXED   : thm
  DEPENDENT_CHOICE         : thm
  deriving Inhabited

/-- The theorems of arith.ml 1672-1870.  The conversions MOD_DOWN_CONV and
    NUM_CANCEL_CONV and the rule LE_IMP, which sit among them in the OCaml,
    are separate definitions below; `parse_as_binder "minimal"` is
    `setupMinimalBinder`, which Session runs first. -/
@[nospecialize]
def setupArith9 [HolBase] (N : HolMath.Nums.NumsThms)
    (A1 : ArithThms1) (A2 : ArithThms2) (A3 : ArithThms3) (A4 : ArithThms4)
    (A5 : ArithThms5) (A7 : ArithThms7)
    (MESON_TAC : List thm → tactic) (ASM_MESON_TAC : List thm → tactic)
    (MESON' : List thm → term → IO (Except String thm))
    (SELECT_CONV' : term → Except String thm)
    (new_definition' : term → IO (Except String thm))
    (prove_recursive_functions_exist' : thm → term → IO (Except String thm)) :
    ExceptT String IO ArithThms9 := do
  let MESON (ths : List thm) (t : term) : ExceptT String IO thm := MESON' ths t
  let SELECT_CONV : ioconv := fun t => pure (SELECT_CONV' t)
  let new_definition (s : String) : ExceptT String IO thm := do
    new_definition' (← q s)
  let prove_recursive_functions_exist (ax : thm) (t : term) : ExceptT String IO thm :=
    prove_recursive_functions_exist' ax t
  let INDUCT_TAC := HolMath.Nums.INDUCT_TAC N.num_INDUCTION
  let { NOT_SUC, SUC_INJ, num_CASES, num_RECURSION, .. } := N
  let { LEFT_IMP_EXISTS_THM, SWAP_FORALL_THM, LEFT_FORALL_IMP_THM, EXISTS_REFL,
        MONO_EXISTS, AND_FORALL_THM, .. } := HolBase.T
  let { SELECT_UNIQUE, .. } := HolBase.C
  let { PRE, ADD_CLAUSES, EQ_ADD_LCANCEL, .. } := A1
  let { LE, LT, LE_SUC_LT, .. } := A2
  let { LE_REFL, LE_TRANS, LT_CASES, LTE_CASES, NOT_LE, NOT_LT, LT_IMP_LE, .. } := A3
  let { LE_EXISTS, LT_EXISTS, LE_ADD, num_WOP, .. } := A4
  let { ADD_SUB2, SUB_EQ_0, .. } := A5
  let { DIVISION_0, DIVISION, DIVMOD_UNIQ, .. } := A7

  /- Theorems for eliminating cutoff subtraction, predecessor, DIV and MOD.
     We have versions that introduce universal or existential quantifiers. -/

  let PRE_ELIM_THM ← prove
   r"P(PRE n) <=> !m. n = SUC m \/ m = 0 /\ n = 0 ==> P m"
   (SPEC_TAC (← q r"n:num", ← q r"n:num") THEN INDUCT_TAC THEN
    REWRITE_TAC [NOT_SUC, SUC_INJ, PRE] THEN MESON_TAC [])

  let PRE_ELIM_THM' ← prove
   r"P(PRE n) <=> ?m. (n = SUC m \/ m = 0 /\ n = 0) /\ P m"
   (MP_TAC (← INST [(← q r"\x:num. ~P x", ← q r"P:num->bool")] PRE_ELIM_THM) THEN
    MESON_TAC [])

  let SUB_ELIM_THM ← prove
   r"P(a - b) <=> !d. a = b + d \/ a < b /\ d = 0 ==> P d"
   (DISJ_CASES_TAC (← SPECL [← q r"a:num", ← q r"b:num"] LTE_CASES) THENL
     [ASM_MESON_TAC [NOT_LT, SUB_EQ_0, LT_IMP_LE, LE_ADD], ALL_TAC] THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q r"e:num") SUBST1_TAC o REWRITE_RULE [LE_EXISTS]) THEN
    SIMP_TAC [ADD_SUB2, ← GSYM NOT_LE, LE_ADD, EQ_ADD_LCANCEL] THEN MESON_TAC [])

  let SUB_ELIM_THM' ← prove
   r"P(a - b) <=> ?d. (a = b + d \/ a < b /\ d = 0) /\ P d"
   (MP_TAC (← INST [(← q r"\x:num. ~P x", ← q r"P:num->bool")] SUB_ELIM_THM) THEN
    MESON_TAC [])

  let DIVMOD_ELIM_THM ← prove
   r"P (m DIV n) (m MOD n) <=>
        !q r. n = 0 /\ q = 0 /\ r = m \/ m = q * n + r /\ r < n ==> P q r"
   (ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [] THENL
     [ASM_MESON_TAC [DIVISION_0, LT],
      FIRST_ASSUM (MP_TAC o MATCH_MP DIVISION) THEN MESON_TAC [DIVMOD_UNIQ]])

  let DIVMOD_ELIM_THM' ← prove
   r"P (m DIV n) (m MOD n) <=>
        ?q r. (n = 0 /\ q = 0 /\ r = m \/ m = q * n + r /\ r < n) /\ P q r"
   (MP_TAC (← INST [(← q r"\x:num y:num. ~P x y", ← q r"P:num->num->bool")]
      DIVMOD_ELIM_THM) THEN
    MESON_TAC [])

  /- Binder for "the minimal n such that". -/

  let minimal ← new_definition
   r"(minimal) (P:num->bool) = @n. P n /\ !m. m < n ==> ~(P m)"

  let MINIMAL ← prove
   r"!P. (?n. P n) <=> P((minimal) P) /\ (!m. m < (minimal) P ==> ~(P m))"
   (GEN_TAC THEN REWRITE_TAC [minimal] THEN CONV_TAC (RAND_CONV SELECT_CONV) THEN
    REWRITE_TAC [← GSYM num_WOP])

  let MINIMAL_UNIQUE ← prove
   r"!P n. P n /\ (!m. m < n ==> ~P m) ==> (minimal) P = n"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [minimal] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC [LT_CASES])

  let LE_MINIMAL ← prove
   r"!P n.
        (?r. P r) ==> (n <= (minimal) P <=> !i. P i ==> n <= i)"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN
    MESON_TAC [NOT_LE, LE_TRANS])

  let MINIMAL_LE ← prove
   r"!P n. (?r. P r) ==> ((minimal) P <= n <=> ?i. i <= n /\ P i)"
   (REWRITE_TAC [← GSYM NOT_LT] THEN REWRITE_TAC [← GSYM LE_SUC_LT] THEN
    SIMP_TAC [LE_MINIMAL] THEN MESON_TAC [])

  let MINIMAL_UBOUND ← prove
   r"!P n. P n ==> (minimal) P <= n"
   (MESON_TAC [MINIMAL, NOT_LT])

  let MINIMAL_LBOUND ← prove
   r"!P n. (?r. P r) /\ (!m. m < n ==> ~P m) ==> n <= (minimal) P"
   (SIMP_TAC [LE_MINIMAL] THEN MESON_TAC [NOT_LT])

  let MINIMAL_MONO ← prove
   r"!P Q. (?n. P n) /\ (!n. P n ==> Q n) ==> (minimal) Q <= (minimal) P"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"?n:num. Q n") ASSUME_TAC THENL [ASM_MESON_TAC [], ALL_TAC] THEN
    MATCH_MP_TAC (← MESON [LE_TRANS, LE_REFL]
     (← q r"(!p:num. p <= m ==> p <= n) ==> m <= n")) THEN
    ASM_SIMP_TAC [LE_MINIMAL])

  /- A common lemma for transitive relations. -/

  let TRANSITIVE_STEPWISE_LT_EQ ← prove
   r"!R. (!x y z. R x y /\ R y z ==> R x z)
         ==> ((!m n. m < n ==> R m n) <=> (!n. R n (SUC n)))"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC [LT] THEN
    DISCH_TAC THEN SIMP_TAC [LT_EXISTS, LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    REWRITE_TAC [LEFT_FORALL_IMP_THM, EXISTS_REFL, ADD_CLAUSES] THEN
    INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES] THEN ASM_MESON_TAC [])

  let TRANSITIVE_STEPWISE_LT ← prove
   r"!R. (!x y z. R x y /\ R y z ==> R x z) /\ (!n. R n (SUC n))
       ==> !m n. m < n ==> R m n"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC (← TAUT
     (← q r"(a ==> (c <=> b)) ==> a /\ b ==> c")) THEN
    MATCH_ACCEPT_TAC TRANSITIVE_STEPWISE_LT_EQ)

  let TRANSITIVE_STEPWISE_LE_EQ ← prove
   r"!R. (!x. R x x) /\ (!x y z. R x y /\ R y z ==> R x z)
       ==> ((!m n. m <= n ==> R m n) <=> (!n. R n (SUC n)))"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC [LE, LE_REFL] THEN
    DISCH_TAC THEN SIMP_TAC [LE_EXISTS, LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
    REWRITE_TAC [LEFT_FORALL_IMP_THM, EXISTS_REFL, ADD_CLAUSES] THEN
    INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES] THEN ASM_MESON_TAC [])

  let TRANSITIVE_STEPWISE_LE ← prove
   r"!R. (!x. R x x) /\ (!x y z. R x y /\ R y z ==> R x z) /\
       (!n. R n (SUC n))
       ==> !m n. m <= n ==> R m n"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC (← TAUT
     (← q r"(a /\ a' ==> (c <=> b)) ==> a /\ a' /\ b ==> c")) THEN
    MATCH_ACCEPT_TAC TRANSITIVE_STEPWISE_LE_EQ)

  /- A couple of forms of Dependent Choice. -/

  let DEPENDENT_CHOICE_FIXED ← prove
   r"!P R a:A.
        P 0 a /\ (!n x. P n x ==> ?y. P (SUC n) y /\ R n x y)
        ==> ?f. f 0 = a /\ (!n. P n (f n)) /\ (!n. R n (f n) (f(SUC n)))"
   (← do
    let m1 ← MESON [num_CASES] (← q r"(!n. P n) <=> P 0 /\ !n. P(SUC n)")
    pure
     (REPEAT STRIP_TAC THEN
      MP_TAC (← prove_recursive_functions_exist num_RECURSION
        (← q r"f 0 = (a:A) /\ (!n. f(SUC n) = @y. P (SUC n) y /\ R n (f n) y)")) THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN GEN_REWRITE_TAC LAND_CONV [m1] THEN
      ASM_REWRITE_TAC [AND_FORALL_THM] THEN INDUCT_TAC THEN ASM_MESON_TAC []))

  let DEPENDENT_CHOICE ← prove
   r"!P R:num->A->A->bool.
        (?a. P 0 a) /\ (!n x. P n x ==> ?y. P (SUC n) y /\ R n x y)
        ==> ?f. (!n. P n (f n)) /\ (!n. R n (f n) (f(SUC n)))"
   (MESON_TAC [DEPENDENT_CHOICE_FIXED])

  return {
    PRE_ELIM_THM, PRE_ELIM_THM', SUB_ELIM_THM, SUB_ELIM_THM', DIVMOD_ELIM_THM,
    DIVMOD_ELIM_THM', minimal, MINIMAL, MINIMAL_UNIQUE, LE_MINIMAL, MINIMAL_LE,
    MINIMAL_UBOUND, MINIMAL_LBOUND, MINIMAL_MONO, TRANSITIVE_STEPWISE_LT_EQ,
    TRANSITIVE_STEPWISE_LT, TRANSITIVE_STEPWISE_LE_EQ, TRANSITIVE_STEPWISE_LE,
    DEPENDENT_CHOICE_FIXED, DEPENDENT_CHOICE }

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv conv lhs lhand rhs)
open HolLight HolLight.Syntax

/-- arith.ml: `parse_as_binder "minimal"`, run before any term with the
    `minimal` binder is parsed. -/
def setupMinimalBinder : IO Unit :=
  HolCore.Printer.parse_as_binder "minimal"

/- ---------------------------------------------------------------------- -/
/- Pushing and pulling to combine nested MOD terms into a single MOD.     -/
/- ---------------------------------------------------------------------- -/

/-- The recursive `downconv` of `MOD_DOWN_CONV` (arith.ml 1719-1722). -/
partial def modDownDownConv (addmul_conv mod_conv : ioconv) : ioconv :=
  fun tm =>
    let downconv := modDownDownConv addmul_conv mod_conv
    (orelsec_ (thenc_ addmul_conv (LAND_CONV downconv))
      (orelsec_ (thenc_ mod_conv downconv)
        (SUB_CONV downconv))) tm

/-- `MOD_DOWN_CONV` (arith.ml 1713-1726).  As in OCaml, `MOD_SUC_MOD` and
    the rewrite conversions are built once, here; the result is the
    conversion. -/
def MOD_DOWN_CONV [HolBase]
    (METIS' : List thm → term → IO (Except String thm))
    (ADD1 MOD_ADD_MOD MOD_MOD_REFL MOD_MULT_MOD2 MOD_EXP_MOD : thm) :
    ExceptT String IO ioconv := do
  let METIS (ths : List thm) (t : term) : ExceptT String IO thm := METIS' ths t
  let MOD_SUC_MOD ← METIS [ADD1, MOD_ADD_MOD, MOD_MOD_REFL]
   (← q r"(SUC(m MOD n)) MOD n = SUC m MOD n")
  let addmul_conv ← GEN_REWRITE_CONV_NET id
    [← GSYM MOD_SUC_MOD, ← GSYM MOD_ADD_MOD, ← GSYM MOD_MULT_MOD2, ← GSYM MOD_EXP_MOD]
  let mod_conv ← GEN_REWRITE_CONV_NET id [MOD_MOD_REFL]
  let downconv := modDownDownConv addmul_conv mod_conv
  let upconv ← GEN_REWRITE_CONV_NET DEPTH_CONV
     [MOD_SUC_MOD, MOD_ADD_MOD, MOD_MULT_MOD2, MOD_EXP_MOD, MOD_MOD_REFL]
  return thenc_ downconv upconv

/- ---------------------------------------------------------------------- -/
/- Crude but useful conversion for cancelling down equations.             -/
/- ---------------------------------------------------------------------- -/

/-- The `minter` of `NUM_CANCEL_CONV` (arith.ml 1733-1739). -/
partial def numCancelMinter (i l1' l2' l1 l2 : List term) :
    List term × List term × List term :=
  match l1, l2 with
  | [], _ => (i, l1', l2' ++ l2)
  | _, [] => (i, l1 ++ l1', l2')
  | h1 :: t1, h2 :: t2 =>
    if h1 == h2 then numCancelMinter (h1 :: i) l1' l2' t1 t2
    else if (compare h1 h2 = Ordering.lt) then
      numCancelMinter i (h1 :: l1') l2' t1 l2
    else numCancelMinter i l1' (h2 :: l2') l1 t2

/-- `NUM_CANCEL_CONV` (arith.ml 1732-1756).  `add_tm`, `eq_tm`,
    `EQ_ADD_LCANCEL_0'` are built once, as in OCaml; the rest runs per call.
    Session builds it at arith.ml's position, where `(+)` is `num` addition. -/
def NUM_CANCEL_CONV [HolBase] (EQ_ADD_LCANCEL EQ_ADD_LCANCEL_0 ADD_AC : thm) :
    ExceptT String IO ioconv := do
  let add_tm ← q r"(+)"
  let eq_tm ← q r"(=) :num->num->bool"
  let EQ_ADD_LCANCEL_0' ←
    GEN_REWRITE_RULE (Lib.funpow 2 BINDER_CONV ∘ LAND_CONV) [HolBase.T.EQ_SYM_EQ]
      EQ_ADD_LCANCEL_0
  let AC_RULE := AC ADD_AC
  return fun tm => ExceptT.run do
    let (l, r) ← liftExcept (dest_eq tm)
    -- `binops `(+)``: the quotation is inside `fun tm ->`, so OCaml parses it
    -- at every call, once for each side (after `prioritize_int()` it is
    -- integer addition).
    let le := fun a b => decide (compare a b ≠ Ordering.gt)
    let lats := Lib.sort le (binops (← q r"(+)") l)
    let rats := Lib.sort le (binops (← q r"(+)") r)
    let (i, lats', rats') := numCancelMinter [] [] [] lats rats
    let l' ← liftExcept (list_mk_binop add_tm (i ++ lats'))
    let r' ← liftExcept (list_mk_binop add_tm (i ++ rats'))
    let rth ← AC_RULE (safe_mk_eq r r')
    let lth ← AC_RULE (safe_mk_eq l l')
    let eth ← MK_COMB (← AP_TERM eq_tm lth, rth)
    GEN_REWRITE_RULE (RAND_CONV ∘ REPEATC)
      [EQ_ADD_LCANCEL, EQ_ADD_LCANCEL_0, EQ_ADD_LCANCEL_0'] eth

/- ---------------------------------------------------------------------- -/
/- This is handy for easing MATCH_MP on inequalities.                     -/
/- ---------------------------------------------------------------------- -/

/-- `LE_IMP` (arith.ml 1762-1764).  `pth` is derived once; the result is the
    rule `fun th -> GEN_ALL(MATCH_MP pth (SPEC_ALL th))`. -/
def LE_IMP [HolBase] (IMP_CONJ LE_TRANS : thm) :
    ExceptT String IO (thm → ExceptT String IO thm) := do
  let pth ← PURE_ONCE_REWRITE_RULE [IMP_CONJ] LE_TRANS
  return fun th => do GEN_ALL (← MATCH_MP pth (← SPEC_ALL th))

/- ---------------------------------------------------------------------- -/
/- Conversion that elimimates every occurrence of `NUMERAL`, `BIT0`,      -/
/- `BIT1`, `_0` that is not part of a well-formed numeral.                -/
/- ---------------------------------------------------------------------- -/

/-- The recursive `BITS_ELIM_CONV` of arith.ml 1888-1903, closed over the
    proformas. -/
partial def bitsElimCore
    (ZERO_pth NUMERAL_pth BIT0_pth BIT1_pth : thm) (mvar nvar : term) : conv :=
  fun tm =>
    let rec_ := bitsElimCore ZERO_pth NUMERAL_pth BIT0_pth BIT1_pth mvar nvar
    match tm with
    | .Const "_0" _ => .ok ZERO_pth
    | .Var _ _ | .Const _ _ => .ok (REFL tm)
    | .Comb (.Const "NUMERAL" _) mtm =>
        if HolMath.Nums.is_numeral tm then .ok (REFL tm) else do
          let th ← rec_ mtm
          HolCore.Kernel.EQ_MP
            (← HolCore.Kernel.INST [(mtm, mvar), (← rand (concl th), nvar)] NUMERAL_pth) th
    | .Comb (.Const "BIT0" _) mtm => do
          let th ← rec_ mtm
          HolCore.Kernel.EQ_MP
            (← HolCore.Kernel.INST [(mtm, mvar), (← rand (concl th), nvar)] BIT0_pth) th
    | .Comb (.Const "BIT1" _) mtm => do
          let th ← rec_ mtm
          HolCore.Kernel.EQ_MP
            (← HolCore.Kernel.INST [(mtm, mvar), (← rand (concl th), nvar)] BIT1_pth) th
    | .Comb _ _ => HolCore.Equal.COMB_CONV rec_ tm
    | .Abs _ _ => HolCore.Equal.ABS_CONV rec_ tm

/-- `BITS_ELIM_CONV` (arith.ml 1877-1904): the proformas are proved once,
    here; the result is the conversion. -/
def BITS_ELIM_CONV [HolBase]
    (NUMERAL BIT0 BIT1 ADD1 EQ_ADD_RCANCEL MULT_2 EQ_MULT_LCANCEL TWO NOT_SUC : thm) :
    ExceptT String IO conv := do
  let NUMERAL_pth ← prove r"m = n <=> NUMERAL m = n" (REWRITE_TAC [NUMERAL])
  let ZERO_pth ← GSYM (← ExceptT.mk (REWRITE_CONV [NUMERAL] (← q r"0")))
  let (BIT0_pth, BIT1_pth) ← CONJ_PAIR (← prove
   r"(m = n <=> BIT0 m = 2 * n) /\
     (m = n <=> BIT1 m = 2 * n + 1)"
   (CONJ_TAC THEN GEN_REWRITE_TAC (RAND_CONV ∘ LAND_CONV) [BIT0, BIT1] THEN
    REWRITE_TAC [ADD1, EQ_ADD_RCANCEL, ← GSYM MULT_2] THEN
    REWRITE_TAC [EQ_MULT_LCANCEL] THEN
    REWRITE_TAC [TWO, NOT_SUC]))
  let mvar ← q r"m:num"
  let nvar ← q r"n:num"
  return bitsElimCore ZERO_pth NUMERAL_pth BIT0_pth BIT1_pth mvar nvar

end

end HolMath.Arith
