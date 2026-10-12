/- ========================================================================= -/
/- Basic theory of divisibility, gcd, coprimality and primality (over N).    -/
/- ========================================================================= -/
/- File: HolLibrary/Prime.lean

  Original (c) Copyright, John Harrison 1998-2017
  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/prime.ml`, which HOL Light loads with
  `needs "Library/prime.ml"` after the core library.

  The file is PURE, like HolMath: what it uses from Session arrives in a
  `PrimeDeps` structure, and the core tactics come from `HolMath.Base`
  under their HOL Light names.  Each section of prime.ml is a theorem
  bundle (a `structure`) proved by a `setup` function, in file order;
  SessionLibrary/Prime.lean builds the bundles and exports the theorems.

  The proofs are translated by hand, one `let` per OCaml `let`, in file
  order.  Conventions (see HolMath/Base.lean):
    let NAME = prove(`goal`, tac)   ~>  let NAME ← prove r"goal" (tac)
    let NAME = new_definition `..`  ~>  let NAME ← new_definition r".."
    `term` inside a proof           ~>  (← q r"term")
    a rule (GSYM th, ARITH_RULE..)  ~>  (← GSYM th), (← ARITH_RULE (← q r"..."))
    fun th -> tac                   ~>  fun th => tac, or
                                        fun th => tactic_of do pure (tac)
                                        when tac applies a rule that can fail
    let x = ... in tac              ~>  (← do let x ← ...; pure (tac))
  THEN, THENL, ORELSE, THENC, ORELSEC and `o` are infix, as in OCaml; raw
  strings keep the quotations' text verbatim.  Lists use `,` for `;`.

  EVALUATION ORDER.  OCaml evaluates a function's arguments right to left,
  Lean's `(← ...)` left to right.  That only shows when two rules in one
  proof print (MESON, NUMBER_RULE); in the two proofs where it does
  (DIVIDES_INDEX, PRIMEPOW_DIVIDES_LCM) those rules are bound first, in
  OCaml's order.  tools/primediff checks the 7,068 messages printed while
  loading against HOL Light's.

  Each section takes the core theorems it uses from `D.core1` (A-L) and
  `D.core2` (M-Z, lower case).  They were split because Lean 4.33.1 crashed
  on a structure constructor with 128 or more fields; that could not be
  reproduced on 4.34.1.  The runtime limit is 255 fields.
-/

import HolMath

open HolCore HolCore.Lib
open HolCore.Kernel hiding ASSUME INST
open HolCore.Equal (ioconv lhs lhand)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal)
open HolLight HolLight.Syntax

namespace HolLibrary.Prime

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000

/- ------------------------------------------------------------------------- -/
/- What prime.ml uses from the core library (supplied by Session).           -/
/- ------------------------------------------------------------------------- -/

/-- Theorems prime.ml uses from the core library, A-L.  (Two structures,
    split under 128 fields: see the note at the top of the file.) -/
structure CoreThms1 where
  (ADD1 ADD_AC ADD_CLAUSES ADD_EQ_0 ADD_SYM ARITH ARITH_EQ CARD_CLAUSES
   CARD_IMAGE_INJ CARD_NUMSEG_1 COND_CLAUSES COND_ID COND_RAND COND_RATOR
   CONJ_ASSOC CONJ_SYM CONTRAPOS_THM COPRIME_RMOD DE_MORGAN_THM DISJ_ACI
   DISJ_SYM DIVIDES_ANTISYM DIVIDES_DIV_MULT DIVIDES_LE DIVIDES_LE_IMP
   DIVIDES_LE_STRONG DIVIDES_MOD DIVIDES_ONE DIV_1 DIV_EQ_0 DIV_EQ_SELF DIV_LE
   DIV_MULT DIV_MULT2 DIV_UNIQ DIV_ZERO EMPTY_GSPEC EQ_ADD_RCANCEL
   EQ_ADD_RCANCEL_0 EQ_IMP EQ_MULT_LCANCEL EQ_SYM_EQ EQ_TRANS ETA_AX
   EVEN_EXISTS EXISTS_INT_CASES EXISTS_IN_INSERT EXISTS_REFL EXP EXP_1 EXP_2
   EXP_ADD EXP_EQ_0 EXP_EQ_1 EXP_EXP EXP_MONO_EQ EXP_MONO_LE EXP_MONO_LE_IMP
   EXP_ONE EXP_ZERO EXTENSION FACT FACT_LT FACT_NZ FINITE_INDUCT_STRONG
   FINITE_NUMSEG FINITE_NUMSEG_LE FINITE_RESTRICT FINITE_SUBSET FORALL_AND_THM
   FORALL_INT_CASES FORALL_IN_INSERT FORALL_UNWIND_THM2 FUN_EQ_THM GCD GT
   IMP_CONJ IMP_CONJ_ALT INFINITE INT_ABS_NUM INT_CONG_NUM_EXISTS INT_MUL_LNEG
   INT_MUL_RNEG INT_NEG_NEG INT_OF_NUM_ADD INT_OF_NUM_CLAUSES INT_OF_NUM_DIV
   INT_OF_NUM_EQ INT_OF_NUM_MUL INT_OF_NUM_POW INT_OF_NUM_SUB INT_POW
   IN_ELIM_THM IN_IMAGE IN_NUMSEG IN_UNIV ITERATE_CLAUSES ITERATE_DELTA
   ITERATE_EQ ITERATE_EQ_NEUTRAL ITERATE_EXPAND_CASES ITERATE_OP_GEN
   ITERATE_SUPERSET LE LEFT_ADD_DISTRIB LEFT_AND_EXISTS_THM LEFT_IMP_EXISTS_THM
   LE_0 LE_1 LE_ADD LE_ADD2 LE_ANTISYM LE_EXISTS LE_EXP LE_MULT_LCANCEL
   LE_RDIV_EQ LE_REFL LE_TRANS LT LTE_TRANS LT_EXISTS LT_EXP LT_IMP_LE LT_LE
   LT_MULT_RCANCEL LT_POW2_REFL LT_REFL : thm)

/-- Theorems prime.ml uses from the core library, M-Z and lower case. -/
structure CoreThms2 where
  (MAX MOD_LT_EQ MONOIDAL_MUL MONO_EXISTS MONO_OR MULT_AC MULT_ASSOC
   MULT_CLAUSES MULT_EQ_0 MULT_EQ_1 MULT_EXP MULT_SYM NEUTRAL_MUL NOT_EVEN
   NOT_FORALL_THM NOT_IMP NOT_IN_EMPTY NOT_LE NOT_LT NOT_SUC NPRODUCT_CLAUSES
   NSUM_ADD_NUMSEG NSUM_CLAUSES NSUM_CLAUSES_NUMSEG NSUM_CLOSED_NONEMPTY
   NSUM_CONST NSUM_EQ NSUM_EQ_NUMSEG NSUM_IMAGE NSUM_RESTRICT_SET NSUM_SUPERSET
   NSUM_SWAP NUM_GCD NUM_LCM ODD_EXISTS ONE_OR_PRIME_DIVIDES_OR_COPRIME
   PRIME_COPRIME_EQ_NONDIVISIBLE RIGHT_ADD_DISTRIB RIGHT_AND_EXISTS_THM
   RIGHT_EXISTS_AND_THM RIGHT_FORALL_IMP_THM RIGHT_SUB_DISTRIB SELECT_UNIQUE
   SUBSET SUBSET_REFL SUB_0 SUB_ADD SUB_EQ_0 SWAP_EXISTS_THM SWAP_FORALL_THM
   UNWIND_THM2 ZERO_ONE_OR_PRIME coprime divides int_divides int_lcm monoidal
   neutral nproduct num_CASES num_FINITE num_MAX num_WF num_divides numseg
   o_DEF prime support : thm)

/-- The decision procedures, rules, conversions and theorems prime.ml uses
    from hol.ml's library.  Rules that can fail are in `ExceptT`. -/
structure PrimeDeps where
  -- definitions
  new_definition : String → ExceptT String IO thm
  -- decision procedures and other Session tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  ASM_MESON_TAC : List thm → tactic
  INDUCT_TAC : tactic
  INTEGER_RULE : term → ExceptT String IO thm
  INTEGER_TAC : tactic
  INT_ARITH : term → ExceptT String IO thm
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  NUMBER_RULE : term → ExceptT String IO thm
  NUMBER_TAC : tactic
  NUM_RING : term → ExceptT String IO thm
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  CONTRAPOS_CONV : ioconv
  EXPAND_CASES_CONV : ioconv
  NUM_DIV_CONV : ioconv
  NUM_EQ_CONV : ioconv
  NUM_MOD_CONV : ioconv
  NUM_MULT_CONV : ioconv
  NUM_REDUCE_CONV : ioconv
  mk_numeral : Rat → Except String term
  -- theorems
  core1 : CoreThms1
  core2 : CoreThms2

/- ------------------------------------------------------------------------- -/
/- Elementary theory of divisibility (prime.ml 7-188)                        -/
/- ------------------------------------------------------------------------- -/

structure Divides where
  DIVIDES_0 : thm
  DIVIDES_ZERO : thm
  DIVIDES_1 : thm
  DIVIDES_REFL : thm
  DIVIDES_TRANS : thm
  DIVIDES_ADD : thm
  DIVIDES_SUB_EQ : thm
  DIVIDES_SUB : thm
  DIVIDES_SUB_1 : thm
  DIVIDES_LMUL : thm
  DIVIDES_RMUL : thm
  DIVIDES_ADD_REVR : thm
  DIVIDES_ADD_REVL : thm
  DIVIDES_MUL_L : thm
  DIVIDES_MUL_R : thm
  DIVIDES_LMUL2 : thm
  DIVIDES_RMUL2 : thm
  DIVIDES_CMUL2 : thm
  DIVIDES_LMUL2_EQ : thm
  DIVIDES_RMUL2_EQ : thm
  DIVIDES_EQ_ZERO : thm
  DIVIDES_CASES : thm
  DIVIDES_DIV_NOT : thm
  DIVIDES_MUL2 : thm
  DIVIDES_EXP : thm
  DIVIDES_EXP2 : thm
  DIVIDES_EXP_LE_IMP : thm
  DIVIDES_EXP_LE : thm
  DIVIDES_TRIVIAL_UPPERBOUND : thm
  DIVIDES_FACT : thm
  DIVIDES_2 : thm
  DIVIDES_REXP_SUC : thm
  DIVIDES_REXP : thm
  FINITE_DIVISORS : thm
  FINITE_SPECIAL_DIVISORS : thm
  DIVISORS_EQ : thm
  MULTIPLES_EQ : thm
  DIVIDES_NSUM : thm
  deriving Inhabited

@[nospecialize]
def setupDivides [HolBase] (D : PrimeDeps) : ExceptT String IO Divides := do
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, NUMBER_RULE, NUMBER_TAC, SET_TAC, .. } := D
  let { DIVIDES_LE_STRONG, LT, LEFT_IMP_EXISTS_THM, EQ_MULT_LCANCEL, LE_MULT_LCANCEL, DIVIDES_LE, EXP, LE_EXISTS, EXP_ADD, LE_EXP, EXP_EQ_0, LTE_TRANS, LT_POW2_REFL, EXP_MONO_LE, FACT, LE, EVEN_EXISTS, FINITE_SUBSET, FINITE_NUMSEG_LE, IN_ELIM_THM, DIVIDES_ANTISYM, IMP_CONJ, FINITE_INDUCT_STRONG, FORALL_IN_INSERT, .. } := D.core1
  let { NOT_LE, divides, MULT_EQ_0, MULT_EXP, NOT_SUC, SUBSET, NSUM_CLAUSES, .. } := D.core2

  let DIVIDES_0 ← prove
   r"!x. x divides 0"
   (NUMBER_TAC)

  let DIVIDES_ZERO ← prove
   r"!x. 0 divides x <=> x = 0"
   (NUMBER_TAC)

  let DIVIDES_1 ← prove
   r"!x. 1 divides x"
   (NUMBER_TAC)

  let DIVIDES_REFL ← prove
   r"!x. x divides x"
   (NUMBER_TAC)

  let DIVIDES_TRANS ← prove
   r"!a b c. a divides b /\ b divides c ==> a divides c"
   (NUMBER_TAC)

  let DIVIDES_ADD ← prove
   r"!d a b. d divides a /\ d divides b ==> d divides (a + b)"
   (NUMBER_TAC)

  let DIVIDES_SUB_EQ ← prove
   r"!d a b. d divides (a - b) <=> a < b \/ (a == b) (mod d)"
   (REPEAT GEN_TAC THEN
    DISJ_CASES_THEN MP_TAC (← ARITH_RULE
     (← q r"a < b /\ a - b = 0 \/ ~(a < b) /\ (a - b) + b = a")) THEN
    SIMP_TAC [] THEN NUMBER_TAC)

  let DIVIDES_SUB ← prove
   r"!d a b. d divides a /\ d divides b ==> d divides (a - b)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [DIVIDES_SUB_EQ] THEN
    DISJ2_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN NUMBER_TAC)

  let DIVIDES_SUB_1 ← prove
   r"!d n. d divides n - 1 <=> n = 0 \/ (n == 1) (mod d)"
   (REWRITE_TAC [DIVIDES_SUB_EQ, ← ARITH_RULE (← q r"n < 1 <=> n = 0")])

  let DIVIDES_LMUL ← prove
   r"!d a x. d divides a ==> d divides (x * a)"
   (NUMBER_TAC)

  let DIVIDES_RMUL ← prove
   r"!d a x. d divides a ==> d divides (a * x)"
   (NUMBER_TAC)

  let DIVIDES_ADD_REVR ← prove
   r"!d a b. d divides a /\ d divides (a + b) ==> d divides b"
   (NUMBER_TAC)

  let DIVIDES_ADD_REVL ← prove
   r"!d a b. d divides b /\ d divides (a + b) ==> d divides a"
   (NUMBER_TAC)

  let DIVIDES_MUL_L ← prove
   r"!a b c. a divides b ==> (c * a) divides (c * b)"
   (NUMBER_TAC)

  let DIVIDES_MUL_R ← prove
   r"!a b c. a divides b ==> (a * c) divides (b * c)"
   (NUMBER_TAC)

  let DIVIDES_LMUL2 ← prove
   r"!d a x. (x * d) divides a ==> d divides a"
   (NUMBER_TAC)

  let DIVIDES_RMUL2 ← prove
   r"!d a x. (d * x) divides a ==> d divides a"
   (NUMBER_TAC)

  let DIVIDES_CMUL2 ← prove
   r"!a b c. (c * a) divides (c * b) /\ ~(c = 0) ==> a divides b"
   (NUMBER_TAC)

  let DIVIDES_LMUL2_EQ ← prove
   r"!a b c. ~(c = 0) ==> ((c * a) divides (c * b) <=> a divides b)"
   (NUMBER_TAC)

  let DIVIDES_RMUL2_EQ ← prove
   r"!a b c. ~(c = 0) ==> ((a * c) divides (b * c) <=> a divides b)"
   (NUMBER_TAC)

  let DIVIDES_EQ_ZERO ← prove
   r"!p n. n < p ==> (p divides n <=> n = 0)"
   (MESON_TAC [DIVIDES_0, DIVIDES_LE_STRONG, NOT_LE, LT])

  let DIVIDES_CASES ← prove
   r"!m n. n divides m ==> m = 0 \/ m = n \/ 2 * n <= m"
   (SIMP_TAC [← ARITH_RULE (← q r"m = n \/ 2 * n <= m <=> m = n * 1 \/ n * 2 <= m")] THEN
    SIMP_TAC [divides, LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [MULT_EQ_0, EQ_MULT_LCANCEL, LE_MULT_LCANCEL] THEN ARITH_TAC)

  let DIVIDES_DIV_NOT ← prove
   r"!n x q r. x = q * n + r /\ 0 < r /\ r < n ==> ~(n divides x)"
   (SIMP_TAC [← NUMBER_RULE (← q r"n divides (q * n + r) <=> n divides r")] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_ARITH_TAC)

  let DIVIDES_MUL2 ← prove
   r"!a b c d. a divides b /\ c divides d ==> (a * c) divides (b * d)"
   (NUMBER_TAC)

  let DIVIDES_EXP ← prove
   r"!x y n. x divides y ==> (x EXP n) divides (y EXP n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [divides] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:num") SUBST1_TAC) THEN
    EXISTS_TAC (← q r"d EXP n") THEN MATCH_ACCEPT_TAC MULT_EXP)

  let DIVIDES_EXP2 ← prove
   r"!n x y. ~(n = 0) /\ (x EXP n) divides y ==> x divides y"
   (INDUCT_TAC THEN REWRITE_TAC [NOT_SUC, EXP] THEN NUMBER_TAC)

  let DIVIDES_EXP_LE_IMP ← prove
   r"!p m n. m <= n ==> (p EXP m) divides (p EXP n)"
   (SIMP_TAC [LE_EXISTS, LEFT_IMP_EXISTS_THM, EXP_ADD] THEN NUMBER_TAC)

  let DIVIDES_EXP_LE ← prove
   r"!p m n. 2 <= p ==> ((p EXP m) divides (p EXP n) <=> m <= n)"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_THEN (MP_TAC o MATCH_MP DIVIDES_LE) THEN
      ASM_REWRITE_TAC [LE_EXP, EXP_EQ_0] THEN POP_ASSUM MP_TAC THEN ARITH_TAC,
      SIMP_TAC [LE_EXISTS, LEFT_IMP_EXISTS_THM, EXP_ADD] THEN NUMBER_TAC])

  let DIVIDES_TRIVIAL_UPPERBOUND ← prove
   r"!p n. ~(n = 0) /\ 2 <= p ==> ~((p EXP n) divides n)"
   (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_REWRITE_TAC [NOT_LE] THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC (← q r"2 EXP n") THEN REWRITE_TAC [LT_POW2_REFL] THEN
    UNDISCH_TAC (← q r"~(n = 0)") THEN SPEC_TAC ((← q r"n:num"), (← q r"n:num")) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC [EXP_MONO_LE, NOT_SUC])

  let DIVIDES_FACT ← prove
   r"!n p. 1 <= p /\ p <= n ==> p divides (FACT n)"
   (INDUCT_TAC THEN REWRITE_TAC [FACT, LE] THENL
     [ARITH_TAC, ASM_MESON_TAC [DIVIDES_LMUL, DIVIDES_RMUL, DIVIDES_REFL]])

  let DIVIDES_2 ← prove
   r"!n. 2 divides n <=> EVEN(n)"
   (REWRITE_TAC [divides, EVEN_EXISTS])

  let DIVIDES_REXP_SUC ← prove
   r"!x y n. x divides y ==> x divides (y EXP (SUC n))"
   (REWRITE_TAC [EXP, DIVIDES_RMUL])

  let DIVIDES_REXP ← prove
   r"!x y n. x divides y /\ ~(n = 0) ==> x divides (y EXP n)"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC [DIVIDES_REXP_SUC])

  let FINITE_DIVISORS ← prove
   r"!n. ~(n = 0) ==> FINITE {d | d divides n}"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC (← q r"{d:num | d <= n}") THEN REWRITE_TAC [FINITE_NUMSEG_LE] THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN ASM_MESON_TAC [DIVIDES_LE])

  let FINITE_SPECIAL_DIVISORS ← prove
   r"!n. ~(n = 0) ==> FINITE {d | P d /\ d divides n}"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC (← q r"{d | d divides n}") THEN ASM_SIMP_TAC [FINITE_DIVISORS] THEN
    SET_TAC [])

  let DIVISORS_EQ ← prove
   r"!m n. m = n <=> !d. d divides m <=> d divides n"
   (REWRITE_TAC [← GSYM DIVIDES_ANTISYM] THEN
    MESON_TAC [DIVIDES_REFL, DIVIDES_TRANS])

  let MULTIPLES_EQ ← prove
   r"!m n. m = n <=> !d. m divides d <=> n divides d"
   (REWRITE_TAC [← GSYM DIVIDES_ANTISYM] THEN
    MESON_TAC [DIVIDES_REFL, DIVIDES_TRANS])

  let DIVIDES_NSUM ← prove
   r"!n f s. FINITE s /\ (!i. i IN s ==> n divides (f i))
           ==> n divides nsum s f"
   (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [DIVIDES_0, NSUM_CLAUSES, FORALL_IN_INSERT, DIVIDES_ADD])

  return { DIVIDES_0, DIVIDES_ZERO, DIVIDES_1, DIVIDES_REFL, DIVIDES_TRANS, DIVIDES_ADD,
           DIVIDES_SUB_EQ, DIVIDES_SUB, DIVIDES_SUB_1, DIVIDES_LMUL, DIVIDES_RMUL,
           DIVIDES_ADD_REVR, DIVIDES_ADD_REVL, DIVIDES_MUL_L, DIVIDES_MUL_R, DIVIDES_LMUL2,
           DIVIDES_RMUL2, DIVIDES_CMUL2, DIVIDES_LMUL2_EQ, DIVIDES_RMUL2_EQ,
           DIVIDES_EQ_ZERO, DIVIDES_CASES, DIVIDES_DIV_NOT, DIVIDES_MUL2, DIVIDES_EXP,
           DIVIDES_EXP2, DIVIDES_EXP_LE_IMP, DIVIDES_EXP_LE, DIVIDES_TRIVIAL_UPPERBOUND,
           DIVIDES_FACT, DIVIDES_2, DIVIDES_REXP_SUC, DIVIDES_REXP, FINITE_DIVISORS,
           FINITE_SPECIAL_DIVISORS, DIVISORS_EQ, MULTIPLES_EQ, DIVIDES_NSUM }

/- ------------------------------------------------------------------------- -/
/- Greatest common divisor (prime.ml 191-398)                                -/
/- ------------------------------------------------------------------------- -/

structure Gcd where
  DIVIDES_GCD : thm
  GCD_0 : thm
  GCD_ZERO : thm
  GCD_REFL : thm
  GCD_1 : thm
  GCD_MULTIPLE : thm
  GCD_ADD : thm
  GCD_SUB : thm
  DIVIDES_GCD_LEFT : thm
  DIVIDES_GCD_RIGHT : thm
  GCD_COPRIME_LMUL : thm
  GCD_COPRIME_RMUL : thm
  DIVIDES_LMUL_GCD : thm
  DIVIDES_RMUL_GCD : thm
  GCD_MUL_COPRIME : thm
  GCD_SYM : thm
  GCD_ASSOC : thm
  GCD_LMUL : thm
  GCD_RMUL : thm
  GCD_BEZOUT_SUM : thm
  GCD_COPRIME_DIVIDES_LMUL : thm
  GCD_COPRIME_DIVIDES_RMUL : thm
  GCD_UNIQUE : thm
  GCD_EQ : thm
  BEZOUT_GCD_STRONG : thm
  BEZOUT_ADD_STRONG : thm
  BEZOUT_GCD : thm
  BEZOUT_ADD : thm
  BEZOUT : thm
  GCD_BEZOUT : thm
  GCD_LE : thm
  GCD_LE_MIN_EQ : thm
  GCD_LE_MIN : thm
  GCD_LE_MAX : thm
  deriving Inhabited

@[nospecialize]
def setupGcd [HolBase] (D : PrimeDeps) (PDivides : Divides) : ExceptT String IO Gcd := do
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE, INT_ARITH, MESON_TAC, 
        NUMBER_TAC, .. } := D
  let { ADD_CLAUSES, ADD_EQ_0, ADD_SYM, DE_MORGAN_THM, DIVIDES_ANTISYM, 
        DIVIDES_LE_IMP, EXISTS_INT_CASES, EXISTS_REFL, GCD, INT_CONG_NUM_EXISTS, 
        INT_MUL_RNEG, INT_OF_NUM_ADD, INT_OF_NUM_EQ, INT_OF_NUM_MUL, LE, 
        LEFT_IMP_EXISTS_THM, LE_REFL, .. } := D.core1
  let { MONO_EXISTS, MULT_ASSOC, MULT_CLAUSES, MULT_SYM, NUM_GCD, 
        RIGHT_SUB_DISTRIB, SUB_0, SUB_ADD, SWAP_EXISTS_THM, divides, int_divides, .. } := D.core2
  let { DIVIDES_0, DIVIDES_SUB, DIVIDES_RMUL, .. } := PDivides

  let DIVIDES_GCD ← prove
   r"!a b d. d divides gcd(a,b) <=> d divides a /\ d divides b"
   (NUMBER_TAC)

  let GCD_0 ← prove
   r"(!a. gcd(0,a) = a) /\ (!a. gcd(a,0) = a)"
   (NUMBER_TAC)

  let GCD_ZERO ← prove
   r"!a b. gcd(a,b) = 0 <=> a = 0 /\ b = 0"
   (NUMBER_TAC)

  let GCD_REFL ← prove
   r"!a. gcd(a,a) = a"
   (NUMBER_TAC)

  let GCD_1 ← prove
   r"(!a. gcd(1,a) = 1) /\ (!a. gcd(a,1) = 1)"
   (NUMBER_TAC)

  let GCD_MULTIPLE ← prove
   r"!a b. gcd(b,a * b) = b"
   (NUMBER_TAC)

  let GCD_ADD ← prove
   r"(!a b. gcd(a + b,b) = gcd(a,b)) /\
   (!a b. gcd(b + a,b) = gcd(a,b)) /\
   (!a b. gcd(a,a + b) = gcd(a,b)) /\
   (!a b. gcd(a,b + a) = gcd(a,b))"
   (NUMBER_TAC)

  let GCD_SUB ← prove
   r"(!a b. b <= a ==> gcd(a - b,b) = gcd(a,b)) /\
   (!a b. a <= b ==> gcd(a,b - a) = gcd(a,b))"
   (MESON_TAC [SUB_ADD, GCD_ADD])

  let DIVIDES_GCD_LEFT ← prove
   r"!m n:num. m divides n <=> gcd(m,n) = m"
   (NUMBER_TAC)

  let DIVIDES_GCD_RIGHT ← prove
   r"!m n:num. n divides m <=> gcd(m,n) = n"
   (NUMBER_TAC)

  let GCD_COPRIME_LMUL ← prove
   r"!a b c. coprime(a,b) ==> gcd(a * b,c) = gcd(a,c) * gcd(b,c)"
   (NUMBER_TAC)

  let GCD_COPRIME_RMUL ← prove
   r"!a b c. coprime(a,b) ==> gcd(c,a * b) = gcd(c,a) * gcd(c,b)"
   (NUMBER_TAC)

  let DIVIDES_LMUL_GCD ← prove
   r"(!d a b. d divides gcd(d,a) * b <=> d divides a * b) /\
   (!d a b. d divides gcd(a,d) * b <=> d divides a * b)"
   (NUMBER_TAC)

  let DIVIDES_RMUL_GCD ← prove
   r"(!d a b. d divides a * gcd(d,b) <=> d divides a * b) /\
   (!d a b. d divides a * gcd(b,d) <=> d divides a * b)"
   (NUMBER_TAC)

  let GCD_MUL_COPRIME ← prove
   r"(!a b c. coprime(a,b) ==> gcd(a,b * c) = gcd(a,c)) /\
   (!a b c. coprime(a,c) ==> gcd(a,b * c) = gcd(a,b)) /\
   (!a b c. coprime(b,c) ==> gcd(a,b * c) = gcd(a,b) * gcd(a,c)) /\
   (!a b c. coprime(a,c) ==> gcd(a * b,c) = gcd(b,c)) /\
   (!a b c. coprime(b,c) ==> gcd(a * b,c) = gcd(a,c)) /\
   (!a b c. coprime(a,b) ==> gcd(a * b,c) = gcd(a,c) * gcd(b,c))"
   (NUMBER_TAC)

  let GCD_SYM ← prove
   r"!a b. gcd(a,b) = gcd(b,a)"
   (NUMBER_TAC)

  let GCD_ASSOC ← prove
   r"!a b c. gcd(a,gcd(b,c)) = gcd(gcd(a,b),c)"
   (NUMBER_TAC)

  let GCD_LMUL ← prove
   r"!a b c. gcd(c * a, c * b) = c * gcd(a,b)"
   (NUMBER_TAC)

  let GCD_RMUL ← prove
   r"!a b c. gcd(a * c, b * c) = c * gcd(a,b)"
   (NUMBER_TAC)

  let GCD_BEZOUT_SUM ← prove
   r"!a b d x y. a * x + b * y = d ==> gcd(a,b) divides d"
   (NUMBER_TAC)

  let GCD_COPRIME_DIVIDES_LMUL ← prove
   r"!a b c:num. coprime(a,b) /\ a divides c ==> gcd(a * b,c) = a * gcd(b,c)"
   (NUMBER_TAC)

  let GCD_COPRIME_DIVIDES_RMUL ← prove
   r"!a b c:num. coprime(b,c) /\ b divides a ==> gcd(a,b * c) = b * gcd(a,c)"
   (ONCE_REWRITE_TAC [GCD_SYM] THEN REWRITE_TAC [GCD_COPRIME_DIVIDES_LMUL])

  let GCD_UNIQUE ← prove
   r"!d a b. (d divides a /\ d divides b) /\
           (!e. e divides a /\ e divides b ==> e divides d) <=>
           d = gcd(a,b)"
   (REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [GCD] THEN
    ONCE_REWRITE_TAC [← GSYM DIVIDES_ANTISYM] THEN
    ASM_REWRITE_TAC [DIVIDES_GCD] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [GCD])

  let GCD_EQ ← prove
   r"(!d. d divides x /\ d divides y <=> d divides u /\ d divides v)
   ==> gcd(x,y) = gcd(u,v)"
   (REWRITE_TAC [DIVIDES_GCD, ← GSYM DIVIDES_ANTISYM] THEN MESON_TAC [GCD])

  let BEZOUT_GCD_STRONG ← prove
   r"!a b. ~(a = 0) ==> ?x y. a * x = b * y + gcd(a,b)"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [SWAP_EXISTS_THM] THEN
    MP_TAC (← INTEGER_RULE (← q r"?x y. &a * x:int = &b * y + gcd(&a,&b)")) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:int", ← q r"y:int"] THEN STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"y:int", ← q r"&a:int"] INT_CONG_NUM_EXISTS) THEN
    ASM_REWRITE_TAC [INT_OF_NUM_EQ] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q r"r:num") THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"&a divides (&b * &r + gcd(&a,&b):int)") MP_TAC THENL
     [REPLICATE_TAC 2 (POP_ASSUM MP_TAC) THEN CONV_TAC INTEGER_RULE,
      ASM_REWRITE_TAC [int_divides, EXISTS_INT_CASES] THEN
      DISCH_THEN (DISJ_CASES_THEN MP_TAC) THEN MATCH_MP_TAC MONO_EXISTS THEN
      SIMP_TAC [← GSYM NUM_GCD, INT_OF_NUM_MUL, INT_OF_NUM_ADD, INT_OF_NUM_EQ] THEN
      REWRITE_TAC [INT_MUL_RNEG, INT_OF_NUM_MUL,
                   ← INT_ARITH (← q r"&x:int = -- &y <=> &x:int = &0 /\ &y:int = &0")] THEN
      ASM_REWRITE_TAC [INT_OF_NUM_EQ, ADD_EQ_0, GCD_ZERO]])

  let BEZOUT_ADD_STRONG ← prove
   r"!a b. ~(a = 0)
         ==> ?d x y. d divides a /\ d divides b /\ a * x = b * y + d"
   (MESON_TAC [BEZOUT_GCD_STRONG, GCD])

  let BEZOUT_GCD ← prove
   r"!a b. ?x y. a * x - b * y = gcd(a,b) \/ b * x - a * y = gcd(a,b)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"a = 0 /\ b = 0") THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, GCD_0, SUB_0] THEN
    FIRST_X_ASSUM (DISJ_CASES_TAC o REWRITE_RULE [DE_MORGAN_THM]) THENL
     [MP_TAC (← SPECL [← q r"a:num", ← q r"b:num"] BEZOUT_GCD_STRONG),
      MP_TAC (← SPECL [← q r"b:num", ← q r"a:num"] BEZOUT_GCD_STRONG)] THEN
    ASM_REWRITE_TAC [] THEN REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    REWRITE_TAC [GCD_SYM] THEN ARITH_TAC)

  let BEZOUT_ADD ← prove
   r"!a b. ?d x y. (d divides a /\ d divides b) /\
                 (a * x = b * y + d \/ b * x = a * y + d)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"a = 0 /\ b = 0") THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES, DIVIDES_0, ← GSYM EXISTS_REFL] THEN
    ASM_MESON_TAC [BEZOUT_ADD_STRONG, MULT_SYM, ADD_SYM])

  let BEZOUT ← prove
   r"!a b. ?d x y. (d divides a /\ d divides b) /\
                 (a * x - b * y = d \/ b * x - a * y = d)"
   (MESON_TAC [BEZOUT_GCD, GCD])

  let GCD_BEZOUT ← prove
   r"!a b d. (?x y. a * x - b * y = d \/ b * x - a * y = d) <=>
           gcd(a,b) divides d"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC DIVIDES_SUB THEN CONJ_TAC THEN
      MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC [GCD],
      DISCH_THEN (X_CHOOSE_THEN (← q r"k:num") SUBST1_TAC o REWRITE_RULE [divides]) THEN
      STRIP_ASSUME_TAC (← SPECL [← q r"a:num", ← q r"b:num"] BEZOUT_GCD) THEN
      MAP_EVERY EXISTS_TAC [← q r"x * k", ← q r"y * k"] THEN
      ASM_REWRITE_TAC [← GSYM RIGHT_SUB_DISTRIB, MULT_ASSOC] THEN
      FIRST_ASSUM (DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC []])

  let GCD_LE ← prove
   r"(!m n. gcd(m,n) <= m <=> (m = 0 ==> n = 0)) /\
   (!m n. gcd(m,n) <= n <=> (n = 0 ==> m = 0))"
   (REPEAT STRIP_TAC THEN
    MAP_EVERY ASM_CASES_TAC [← q r"m = 0", ← q r"n = 0"] THEN
    ASM_REWRITE_TAC [GCD_0, LE_REFL, LE] THEN
    MATCH_MP_TAC DIVIDES_LE_IMP THEN
    ASM_REWRITE_TAC [GCD])

  let GCD_LE_MIN_EQ ← prove
   r"!m n. gcd(m,n) <= MIN m n <=> (m = 0 <=> n = 0)"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [GCD_0, ← CONJUNCT1 LE, ← ARITH_RULE (← q r"MIN m 0 = 0")] THEN
    ASM_CASES_TAC (← q r"m = 0") THEN
    ASM_REWRITE_TAC [GCD_0, ← CONJUNCT1 LE, ← ARITH_RULE (← q r"MIN 0 n = 0")] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"p <= MIN m n <=> p <= m /\ p <= n")] THEN
    CONJ_TAC THEN MATCH_MP_TAC DIVIDES_LE_IMP THEN ASM_REWRITE_TAC [GCD])

  let GCD_LE_MIN ← prove
   r"!m n. (m = 0 <=> n = 0) ==> gcd(m,n) <= MIN m n"
   (REWRITE_TAC [GCD_LE_MIN_EQ])

  let GCD_LE_MAX ← prove
   r"!m n. gcd(m,n) <= MAX m n"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [GCD_0, ← ARITH_RULE (← q r"MAX m 0 = m"), LE_REFL] THEN
    ASM_CASES_TAC (← q r"m = 0") THEN
    ASM_REWRITE_TAC [GCD_0, ← ARITH_RULE (← q r"MAX 0 n = n"), LE_REFL] THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"p <= MIN m n ==> p <= MAX m n")) THEN
    ASM_REWRITE_TAC [GCD_LE_MIN_EQ])
  return { DIVIDES_GCD, GCD_0, GCD_ZERO, GCD_REFL, GCD_1, GCD_MULTIPLE, GCD_ADD, 
           GCD_SUB, DIVIDES_GCD_LEFT, DIVIDES_GCD_RIGHT, GCD_COPRIME_LMUL, 
           GCD_COPRIME_RMUL, DIVIDES_LMUL_GCD, DIVIDES_RMUL_GCD, GCD_MUL_COPRIME, 
           GCD_SYM, GCD_ASSOC, GCD_LMUL, GCD_RMUL, GCD_BEZOUT_SUM, 
           GCD_COPRIME_DIVIDES_LMUL, GCD_COPRIME_DIVIDES_RMUL, GCD_UNIQUE, 
           GCD_EQ, BEZOUT_GCD_STRONG, BEZOUT_ADD_STRONG, BEZOUT_GCD, BEZOUT_ADD, 
           BEZOUT, GCD_BEZOUT, GCD_LE, GCD_LE_MIN_EQ, GCD_LE_MIN, GCD_LE_MAX }

/- ------------------------------------------------------------------------- -/
/- Coprimality (prime.ml 399-608)                                            -/
/- ------------------------------------------------------------------------- -/

structure Coprime where
  COPRIME : thm
  COPRIME_GCD : thm
  GCD_ONE : thm
  COPRIME_SYM : thm
  COPRIME_BEZOUT : thm
  COPRIME_DIVPROD : thm
  COPRIME_1 : thm
  GCD_COPRIME : thm
  GCD_COPRIME_EXISTS : thm
  COPRIME_DIVPROD_IFF : thm
  CONG_MULT_LCANCEL_IFF : thm
  CONG_MULT_RCANCEL_IFF : thm
  COPRIME_0 : thm
  COPRIME_MUL : thm
  COPRIME_LMUL2 : thm
  COPRIME_RMUL2 : thm
  COPRIME_LMUL : thm
  COPRIME_RMUL : thm
  COPRIME_EXP : thm
  COPRIME_EXP_IMP : thm
  COPRIME_REXP : thm
  COPRIME_LEXP : thm
  COPRIME_EXP2 : thm
  COPRIME_EXP2_SUC : thm
  COPRIME_NPRODUCT_EQ : thm
  COPRIME_NPRODUCT : thm
  COPRIME_DIVISORS : thm
  COPRIME_REFL : thm
  COPRIME_PLUS1 : thm
  COPRIME_MINUS1 : thm
  GCD_EXP : thm
  DIVIDES_EXP2_REV : thm
  DIVIDES_EXP2_EQ : thm
  DIVIDES_MUL : thm
  DIVISION_DECOMP : thm
  deriving Inhabited

@[nospecialize]
def setupCoprime [HolBase] (D : PrimeDeps) (PDivides : Divides) (PGcd : Gcd) : ExceptT String IO Coprime := do
  let { ARITH_RULE, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, NUMBER_RULE, 
        NUMBER_TAC, NUM_RING, .. } := D
  let { CONJ_SYM, DISJ_ACI, DIVIDES_ONE, EXP, EXP_EQ_1, EXP_MONO_EQ, 
        FINITE_INDUCT_STRONG, FORALL_IN_INSERT, GCD, LEFT_AND_EXISTS_THM, 
        LEFT_IMP_EXISTS_THM, .. } := D.core1
  let { MONO_EXISTS, MULT_CLAUSES, MULT_EXP, MULT_SYM, NOT_IN_EMPTY, NOT_SUC, 
        NPRODUCT_CLAUSES, RIGHT_AND_EXISTS_THM, coprime, divides, .. } := D.core2
  let { DIVIDES_1, DIVIDES_SUB, DIVIDES_EXP, .. } := PDivides
  let { GCD_ZERO, DIVIDES_GCD_LEFT, GCD_RMUL, GCD_BEZOUT, .. } := PGcd

  let COPRIME ← prove
   r"!a b. coprime(a,b) <=> !d. d divides a /\ d divides b <=> d = 1"
   (REPEAT GEN_TAC THEN REWRITE_TAC [coprime] THEN
    REPEAT (EQ_TAC ORELSE STRIP_TAC) THEN ASM_REWRITE_TAC [DIVIDES_1] THENL
     [FIRST_ASSUM MATCH_MP_TAC,
      FIRST_ASSUM (CONV_TAC o REWR_CONV o GSYM) THEN CONJ_TAC] THEN
    ASM_REWRITE_TAC [])

  let COPRIME_GCD ← prove
   r"!a b. coprime(a,b) <=> gcd(a,b) = 1"
   (REWRITE_TAC [← GSYM DIVIDES_ONE] THEN NUMBER_TAC)

  let GCD_ONE ← prove
   r"!a b. coprime(a,b) ==> gcd(a,b) = 1"
   (NUMBER_TAC)

  let COPRIME_SYM ← prove
   r"!a b. coprime(a,b) <=> coprime(b,a)"
   (NUMBER_TAC)

  let COPRIME_BEZOUT ← prove
   r"!a b. coprime(a,b) <=> ?x y. a * x - b * y = 1 \/ b * x - a * y = 1"
   (REWRITE_TAC [GCD_BEZOUT, DIVIDES_ONE, COPRIME_GCD])

  let COPRIME_DIVPROD ← prove
   r"!d a b. d divides (a * b) /\ coprime(d,a) ==> d divides b"
   (NUMBER_TAC)

  let COPRIME_1 ← prove
   r"(!a. coprime(a,1)) /\ (!a. coprime(1,a))"
   (NUMBER_TAC)

  let GCD_COPRIME ← prove
   r"!a b a' b'. ~(gcd(a,b) = 0) /\ a = a' * gcd(a,b) /\ b = b' * gcd(a,b)
               ==> coprime(a',b')"
   (NUMBER_TAC)

  let GCD_COPRIME_EXISTS ← prove
   r"!a b. ?a' b'. a = a' * gcd(a,b) /\ b = b' * gcd(a,b) /\ coprime(a',b')"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"gcd(a,b) = 0") THENL
     [FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE [GCD_ZERO]) THEN
      MAP_EVERY EXISTS_TAC [← q r"0", ← q r"1"] THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN
      CONV_TAC NUMBER_RULE,
      MP_TAC (← CONJUNCT1 (← SPECL [← q r"a:num", ← q r"b:num"] GCD)) THEN
      REWRITE_TAC [divides, LEFT_AND_EXISTS_THM] THEN
      REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
      REPEAT (MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      ASM_MESON_TAC [GCD_COPRIME, MULT_SYM]])

  let COPRIME_DIVPROD_IFF ← prove
   r"!d a. ~(d = 0)
         ==> ((!b. d divides a * b ==> d divides b) <=> coprime(d,a))"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC, CONV_TAC NUMBER_RULE] THEN
    MP_TAC (← GSYM (← ISPECL [← q r"d:num", ← q r"a:num"] GCD_COPRIME_EXISTS)) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"a':num", ← q r"b':num"] THEN STRIP_TAC THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"a':num")) THEN ANTS_TAC THEN
    REPEAT (POP_ASSUM MP_TAC) THEN NUMBER_TAC)

  let CONG_MULT_LCANCEL_IFF ← prove
   r"!a n. ~(n = 0)
         ==> ((!x y. (a * x == a * y) (mod n) ==> (x == y) (mod n)) <=>
              coprime(a,n))"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC, CONV_TAC NUMBER_RULE] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"0")) THEN
    ASM_SIMP_TAC [MULT_CLAUSES, ← NUMBER_RULE (← q r"(0 == x) (mod n) <=> n divides x"),
                  COPRIME_DIVPROD_IFF] THEN
    CONV_TAC NUMBER_RULE)

  let CONG_MULT_RCANCEL_IFF ← prove
   r"!a n. ~(n = 0)
         ==> ((!x y. (x * a == y * a) (mod n) ==> (x == y) (mod n)) <=>
              coprime(a,n))"
   (ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [CONG_MULT_LCANCEL_IFF])

  let COPRIME_0 ← prove
   r"(!d. coprime(d,0) <=> d = 1) /\
   (!d. coprime(0,d) <=> d = 1)"
   (NUMBER_TAC)

  let COPRIME_MUL ← prove
   r"!d a b. coprime(d,a) /\ coprime(d,b) ==> coprime(d,a * b)"
   (NUMBER_TAC)

  let COPRIME_LMUL2 ← prove
   r"!d a b. coprime(d,a * b) ==> coprime(d,b)"
   (NUMBER_TAC)

  let COPRIME_RMUL2 ← prove
   r"!d a b.  coprime(d,a * b) ==> coprime(d,a)"
   (NUMBER_TAC)

  let COPRIME_LMUL ← prove
   r"!d a b. coprime(a * b,d) <=> coprime(a,d) /\ coprime(b,d)"
   (NUMBER_TAC)

  let COPRIME_RMUL ← prove
   r"!d a b. coprime(d,a * b) <=> coprime(d,a) /\ coprime(d,b)"
   (NUMBER_TAC)

  let COPRIME_EXP ← prove
   r"!n a d. coprime(d,a) ==> coprime(d,a EXP n)"
   (INDUCT_TAC THEN REWRITE_TAC [EXP, COPRIME_1] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC COPRIME_MUL THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC [])

  let COPRIME_EXP_IMP ← prove
   r"!n a b. coprime(a,b) ==> coprime(a EXP n,b EXP n)"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC COPRIME_EXP THEN ONCE_REWRITE_TAC [COPRIME_SYM] THEN
    MATCH_MP_TAC COPRIME_EXP THEN
    ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_REWRITE_TAC [])

  let COPRIME_REXP ← prove
   r"!m n k. coprime(m,n EXP k) <=> coprime(m,n) \/ k = 0"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [← CONJUNCT1 EXP, COPRIME_1] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC [COPRIME_EXP, NOT_SUC] THEN
    REWRITE_TAC [EXP] THEN CONV_TAC NUMBER_RULE)

  let COPRIME_LEXP ← prove
   r"!m n k. coprime(m EXP k,n) <=> coprime(m,n) \/ k = 0"
   (ONCE_REWRITE_TAC [COPRIME_SYM] THEN REWRITE_TAC [COPRIME_REXP])

  let COPRIME_EXP2 ← prove
   r"!m n k. coprime(m EXP k,n EXP k) <=> coprime(m,n) \/ k = 0"
   (REWRITE_TAC [COPRIME_REXP, COPRIME_LEXP, DISJ_ACI])

  let COPRIME_EXP2_SUC ← prove
   r"!n a b. coprime(a EXP (SUC n),b EXP (SUC n)) <=> coprime(a,b)"
   (REWRITE_TAC [COPRIME_EXP2, NOT_SUC])

  let COPRIME_NPRODUCT_EQ ← prove
   r"(!(f:A->num) a s.
        FINITE s
        ==> (coprime(a,nproduct s f) <=> !i. i IN s ==> coprime(a,f i))) /\
   (!(f:A->num) b s.
        FINITE s
        ==> (coprime(nproduct s f,b) <=> !i. i IN s ==> coprime(f i,b)))"
   (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [COPRIME_SYM] THEN
    REWRITE_TAC [] THEN GEN_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [NPRODUCT_CLAUSES, NOT_IN_EMPTY, COPRIME_1] THEN
    SIMP_TAC [COPRIME_RMUL, FORALL_IN_INSERT])

  let COPRIME_NPRODUCT ← prove
   r"!s n. FINITE s /\ (!x. x IN s ==> coprime(n,a x))
         ==> coprime(n,nproduct s a)"
   (SIMP_TAC [COPRIME_NPRODUCT_EQ])

  let COPRIME_DIVISORS ← prove
   r"!a b d e. d divides a /\ e divides b /\ coprime(a,b) ==> coprime(d,e)"
   (NUMBER_TAC)

  let COPRIME_REFL ← prove
   r"!n. coprime(n,n) <=> n = 1"
   (NUMBER_TAC)

  let COPRIME_PLUS1 ← prove
   r"!n. coprime(n + 1,n)"
   (NUMBER_TAC)

  let COPRIME_MINUS1 ← prove
   r"!n. ~(n = 0) ==> coprime(n - 1,n)"
   (REPEAT STRIP_TAC THEN SIMP_TAC [coprime] THEN ONCE_REWRITE_TAC [CONJ_SYM] THEN
    GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP DIVIDES_SUB) THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"~(n = 0) ==> n - (n - 1) = 1"), DIVIDES_ONE])

  let GCD_EXP ← prove
   r"!n a b. gcd(a EXP n,b EXP n) = gcd(a,b) EXP n"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"a:num", ← q r"b:num"] GCD_COPRIME_EXISTS) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"a':num", ← q r"b':num"] THEN
    STRIP_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [MULT_EXP, GCD_RMUL] THEN
    MATCH_MP_TAC (← NUM_RING (← q r"x = 1 /\ y = 1 ==> a * x = a * y")) THEN
    ASM_REWRITE_TAC [← GSYM COPRIME_GCD, EXP_EQ_1] THEN
    ASM_REWRITE_TAC [COPRIME_LEXP, COPRIME_REXP])

  let DIVIDES_EXP2_REV ← prove
   r"!n a b. (a EXP n) divides (b EXP n) /\ ~(n = 0) ==> a divides b"
   (REWRITE_TAC [DIVIDES_GCD_LEFT, GCD_EXP, EXP_MONO_EQ] THEN MESON_TAC [])

  let DIVIDES_EXP2_EQ ← prove
   r"!n a b. ~(n = 0) ==> ((a EXP n) divides (b EXP n) <=> a divides b)"
   (MESON_TAC [DIVIDES_EXP2_REV, DIVIDES_EXP])

  let DIVIDES_MUL ← prove
   r"!m n r. m divides r /\ n divides r /\ coprime(m,n) ==> (m * n) divides r"
   (NUMBER_TAC)

  let DIVISION_DECOMP ← prove
   r"!a b c.
        a divides (b * c)
        ==> ?b' c'. a = b' * c' /\ b' divides b /\ c' divides c"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC (← q r"gcd(a,b)") THEN
    REWRITE_TAC [GCD] THEN ASM_CASES_TAC (← q r"gcd(a,b) = 0") THENL
     [ASM_REWRITE_TAC [] THEN EXISTS_TAC (← q r"1") THEN
      RULE_ASSUM_TAC (REWRITE_RULE [GCD_ZERO]) THEN
      ASM_REWRITE_TAC [MULT_CLAUSES, DIVIDES_1],
      MP_TAC (← SPECL [← q r"a:num", ← q r"b:num"] GCD_COPRIME_EXISTS) THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC NUMBER_RULE])
  return { COPRIME, COPRIME_GCD, GCD_ONE, COPRIME_SYM, COPRIME_BEZOUT, 
           COPRIME_DIVPROD, COPRIME_1, GCD_COPRIME, GCD_COPRIME_EXISTS, 
           COPRIME_DIVPROD_IFF, CONG_MULT_LCANCEL_IFF, CONG_MULT_RCANCEL_IFF, 
           COPRIME_0, COPRIME_MUL, COPRIME_LMUL2, COPRIME_RMUL2, COPRIME_LMUL, 
           COPRIME_RMUL, COPRIME_EXP, COPRIME_EXP_IMP, COPRIME_REXP, 
           COPRIME_LEXP, COPRIME_EXP2, COPRIME_EXP2_SUC, COPRIME_NPRODUCT_EQ, 
           COPRIME_NPRODUCT, COPRIME_DIVISORS, COPRIME_REFL, COPRIME_PLUS1, 
           COPRIME_MINUS1, GCD_EXP, DIVIDES_EXP2_REV, DIVIDES_EXP2_EQ, 
           DIVIDES_MUL, DIVISION_DECOMP }

/- ------------------------------------------------------------------------- -/
/- Primes (prime.ml 609-1188)                                                -/
/- ------------------------------------------------------------------------- -/

structure Primes where
  PRIME_0 : thm
  PRIME_1 : thm
  PRIME_ALT : thm
  PRIME_2 : thm
  PRIME_COPRIME_STRONG : thm
  PRIME_COPRIME : thm
  PRIME_COPRIME_EQ : thm
  COPRIME_PRIME : thm
  PRIME_DIVPROD : thm
  PRIME_DIVPROD_EQ : thm
  PRIME_INT_DIVPROD_EQ : thm
  PRIME_GE_2 : thm
  PRIME_FACTOR : thm
  PRIME : thm
  PRIME_PRIME_FACTOR : thm
  PRIME_FACTOR_LT : thm
  COPRIME_PRIME_EQ : thm
  GCD_PRIME_CASES : thm
  GCD_2_CASES : thm
  COPRIME_PRIMEPOW : thm
  COPRIME_BEZOUT_STRONG : thm
  COPRIME_BEZOUT_ALT : thm
  BEZOUT_PRIME : thm
  PRIME_DIVEXP : thm
  PRIME_DIVEXP_N : thm
  PRIME_DIVEXP_EQ : thm
  COPRIME_SOS : thm
  PRIME_IMP_NZ : thm
  DISTINCT_PRIME_COPRIME : thm
  PRIME_COPRIME_LT : thm
  DIVIDES_PRIME_PRIME : thm
  COPRIME_PRIME_PRIME : thm
  DIVIDES_PRIME_EXP_LE : thm
  EQ_PRIME_EXP : thm
  PRIME_ODD : thm
  ODD_PRIME : thm
  DIVIDES_FACT_PRIME : thm
  EQ_PRIMEPOW : thm
  COPRIME_2 : thm
  DIVIDES_EXP_PLUS1 : thm
  DIVIDES_EXP_MINUS1 : thm
  PRIME_IRREDUCIBLE : thm
  COPRIME_EXP_DIVPROD : thm
  PRIME_COPRIME_CASES : thm
  PRIME_DIVPROD_POW_GEN : thm
  PRIME_DIVPROD_POW_GEN_EQ : thm
  PRIME_DIVPROD_POW : thm
  PRIME_DIVPROD_POW_EQ : thm
  PRIME_FACTOR_INDUCT : thm
  COMPLETE_FACTOR_INDUCT : thm
  PRIME_FACTOR_PARTITION : thm
  COPRIME_PAIR_DECOMP : thm
  EXP_MULT_EXISTS : thm
  COPRIME_POW : thm
  PRIME_EXP : thm
  PRIME_POWER_MULT : thm
  PRIME_POWER_EXP : thm
  DIVIDES_PRIMEPOW : thm
  PRIMEPOW_DIVIDES_PROD : thm
  EUCLID_BOUND : thm
  EUCLID : thm
  PRIMES_INFINITE : thm
  FACTORIZATION_INDEX : thm
  PRIMEPOW_FACTOR : thm
  PRIMEPOW_DIVISORS_DIVIDES : thm
  PRIMEPOW_DIVISORS_EQ : thm
  deriving Inhabited

@[nospecialize]
def setupPrimes [HolBase] (D : PrimeDeps) (PDivides : Divides) (PGcd : Gcd) (PCoprime : Coprime) : ExceptT String IO Primes := do
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, 
        INTEGER_RULE, INTEGER_TAC, MESON_TAC, NUMBER_RULE, NUMBER_TAC, NUM_RING, 
        CONTRAPOS_CONV, NUM_REDUCE_CONV, .. } := D
  let { ADD1, ARITH, ARITH_EQ, CONJ_ASSOC, CONTRAPOS_THM, COPRIME_RMOD, 
        DE_MORGAN_THM, DISJ_SYM, DIVIDES_ANTISYM, DIVIDES_LE, DIVIDES_LE_STRONG, 
        DIVIDES_MOD, DIVIDES_ONE, EQ_MULT_LCANCEL, EVEN_EXISTS, EXP, EXP_1, 
        EXP_2, EXP_ADD, EXP_EQ_0, EXP_EQ_1, EXP_MONO_LE, EXP_ONE, EXP_ZERO, FACT, 
        FACT_LT, FORALL_AND_THM, FORALL_INT_CASES, FORALL_UNWIND_THM2, GT, 
        IMP_CONJ, INFINITE, INT_MUL_LNEG, INT_MUL_RNEG, INT_NEG_NEG, 
        INT_OF_NUM_CLAUSES, INT_OF_NUM_POW, INT_OF_NUM_SUB, INT_POW, IN_ELIM_THM, 
        LE, LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, LE_1, LE_ADD, LE_ANTISYM, 
        LE_EXISTS, LE_EXP, LE_TRANS, LT_EXP, LT_IMP_LE, LT_LE, LT_MULT_RCANCEL, 
        LT_POW2_REFL, LT_REFL, .. } := D.core1
  let { MOD_LT_EQ, MONO_EXISTS, MULT_AC, MULT_ASSOC, MULT_CLAUSES, MULT_EQ_0, 
        MULT_EQ_1, MULT_EXP, MULT_SYM, NOT_EVEN, NOT_FORALL_THM, NOT_IMP, NOT_LE, 
        NOT_LT, NOT_SUC, ODD_EXISTS, ONE_OR_PRIME_DIVIDES_OR_COPRIME, 
        PRIME_COPRIME_EQ_NONDIVISIBLE, RIGHT_EXISTS_AND_THM, SWAP_FORALL_THM, 
        UNWIND_THM2, ZERO_ONE_OR_PRIME, coprime, divides, num_CASES, num_FINITE, 
        num_MAX, num_WF, num_divides, prime, .. } := D.core2
  let { DIVIDES_0, DIVIDES_1, DIVIDES_REFL, DIVIDES_TRANS, DIVIDES_LMUL, 
        DIVIDES_RMUL, DIVIDES_ADD_REVR, DIVIDES_MUL_L, DIVIDES_RMUL2, 
        DIVIDES_EXP, DIVIDES_EXP_LE, DIVIDES_FACT, DIVIDES_2, DIVIDES_REXP, .. } := PDivides
  let { DIVIDES_GCD, DIVIDES_GCD_LEFT, GCD_SYM, BEZOUT_GCD_STRONG, .. } := PGcd
  let { COPRIME_GCD, COPRIME_SYM, COPRIME_DIVPROD, COPRIME_0, COPRIME_LMUL, 
        COPRIME_RMUL, COPRIME_EXP, COPRIME_REXP, COPRIME_LEXP, DIVIDES_EXP2_REV, 
        DIVISION_DECOMP, .. } := PCoprime

  let PRIME_0 ← prove
   r"~prime(0)"
   (REWRITE_TAC [prime] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"2") o CONJUNCT2) THEN
    REWRITE_TAC [DIVIDES_0, ARITH])

  let PRIME_1 ← prove
   r"~prime(1)"
   (REWRITE_TAC [prime])

  let PRIME_ALT ← prove
   r"!p. prime p <=>
       ~(p = 0) /\ ~(p = 1) /\ !n. 1 < n /\ n < p ==> ~(n divides p)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"p = 0") THEN ASM_REWRITE_TAC [PRIME_0] THEN
    REWRITE_TAC [prime, LT_LE] THEN
    ASM_MESON_TAC [DIVIDES_LE_STRONG, DIVIDES_0, LE_1])

  let PRIME_2 ← prove
   r"prime(2)"
   (REWRITE_TAC [PRIME_ALT] THEN ARITH_TAC)

  let PRIME_COPRIME_STRONG ← prove
   r"!n p. prime(p) ==> p divides n \/ coprime(p,n)"
   (REWRITE_TAC [prime, coprime] THEN MESON_TAC [])

  let PRIME_COPRIME ← prove
   r"!n p. prime(p) ==> n = 1 \/ p divides n \/ coprime(p,n)"
   (MESON_TAC [PRIME_COPRIME_STRONG])

  let PRIME_COPRIME_EQ ← prove
   r"!p n. prime p ==> (coprime(p,n) <=> ~(p divides n))"
   (SIMP_TAC [PRIME_COPRIME_EQ_NONDIVISIBLE])

  let COPRIME_PRIME ← prove
   r"!p a b. coprime(a,b) ==> ~(prime(p) /\ p divides a /\ p divides b)"
   (MESON_TAC [coprime, PRIME_1])

  let PRIME_DIVPROD ← prove
   r"!p a b. prime(p) /\ p divides (a * b) ==> p divides a \/ p divides b"
   (MESON_TAC [PRIME_COPRIME_STRONG, COPRIME_DIVPROD])

  let PRIME_DIVPROD_EQ ← prove
   r"!p a b. prime(p) ==> (p divides (a * b) <=> p divides a \/ p divides b)"
   (MESON_TAC [PRIME_DIVPROD, DIVIDES_LMUL, DIVIDES_RMUL])

  let PRIME_INT_DIVPROD_EQ ← prove
   r"!p a b:int.
        prime p ==> (&p divides a * b <=> &p divides a \/ &p divides b)"
   (REWRITE_TAC [FORALL_INT_CASES, INT_MUL_LNEG, INT_MUL_RNEG, INT_NEG_NEG] THEN
    REWRITE_TAC [← INTEGER_RULE (← q r"(a:int) divides --b <=> a divides b")] THEN
    REWRITE_TAC [← GSYM num_divides, PRIME_DIVPROD_EQ, INT_OF_NUM_CLAUSES])

  let PRIME_GE_2 ← prove
   r"!p. prime(p) ==> 2 <= p"
   (REWRITE_TAC [← ARITH_RULE (← q r"2 <= p <=> ~(p = 0) /\ ~(p = 1)")] THEN
    MESON_TAC [PRIME_0, PRIME_1])

  let PRIME_FACTOR ← prove
   r"!n. ~(n = 1) ==> ?p. prime(p) /\ p divides n"
   (MATCH_MP_TAC num_WF THEN
    X_GEN_TAC (← q r"n:num") THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"prime(n)") THENL [ASM_MESON_TAC [DIVIDES_REFL], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [PRIME_ALT]) THEN
    ASM_REWRITE_TAC [DE_MORGAN_THM, NOT_FORALL_THM, NOT_IMP] THEN
    STRIP_TAC THENL [ASM_MESON_TAC [PRIME_2, DIVIDES_0], ALL_TAC] THEN
    ASM_MESON_TAC [DIVIDES_TRANS, LT_REFL])

  let PRIME ← prove
   r"!p. prime p <=>
       ~(p = 0) /\ ~(p = 1) /\ !m. 0 < m /\ m < p ==> coprime(p,m)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"p = 0") THEN ASM_REWRITE_TAC [PRIME_0] THEN
    ASM_CASES_TAC (← q r"p = 1") THEN ASM_REWRITE_TAC [PRIME_1] THEN
    MP_TAC (← SPEC (← q r"p:num") ONE_OR_PRIME_DIVIDES_OR_COPRIME) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
    EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC (← q r"n:num") THENL
     [STRIP_TAC THEN FIRST_X_ASSUM (DISJ_CASES_TAC o SPEC (← q r"n:num")) THEN
      ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o MATCH_MP DIVIDES_LE_STRONG) THEN ASM_ARITH_TAC,
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"n MOD p")) THEN
      ASM_REWRITE_TAC [MOD_LT_EQ, COPRIME_RMOD, DIVIDES_MOD] THEN
      MESON_TAC [LE_1]])

  let PRIME_PRIME_FACTOR ← prove
   r"!n. prime n <=> ~(n = 1) /\ !p. prime p /\ p divides n ==> p = n"
   (GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [prime] THEN
    ASM_CASES_TAC (← q r"n = 1") THEN ASM_REWRITE_TAC [] THEN EQ_TAC THENL
     [MESON_TAC [PRIME_1], ALL_TAC] THEN
    STRIP_TAC THEN X_GEN_TAC (← q r"d:num") THEN
    ASM_CASES_TAC (← q r"d = 1") THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q r"p:num") STRIP_ASSUME_TAC o
      MATCH_MP PRIME_FACTOR) THEN
    ASM_MESON_TAC [DIVIDES_TRANS, DIVIDES_ANTISYM])

  let PRIME_FACTOR_LT ← prove
   r"!n m p. prime(p) /\ ~(n = 0) /\ n = p * m ==> m < n"
   (REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [MULT_EQ_0, DE_MORGAN_THM]) THEN
    ASM_SIMP_TAC [LT_MULT_RCANCEL, ← ARITH_RULE (← q r"m < p * m <=> 1 * m < p * m")] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC)

  let COPRIME_PRIME_EQ ← prove
   r"!a b. coprime(a,b) <=> !p. ~(prime(p) /\ p divides a /\ p divides b)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← MATCH_MP COPRIME_PRIME th])),
      CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [coprime] THEN
      ONCE_REWRITE_TAC [NOT_FORALL_THM] THEN REWRITE_TAC [NOT_IMP] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"d:num") STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM (X_CHOOSE_TAC (← q r"p:num") o MATCH_MP PRIME_FACTOR) THEN
      EXISTS_TAC (← q r"p:num") THEN ASM_REWRITE_TAC [] THEN CONJ_TAC THEN
      MATCH_MP_TAC DIVIDES_TRANS THEN EXISTS_TAC (← q r"d:num") THEN
      ASM_REWRITE_TAC []])

  let GCD_PRIME_CASES ← prove
   r"(!p n. prime p ==> gcd(p,n) = if p divides n then p else 1) /\
   (!p n. prime p ==> gcd(n,p) = if p divides n then p else 1)"
   (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GCD_SYM] THEN
    REWRITE_TAC [] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [← GSYM DIVIDES_GCD_LEFT] THEN
    REWRITE_TAC [← GSYM COPRIME_GCD] THEN
    ASM_MESON_TAC [PRIME_COPRIME_EQ])

  let GCD_2_CASES ← prove
   r"(!n. gcd(2,n) = if EVEN n then 2 else 1) /\
   (!n. gcd(n,2) = if EVEN n then 2 else 1)"
   (SIMP_TAC [GCD_PRIME_CASES, PRIME_2, DIVIDES_2])

  let COPRIME_PRIMEPOW ← prove
   r"!p k m. prime p /\ ~(k = 0) ==> (coprime(m,p EXP k) <=> ~(p divides m))"
   (SIMP_TAC [COPRIME_REXP] THEN ONCE_REWRITE_TAC [COPRIME_SYM] THEN
    SIMP_TAC [PRIME_COPRIME_EQ])

  let COPRIME_BEZOUT_STRONG ← prove
   r"!a b. coprime(a,b) /\ ~(b = 1) ==> ?x y. a * x = b * y + 1"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [COPRIME_GCD]) THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC BEZOUT_GCD_STRONG THEN
    ASM_MESON_TAC [COPRIME_0, COPRIME_SYM])

  let COPRIME_BEZOUT_ALT ← prove
   r"!a b. coprime(a,b) /\ ~(a = 0) ==> ?x y. a * x = b * y + 1"
   (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o GEN_REWRITE_RULE I [COPRIME_GCD]) THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC BEZOUT_GCD_STRONG THEN
    ASM_MESON_TAC [COPRIME_0, COPRIME_SYM])

  let BEZOUT_PRIME ← prove
   r"!a p. prime p /\ ~(p divides a) ==> ?x y. a * x = p * y + 1"
   (MESON_TAC [PRIME_COPRIME_STRONG, COPRIME_SYM,
       COPRIME_BEZOUT_STRONG, PRIME_1])

  let PRIME_DIVEXP ← prove
   r"!n p x. prime(p) /\ p divides (x EXP n) ==> p divides x"
   (INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC [EXP, DIVIDES_ONE] THENL
     [DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC [DIVIDES_1],
      DISCH_THEN (fun th => tactic_of do pure (ASSUME_TAC (← CONJUNCT1 th) THEN MP_TAC th)) THEN
      DISCH_THEN (DISJ_CASES_TAC o MATCH_MP PRIME_DIVPROD) THEN
      ASM_REWRITE_TAC [] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC []])

  let PRIME_DIVEXP_N ← prove
   r"!n p x. prime(p) /\ p divides (x EXP n) ==> (p EXP n) divides (x EXP n)"
   (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP PRIME_DIVEXP) THEN
    MATCH_ACCEPT_TAC DIVIDES_EXP)

  let PRIME_DIVEXP_EQ ← prove
   r"!n p x. prime p ==> (p divides x EXP n <=> p divides x /\ ~(n = 0))"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [EXP, DIVIDES_ONE] THEN
    ASM_MESON_TAC [PRIME_DIVEXP, DIVIDES_REXP, PRIME_1])

  let COPRIME_SOS ← prove
   r"!x y. coprime(x,y) ==> coprime(x * y,(x EXP 2) + (y EXP 2))"
   (NUMBER_TAC)

  let PRIME_IMP_NZ ← prove
   r"!p. prime(p) ==> ~(p = 0)"
   (MESON_TAC [PRIME_0])

  let DISTINCT_PRIME_COPRIME ← prove
   r"!p q. prime p /\ prime q /\ ~(p = q) ==> coprime(p,q)"
   (MESON_TAC [prime, coprime, PRIME_1])

  let PRIME_COPRIME_LT ← prove
   r"!x p. prime p /\ 0 < x /\ x < p ==> coprime(x,p)"
   (REWRITE_TAC [coprime, prime] THEN
    MESON_TAC [LT_REFL, DIVIDES_LE, NOT_LT, PRIME_0])

  let DIVIDES_PRIME_PRIME ← prove
   r"!p q. prime p /\ prime q  ==> (p divides q <=> p = q)"
   (MESON_TAC [DIVIDES_REFL, DISTINCT_PRIME_COPRIME, PRIME_COPRIME_EQ])

  let COPRIME_PRIME_PRIME ← prove
   r"!p q. prime p /\ prime q ==> (coprime(p,q) <=> ~(p = q))"
   (MESON_TAC [PRIME_COPRIME_EQ, DIVIDES_PRIME_PRIME, COPRIME_SYM])

  let DIVIDES_PRIME_EXP_LE ← prove
   r"!p q m n. prime p /\ prime q
             ==> ((p EXP m) divides (q EXP n) <=> m = 0 \/ p = q /\ m <= n)"
   (GEN_TAC THEN GEN_TAC THEN REPEAT INDUCT_TAC THEN
    ASM_SIMP_TAC [EXP, DIVIDES_1, DIVIDES_ONE, MULT_EQ_1, NOT_SUC] THENL
     [MESON_TAC [PRIME_1, ← ARITH_RULE (← q r"~(SUC m <= 0)")], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"p:num = q") THEN
    ASM_SIMP_TAC [DIVIDES_EXP_LE, PRIME_GE_2, ← GSYM (← CONJUNCT2 EXP)] THEN
    ASM_MESON_TAC [PRIME_DIVEXP, DIVIDES_PRIME_PRIME, EXP, DIVIDES_RMUL2])

  let EQ_PRIME_EXP ← prove
   r"!p q m n. prime p /\ prime q
             ==> (p EXP m = q EXP n <=> m = 0 /\ n = 0 \/ p = q /\ m = n)"
   (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM DIVIDES_ANTISYM] THEN
    ASM_SIMP_TAC [DIVIDES_PRIME_EXP_LE] THEN ARITH_TAC)

  let PRIME_ODD ← prove
   r"!p. prime p ==> p = 2 \/ ODD p"
   (GEN_TAC THEN REWRITE_TAC [prime, ← GSYM NOT_EVEN, EVEN_EXISTS] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC (← q r"2"))) THEN
    REWRITE_TAC [divides, ARITH] THEN MESON_TAC [])

  let ODD_PRIME ← prove
   r"!p. prime p ==> (ODD p <=> 3 <= p)"
   (GEN_TAC THEN
    ASM_CASES_TAC (← q r"p = 0") THENL [ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"p = 1") THENL [ASM_MESON_TAC [PRIME_1], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o MATCH_MP PRIME_ODD) THEN
    ASM_CASES_TAC (← q r"p = 2") THEN ASM_SIMP_TAC [ARITH] THEN ASM_ARITH_TAC)

  let DIVIDES_FACT_PRIME ← prove
   r"!p. prime p ==> !n. p divides (FACT n) <=> p <= n"
   (GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC [FACT, LE] THENL
     [ASM_MESON_TAC [DIVIDES_ONE, PRIME_0, PRIME_1],
      ASM_MESON_TAC [PRIME_DIVPROD_EQ, DIVIDES_LE, NOT_SUC, DIVIDES_REFL,
                     ← ARITH_RULE (← q r"~(p <= n) /\ p <= SUC n ==> p = SUC n")]])

  let EQ_PRIMEPOW ← prove
   r"!p m n. prime p ==> (p EXP m = p EXP n <=> m = n)"
   (ONCE_REWRITE_TAC [← GSYM LE_ANTISYM] THEN
    SIMP_TAC [LE_EXP, PRIME_IMP_NZ] THEN MESON_TAC [PRIME_1])

  let COPRIME_2 ← prove
   r"(!n. coprime(2,n) <=> ODD n) /\ (!n. coprime(n,2) <=> ODD n)"
   (GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [COPRIME_SYM] THEN
    SIMP_TAC [PRIME_COPRIME_EQ, PRIME_2, DIVIDES_2, NOT_EVEN])

  let DIVIDES_EXP_PLUS1 ← prove
   r"!n k. ODD k ==> (n + 1) divides (n EXP k + 1)"
   (GEN_TAC THEN REWRITE_TAC [ODD_EXISTS, LEFT_IMP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN REWRITE_TAC [FORALL_UNWIND_THM2] THEN
    INDUCT_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC [EXP_1, DIVIDES_REFL] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"SUC(2 * SUC n) = SUC(2 * n) + 2")] THEN
    REWRITE_TAC [EXP_ADD, EXP_2] THEN POP_ASSUM MP_TAC THEN NUMBER_TAC)

  let DIVIDES_EXP_MINUS1 ← prove
   r"!k n. (n - 1) divides (n EXP k - 1)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THENL
     [STRUCT_CASES_TAC (← SPEC (← q r"k:num") num_CASES) THEN
      ASM_REWRITE_TAC [EXP, MULT_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC [DIVIDES_REFL],
      REWRITE_TAC [num_divides] THEN
      ASM_SIMP_TAC [← GSYM INT_OF_NUM_SUB, LE_1, EXP_EQ_0, ARITH] THEN
      POP_ASSUM (K ALL_TAC) THEN REWRITE_TAC [← GSYM INT_OF_NUM_POW] THEN
      SPEC_TAC ((← q r"k:num"), (← q r"k:num")) THEN INDUCT_TAC THEN REWRITE_TAC [INT_POW] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN INTEGER_TAC])

  let PRIME_IRREDUCIBLE ← prove
   r"!p. prime p <=>
       p > 1 /\ !a b. p divides (a * b) ==> p divides a \/ p divides b"
   (GEN_TAC THEN REWRITE_TAC [← GSYM ZERO_ONE_OR_PRIME] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"p > 1 <=> ~(p = 0) /\ ~(p = 1)")] THEN
    MESON_TAC [PRIME_0, PRIME_1])

  let COPRIME_EXP_DIVPROD ← prove
   r"!d n a b.
      (d EXP n) divides (a * b) /\ coprime(d,a) ==> (d EXP n) divides b"
   (MESON_TAC [COPRIME_DIVPROD, COPRIME_EXP, COPRIME_SYM])

  let PRIME_COPRIME_CASES ← prove
   r"!p a b. prime p /\ coprime(a,b) ==> coprime(p,a) \/ coprime(p,b)"
   (MESON_TAC [COPRIME_PRIME, PRIME_COPRIME_EQ])

  let PRIME_DIVPROD_POW_GEN ← prove
   r"!n p a b.
        prime p /\ ~(p divides gcd(a,b)) /\ p EXP n divides a * b
        ==> p EXP n divides a \/ p EXP n divides b"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [DISJ_SYM] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [DIVIDES_GCD]) THEN
    ASM_SIMP_TAC [DE_MORGAN_THM, ← GSYM PRIME_COPRIME_EQ] THEN
    ASM_MESON_TAC [COPRIME_LEXP, COPRIME_DIVPROD, MULT_SYM])

  let PRIME_DIVPROD_POW_GEN_EQ ← prove
   r"!n p a b.
        prime p /\ ~(p divides gcd(a,b))
        ==> (p EXP n divides a * b <=>
             p EXP n divides a \/ p EXP n divides b)"
   (MESON_TAC [PRIME_DIVPROD_POW_GEN, DIVIDES_RMUL, DIVIDES_LMUL])

  let PRIME_DIVPROD_POW ← prove
   r"!n p a b. prime(p) /\ coprime(a,b) /\ (p EXP n) divides (a * b)
             ==> (p EXP n) divides a \/ (p EXP n) divides b"
   (MESON_TAC [COPRIME_EXP_DIVPROD, PRIME_COPRIME_CASES, MULT_SYM])

  let PRIME_DIVPROD_POW_EQ ← prove
   r"!n p a b.
        prime p /\ coprime(a,b)
        ==> (p EXP n divides a * b <=>
             p EXP n divides a \/ p EXP n divides b)"
   (MESON_TAC [PRIME_DIVPROD_POW, DIVIDES_RMUL, DIVIDES_LMUL])

  let PRIME_FACTOR_INDUCT ← prove
   r"!P. P 0 /\ P 1 /\
       (!p n. prime p /\ ~(n = 0) /\ P n ==> P(p * n))
       ==> !n. P n"
   (GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q r"n:num") THEN
    DISCH_TAC THEN MAP_EVERY ASM_CASES_TAC [← q r"n = 0", ← q r"n = 1"] THEN
    ASM_REWRITE_TAC [] THEN FIRST_ASSUM (X_CHOOSE_THEN (← q r"p:num")
      STRIP_ASSUME_TAC o MATCH_MP PRIME_FACTOR) THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"d:num") SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [divides]) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q r"p:num", ← q r"d:num"]) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [MULT_EQ_0, DE_MORGAN_THM]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC [PRIME_FACTOR_LT, MULT_EQ_0])

  let COMPLETE_FACTOR_INDUCT ← prove
   r"!P. P 0 /\ P 1 /\
       (!p. prime p ==> P p) /\
       (!m n. P m /\ P n ==> P(m * n))
       ==> !n. P n"
   (GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC PRIME_FACTOR_INDUCT THEN
    ASM_SIMP_TAC [])

  let PRIME_FACTOR_PARTITION ← prove
   r"!Q n. ~(n = 0)
         ==> ?n1 n2. n1 * n2 = n /\
                     (!p. prime p /\ p divides n1 ==> Q p) /\
                     (!p. prime p /\ p divides n2 ==> ~Q p)"
   (GEN_TAC THEN MATCH_MP_TAC PRIME_FACTOR_INDUCT THEN
    REWRITE_TAC [MULT_EQ_1, ← GSYM CONJ_ASSOC, UNWIND_THM2, RIGHT_EXISTS_AND_THM,
                 DIVIDES_ONE] THEN
    CONJ_TAC THENL [MESON_TAC [PRIME_1], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q r"p:num", ← q r"n:num"] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_REWRITE_TAC [MULT_EQ_0, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"n1:num", ← q r"n2:num"] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"(Q:num->bool) p") THENL
     [MAP_EVERY EXISTS_TAC [← q r"p * n1:num", ← q r"n2:num"],
      MAP_EVERY EXISTS_TAC [← q r"n1:num", ← q r"p * n2:num"]] THEN
    ASM_SIMP_TAC [IMP_CONJ, PRIME_DIVPROD_EQ] THEN
    EXPAND_TAC "n" THEN REWRITE_TAC [MULT_AC] THEN
    ASM_SIMP_TAC [DIVIDES_PRIME_PRIME] THEN ASM_MESON_TAC [])

  let COPRIME_PAIR_DECOMP ← prove
   r"!n1 n2 m.
        coprime(n1,n2) /\ ~(m = 0)
        ==> ?m1 m2. coprime(m1,n1) /\ coprime(m2,n2) /\
                    coprime(m1,m2) /\ m1 * m2 = m"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"\p:num. p divides n2", ← q r"m:num"] PRIME_FACTOR_PARTITION) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"m1:num") THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"m2:num") THEN
    REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [COPRIME_PRIME_EQ] THEN
    MESON_TAC [])

  let EXP_MULT_EXISTS ← prove
   r"!m n p k. ~(m = 0) /\ m EXP k * n = p EXP k ==> ?q. n = q EXP k"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"k = 0") THEN
    ASM_REWRITE_TAC [EXP, MULT_CLAUSES] THEN STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"k:num", ← q r"m:num", ← q r"p:num"] DIVIDES_EXP2_REV) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [ASM_MESON_TAC [divides, MULT_SYM], ALL_TAC] THEN
    REWRITE_TAC [divides] THEN DISCH_THEN (CHOOSE_THEN SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o SYM) THEN
    ASM_REWRITE_TAC [MULT_EXP, ← GSYM MULT_ASSOC, EQ_MULT_LCANCEL, EXP_EQ_0] THEN
    MESON_TAC [])

  let COPRIME_POW ← prove
   r"!n a b c. coprime(a,b) /\ a * b = c EXP n
             ==> ?r s. a = r EXP n /\ b = s EXP n"
   (GEN_TAC THEN GEN_REWRITE_TAC BINDER_CONV [SWAP_FORALL_THM] THEN
    GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_SIMP_TAC [EXP, MULT_EQ_1] THEN MATCH_MP_TAC PRIME_FACTOR_INDUCT THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC [EXP_ZERO, MULT_EQ_0] THEN
      ASM_MESON_TAC [COPRIME_0, EXP_ZERO, COPRIME_0, EXP_ONE],
      SIMP_TAC [EXP_ONE, MULT_EQ_1] THEN MESON_TAC [EXP_ONE],
      REWRITE_TAC [MULT_EXP] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"p EXP n divides a \/ p EXP n divides b") MP_TAC THENL
       [ASM_MESON_TAC [PRIME_DIVPROD_POW, divides], ALL_TAC] THEN
      REWRITE_TAC [divides] THEN
      DISCH_THEN (DISJ_CASES_THEN (X_CHOOSE_THEN (← q r"d:num") SUBST_ALL_TAC)) THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [COPRIME_SYM]) THEN
      ASM_SIMP_TAC [COPRIME_RMUL, COPRIME_LMUL, COPRIME_LEXP, COPRIME_REXP] THEN
      STRIP_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o SPECL [← q r"b:num", ← q r"d:num"]),
        FIRST_X_ASSUM (MP_TAC o SPECL [← q r"d:num", ← q r"a:num"])] THEN
      ASM_REWRITE_TAC [] THEN
      (ANTS_TAC THENL
        [MATCH_MP_TAC (← NUM_RING (← q r"!p. ~(p = 0) /\ a * p = b * p ==> a = b")) THEN
         EXISTS_TAC (← q r"p EXP n") THEN ASM_SIMP_TAC [EXP_EQ_0, PRIME_IMP_NZ] THEN
         FIRST_X_ASSUM (MP_TAC o SYM) THEN CONV_TAC NUM_RING,
         STRIP_TAC THEN ASM_REWRITE_TAC [← GSYM MULT_EXP] THEN MESON_TAC []])])

  let PRIME_EXP ← prove
   r"!p n. prime(p EXP n) <=> prime(p) /\ (n = 1)"
   (GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC [EXP, PRIME_1, ARITH_EQ] THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN SPEC_TAC ((← q r"n:num"), (← q r"n:num")) THEN
    ASM_CASES_TAC (← q r"p = 0") THENL
     [ASM_REWRITE_TAC [PRIME_0, EXP, MULT_CLAUSES], ALL_TAC] THEN
    INDUCT_TAC THEN REWRITE_TAC [ARITH, EXP_1, EXP, MULT_CLAUSES] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"~(SUC(SUC n) = 1)")] THEN
    REWRITE_TAC [prime, DE_MORGAN_THM] THEN
    ASM_REWRITE_TAC [MULT_EQ_1, EXP_EQ_1] THEN ASM_CASES_TAC (← q r"p = 1") THEN
    ASM_REWRITE_TAC [NOT_IMP, DE_MORGAN_THM] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"p:num")) THEN ASM_REWRITE_TAC [NOT_IMP] THEN
    CONJ_TAC THENL [MESON_TAC [EXP, divides], ALL_TAC] THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"p < pn:num ==> ~(p = pn)")) THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM EXP_1] THEN
    REWRITE_TAC [← GSYM (← CONJUNCT2 EXP)] THEN
    ASM_REWRITE_TAC [LT_EXP, ARITH_EQ] THEN
    MAP_EVERY UNDISCH_TAC [← q r"~(p = 0)", ← q r"~(p = 1)"] THEN ARITH_TAC)

  let PRIME_POWER_MULT ← prove
   r"!k x y p. prime p /\ (x * y = p EXP k)
           ==> ?i j. (x = p EXP i) /\ (y = p EXP j)"
   (INDUCT_TAC THEN REWRITE_TAC [EXP, MULT_EQ_1] THENL
     [MESON_TAC [EXP], ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"p divides x \/ p divides y") MP_TAC THENL
     [ASM_MESON_TAC [PRIME_DIVPROD, divides, MULT_AC], ALL_TAC] THEN
    REWRITE_TAC [divides] THEN
    SUBGOAL_THEN (← q r"~(p = 0)") ASSUME_TAC THENL
     [ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN
    DISCH_THEN (DISJ_CASES_THEN (X_CHOOSE_THEN (← q r"d:num") SUBST_ALL_TAC)) THENL
     [UNDISCH_TAC (← q r"(p * d) * y = p * p EXP k"),
      UNDISCH_TAC (← q r"x * p * d = p * p EXP k") THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [MULT_SYM]] THEN
    REWRITE_TAC [← GSYM MULT_ASSOC] THEN
    ASM_REWRITE_TAC [EQ_MULT_LCANCEL] THEN DISCH_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o SPECL [← q r"d:num", ← q r"y:num", ← q r"p:num"]),
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"d:num", ← q r"x:num", ← q r"p:num"])] THEN
    ASM_REWRITE_TAC [] THEN MESON_TAC [EXP])

  let PRIME_POWER_EXP ← prove
   r"!n x p k. prime p /\ ~(n = 0) /\ (x EXP n = p EXP k) ==> ?i. x = p EXP i"
   (INDUCT_TAC THEN REWRITE_TAC [EXP] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [NOT_SUC] THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [EXP] THEN
    ASM_MESON_TAC [PRIME_POWER_MULT])

  let DIVIDES_PRIMEPOW ← prove
   r"!p. prime p ==> !d. d divides (p EXP k) <=> ?i. i <= k /\ d = p EXP i"
   (GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [divides, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"e:num") THEN
      DISCH_TAC THEN
      MP_TAC (← SPECL [← q r"k:num", ← q r"d:num", ← q r"e:num", ← q r"p:num"]
                     PRIME_POWER_MULT) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
      FIRST_X_ASSUM (MP_TAC o SYM) THEN REWRITE_TAC [← GSYM EXP_ADD] THEN
      REWRITE_TAC [← GSYM LE_ANTISYM, LE_EXP] THEN REWRITE_TAC [LE_ANTISYM] THEN
      POP_ASSUM MP_TAC THEN ASM_CASES_TAC (← q r"p = 0") THEN ASM_SIMP_TAC [PRIME_0] THEN
      ASM_CASES_TAC (← q r"p = 1") THEN ASM_REWRITE_TAC [PRIME_1, LE_ANTISYM] THEN
      MESON_TAC [LE_ADD],
      REWRITE_TAC [LE_EXISTS] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [EXP_ADD] THEN MESON_TAC [DIVIDES_RMUL, DIVIDES_REFL]])

  let PRIMEPOW_DIVIDES_PROD ← prove
   r"!p k m n.
        prime p /\ (p EXP k) divides (m * n)
        ==> ?i j. (p EXP i) divides m /\ (p EXP j) divides n /\ k = i + j"
   (REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP DIVISION_DECOMP) THEN
    REWRITE_TAC [← NUMBER_RULE
     (← q r"a = b * c <=> b divides a /\ c divides a /\ b * c = a")] THEN
    ASM_MESON_TAC [EXP_ADD, EQ_PRIMEPOW, DIVIDES_PRIMEPOW])

  let EUCLID_BOUND ← prove
   r"!n. ?p. prime(p) /\ n < p /\ p <= SUC(FACT n)"
   (GEN_TAC THEN MP_TAC (← SPEC (← q r"FACT n + 1") PRIME_FACTOR) THEN
    SIMP_TAC [← ARITH_RULE (← q r"0 < n ==> ~(n + 1 = 1)"), ADD1, FACT_LT] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
     [ASM_MESON_TAC [DIVIDES_ADD_REVR, DIVIDES_ONE, PRIME_1, NOT_LT, PRIME_0,
                     ← ARITH_RULE (← q r"(p = 0) \/ 1 <= p"), DIVIDES_FACT],
      ASM_MESON_TAC [DIVIDES_LE, ← ARITH_RULE (← q r"~(x + 1 = 0)")]])

  let EUCLID ← prove
   r"!n. ?p. prime(p) /\ p > n"
   (REWRITE_TAC [GT] THEN MESON_TAC [EUCLID_BOUND])

  let PRIMES_INFINITE ← prove
   r"INFINITE {p | prime p}"
   (REWRITE_TAC [INFINITE, num_FINITE, IN_ELIM_THM] THEN
    MESON_TAC [EUCLID, NOT_LE, GT])

  let FACTORIZATION_INDEX ← prove
   r"!n p. ~(n = 0) /\ 2 <= p
         ==> ?k. (p EXP k) divides n /\
                 !l. k < l ==> ~((p EXP l) divides n)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM NOT_LE, CONTRAPOS_THM] THEN
    REWRITE_TAC [← GSYM num_MAX] THEN CONJ_TAC THENL
     [EXISTS_TAC (← q r"0") THEN REWRITE_TAC [EXP, DIVIDES_1],
      EXISTS_TAC (← q r"n:num") THEN
      GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP DIVIDES_LE) THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] LE_TRANS) THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"2 EXP l") THEN
      SIMP_TAC [LT_POW2_REFL, LT_IMP_LE] THEN
      SPEC_TAC ((← q r"l:num"), (← q r"l:num")) THEN INDUCT_TAC THEN
      ASM_REWRITE_TAC [ARITH, ← CONJUNCT1 EXP, EXP_MONO_LE, NOT_SUC]])

  let PRIMEPOW_FACTOR ← prove
   r"!n. 2 <= n
       ==> ?p k m. prime p /\ 1 <= k /\ coprime(p,m) /\ n = p EXP k * m"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"n:num") PRIME_FACTOR) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"p:num") THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"n:num", ← q r"p:num"] FACTORIZATION_INDEX) THEN
    ASM_SIMP_TAC [PRIME_GE_2, ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0)")] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"k:num") THEN
    REWRITE_TAC [divides, LEFT_AND_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"m:num") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC (← q r"k + 1"))) THEN
    ASM_REWRITE_TAC [← ARITH_RULE (← q r"k < k + 1"), EXP_ADD, ← GSYM MULT_ASSOC] THEN
    ASM_SIMP_TAC [EQ_MULT_LCANCEL, EXP_EQ_0, PRIME_IMP_NZ] THEN
    REWRITE_TAC [EXP_1, ← GSYM divides] THEN UNDISCH_TAC (← q r"(p:num) divides n") THEN
    ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"k = 0") THEN ASM_SIMP_TAC [EXP, MULT_CLAUSES, LE_1] THEN
    ASM_MESON_TAC [PRIME_COPRIME_STRONG])

  let PRIMEPOW_DIVISORS_DIVIDES ← prove
   r"!m n. m divides n <=>
         !p k. prime p /\ p EXP k divides m ==> p EXP k divides n"
   (REWRITE_TAC [← TAUT (← q r"(p <=> q) <=> (p ==> q) /\ (q ==> p)")] THEN
    REWRITE_TAC [FORALL_AND_THM] THEN CONJ_TAC THENL
     [MESON_TAC [DIVIDES_TRANS], ALL_TAC] THEN
    MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q r"m:num") THEN
    DISCH_THEN (LABEL_TAC "*") THEN X_GEN_TAC (← q r"n:num") THEN
    ASM_CASES_TAC (← q r"m = 0") THEN ASM_REWRITE_TAC [DIVIDES_0] THENL
     [MP_TAC (← SPEC (← q r"n:num") EUCLID) THEN REWRITE_TAC [GT] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"p:num") STRIP_ASSUME_TAC) THEN
      DISCH_THEN (MP_TAC o SPECL [← q r"p:num", ← q r"1"]) THEN ASM_REWRITE_TAC [EXP_1] THEN
      DISCH_THEN (MP_TAC o MATCH_MP DIVIDES_LE) THEN
      ASM_SIMP_TAC [← GSYM NOT_LT, DIVIDES_REFL],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"m = 1") THEN ASM_REWRITE_TAC [DIVIDES_1] THEN
    MP_TAC (← SPEC (← q r"m:num") PRIMEPOW_FACTOR) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [← q r"p:num", ← q r"k:num", ← q r"r:num"] THEN STRIP_TAC THEN
    DISCH_THEN (fun th => tactic_of do pure (
      MP_TAC (← SPECL [← q r"p:num", ← q r"k:num"] th) THEN
      ASM_REWRITE_TAC [← NUMBER_RULE (← q r"a divides (a * b)")] THEN
      ASSUME_TAC th)) THEN
    REWRITE_TAC [divides, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"s:num") THEN DISCH_TAC THEN ASM_REWRITE_TAC [← GSYM divides] THEN
    MATCH_MP_TAC DIVIDES_MUL_L THEN REMOVE_THEN "*" (MP_TAC o SPEC (← q r"r:num")) THEN
    ASM_CASES_TAC (← q r"r = 0") THENL [ASM_MESON_TAC [MULT_CLAUSES], ALL_TAC] THEN
    ASM_REWRITE_TAC [← ARITH_RULE (← q r"q < p * q <=> 1 * q < p * q")] THEN
    ASM_SIMP_TAC [LT_MULT_RCANCEL, ← ARITH_RULE (← q r"1 < p <=> ~(p = 0 \/ p = 1)")] THEN
    REWRITE_TAC [EXP_EQ_0, EXP_EQ_1] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [PRIME_0, PRIME_1, LE_1], ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN MAP_EVERY X_GEN_TAC [← q r"q:num", ← q r"l:num"] THEN
    ASM_CASES_TAC (← q r"l = 0") THEN ASM_REWRITE_TAC [EXP, DIVIDES_1] THEN
    STRIP_TAC THEN ASM_CASES_TAC (← q r"q:num = p") THENL
     [UNDISCH_TAC (← q r"coprime(p,r)") THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC [coprime] THEN DISCH_THEN (MP_TAC o SPEC (← q r"p:num")) THEN
      ASM_SIMP_TAC [DIVIDES_REFL, PRIME_GE_2, ← ARITH_RULE
       (← q r"2 <= p ==> ~(p = 1)")] THEN
      MATCH_MP_TAC (← TAUT (← q r"p ==> ~p ==> q")) THEN
      TRANS_TAC DIVIDES_TRANS (← q r"p EXP l") THEN
      ASM_MESON_TAC [DIVIDES_REXP, DIVIDES_REFL],
      FIRST_X_ASSUM (MP_TAC o SPECL [← q r"q:num", ← q r"l:num"]) THEN
      ASM_SIMP_TAC [DIVIDES_LMUL] THEN DISCH_THEN (MATCH_MP_TAC o MATCH_MP
       (← REWRITE_RULE [IMP_CONJ] COPRIME_EXP_DIVPROD)) THEN
      MATCH_MP_TAC COPRIME_EXP THEN ASM_MESON_TAC [DISTINCT_PRIME_COPRIME]])

  let PRIMEPOW_DIVISORS_EQ ← prove
   r"!m n. m = n <=>
         !p k. prime p ==> (p EXP k divides m <=> p EXP k divides n)"
   (MESON_TAC [DIVIDES_ANTISYM, PRIMEPOW_DIVISORS_DIVIDES])
  return { PRIME_0, PRIME_1, PRIME_ALT, PRIME_2, PRIME_COPRIME_STRONG, 
           PRIME_COPRIME, PRIME_COPRIME_EQ, COPRIME_PRIME, PRIME_DIVPROD, 
           PRIME_DIVPROD_EQ, PRIME_INT_DIVPROD_EQ, PRIME_GE_2, PRIME_FACTOR, 
           PRIME, PRIME_PRIME_FACTOR, PRIME_FACTOR_LT, COPRIME_PRIME_EQ, 
           GCD_PRIME_CASES, GCD_2_CASES, COPRIME_PRIMEPOW, COPRIME_BEZOUT_STRONG, 
           COPRIME_BEZOUT_ALT, BEZOUT_PRIME, PRIME_DIVEXP, PRIME_DIVEXP_N, 
           PRIME_DIVEXP_EQ, COPRIME_SOS, PRIME_IMP_NZ, DISTINCT_PRIME_COPRIME, 
           PRIME_COPRIME_LT, DIVIDES_PRIME_PRIME, COPRIME_PRIME_PRIME, 
           DIVIDES_PRIME_EXP_LE, EQ_PRIME_EXP, PRIME_ODD, ODD_PRIME, 
           DIVIDES_FACT_PRIME, EQ_PRIMEPOW, COPRIME_2, DIVIDES_EXP_PLUS1, 
           DIVIDES_EXP_MINUS1, PRIME_IRREDUCIBLE, COPRIME_EXP_DIVPROD, 
           PRIME_COPRIME_CASES, PRIME_DIVPROD_POW_GEN, PRIME_DIVPROD_POW_GEN_EQ, 
           PRIME_DIVPROD_POW, PRIME_DIVPROD_POW_EQ, PRIME_FACTOR_INDUCT, 
           COMPLETE_FACTOR_INDUCT, PRIME_FACTOR_PARTITION, COPRIME_PAIR_DECOMP, 
           EXP_MULT_EXISTS, COPRIME_POW, PRIME_EXP, PRIME_POWER_MULT, 
           PRIME_POWER_EXP, DIVIDES_PRIMEPOW, PRIMEPOW_DIVIDES_PROD, 
           EUCLID_BOUND, EUCLID, PRIMES_INFINITE, FACTORIZATION_INDEX, 
           PRIMEPOW_FACTOR, PRIMEPOW_DIVISORS_DIVIDES, PRIMEPOW_DIVISORS_EQ }

/- ------------------------------------------------------------------------- -/
/- A binary form of the Chinese Remainder Theorem (prime.ml 1192-1220)       -/
/- ------------------------------------------------------------------------- -/

structure Chinese where
  CHINESE_REMAINDER : thm
  deriving Inhabited

@[nospecialize]
def setupChinese [HolBase] (D : PrimeDeps) (PGcd : Gcd) (PCoprime : Coprime) : ExceptT String IO Chinese := do
  let { MESON_TAC, .. } := D
  let { ADD_AC, CONJ_ASSOC, CONJ_SYM, DIVIDES_ONE, LEFT_ADD_DISTRIB, .. } := D.core1
  let { MULT_AC, MULT_CLAUSES, RIGHT_ADD_DISTRIB, .. } := D.core2
  let { DIVIDES_GCD, BEZOUT_ADD_STRONG, .. } := PGcd
  let { COPRIME_GCD, .. } := PCoprime

  let CHINESE_REMAINDER ← prove
   r"!a b u v. coprime(a,b) /\ ~(a = 0) /\ ~(b = 0)
             ==> ?x q1 q2. x = u + q1 * a /\ x = v + q2 * b"
   (← do
    let lemma ← prove
     r"(?d x y. (d = 1) /\ P x y d) <=> (?x y. P x y 1)"
     (MESON_TAC [])
    pure
     (REPEAT STRIP_TAC THEN
      MP_TAC (← SPECL [← q r"b:num", ← q r"a:num"] BEZOUT_ADD_STRONG) THEN
      MP_TAC (← SPECL [← q r"a:num", ← q r"b:num"] BEZOUT_ADD_STRONG) THEN
      ASM_REWRITE_TAC [CONJ_ASSOC] THEN
      SUBGOAL_THEN (← q r"!d. d divides a /\ d divides b <=> (d = 1)")
       (fun th => tactic_of do pure (REWRITE_TAC [th, ← ONCE_REWRITE_RULE [CONJ_SYM] th]))
      THENL
       [UNDISCH_TAC (← q r"coprime(a,b)") THEN
        SIMP_TAC [← GSYM DIVIDES_GCD, COPRIME_GCD, DIVIDES_ONE], ALL_TAC] THEN
      REWRITE_TAC [lemma] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"x1:num") (X_CHOOSE_TAC (← q r"y1:num"))) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"x2:num") (X_CHOOSE_TAC (← q r"y2:num"))) THEN
      EXISTS_TAC (← q r"v * a * x1 + u * b * x2:num") THEN
      EXISTS_TAC (← q r"v * x1 + u * y2:num") THEN
      EXISTS_TAC (← q r"v * y1 + u * x2:num") THEN CONJ_TAC THENL
       [SUBST1_TAC (← ASSUME (← q r"b * x2 = a * y2 + 1")),
        SUBST1_TAC (← ASSUME (← q r"a * x1 = b * y1 + 1"))] THEN
      REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES] THEN
      REWRITE_TAC [MULT_AC] THEN REWRITE_TAC [ADD_AC]))
  return { CHINESE_REMAINDER }

/- ------------------------------------------------------------------------- -/
/- Index of a (usually prime) divisor of a number (prime.ml 1222-1776)       -/
/- ------------------------------------------------------------------------- -/

structure Index where
  FINITE_EXP_LE : thm
  FINITE_INDICES : thm
  index_def : thm
  INDEX_0 : thm
  PRIMEPOW_DIVIDES_INDEX : thm
  LE_INDEX : thm
  EXP_INDEX_DIVIDES : thm
  INDEX_LT : thm
  INDEX_1 : thm
  INDEX_MUL : thm
  INDEX_EXP : thm
  INDEX_FACT : thm
  INDEX_FACT_ALT : thm
  INDEX_FACT_UNBOUNDED : thm
  PRIMEPOW_DIVIDES_FACT : thm
  INDEX_REFL : thm
  INDEX_EQ_0 : thm
  INDEX_ZERO : thm
  INDEX_POW : thm
  INDEX_PRIME : thm
  INDEX_TRIVIAL_BOUND : thm
  INDEX_DECOMPOSITION : thm
  INDEX_DECOMPOSITION_PRIME : thm
  INDEX_DECOMPOSITION_LE : thm
  INDEX_DECOMPOSITION_UNIQUE : thm
  INDEX_UNIQUE : thm
  INDEX_UNIQUE_EQ : thm
  INDEX_UNIQUE_ALT : thm
  INDEX_ADD_MIN : thm
  INDEX_SUB_MIN : thm
  INDEX_ADD : thm
  INDEX_MULT_BASE : thm
  INDEX_MULT_EXP : thm
  INDEX_MULT_ADD : thm
  INDEX_NSUM_LE : thm
  DIVIDES_INDEX : thm
  EQ_INDEX : thm
  COPRIME_INDEX : thm
  INDEX_GCD : thm
  FORALL_PRIME_INDEX : thm
  INDEX_FACT_PRIME_MULT : thm
  PRIME_FACTORIZATION_INDEX : thm
  PRIME_POWER_EXISTS : thm
  PRIME_POWER_EXISTS_ALT : thm
  PRIME_FACTORIZATION_ALT : thm
  PRIME_FACTORIZATION : thm
  deriving Inhabited

@[nospecialize]
def setupIndex [HolBase] (D : PrimeDeps) (PDivides : Divides) (PGcd : Gcd) (PCoprime : Coprime) (PPrimes : Primes) : ExceptT String IO Index := do
  let { new_definition, ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, 
        INDUCT_TAC, MESON, MESON_TAC, NUMBER_RULE, NUMBER_TAC, SET_RULE, SET_TAC, 
        EXPAND_CASES_CONV, .. } := D
  let { ADD1, ADD_CLAUSES, ADD_EQ_0, ADD_SYM, ARITH, ARITH_EQ, CARD_CLAUSES, 
        CARD_IMAGE_INJ, CARD_NUMSEG_1, COND_ID, COND_RAND, COND_RATOR, 
        CONJ_ASSOC, CONTRAPOS_THM, DE_MORGAN_THM, DISJ_SYM, DIVIDES_ANTISYM, 
        DIVIDES_LE, DIVIDES_LE_STRONG, DIVIDES_MOD, DIVIDES_ONE, DIV_EQ_0, 
        DIV_ZERO, EMPTY_GSPEC, EQ_ADD_RCANCEL, EQ_ADD_RCANCEL_0, EQ_IMP, 
        EQ_MULT_LCANCEL, EQ_SYM_EQ, EQ_TRANS, ETA_AX, EXP, EXP_1, EXP_ADD, 
        EXP_EQ_0, EXP_EQ_1, EXP_EXP, EXP_MONO_LE_IMP, EXP_ONE, EXP_ZERO, 
        EXTENSION, FACT, FACT_NZ, FINITE_INDUCT_STRONG, FINITE_NUMSEG, 
        FINITE_RESTRICT, FINITE_SUBSET, FUN_EQ_THM, IMP_CONJ, IMP_CONJ_ALT, 
        IN_ELIM_THM, IN_IMAGE, IN_NUMSEG, IN_UNIV, ITERATE_DELTA, ITERATE_EQ, 
        ITERATE_EQ_NEUTRAL, ITERATE_OP_GEN, ITERATE_SUPERSET, LE, 
        LEFT_IMP_EXISTS_THM, LE_0, LE_1, LE_ADD2, LE_ANTISYM, LE_MULT_LCANCEL, 
        LE_RDIV_EQ, LE_REFL, LE_TRANS, LT, LTE_TRANS, LT_EXISTS, LT_IMP_LE, 
        LT_POW2_REFL, LT_REFL, .. } := D.core1
  let { MONOIDAL_MUL, MONO_EXISTS, MULT_ASSOC, MULT_CLAUSES, MULT_EQ_0, MULT_SYM, 
        NEUTRAL_MUL, NOT_IMP, NOT_LE, NOT_LT, NOT_SUC, NSUM_ADD_NUMSEG, 
        NSUM_CLAUSES_NUMSEG, NSUM_CLOSED_NONEMPTY, NSUM_CONST, NSUM_EQ, 
        NSUM_EQ_NUMSEG, NSUM_IMAGE, NSUM_RESTRICT_SET, NSUM_SUPERSET, NSUM_SWAP, 
        RIGHT_AND_EXISTS_THM, RIGHT_FORALL_IMP_THM, SUBSET, SUBSET_REFL, SUB_ADD, 
        SUB_EQ_0, divides, nproduct, numseg, o_DEF, prime, support, .. } := D.core2
  let { DIVIDES_0, DIVIDES_ZERO, DIVIDES_1, DIVIDES_TRANS, DIVIDES_ADD, 
        DIVIDES_ADD_REVR, DIVIDES_ADD_REVL, DIVIDES_LMUL2_EQ, DIVIDES_MUL2, 
        DIVIDES_EXP2, DIVIDES_EXP_LE_IMP, DIVIDES_EXP_LE, 
        FINITE_SPECIAL_DIVISORS, .. } := PDivides
  let { DIVIDES_GCD, GCD_0, GCD_ZERO, .. } := PGcd
  let { COPRIME_0, .. } := PCoprime
  let { PRIME_0, PRIME_1, PRIME_ALT, PRIME_COPRIME_STRONG, PRIME_GE_2, 
        PRIME_FACTOR, COPRIME_PRIME_EQ, PRIME_IMP_NZ, DIVIDES_PRIME_PRIME, 
        DIVIDES_PRIME_EXP_LE, COMPLETE_FACTOR_INDUCT, PRIMEPOW_DIVIDES_PROD, 
        FACTORIZATION_INDEX, PRIMEPOW_DIVISORS_DIVIDES, PRIMEPOW_DIVISORS_EQ, .. } := PPrimes

  let FINITE_EXP_LE ← prove
   r"!P p n. 2 <= p ==> FINITE {j | P j /\ p EXP j <= n}"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"0..n") THEN
    SIMP_TAC [FINITE_NUMSEG, SUBSET, IN_ELIM_THM, LE_0, IN_NUMSEG] THEN
    X_GEN_TAC (← q r"i:num") THEN STRIP_TAC THEN TRANS_TAC LE_TRANS (← q r"p EXP i") THEN
    ASM_REWRITE_TAC [] THEN TRANS_TAC LE_TRANS (← q r"2 EXP i") THEN
    ASM_SIMP_TAC [EXP_MONO_LE_IMP, LT_POW2_REFL, LT_IMP_LE])

  let FINITE_INDICES ← prove
   r"!P p n. 2 <= p /\ ~(n = 0) ==> FINITE {j | P j /\ p EXP j divides n}"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC (← q r"{j | P j /\ p EXP j <= n}") THEN
    ASM_SIMP_TAC [FINITE_EXP_LE] THEN REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
    ASM_MESON_TAC [DIVIDES_LE])

  let index_def ← new_definition
   r"index p n = if p <= 1 \/ n = 0 then 0
              else CARD {j | 1 <= j /\ p EXP j divides n}"

  let INDEX_0 ← prove
   r"!p. index p 0 = 0"
   (REWRITE_TAC [index_def])

  let PRIMEPOW_DIVIDES_INDEX ← prove
   r"!n p k. p EXP k divides n <=> n = 0 \/ p = 1 \/ k <= index p n"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [INDEX_0, DIVIDES_0, EXP_EQ_0] THEN
    ASM_CASES_TAC (← q r"p = 0") THEN
    ASM_REWRITE_TAC [EXP_ZERO, COND_RAND, COND_RATOR] THEN
    ASM_SIMP_TAC [LE_0, DIVIDES_1, ARITH, index_def, DIVIDES_ZERO] THEN
    SIMP_TAC [← CONJUNCT1 LE, COND_ID] THEN
    ASM_CASES_TAC (← q r"p = 1") THEN ASM_REWRITE_TAC [EXP_ONE, DIVIDES_1] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC, ALL_TAC]  THEN
    SUBGOAL_THEN (← q r"2 <= p") ASSUME_TAC THENL  [ASM_ARITH_TAC, ALL_TAC]  THEN
    MP_TAC (← ISPECL [← q r"n:num", ← q r"p:num"] FACTORIZATION_INDEX) THEN
    ASM_SIMP_TAC [LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"a:num") THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q r"!k. p EXP k divides n <=> k <= a") ASSUME_TAC THENL
     [GEN_TAC THEN EQ_TAC THENL [ASM_MESON_TAC [NOT_LE], ALL_TAC] THEN
      DISCH_TAC THEN TRANS_TAC DIVIDES_TRANS (← q r"p EXP a") THEN
      ASM_SIMP_TAC [DIVIDES_EXP_LE],
      ASM_REWRITE_TAC [← GSYM numseg, CARD_NUMSEG_1]])

  let LE_INDEX ← prove
   r"!n p k. k <= index p n <=> (n = 0 \/ p = 1 ==> k = 0) /\ p EXP k divides n"
   (REPEAT GEN_TAC THEN REWRITE_TAC [PRIMEPOW_DIVIDES_INDEX] THEN
    ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [INDEX_0, ← CONJUNCT1 LE] THEN
    ASM_CASES_TAC (← q r"p = 1") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [index_def, ARITH, ← CONJUNCT1 LE])

  let EXP_INDEX_DIVIDES ← prove
   r"!p n. p EXP (index p n) divides n"
   (MESON_TAC [LE_INDEX, LE_REFL])

  let INDEX_LT ← prove
   r"!n p k. (~(n = 0) \/ ~(k = 0)) /\ n < p EXP k ==> index p n < k"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [← GSYM DE_MORGAN_THM, ← GSYM NOT_LE, LE_INDEX] THEN
    REWRITE_TAC [CONTRAPOS_THM] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (MP_TAC o MATCH_MP DIVIDES_LE_STRONG)) THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_SIMP_TAC [])

  let INDEX_1 ← prove
   r"!p. index p 1 = 0"
   (GEN_TAC THEN REWRITE_TAC [index_def, ARITH] THEN COND_CASES_TAC THEN
    REWRITE_TAC [DIVIDES_ONE, EXP_EQ_1] THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"~(p <= 1) ==> ~(p = 1)"),
                  ← ARITH_RULE (← q r"~(1 <= j /\ j = 0)"),
                  EMPTY_GSPEC, CARD_CLAUSES])

  let INDEX_MUL ← prove
   r"!m n. prime p /\ ~(m = 0) /\ ~(n = 0)
         ==> index p (m * n) = index p m + index p n"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM LE_ANTISYM] THEN
    SUBGOAL_THEN (← q r"~(p = 1)") ASSUME_TAC THENL
     [ASM_MESON_TAC [PRIME_1], ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC (← MESON [LE_REFL]
       (← q r"(!k:num. k <= m ==> k <= n) ==> m <= n")) THEN
      MP_TAC (← SPEC (← q r"p:num") PRIMEPOW_DIVIDES_PROD) THEN
      ASM_REWRITE_TAC [LE_INDEX, MULT_EQ_0] THEN ASM_MESON_TAC [LE_ADD2, LE_INDEX],
      ASM_REWRITE_TAC [LE_INDEX, MULT_EQ_0, EXP_ADD] THEN
      MATCH_MP_TAC DIVIDES_MUL2 THEN ASM_MESON_TAC [LE_INDEX, LE_REFL]])

  let INDEX_EXP ← prove
   r"!p n k. prime p ==> index p (n EXP k) = k * index p n"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [EXP_ZERO, INDEX_0, COND_RAND, COND_RATOR, INDEX_1,
                     MULT_CLAUSES, COND_ID] THEN
    INDUCT_TAC THEN
    ASM_SIMP_TAC [INDEX_MUL, EXP_EQ_0, EXP, INDEX_1, MULT_CLAUSES] THEN
    ARITH_TAC)

  let INDEX_FACT ← prove
   r"!p n. prime p ==> index p (FACT n) = nsum(1..n) (\m. index p m)"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC [FACT, NSUM_CLAUSES_NUMSEG, INDEX_1, ARITH] THEN
    ASM_SIMP_TAC [INDEX_MUL, NOT_SUC, FACT_NZ] THEN ARITH_TAC)

  let INDEX_FACT_ALT ← prove
   r"!p n. prime p
         ==> index p (FACT n) =
             nsum {j | 1 <= j /\ p EXP j <= n} (\j. n DIV (p EXP j))"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [INDEX_FACT] THEN
    SUBGOAL_THEN (← q r"~(p = 0) /\ ~(p = 1) /\ 2 <= p /\ ~(p <= 1)")
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM (MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC, ALL_TAC] THEN
    ASM_SIMP_TAC [index_def, LE_1] THEN
    TRANS_TAC EQ_TRANS
     (← q r"nsum(1..n) (\m. nsum {j | 1 <= j /\ p EXP j <= n}
                         (\j. if p EXP j divides m then 1 else 0))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_EQ_NUMSEG THEN X_GEN_TAC (← q r"m:num") THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [← GSYM NSUM_RESTRICT_SET, IN_ELIM_THM] THEN
      ASM_SIMP_TAC [NSUM_CONST, FINITE_INDICES, LE_1, MULT_CLAUSES] THEN
      AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
      ASM_MESON_TAC [DIVIDES_LE, LE_1, LE_TRANS],
      W (MP_TAC o PART_MATCH (lhs o rand) NSUM_SWAP o lhand o snd) THEN
      ASM_SIMP_TAC [FINITE_NUMSEG, FINITE_EXP_LE] THEN DISCH_THEN (K ALL_TAC) THEN
      MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC (← q r"j:num") THEN
      REWRITE_TAC [IN_ELIM_THM, ← GSYM NSUM_RESTRICT_SET] THEN STRIP_TAC THEN
      ASM_SIMP_TAC [NSUM_CONST, FINITE_NUMSEG, FINITE_RESTRICT, MULT_CLAUSES] THEN
      SUBGOAL_THEN (← q r"{m | m IN 1..n /\ p EXP j divides m} =
                    IMAGE (\q. p EXP j * q) (1..(n DIV p EXP j))")
       (fun th => ASM_SIMP_TAC [CARD_IMAGE_INJ, FINITE_NUMSEG, EQ_MULT_LCANCEL,
                                th, EXP_EQ_0, PRIME_IMP_NZ, CARD_NUMSEG_1]) THEN
      REWRITE_TAC [EXTENSION, IN_IMAGE, IN_NUMSEG, IN_ELIM_THM, divides] THEN
      X_GEN_TAC (← q r"d:num") THEN REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
      AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q r"q:num") THEN
      ASM_CASES_TAC (← q r"d = p EXP j * q") THEN ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [LE_RDIV_EQ, EXP_EQ_0, PRIME_IMP_NZ, MULT_EQ_0,
                    ← ARITH_RULE (← q r"1 <= x <=> ~(x = 0)")]])

  let INDEX_FACT_UNBOUNDED ← prove
   r"!p n. prime p
         ==> index p (FACT n) = nsum {j | 1 <= j} (\j. n DIV (p EXP j))"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [INDEX_FACT_ALT] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN
    ASM_SIMP_TAC [SUBSET, IN_ELIM_THM, IMP_CONJ, DIV_EQ_0, EXP_EQ_0,
                  PRIME_IMP_NZ, NOT_LE])

  let PRIMEPOW_DIVIDES_FACT ← prove
   r"!p n k. prime p
           ==> (p EXP k divides FACT n <=>
                k <= nsum {j | 1 <= j /\ p EXP j <= n} (\j. n DIV (p EXP j)))"
   (SIMP_TAC [PRIMEPOW_DIVIDES_INDEX, INDEX_FACT_ALT, FACT_NZ] THEN
    MESON_TAC [PRIME_1])

  let INDEX_REFL ← prove
   r"!n. index n n = if n <= 1 then 0 else 1"
   (GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [index_def] THEN
    ASM_CASES_TAC (← q r"n = 0") THENL [ASM_ARITH_TAC, ASM_REWRITE_TAC []] THEN
    ONCE_REWRITE_TAC [← MESON [EXP_1] (← q r"a divides b <=> a divides b EXP 1")] THEN
    ASM_CASES_TAC (← q r"2 <= n") THENL [ALL_TAC, ASM_ARITH_TAC] THEN
    ASM_SIMP_TAC [DIVIDES_EXP_LE, ← GSYM numseg, CARD_NUMSEG_1])

  let INDEX_EQ_0 ← prove
   r"!p n. index p n = 0 <=> n = 0 \/ p = 1 \/ ~(p divides n)"
   (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [← ARITH_RULE (← q r"n = 0 <=> ~(1 <= n)")] THEN
    REWRITE_TAC [LE_INDEX, EXP_1, ARITH] THEN MESON_TAC [])

  let INDEX_ZERO ← prove
   r"!p n. ~(p divides n) ==> index p n = 0"
   (SIMP_TAC [INDEX_EQ_0])

  let INDEX_POW ← prove
   r"!p n k. index (p EXP k) n = index p n DIV k"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"k = 0") THENL
     [ASM_REWRITE_TAC [DIV_ZERO, INDEX_EQ_0, EXP], ALL_TAC] THEN
    GEN_REWRITE_TAC I [← MESON [LE_TRANS, LE_ANTISYM]
     (← q r"(m:num = n) <=> !d. d <= m <=> d <= n")] THEN
    X_GEN_TAC (← q r"d:num") THEN ASM_SIMP_TAC [LE_INDEX, LE_RDIV_EQ, EXP_EXP] THEN
    ASM_REWRITE_TAC [MULT_EQ_0, EXP_EQ_1])

  let INDEX_PRIME ← prove
   r"!p a. prime p ==> index a p = if p = a then 1 else 0"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [INDEX_REFL, INDEX_EQ_0] THEN
    ASM_MESON_TAC [prime, PRIME_0, PRIME_1,
                   ← ARITH_RULE (← q r"p <= 1 <=> p = 0 \/ p = 1")])

  let INDEX_TRIVIAL_BOUND ← prove
   r"!n p. index p n <= n"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"n:num", ← q r"p:num", ← q r"n:num"] PRIMEPOW_DIVIDES_INDEX) THEN
    REWRITE_TAC [index_def] THEN COND_CASES_TAC THEN REWRITE_TAC [LE_0] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [DE_MORGAN_THM, NOT_LE]) THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"1 < p ==> ~(p = 1)")] THEN
    DISCH_THEN (ASSUME_TAC o SYM) THEN
    MATCH_MP_TAC (← ARITH_RULE (← q r"~(m:num <= n) ==> n <= m")) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_REWRITE_TAC [NOT_LE] THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC (← q r"2 EXP n") THEN
    REWRITE_TAC [LT_POW2_REFL] THEN
    MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC)

  let INDEX_DECOMPOSITION ← prove
   r"!n p. ?m. p EXP (index p n) * m = n /\ (n = 0 \/ p = 1 \/ ~(p divides m))"
   (REPEAT GEN_TAC THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"p:num", ← q r"index p n"] LE_INDEX) THEN
    REWRITE_TAC [LE_REFL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"m:num") THEN
    DISCH_THEN (ASSUME_TAC o SYM) THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"p:num", ← q r"index p n + 1"] LE_INDEX) THEN
    REWRITE_TAC [ADD_EQ_0, ARITH_EQ, ← ARITH_RULE (← q r"~(n + 1 <= n)")] THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"p = 1") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [EXP_ADD, EXP_1, CONTRAPOS_THM] THEN
    FIRST_X_ASSUM (MP_TAC o SYM) THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    NUMBER_TAC)

  let INDEX_DECOMPOSITION_PRIME ← prove
   r"!n p. prime p ==> ?m. p EXP (index p n) * m = n /\ (n = 0 \/ coprime(p,m))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"p:num"] INDEX_DECOMPOSITION) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"m:num") THEN
    ASM_CASES_TAC (← q r"p = 1") THENL [ASM_MESON_TAC [PRIME_1], ASM_REWRITE_TAC []] THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [PRIME_COPRIME_STRONG])

  let INDEX_DECOMPOSITION_LE ← prove
   r"!p e1 m1 e2 m2.
    p EXP e1 * m1 = p EXP e2 * m2 /\ ~(p = 0) /\ ~(p divides m2) ==> e1 <= e2"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← TAUT
     (← q r"p /\ ~q /\ ~r ==> s <=> ~q ==> ~s ==> p ==> r")] THEN
    DISCH_TAC THEN REWRITE_TAC [NOT_LE, LT_EXISTS, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"d:num") THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC [EXP_ADD, ← GSYM MULT_ASSOC, EQ_MULT_LCANCEL, EXP_EQ_0] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [EXP] THEN
    CONV_TAC NUMBER_RULE)

  let INDEX_DECOMPOSITION_UNIQUE ← prove
   r"!p e1 m1 e2 m2.
        p EXP e1 * m1 = p EXP e2 * m2 /\
        ~(p = 0) /\ ~(p divides m1) /\ ~(p divides m2)
        ==> e1 = e2"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM LE_ANTISYM] THEN
    ASM_MESON_TAC [INDEX_DECOMPOSITION_LE])

  let INDEX_UNIQUE ← prove
   r"!p m n e.
        p EXP e * m = n /\ (p = 0 ==> e = 0) /\ ~(p divides m)
        ==> index p n = e"
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC [← ARITH_RULE (← q r"i = e <=> e <= i /\ ~(e + 1 <= i)")] THEN
    REWRITE_TAC [LE_INDEX, ← ARITH_RULE (← q r"~(e + 1 = 0)")] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN POP_ASSUM MP_TAC THEN
    UNDISCH_TAC (← q r"p = 0 ==> e = 0") THEN
    ASM_CASES_TAC (← q r"p = 1") THEN ASM_REWRITE_TAC [DIVIDES_1] THEN
    ASM_CASES_TAC (← q r"m = 0") THEN ASM_REWRITE_TAC [DIVIDES_0, MULT_EQ_0] THEN
    ASM_CASES_TAC (← q r"p = 0") THEN ASM_REWRITE_TAC [EXP_EQ_0, DIVIDES_ZERO] THEN
    DISCH_TAC THEN
    ASM_REWRITE_TAC [EXP_ZERO, MULT_CLAUSES, ARITH, DIVIDES_1, DIVIDES_ZERO] THEN
    REWRITE_TAC [EXP_ADD, ← NUMBER_RULE (← q r"p divides (p * q:num)")] THEN
    ASM_SIMP_TAC [DIVIDES_LMUL2_EQ, EXP_EQ_0, EXP_1])

  let INDEX_UNIQUE_EQ ← prove
   r"!n p k. index p n = k <=>
           if p = 1 \/ n = 0 then k = 0
           else !j. p EXP j divides n <=> j <= k"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THENL
     [REWRITE_TAC [index_def] THEN ASM_MESON_TAC [LE_REFL],
      RULE_ASSUM_TAC (REWRITE_RULE [DE_MORGAN_THM])] THEN
    ASM_REWRITE_TAC [PRIMEPOW_DIVIDES_INDEX] THEN
    MESON_TAC [LE_ANTISYM])

  let INDEX_UNIQUE_ALT ← prove
   r"!n p k. index p n = k <=>
           if p = 1 \/ n = 0 then k = 0
           else p EXP k divides n /\ ~(p EXP (k + 1) divides n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [INDEX_UNIQUE_EQ] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN EQ_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THENL [ARITH_TAC, ALL_TAC] THEN
    X_GEN_TAC (← q r"j:num") THEN EQ_TAC THEN DISCH_TAC THENL
     [ALL_TAC, ASM_MESON_TAC [DIVIDES_EXP_LE_IMP, DIVIDES_TRANS]] THEN
    UNDISCH_TAC (← q r"~(p EXP (k + 1) divides n)") THEN
    REWRITE_TAC [← GSYM NOT_LT, CONTRAPOS_THM] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"k < j <=> k + 1 <= j")] THEN
    ASM_MESON_TAC [DIVIDES_EXP_LE_IMP, DIVIDES_TRANS])

  let INDEX_ADD_MIN ← prove
   r"!p m n. MIN (index p m) (index p n) <= index p (m + n)"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"p = 1") THENL
     [ASM_SIMP_TAC [index_def] THEN ARITH_TAC, REWRITE_TAC [LE_INDEX]] THEN
    ASM_SIMP_TAC [ADD_EQ_0, INDEX_EQ_0, ← ARITH_RULE
     (← q r"MIN a b = 0 <=> a = 0 \/ b = 0")] THEN
    MATCH_MP_TAC DIVIDES_ADD THEN CONJ_TAC THEN MATCH_MP_TAC DIVIDES_TRANS THENL
     [EXISTS_TAC (← q r"p EXP (index p m)"), EXISTS_TAC (← q r"p EXP (index p n)")] THEN
    REWRITE_TAC [EXP_INDEX_DIVIDES] THEN
    MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ARITH_TAC)

  let INDEX_SUB_MIN ← prove
   r"!p m n. n < m ==> MIN (index p m) (index p n) <= index p (m - n)"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"p = 1") THENL
     [ASM_SIMP_TAC [index_def] THEN ARITH_TAC, REWRITE_TAC [LE_INDEX]] THEN
    ASM_SIMP_TAC [SUB_EQ_0, ← GSYM NOT_LT] THEN
    MATCH_MP_TAC DIVIDES_ADD_REVL THEN EXISTS_TAC (← q r"n:num") THEN
    ASM_SIMP_TAC [SUB_ADD, LT_IMP_LE] THEN
    CONJ_TAC THEN MATCH_MP_TAC DIVIDES_TRANS THENL
     [EXISTS_TAC (← q r"p EXP (index p n)"), EXISTS_TAC (← q r"p EXP (index p m)")] THEN
    REWRITE_TAC [EXP_INDEX_DIVIDES] THEN
    MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ARITH_TAC)

  let INDEX_ADD ← prove
   r"!p n m.
        ~(n = 0) /\ (~(m = 0) ==> index p n < index p m)
        ==> index p (m + n) = index p n"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"m = 0") THEN ASM_REWRITE_TAC [ADD_CLAUSES] THEN
    ASM_CASES_TAC (← q r"p = 1") THENL
     [ASM_MESON_TAC [INDEX_EQ_0, LT_REFL], REPEAT STRIP_TAC] THEN
    ASM_REWRITE_TAC [INDEX_UNIQUE_ALT, ADD_EQ_0] THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIVIDES_ADD,
      MATCH_MP_TAC (← MESON [DIVIDES_ADD_REVR]
       (← q r"(p:num) divides m /\ ~(p divides n) ==> ~(p divides m + n)"))] THEN
    ASM_REWRITE_TAC [PRIMEPOW_DIVIDES_INDEX] THEN ASM_ARITH_TAC)

  let INDEX_MULT_BASE ← prove
   r"(!p n. index p (p * n) = if p <= 1 \/ n = 0 then 0 else index p n + 1) /\
   (!p n. index p (n * p) = if p <= 1 \/ n = 0 then 0 else index p n + 1)"
   (MATCH_MP_TAC (← TAUT (← q r"(p ==> q) /\ p ==> p /\ q")) THEN CONJ_TAC THENL
     [MESON_TAC [MULT_SYM], REPEAT GEN_TAC] THEN
    COND_CASES_TAC THENL
     [ASM_REWRITE_TAC [index_def] THEN ASM_MESON_TAC [MULT_EQ_0],
      RULE_ASSUM_TAC (REWRITE_RULE [DE_MORGAN_THM]) THEN POP_ASSUM MP_TAC] THEN
    ASM_CASES_TAC (← q r"p = 0") THEN ASM_REWRITE_TAC [LE_0] THEN STRIP_TAC THEN
    MATCH_MP_TAC INDEX_UNIQUE THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [← ONCE_REWRITE_RULE [ADD_SYM] EXP_ADD] THEN
    ASM_REWRITE_TAC [EXP_1, ← GSYM MULT_ASSOC] THEN
    ASM_MESON_TAC [INDEX_DECOMPOSITION, LE_REFL])

  let INDEX_MULT_EXP ← prove
   r"(!p n k. index p (p EXP k * n) =
            if p <= 1 \/ n = 0 then 0 else k + index p n) /\
   (!p n k. index p (n * p EXP k) =
            if n = 0 \/ p <= 1 then 0 else index p n + k)"
   (MATCH_MP_TAC (← TAUT (← q r"(p ==> q) /\ p ==> p /\ q")) THEN CONJ_TAC THENL
     [REWRITE_TAC [MULT_SYM, ADD_SYM, DISJ_SYM], GEN_TAC THEN GEN_TAC] THEN
    ASM_CASES_TAC (← q r"p = 0") THENL [ASM_REWRITE_TAC [index_def, ARITH], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"p <= 1") THENL [ASM_REWRITE_TAC [index_def], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"n = 0") THENL
     [ASM_REWRITE_TAC [index_def, MULT_CLAUSES], ASM_REWRITE_TAC []] THEN
    INDUCT_TAC THEN REWRITE_TAC [EXP, MULT_CLAUSES, ← GSYM MULT_ASSOC] THEN
    ASM_REWRITE_TAC [INDEX_MULT_BASE, ADD1, ADD_CLAUSES] THEN
    ASM_REWRITE_TAC [MULT_EQ_0, EXP_EQ_0] THEN ARITH_TAC)

  let INDEX_MULT_ADD ← prove
   r"(!p m n k.
        ~(n = 0) /\ index p n < k ==> index p (p EXP k * m + n) = index p n) /\
   (!p m n k.
        ~(n = 0) /\ index p n < k ==> index p (m * p EXP k + n) = index p n) /\
   (!p m n k.
        ~(n = 0) /\ index p n < k ==> index p (n + m * p EXP k) = index p n) /\
   (!p m n k.
        ~(n = 0) /\ index p n < k ==> index p (n + p EXP k * m) = index p n)"
   (MATCH_MP_TAC (← TAUT (← q r"(p ==> q) /\ p ==> p /\ q")) THEN CONJ_TAC THENL
     [REWRITE_TAC [MULT_SYM, ADD_SYM, DISJ_SYM], REPEAT GEN_TAC] THEN
    ASM_CASES_TAC (← q r"p <= 1") THENL [ASM_REWRITE_TAC [index_def], ALL_TAC] THEN
    STRIP_TAC THEN MATCH_MP_TAC INDEX_ADD THEN
    ASM_SIMP_TAC [MULT_EQ_0, EXP_EQ_0, DE_MORGAN_THM] THEN
    REWRITE_TAC [INDEX_MULT_EXP] THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC)

  let INDEX_NSUM_LE ← prove
   r"!(f:A->num) p n k.
         FINITE k /\ ~(k = {}) /\ (!a. a IN k ==> n <= index p (f a))
         ==> n <= index p (nsum k f)"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPEC (← q r"\m. n <= index p m")
     NSUM_CLOSED_NONEMPTY) THEN
    REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THEN
    W (MP_TAC o PART_MATCH rand INDEX_ADD_MIN o rand o snd) THEN ASM_ARITH_TAC)

  let DIVIDES_INDEX ← prove
   r"!m n. m divides n <=>
         n = 0 \/ ~(m = 0) /\ !p. prime p ==> index p m <= index p n"
   (← do
    -- OCaml evaluates the operands of a THEN chain right to left, so the
    -- second MESON runs first; its progress messages come first.
    let prime_ne_1 ← MESON [PRIME_1] (← q r"prime p ==> ~(p = 1)")
    let le_all ← MESON [LE_REFL, LE_ANTISYM, LE_TRANS]
     (← q r"m <= n <=> !k:num. k <= m ==> k <= n")
    pure
     (REPEAT GEN_TAC THEN
      ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [DIVIDES_0] THEN
      ASM_CASES_TAC (← q r"m = 0") THEN ASM_REWRITE_TAC [DIVIDES_ZERO] THEN
      ONCE_REWRITE_TAC [le_all] THEN
      REWRITE_TAC [LE_INDEX] THEN
      ASM_SIMP_TAC [prime_ne_1] THEN
      GEN_REWRITE_TAC LAND_CONV [PRIMEPOW_DIVISORS_DIVIDES] THEN MESON_TAC []))

  let EQ_INDEX ← prove
   r"!m n. m = n <=> (m = 0 <=> n = 0) /\ !p. prime p ==> index p m = index p n"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM DIVIDES_ANTISYM] THEN
    REWRITE_TAC [DIVIDES_INDEX] THEN
    MAP_EVERY ASM_CASES_TAC [← q r"m = 0", ← q r"n = 0"] THEN
    ASM_REWRITE_TAC [] THEN MESON_TAC [LE_ANTISYM])

  let COPRIME_INDEX ← prove
   r"!m n. coprime(m,n) <=>
         (m = 0 ==> n = 1) /\ (n = 0 ==> m = 1) /\
         !p. prime p ==> index p m = 0 \/ index p n = 0"
   (REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC [← q r"m = 0", ← q r"n = 0"] THEN
    ASM_SIMP_TAC [INDEX_EQ_0, COPRIME_0,
                  ← MESON [PRIME_1] (← q r"prime p ==> ~(p = 1)")] THEN
    MESON_TAC [COPRIME_PRIME_EQ])

  let INDEX_GCD ← prove
   r"!m n p.
        prime p
        ==> index p (gcd(m,n)) =
            if m = 0 then index p n
            else if n = 0 then index p m
            else MIN (index p m) (index p n)"
   (REPEAT STRIP_TAC THEN
    MAP_EVERY ASM_CASES_TAC [← q r"m = 0", ← q r"n = 0"] THEN
    ASM_SIMP_TAC [GCD_0, INDEX_0] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"MIN 0 n = 0 /\ MIN m 0 = 0")] THEN
    MP_TAC (← GEN (← q r"k:num") (← SPECL [← q r"m:num", ← q r"n:num", ← q r"p EXP k"]
                                       DIVIDES_GCD)) THEN
    ASM_REWRITE_TAC [PRIMEPOW_DIVIDES_INDEX] THEN
    ASM_SIMP_TAC [← MESON [PRIME_1] (← q r"prime p ==> ~(p = 1)")] THEN
    ASM_REWRITE_TAC [GCD_ZERO] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"k <= m /\ k <= n <=> k <= MIN m n")] THEN
    MESON_TAC [LE_REFL, LE_ANTISYM, LE_TRANS])

  let FORALL_PRIME_INDEX ← prove
   r"(!p. prime p ==> !P. ((!x. P(index p x)) <=> !k. P k)) /\
   (!p. prime p ==> !P. ((!x. ~(x = 0) ==> P(index p x)) <=> !k. P k))"
   (REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"k:num") THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"p EXP k")) THEN
    ASM_SIMP_TAC [INDEX_EXP, INDEX_REFL, EXP_EQ_0, PRIME_IMP_NZ] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC)

  let INDEX_FACT_PRIME_MULT ← prove
   r"!p n. prime p ==> index p (FACT(p * n)) = n + index p (FACT n)"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, FACT, INDEX_1, ADD_CLAUSES] THEN
    ASM_SIMP_TAC [INDEX_FACT, MULT_EQ_0, PRIME_IMP_NZ, INDEX_MUL] THEN
    TRANS_TAC EQ_TRANS (← q r"nsum (IMAGE (\i. p * i) (1..n)) (\m. index p m)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_SUPERSET THEN MATCH_MP_TAC (← SET_RULE
       (← q r"(!x. f x IN t <=> x IN s) /\
        (!y. ~P y ==> y IN IMAGE f UNIV)
        ==> IMAGE f s SUBSET t /\ !y. y IN t /\ ~(y IN IMAGE f s) ==> P y")) THEN
      REWRITE_TAC [IN_NUMSEG, LE_MULT_LCANCEL, ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)"),
                   MULT_EQ_0, IN_IMAGE, IN_UNIV, INDEX_EQ_0, divides] THEN
      ASM_MESON_TAC [PRIME_0],
      ASM_SIMP_TAC [NSUM_IMAGE, EQ_MULT_LCANCEL, PRIME_IMP_NZ, o_DEF] THEN
      ASM_SIMP_TAC [INDEX_MUL, LE_1, PRIME_IMP_NZ, NSUM_ADD_NUMSEG] THEN
      REWRITE_TAC [ETA_AX, EQ_ADD_RCANCEL] THEN
      SIMP_TAC [NSUM_CONST, FINITE_NUMSEG, CARD_NUMSEG_1] THEN
      REWRITE_TAC [INDEX_REFL] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN
      FIRST_X_ASSUM (MP_TAC o MATCH_MP PRIME_GE_2) THEN ASM_ARITH_TAC])

  let PRIME_FACTORIZATION_INDEX ← prove
   r"!k. FINITE {p | prime p /\ ~(k p = 0)}
       ==> ?n. ~(n = 0) /\ !p. prime p ==> index p n = k p"
   (SUBGOAL_THEN
     (← q r"!s. FINITE s
         ==> !k. {p | prime p /\ ~(k p = 0)} SUBSET s
                 ==> ?n. ~(n = 0) /\ !p. prime p ==> index p n = k p")
    MP_TAC THENL [ALL_TAC, MESON_TAC [SUBSET_REFL]] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
     [REWRITE_TAC [← SET_RULE
       (← q r"{p | prime p /\ ~Z p} SUBSET {} <=> !p. prime p ==> Z p")] THEN
      MESON_TAC [INDEX_1, ← ARITH_RULE (← q r"~(1 = 0)")],
      MAP_EVERY X_GEN_TAC [← q r"p:num", ← q r"s:num->bool"] THEN STRIP_TAC THEN
      X_GEN_TAC (← q r"k:num->num") THEN STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC
       (← q r"\i. if i = p then 0 else (k:num->num) i")) THEN
      REWRITE_TAC [] THEN ANTS_TAC THENL [ASM SET_TAC [], ALL_TAC] THEN
      ASM_CASES_TAC (← q r"prime p") THENL [ALL_TAC, ASM_MESON_TAC []] THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") STRIP_ASSUME_TAC) THEN
      EXISTS_TAC (← q r"p EXP k p * n") THEN
      ASM_SIMP_TAC [INDEX_MUL, MULT_EQ_0, EXP_EQ_0, INDEX_EXP] THEN
      X_GEN_TAC (← q r"q:num") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"q:num")) THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC [INDEX_REFL] THENL
       [COND_CASES_TAC THEN REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES] THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP PRIME_GE_2) THEN ASM_ARITH_TAC,
        DISCH_TAC THEN REWRITE_TAC [EQ_ADD_RCANCEL_0, MULT_EQ_0] THEN
        ASM_SIMP_TAC [INDEX_EQ_0, DIVIDES_PRIME_PRIME]]])

  let PRIME_POWER_EXISTS ← prove
   r"!n q. prime q
         ==> ((?i. n = q EXP i) <=>
              (!p. prime p /\ p divides n ==> p = q))"
   (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [PRIMEPOW_DIVISORS_EQ] THEN
    ASM_SIMP_TAC [DIVIDES_PRIME_EXP_LE] THEN EQ_TAC THEN DISCH_TAC THENL
     [X_GEN_TAC (← q r"p:num") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"i:num") (MP_TAC o SPECL [← q r"p:num", ← q r"1"])) THEN
      ASM_SIMP_TAC [EXP_1, ARITH_EQ],
      EXISTS_TAC (← q r"index q n") THEN MAP_EVERY X_GEN_TAC [← q r"p:num", ← q r"k:num"] THEN
      STRIP_TAC THEN ASM_CASES_TAC (← q r"k = 0") THEN
      ASM_REWRITE_TAC [EXP, DIVIDES_1, LE_INDEX] THEN
      ASM_CASES_TAC (← q r"p EXP k divides n") THENL [ALL_TAC, ASM_MESON_TAC []] THEN
      FIRST_ASSUM (MP_TAC o SPEC (← q r"p:num")) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [DIVIDES_EXP2], DISCH_THEN SUBST_ALL_TAC] THEN
      ASM_REWRITE_TAC [DE_MORGAN_THM] THEN
      CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [PRIME_1]] THEN
      DISCH_TAC THEN FIRST_X_ASSUM (fun th => tactic_of do pure (
        MP_TAC (← SPEC (← q r"3") th) THEN MP_TAC (← SPEC (← q r"2") th))) THEN
      ASM_REWRITE_TAC [DIVIDES_0, NOT_IMP] THEN
      REWRITE_TAC [PRIME_ALT, IMP_CONJ_ALT, DIVIDES_MOD] THEN
      CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
      REWRITE_TAC [LT] THEN ARITH_TAC])

  let PRIME_POWER_EXISTS_ALT ← prove
   r"!n p.
         prime p
         ==> ((?i. n = p EXP i) <=>
              (!d. d divides n ==> d = 1 \/ p divides d))"
   (SIMP_TAC [PRIME_POWER_EXISTS] THEN
    MESON_TAC [DIVIDES_TRANS, DIVIDES_PRIME_PRIME, PRIME_FACTOR, PRIME_1])

  let PRIME_FACTORIZATION_ALT ← prove
   r"!n. ~(n = 0) ==> nproduct {p | prime p} (\p. p EXP index p n) = n"
   (MATCH_MP_TAC COMPLETE_FACTOR_INDUCT THEN
    REWRITE_TAC [INDEX_0, INDEX_1, MULT_EQ_0, ARITH_EQ, DE_MORGAN_THM, EXP] THEN
    SIMP_TAC [← REWRITE_RULE [← GSYM nproduct, NEUTRAL_MUL]
               (← MATCH_MP ITERATE_EQ_NEUTRAL MONOIDAL_MUL)] THEN
    CONJ_TAC THENL
     [X_GEN_TAC (← q r"p:num") THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC [INDEX_PRIME] THEN
      REWRITE_TAC [COND_RAND, EXP, EXP_1] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
      ASM_SIMP_TAC [IN_ELIM_THM, ← REWRITE_RULE [← GSYM nproduct, NEUTRAL_MUL]
          (← MATCH_MP ITERATE_DELTA MONOIDAL_MUL)],
      MAP_EVERY X_GEN_TAC [← q r"m:num", ← q r"n:num"] THEN
      DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC (← MESON []
       (← q r"x * y = z ==> x = m /\ y = n ==> z = m * n")) THEN
      W (MP_TAC o PART_MATCH (rand o rand)
        (← REWRITE_RULE [← GSYM nproduct] (← MATCH_MP ITERATE_OP_GEN MONOIDAL_MUL)) o
        lhand o snd) THEN
      REWRITE_TAC [support, NEUTRAL_MUL] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC [IN_ELIM_THM, EXP_EQ_1, INDEX_EQ_0] THEN
        ASM_SIMP_TAC [DE_MORGAN_THM, CONJ_ASSOC, FINITE_SPECIAL_DIVISORS],
        DISCH_THEN (SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC (← REWRITE_RULE [← GSYM nproduct]
          (← MATCH_MP ITERATE_EQ MONOIDAL_MUL)) THEN
      ASM_SIMP_TAC [IN_ELIM_THM, INDEX_MUL, EXP_ADD]])

  let PRIME_FACTORIZATION ← prove
   r"!n. ~(n = 0)
       ==> nproduct {p | prime p /\ p divides n} (\p. p EXP index p n) = n"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (fun th => tactic_of do pure (GEN_REWRITE_TAC RAND_CONV
          [← SYM (← MATCH_MP PRIME_FACTORIZATION_ALT th)])) THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC [nproduct] THEN
    MATCH_MP_TAC (← MATCH_MP ITERATE_SUPERSET MONOIDAL_MUL) THEN
    SIMP_TAC [IN_ELIM_THM, IMP_CONJ, NEUTRAL_MUL, EXP_EQ_1, INDEX_EQ_0] THEN
    SET_TAC [])
  return { FINITE_EXP_LE, FINITE_INDICES, index_def, INDEX_0, 
           PRIMEPOW_DIVIDES_INDEX, LE_INDEX, EXP_INDEX_DIVIDES, INDEX_LT, 
           INDEX_1, INDEX_MUL, INDEX_EXP, INDEX_FACT, INDEX_FACT_ALT, 
           INDEX_FACT_UNBOUNDED, PRIMEPOW_DIVIDES_FACT, INDEX_REFL, INDEX_EQ_0, 
           INDEX_ZERO, INDEX_POW, INDEX_PRIME, INDEX_TRIVIAL_BOUND, 
           INDEX_DECOMPOSITION, INDEX_DECOMPOSITION_PRIME, 
           INDEX_DECOMPOSITION_LE, INDEX_DECOMPOSITION_UNIQUE, INDEX_UNIQUE, 
           INDEX_UNIQUE_EQ, INDEX_UNIQUE_ALT, INDEX_ADD_MIN, INDEX_SUB_MIN, 
           INDEX_ADD, INDEX_MULT_BASE, INDEX_MULT_EXP, INDEX_MULT_ADD, 
           INDEX_NSUM_LE, DIVIDES_INDEX, EQ_INDEX, COPRIME_INDEX, INDEX_GCD, 
           FORALL_PRIME_INDEX, INDEX_FACT_PRIME_MULT, PRIME_FACTORIZATION_INDEX, 
           PRIME_POWER_EXISTS, PRIME_POWER_EXISTS_ALT, PRIME_FACTORIZATION_ALT, 
           PRIME_FACTORIZATION }

/- ------------------------------------------------------------------------- -/
/- Least common multiples (prime.ml 1779-2062)                               -/
/- ------------------------------------------------------------------------- -/

structure Lcm where
  lcm : thm
  LCM_DIVIDES : thm
  LCM : thm
  LCM_DIVIDES_MUL : thm
  DIVIDES_LCM : thm
  LCM_0 : thm
  LCM_1 : thm
  LCM_SYM : thm
  DIVIDES_LCM_GCD : thm
  PRIMEPOW_DIVIDES_LCM : thm
  PRIME_DIVIDES_LCM : thm
  LCM_ZERO : thm
  INDEX_LCM : thm
  LCM_ASSOC : thm
  LCM_REFL : thm
  LCM_MULTIPLE : thm
  LCM_GCD_DISTRIB : thm
  GCD_LCM_DISTRIB : thm
  LCM_UNIQUE : thm
  LCM_EQ : thm
  LCM_EQ_1 : thm
  DIVIDES_LCM_LEFT : thm
  DIVIDES_LCM_RIGHT : thm
  MULT_LCM_GCD : thm
  MULT_GCD_LCM : thm
  LCM_LMUL : thm
  LCM_RMUL : thm
  LCM_EXP : thm
  LCM_COPRIME_DECOMP : thm
  LE_LCM : thm
  LCM_LE_MULT : thm
  LCM_EQ_MULT : thm
  MAX_LE_LCM_EQ : thm
  MAX_LE_LCM : thm
  deriving Inhabited

@[nospecialize]
def setupLcm [HolBase] (D : PrimeDeps) (PDivides : Divides) (PGcd : Gcd) (PCoprime : Coprime) (PPrimes : Primes) (PIndex : Index) : ExceptT String IO Lcm := do
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, 
        NUMBER_RULE, NUMBER_TAC, NUM_RING, .. } := D
  let { ADD_CLAUSES, CONJ_ASSOC, DE_MORGAN_THM, DISJ_ACI, DIVIDES_DIV_MULT, 
        DIVIDES_LE_IMP, DIVIDES_ONE, DIV_1, DIV_EQ_SELF, DIV_LE, DIV_MULT, 
        DIV_MULT2, DIV_UNIQ, EQ_SYM_EQ, EXP, EXP_1, EXP_ADD, EXP_EQ_0, EXP_ZERO, 
        IMP_CONJ, INT_ABS_NUM, INT_OF_NUM_DIV, INT_OF_NUM_EQ, INT_OF_NUM_MUL, LE, 
        LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, LE_1, LE_ANTISYM, LE_REFL, 
        LE_TRANS, .. } := D.core1
  let { MAX, MONO_OR, MULT_AC, MULT_ASSOC, MULT_CLAUSES, MULT_EQ_0, MULT_EXP, 
        MULT_SYM, NUM_GCD, NUM_LCM, divides, int_lcm, num_CASES, .. } := D.core2
  let { DIVIDES_0, DIVIDES_ZERO, DIVIDES_1, DIVIDES_REFL, DIVIDES_TRANS, 
        DIVIDES_LMUL, DIVIDES_RMUL, DIVIDES_MUL_L, DIVIDES_EXP_LE, MULTIPLES_EQ, .. } := PDivides
  let { DIVIDES_GCD, GCD_0, GCD_ZERO, GCD_REFL, GCD_1, GCD_SYM, GCD_LMUL, .. } := PGcd
  let { COPRIME_GCD, COPRIME_SYM, GCD_COPRIME_EXISTS, COPRIME_0, COPRIME_MUL, 
        COPRIME_LMUL, COPRIME_RMUL, GCD_EXP, .. } := PCoprime
  let { PRIME_1, PRIME_COPRIME_STRONG, PRIME_GE_2, COPRIME_EXP_DIVPROD, 
        COPRIME_PAIR_DECOMP, FACTORIZATION_INDEX, PRIMEPOW_DIVISORS_EQ, .. } := PPrimes
  let { INDEX_0, PRIMEPOW_DIVIDES_INDEX, .. } := PIndex

  let lcm ← prove
   r"lcm(m,n) = if m * n = 0 then 0 else (m * n) DIV gcd(m,n)"
   (REWRITE_TAC [← GSYM INT_OF_NUM_EQ, ← GSYM INT_OF_NUM_MUL, NUM_LCM, int_lcm] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [INT_OF_NUM_MUL, INT_OF_NUM_DIV, INT_ABS_NUM, ← GSYM NUM_GCD])

  let LCM_DIVIDES ← prove
   r"!m n d. lcm(m,n) divides d <=> m divides d /\ n divides d"
   (NUMBER_TAC)

  let LCM ← prove
   r"!m n. m divides lcm(m,n) /\
         n divides lcm(m,n) /\
         (!d. m divides d /\ n divides d ==> lcm(m,n) divides d)"
   (NUMBER_TAC)

  let LCM_DIVIDES_MUL ← prove
   r"!m n. lcm(m,n) divides m * n"
   (REWRITE_TAC [LCM_DIVIDES] THEN CONV_TAC NUMBER_RULE)

  let DIVIDES_LCM ← prove
   r"!m n r. r divides m \/ r divides n
           ==> r divides lcm(m,n)"
   (REPEAT STRIP_TAC THEN FIRST_X_ASSUM
     (MATCH_MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ] DIVIDES_TRANS)) THEN
    ASM_MESON_TAC [LCM])

  let LCM_0 ← prove
   r"(!n. lcm(0,n) = 0) /\ (!n. lcm(n,0) = 0)"
   (REWRITE_TAC [lcm, MULT_CLAUSES] THEN ARITH_TAC)

  let LCM_1 ← prove
   r"(!n. lcm(1,n) = n) /\ (!n. lcm(n,1) = n)"
   (SIMP_TAC [lcm, MULT_CLAUSES, GCD_1, DIV_1] THEN MESON_TAC [])

  let LCM_SYM ← prove
   r"!m n. lcm(m,n) = lcm(n,m)"
   (REWRITE_TAC [lcm, MULT_SYM, GCD_SYM, ← ARITH_RULE (← q r"MAX m n = MAX n m")])

  let DIVIDES_LCM_GCD ← prove
   r"!m n d. d divides lcm(m,n) <=> d * gcd(m,n) divides m * n"
   (NUMBER_TAC)

  let PRIMEPOW_DIVIDES_LCM ← prove
   r"!m n p k.
        prime p
        ==> (p EXP k divides lcm(m,n) <=>
             p EXP k divides m \/ p EXP k divides n)"
   (← do
    -- OCaml evaluates the THEN chain's operands right to left: this MESON
    -- (in the last step) runs before the NUMBER_RULE (in an earlier one).
    let coprime_of_ndiv ← MESON [PRIME_COPRIME_STRONG]
      (← q r"prime p /\ ~(p divides n) ==> coprime(p,n)")
    pure (REPEAT STRIP_TAC THEN EQ_TAC THENL [STRIP_TAC, MESON_TAC [DIVIDES_LCM]] THEN
    ASM_CASES_TAC (← q r"m = 0") THEN ASM_REWRITE_TAC [LCM_0, DIVIDES_0] THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [LCM_0, DIVIDES_0] THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"p:num"] FACTORIZATION_INDEX) THEN
    MP_TAC (← SPECL [← q r"m:num", ← q r"p:num"] FACTORIZATION_INDEX) THEN
    ASM_SIMP_TAC [PRIME_GE_2, LEFT_IMP_EXISTS_THM, divides,
                  LEFT_AND_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"a:num", ← q r"q:num"] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"b:num", ← q r"r:num"] THEN STRIP_TAC THEN
    REWRITE_TAC [← GSYM divides] THEN
    UNDISCH_TAC (← q r"p EXP k divides lcm (m,n)") THEN
    ASM_REWRITE_TAC [DIVIDES_LCM_GCD] THEN
    SUBGOAL_THEN
     (← q r"gcd(p EXP a * q,p EXP b * r) =
      p EXP (MIN a b) * gcd(p EXP (a - MIN a b) * q,p EXP (b - MIN a b) * r)")
    SUBST1_TAC THENL
     [REWRITE_TAC [← GSYM GCD_LMUL, MULT_ASSOC, ← GSYM EXP_ADD] THEN
      AP_TERM_TAC THEN BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      AP_TERM_TAC THEN ARITH_TAC,
      REWRITE_TAC [MULT_ASSOC, ← GSYM EXP_ADD]] THEN
    DISCH_THEN (MP_TAC o
      MATCH_MP (← NUMBER_RULE (← q r"a * b divides c ==> a divides c"))) THEN
    REWRITE_TAC [← ARITH_RULE (← q r"((a * b) * c) * d:num = (a * c) * b * d")] THEN
    REWRITE_TAC [← GSYM EXP_ADD] THEN
    DISCH_THEN (MP_TAC o MATCH_MP (← REWRITE_RULE [IMP_CONJ]
     (← ONCE_REWRITE_RULE [MULT_SYM] COPRIME_EXP_DIVPROD))) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC COPRIME_MUL THEN CONJ_TAC THEN
      MATCH_MP_TAC coprime_of_ndiv THEN
      ASM_REWRITE_TAC [divides] THEN STRIP_TAC THENL
       [UNDISCH_TAC (← q r"!l. a < l ==> ~(?x. m = p EXP l * x)") THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"a + 1")),
        UNDISCH_TAC (← q r"!l. b < l ==> ~(?x. n = p EXP l * x)") THEN
        DISCH_THEN (MP_TAC o SPEC (← q r"b + 1"))] THEN
      ASM_REWRITE_TAC [← ARITH_RULE (← q r"a < a + 1"), EXP_ADD, EXP_1] THEN
      MESON_TAC [MULT_AC],
      ASM_SIMP_TAC [DIVIDES_EXP_LE, PRIME_GE_2] THEN
      DISCH_THEN (MP_TAC o MATCH_MP (← ARITH_RULE
       (← q r"k + MIN a b <= a + b ==> k <= a \/ k <= b"))) THEN
      MATCH_MP_TAC MONO_OR THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC DIVIDES_RMUL THEN ASM_SIMP_TAC [DIVIDES_EXP_LE, PRIME_GE_2]]))

  let PRIME_DIVIDES_LCM ← prove
   r"!m n p.
        prime p
        ==> (p divides lcm(m,n) <=> p divides m \/ p divides n)"
   (REPEAT GEN_TAC THEN
    MP_TAC (← SPECL [← q r"m:num", ← q r"n:num", ← q r"p:num", ← q r"1"] PRIMEPOW_DIVIDES_LCM) THEN
    REWRITE_TAC [EXP_1])

  let LCM_ZERO ← prove
   r"!m n. lcm(m,n) = 0 <=> m = 0 \/ n = 0"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [MULTIPLES_EQ] THEN
    REWRITE_TAC [LCM_DIVIDES, DIVIDES_ZERO] THEN
    MAP_EVERY ASM_CASES_TAC [← q r"m = 0", ← q r"n = 0"] THEN
    ASM_REWRITE_TAC [DIVIDES_ZERO] THEN
    ASM_MESON_TAC [DIVIDES_REFL, MULT_EQ_0, DIVIDES_LMUL, DIVIDES_RMUL])

  let INDEX_LCM ← prove
   r"!m n p.
        prime p
        ==> index p (lcm(m,n)) =
            if m = 0 \/ n = 0 then 0
            else MAX (index p m) (index p n)"
   (REPEAT STRIP_TAC THEN
    MAP_EVERY ASM_CASES_TAC [← q r"m = 0", ← q r"n = 0"] THEN
    ASM_SIMP_TAC [LCM_0, INDEX_0] THEN
    FIRST_ASSUM (MP_TAC o SPECL [← q r"m:num", ← q r"n:num"] o MATCH_MP
      PRIMEPOW_DIVIDES_LCM) THEN
    ASM_REWRITE_TAC [PRIMEPOW_DIVIDES_INDEX, LCM_ZERO] THEN
    ASM_SIMP_TAC [← MESON [PRIME_1] (← q r"prime p ==> ~(p = 1)")] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"k <= m \/ k <= n <=> k <= MAX m n")] THEN
    MESON_TAC [LE_REFL, LE_ANTISYM, LE_TRANS])

  let LCM_ASSOC ← prove
   r"!m n p. lcm(m,lcm(n,p)) = lcm(lcm(m,n),p)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [MULTIPLES_EQ] THEN
    REWRITE_TAC [LCM_DIVIDES] THEN X_GEN_TAC (← q r"q:num") THEN
    REWRITE_TAC [LCM_ZERO] THEN CONV_TAC TAUT)

  let LCM_REFL ← prove
   r"!n. lcm(n,n) = n"
   (REWRITE_TAC [lcm, GCD_REFL, MULT_EQ_0, ← ARITH_RULE (← q r"MAX n n = n")] THEN
    SIMP_TAC [DIV_MULT] THEN MESON_TAC [])

  let LCM_MULTIPLE ← prove
   r"!a b. lcm(b,a * b) = a * b"
   (REWRITE_TAC [MULTIPLES_EQ, LCM_DIVIDES] THEN NUMBER_TAC)

  let LCM_GCD_DISTRIB ← prove
   r"!a b c. lcm(a,gcd(b,c)) = gcd(lcm(a,b),lcm(a,c))"
   (REWRITE_TAC [PRIMEPOW_DIVISORS_EQ] THEN
    SIMP_TAC [PRIMEPOW_DIVIDES_LCM, DIVIDES_GCD] THEN CONV_TAC TAUT)

  let GCD_LCM_DISTRIB ← prove
   r"!a b c. gcd(a,lcm(b,c)) = lcm(gcd(a,b),gcd(a,c))"
   (REWRITE_TAC [PRIMEPOW_DIVISORS_EQ] THEN
    SIMP_TAC [PRIMEPOW_DIVIDES_LCM, DIVIDES_GCD] THEN CONV_TAC TAUT)

  let LCM_UNIQUE ← prove
   r"!d m n.
       m divides d /\ n divides d /\
       (!e. m divides e /\ n divides e ==> d divides e) <=>
       d = lcm(m,n)"
   (REWRITE_TAC [MULTIPLES_EQ, LCM_DIVIDES] THEN
    MESON_TAC [DIVIDES_REFL, DIVIDES_TRANS])

  let LCM_EQ ← prove
   r"!x y u v. (!d. x divides d /\ y divides d <=> u divides d /\ v divides d)
             ==> lcm(x,y) = lcm(u,v)"
   (SIMP_TAC [MULTIPLES_EQ, LCM_DIVIDES])

  let LCM_EQ_1 ← prove
   r"!m n. lcm(m,n) = 1 <=> m = 1 /\ n = 1"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
    REWRITE_TAC [← GSYM LCM_UNIQUE, DIVIDES_1, DIVIDES_ONE])

  let DIVIDES_LCM_LEFT ← prove
   r"!m n. n divides m <=> lcm(m,n) = m"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [EQ_SYM_EQ] THEN
    SIMP_TAC [← GSYM LCM_UNIQUE, DIVIDES_REFL])

  let DIVIDES_LCM_RIGHT ← prove
   r"!m n. m divides n <=> lcm(m,n) = n"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [EQ_SYM_EQ] THEN
    SIMP_TAC [← GSYM LCM_UNIQUE, DIVIDES_REFL])

  let MULT_LCM_GCD ← prove
   r"!m n. lcm(m,n) * gcd(m,n) = m * n"
   (REPEAT GEN_TAC THEN
    MAP_EVERY ASM_CASES_TAC [← q r"m = 0", ← q r"n = 0"] THEN
    ASM_REWRITE_TAC [GCD_0, LCM_0, MULT_CLAUSES] THEN
    ASM_REWRITE_TAC [lcm, MULT_EQ_0, ← GSYM DIVIDES_DIV_MULT] THEN
    CONV_TAC NUMBER_RULE)

  let MULT_GCD_LCM ← prove
   r"!m n. gcd(m,n) * lcm(m,n) = m * n"
   (MESON_TAC [MULT_SYM, MULT_LCM_GCD])

  let LCM_LMUL ← prove
   r"!a b c. lcm(c * a,c * b) = c * lcm(a,b)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"c = 0") THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, LCM_0] THEN
    ASM_REWRITE_TAC [lcm, GCD_LMUL, MULT_EQ_0, DISJ_ACI] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [DE_MORGAN_THM]) THEN
    ASM_SIMP_TAC [← GSYM MULT_ASSOC, DIV_MULT2, MULT_EQ_0, GCD_ZERO] THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC (← q r"0") THEN
    ASM_SIMP_TAC [ADD_CLAUSES, LE_1, GCD_ZERO] THEN
    ONCE_REWRITE_TAC [← ARITH_RULE
      (← q r"a * c * b:num = (c * d) * g <=> c * d * g = c * a * b")] THEN
    AP_TERM_TAC THEN REWRITE_TAC [← GSYM DIVIDES_DIV_MULT] THEN
    CONV_TAC NUMBER_RULE)

  let LCM_RMUL ← prove
   r"!a b c. lcm(a * c,b * c) = c * lcm(a,b)"
   (MESON_TAC [LCM_LMUL, MULT_SYM])

  let LCM_EXP ← prove
   r"!n a b. lcm(a EXP n,b EXP n) = lcm(a,b) EXP n"
   (REPEAT GEN_TAC THEN REWRITE_TAC [lcm] THEN
    REWRITE_TAC [MULT_EQ_0, EXP_EQ_0] THEN
    ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [EXP, GCD_REFL, DIV_1, MULT_CLAUSES] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
     [ASM_MESON_TAC [num_CASES, EXP_ZERO], ALL_TAC] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [DE_MORGAN_THM]) THEN
    REWRITE_TAC [GCD_EXP, ← GSYM MULT_EXP] THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC (← q r"0") THEN
    ASM_SIMP_TAC [ADD_CLAUSES, LE_1, GCD_ZERO, EXP_EQ_0] THEN
    REWRITE_TAC [← GSYM MULT_EXP] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC [← GSYM DIVIDES_DIV_MULT] THEN
    CONV_TAC NUMBER_RULE)

  let LCM_COPRIME_DECOMP ← prove
   r"!m n:num.
     ?m' n'.
        m' divides m /\ n' divides n /\ coprime(m',n') /\ m' * n' = lcm(m,n)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"m = 0") THENL
     [ASM_REWRITE_TAC [DIVIDES_0, COPRIME_0, GCD_0, LCM_0] THEN
      MAP_EVERY EXISTS_TAC [← q r"0", ← q r"1"] THEN CONV_TAC NUMBER_RULE,
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"m:num", ← q r"n:num"] GCD_COPRIME_EXISTS) THEN
    ASM_REWRITE_TAC [GCD_ZERO, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"m':num", ← q r"n':num"] THEN
    DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN
    MP_TAC (← ISPECL [← q r"m':num", ← q r"n':num", ← q r"gcd(m,n)"] COPRIME_PAIR_DECOMP) THEN
    ASM_REWRITE_TAC [GCD_ZERO, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"n'':num", ← q r"m'':num"] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [← q r"m' * m'':num", ← q r"n' * n'':num"] THEN
    REWRITE_TAC [COPRIME_LMUL, COPRIME_RMUL, ← GSYM CONJ_ASSOC] THEN
    ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [COPRIME_SYM] THEN
    ASM_REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
     [ASM_MESON_TAC [DIVIDES_MUL_L, DIVIDES_REFL, DIVIDES_RMUL, DIVIDES_LMUL],
      ALL_TAC] THEN
    MATCH_MP_TAC (← NUM_RING (← q r"!d. ~(d = 0) /\ a * d = b * d ==> a = b")) THEN
    EXISTS_TAC (← q r"gcd(m,n):num") THEN
    ASM_REWRITE_TAC [MULT_LCM_GCD, GCD_ZERO] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC NUM_RING)

  let LE_LCM ← prove
   r"(!m n. m <= lcm(m,n) <=> n = 0 ==> m = 0) /\
   (!m n. n <= lcm(m,n) <=> m = 0 ==> n = 0)"
   (REPEAT STRIP_TAC THEN
    MAP_EVERY ASM_CASES_TAC [← q r"m = 0", ← q r"n = 0"] THEN
    ASM_REWRITE_TAC [LCM_0, LE_REFL, LE] THEN
    MATCH_MP_TAC DIVIDES_LE_IMP THEN
    ASM_REWRITE_TAC [LCM, LCM_ZERO])

  let LCM_LE_MULT ← prove
   r"!m n. lcm(m,n) <= m * n"
   (REPEAT GEN_TAC THEN REWRITE_TAC [lcm] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [LE_REFL, DIV_LE])

  let LCM_EQ_MULT ← prove
   r"!m n. lcm(m,n) = m * n <=> m = 0 \/ n = 0 \/ coprime(m,n)"
   (REPEAT GEN_TAC THEN
    MAP_EVERY ASM_CASES_TAC [← q r"m = 0", ← q r"n = 0"] THEN
    ASM_REWRITE_TAC [LCM_0, MULT_CLAUSES] THEN
    ASM_REWRITE_TAC [lcm, DIV_EQ_SELF, MULT_EQ_0, COPRIME_GCD])

  let MAX_LE_LCM_EQ ← prove
   r"!m n. MAX m n <= lcm(m,n) <=> (m = 0 <=> n = 0)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [MAX] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [LE_LCM] THEN
    ASM_ARITH_TAC)

  let MAX_LE_LCM ← prove
   r"!m n. (m = 0 <=> n = 0) ==> MAX m n <= lcm(m,n)"
   (REWRITE_TAC [MAX_LE_LCM_EQ])
  return { lcm, LCM_DIVIDES, LCM, LCM_DIVIDES_MUL, DIVIDES_LCM, LCM_0, LCM_1, 
           LCM_SYM, DIVIDES_LCM_GCD, PRIMEPOW_DIVIDES_LCM, PRIME_DIVIDES_LCM, 
           LCM_ZERO, INDEX_LCM, LCM_ASSOC, LCM_REFL, LCM_MULTIPLE, 
           LCM_GCD_DISTRIB, GCD_LCM_DISTRIB, LCM_UNIQUE, LCM_EQ, LCM_EQ_1, 
           DIVIDES_LCM_LEFT, DIVIDES_LCM_RIGHT, MULT_LCM_GCD, MULT_GCD_LCM, 
           LCM_LMUL, LCM_RMUL, LCM_EXP, LCM_COPRIME_DECOMP, LE_LCM, LCM_LE_MULT, 
           LCM_EQ_MULT, MAX_LE_LCM_EQ, MAX_LE_LCM }

/- ------------------------------------------------------------------------- -/
/- Iterated GCD and LCM over a finite set (prime.ml 2063-2286)               -/
/- ------------------------------------------------------------------------- -/

structure Iterated where
  NEUTRAL_GCD : thm
  MONOIDAL_GCD : thm
  NEUTRAL_LCM : thm
  MONOIDAL_LCM : thm
  ITERATE_GCD_DIVIDES : thm
  ITERATE_GCD_DIVIDES_EQ : thm
  DIVIDES_ITERATE_GCD : thm
  DIVIDES_ITERATE_GCD_GEN : thm
  DIVIDES_ITERATE_LCM : thm
  DIVIDES_ITERATE_LCM_GEN : thm
  ITERATE_LCM_DIVIDES : thm
  ITERATE_LCM_DIVIDES_GEN : thm
  PRIMEPOW_DIVIDES_ITERATE_LCM : thm
  PRIMEPOW_DIVIDES_ITERATE_LCM_GEN : thm
  PRIME_DIVIDES_ITERATE_LCM_GEN : thm
  PRIME_DIVIDES_ITERATE_LCM : thm
  ITERATE_LCM_EQ_0_GEN : thm
  ITERATE_LCM_EQ_0 : thm
  ITERATE_LCM_EQ_1_GEN : thm
  ITERATE_LCM_EQ_1 : thm
  ITERATE_GCD_EQ_0_GEN : thm
  ITERATE_GCD_EQ_0 : thm
  deriving Inhabited

@[nospecialize]
def setupIterated [HolBase] (D : PrimeDeps) (PDivides : Divides) (PGcd : Gcd) (PPrimes : Primes) (PLcm : Lcm) : ExceptT String IO Iterated := do
  let { ARITH_RULE, ASM_MESON_TAC, MESON_TAC, SET_RULE, SET_TAC, NUM_REDUCE_CONV, .. } := D
  let { ARITH_EQ, DIVIDES_ONE, EXISTS_IN_INSERT, EXP, EXP_1, EXP_EQ_1, 
        FINITE_INDUCT_STRONG, FINITE_RESTRICT, FORALL_IN_INSERT, GCD, IMP_CONJ, 
        IN_ELIM_THM, ITERATE_CLAUSES, ITERATE_EXPAND_CASES, .. } := D.core1
  let { NOT_IN_EMPTY, RIGHT_FORALL_IMP_THM, SELECT_UNIQUE, monoidal, neutral, 
        support, .. } := D.core2
  let { DIVIDES_0, DIVIDES_ZERO, DIVIDES_1, DIVIDES_REFL, DIVIDES_TRANS, .. } := PDivides
  let { DIVIDES_GCD, GCD_0, GCD_ZERO, GCD_SYM, GCD_ASSOC, .. } := PGcd
  let { PRIME_1, .. } := PPrimes
  let { LCM_DIVIDES, DIVIDES_LCM, LCM_1, LCM_SYM, PRIMEPOW_DIVIDES_LCM, LCM_ZERO, 
        LCM_ASSOC, LCM_EQ_1, .. } := PLcm

  let NEUTRAL_GCD ← prove
   r"neutral (\m n. gcd(m,n)) = 0"
   (REWRITE_TAC [neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN MESON_TAC [GCD_0])

  let MONOIDAL_GCD ← prove
   r"monoidal (\m n:num. gcd(m,n))"
   (REWRITE_TAC [monoidal, NEUTRAL_GCD, GCD_0] THEN
    MESON_TAC [GCD_ASSOC, GCD_SYM])

  let NEUTRAL_LCM ← prove
   r"neutral (\m n. lcm(m,n)) = 1"
   (REWRITE_TAC [neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN MESON_TAC [LCM_1])

  let MONOIDAL_LCM ← prove
   r"monoidal (\m n:num. lcm(m,n))"
   (REWRITE_TAC [monoidal, NEUTRAL_LCM, LCM_1] THEN
    MESON_TAC [LCM_ASSOC, LCM_SYM])

  let ITERATE_GCD_DIVIDES ← prove
   r"!f k i:K.
        FINITE k /\ i IN k
        ==> iterate (\m n:num. gcd(m,n)) k f divides f i"
   (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [FORALL_IN_INSERT, ← MATCH_MP ITERATE_CLAUSES MONOIDAL_GCD] THEN
    MESON_TAC [NOT_IN_EMPTY, GCD, DIVIDES_REFL, DIVIDES_TRANS])

  let ITERATE_GCD_DIVIDES_EQ ← prove
   r"!f k i:K.
        i IN k
        ==> (iterate (\m n:num. gcd(m,n)) k f divides f i <=>
             FINITE {j | j IN k /\ ~(f j = 0)} \/ f i = 0)"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"f(i:K) = 0") THEN ASM_REWRITE_TAC [DIVIDES_0] THEN
    ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
    REWRITE_TAC [support, NEUTRAL_GCD] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [DIVIDES_ZERO] THEN
    MATCH_MP_TAC ITERATE_GCD_DIVIDES THEN
    ASM_REWRITE_TAC [IN_ELIM_THM])

  let DIVIDES_ITERATE_GCD ← prove
   r"!f (k:K->bool) d.
        FINITE k
        ==> (d divides iterate (\m n:num. gcd(m,n)) k f <=>
             !i. i IN k ==> d divides f i)"
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [FORALL_IN_INSERT, ← MATCH_MP ITERATE_CLAUSES MONOIDAL_GCD] THEN
    SIMP_TAC [NEUTRAL_GCD, DIVIDES_0, NOT_IN_EMPTY, DIVIDES_GCD])

  let DIVIDES_ITERATE_GCD_GEN ← prove
   r"!f (k:K->bool) d.
        d divides iterate (\m n:num. gcd(m,n)) k f <=>
        FINITE {j | j IN k /\ ~(f j = 0)} ==> !i. i IN k ==> d divides f i"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
    REWRITE_TAC [support, NEUTRAL_GCD] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [DIVIDES_0] THEN
    ASM_SIMP_TAC [DIVIDES_ITERATE_GCD, IN_ELIM_THM] THEN
    MESON_TAC [DIVIDES_0])

  let DIVIDES_ITERATE_LCM ← prove
   r"!f k i:K.
        FINITE k /\ i IN k
        ==> f i divides iterate (\m n:num. lcm(m,n)) k f"
   (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [FORALL_IN_INSERT, ← MATCH_MP ITERATE_CLAUSES MONOIDAL_LCM] THEN
    ASM_SIMP_TAC [NOT_IN_EMPTY, DIVIDES_LCM, DIVIDES_REFL])

  let DIVIDES_ITERATE_LCM_GEN ← prove
   r"!f k i:K.
        i IN k
        ==> (f i divides iterate (\m n:num. lcm(m,n)) k f <=>
             FINITE {j | j IN k /\ ~(f j = 1)} \/ f i = 1)"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"f(i:K) = 1") THEN ASM_REWRITE_TAC [DIVIDES_1] THEN
    ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
    REWRITE_TAC [support, NEUTRAL_LCM] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [DIVIDES_ONE] THEN
    MATCH_MP_TAC DIVIDES_ITERATE_LCM THEN
    ASM_REWRITE_TAC [IN_ELIM_THM])

  let ITERATE_LCM_DIVIDES ← prove
   r"!f (k:K->bool) n.
        FINITE k
        ==> (iterate (\m n:num. lcm(m,n)) k f divides n <=>
             !i. i IN k ==> f i divides n)"
   (GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [FORALL_IN_INSERT, ← MATCH_MP ITERATE_CLAUSES MONOIDAL_LCM] THEN
    SIMP_TAC [NEUTRAL_LCM, DIVIDES_1, NOT_IN_EMPTY, LCM_DIVIDES])

  let ITERATE_LCM_DIVIDES_GEN ← prove
   r"!f (k:K->bool) n.
        iterate (\m n:num. lcm(m,n)) k f divides n <=>
        FINITE {j | j IN k /\ ~(f j = 1)} ==> !i. i IN k ==> f i divides n"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
    REWRITE_TAC [support, NEUTRAL_LCM] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [ITERATE_LCM_DIVIDES, DIVIDES_1, IN_ELIM_THM] THEN
    MESON_TAC [DIVIDES_1])

  let PRIMEPOW_DIVIDES_ITERATE_LCM ← prove
   r"!f (k:K->bool) p m.
        FINITE k /\ prime p
        ==> (p EXP m divides iterate (\m n:num. lcm(m,n)) k f <=>
             m = 0 \/ ?i. i IN k /\ p EXP m divides (f i))"
   (GEN_TAC THEN REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [EXISTS_IN_INSERT, ← MATCH_MP ITERATE_CLAUSES MONOIDAL_LCM,
          PRIMEPOW_DIVIDES_LCM, NOT_IN_EMPTY, NEUTRAL_LCM] THEN
    MESON_TAC [DIVIDES_ONE, EXP_EQ_1, PRIME_1])

  let PRIMEPOW_DIVIDES_ITERATE_LCM_GEN ← prove
   r"!f (k:K->bool) p m.
        prime p
        ==> (p EXP m divides iterate (\m n:num. lcm(m,n)) k f <=>
             m = 0 \/
             FINITE {j | j IN k /\ ~(f j = 1)} /\
             ?i. i IN k /\ p EXP m divides (f i))"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"m = 0") THEN ASM_REWRITE_TAC [EXP, DIVIDES_1] THEN
    ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
    REWRITE_TAC [support, NEUTRAL_LCM] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [DIVIDES_ONE, EXP_EQ_1] THEN
    ASM_SIMP_TAC [PRIMEPOW_DIVIDES_ITERATE_LCM, IN_ELIM_THM] THEN
    ASM_MESON_TAC [DIVIDES_1, DIVIDES_ONE, PRIME_1, EXP_EQ_1])

  let PRIME_DIVIDES_ITERATE_LCM_GEN ← prove
   r"!f (k:K->bool) p.
        prime p
        ==> (p divides iterate (\m n:num. lcm(m,n)) k f <=>
             FINITE {j | j IN k /\ ~(f j = 1)} /\
             ?i. i IN k /\ p divides (f i))"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"f:K->num", ← q r"k:K->bool", ← q r"p:num", ← q r"1"]
      PRIMEPOW_DIVIDES_ITERATE_LCM_GEN) THEN
    REWRITE_TAC [EXP_1, ARITH_EQ])

  let PRIME_DIVIDES_ITERATE_LCM ← prove
   r"!f (k:K->bool) p.
        FINITE k /\ prime p
        ==> (p divides iterate (\m n:num. lcm(m,n)) k f <=>
             ?i. i IN k /\ p divides (f i))"
   (SIMP_TAC [PRIME_DIVIDES_ITERATE_LCM_GEN, FINITE_RESTRICT])

  let ITERATE_LCM_EQ_0_GEN ← prove
   r"!(k:K->bool) f.
        iterate (\m n. lcm(m,n)) k f = 0 <=>
        FINITE {j | j IN k /\ ~(f j = 1)} /\
        ?j. j IN k /\ f j = 0"
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
    REWRITE_TAC [support, NEUTRAL_LCM] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [ARITH_EQ] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
     [← ARITH_RULE (← q r"n = 0 <=> ~(n = 1) /\ n = 0")] THEN
    ONCE_REWRITE_TAC [← SET_RULE
     (← q r"j IN k /\ ~(f j = 1) /\ f j = 0 <=>
      j IN {j | j IN k /\ ~(f j = 1)} /\ f j = 0")] THEN
    POP_ASSUM MP_TAC THEN
    SPEC_TAC ((← q r"{j:K | j IN k /\ ~(f j = 1)}"), (← q r"k:K->bool")) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [← MATCH_MP ITERATE_CLAUSES MONOIDAL_LCM] THEN
    SIMP_TAC [NEUTRAL_LCM, LCM_ZERO, EXISTS_IN_INSERT, NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV)

  let ITERATE_LCM_EQ_0 ← prove
   r"!(k:K->bool) f.
        FINITE k
        ==> (iterate (\m n. lcm(m,n)) k f = 0 <=>
             ?j. j IN k /\ f j = 0)"
   (SIMP_TAC [ITERATE_LCM_EQ_0_GEN, FINITE_RESTRICT])

  let ITERATE_LCM_EQ_1_GEN ← prove
   r"!(k:K->bool) f.
        iterate (\m n. lcm(m,n)) k f = 1 <=>
        FINITE {j | j IN k /\ ~(f j = 1)} ==> !j. j IN k ==> f j = 1"
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
    REWRITE_TAC [support, NEUTRAL_LCM] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [← SET_RULE
     (← q r"(!j. j IN k ==> f j = 1) <=>
      !j. j IN {j | j IN k /\ ~(f j = 1)} ==> f j = 1")] THEN
    POP_ASSUM MP_TAC THEN
    SPEC_TAC ((← q r"{j:K | j IN k /\ ~(f j = 1)}"), (← q r"k:K->bool")) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [← MATCH_MP ITERATE_CLAUSES MONOIDAL_LCM] THEN
    SIMP_TAC [NEUTRAL_LCM, LCM_EQ_1, NOT_IN_EMPTY] THEN SET_TAC [])

  let ITERATE_LCM_EQ_1 ← prove
   r"!(k:K->bool) f.
        FINITE k
        ==> (iterate (\m n. lcm(m,n)) k f = 1 <=>
             !j. j IN k ==> f j = 1)"
   (SIMP_TAC [ITERATE_LCM_EQ_1_GEN, FINITE_RESTRICT])

  let ITERATE_GCD_EQ_0_GEN ← prove
   r"!(k:K->bool) f.
        iterate (\m n. gcd(m,n)) k f = 0 <=>
        FINITE {j | j IN k /\ ~(f j = 0)} ==> !j. j IN k ==> f j = 0"
   (REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC [ITERATE_EXPAND_CASES] THEN
    REWRITE_TAC [support, NEUTRAL_GCD] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [← SET_RULE
     (← q r"(!j. j IN k ==> f j = 0) <=>
      !j. j IN {j | j IN k /\ ~(f j = 0)} ==> f j = 0")] THEN
    POP_ASSUM MP_TAC THEN
    SPEC_TAC ((← q r"{j:K | j IN k /\ ~(f j = 0)}"), (← q r"k:K->bool")) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [← MATCH_MP ITERATE_CLAUSES MONOIDAL_GCD] THEN
    SIMP_TAC [NEUTRAL_GCD, GCD_ZERO, NOT_IN_EMPTY] THEN SET_TAC [])

  let ITERATE_GCD_EQ_0 ← prove
   r"!(k:K->bool) f.
        FINITE k
        ==> (iterate (\m n. gcd(m,n)) k f = 0 <=>
             !j. j IN k ==> f j = 0)"
   (SIMP_TAC [ITERATE_GCD_EQ_0_GEN, FINITE_RESTRICT])
  return { NEUTRAL_GCD, MONOIDAL_GCD, NEUTRAL_LCM, MONOIDAL_LCM, 
           ITERATE_GCD_DIVIDES, ITERATE_GCD_DIVIDES_EQ, DIVIDES_ITERATE_GCD, 
           DIVIDES_ITERATE_GCD_GEN, DIVIDES_ITERATE_LCM, DIVIDES_ITERATE_LCM_GEN, 
           ITERATE_LCM_DIVIDES, ITERATE_LCM_DIVIDES_GEN, 
           PRIMEPOW_DIVIDES_ITERATE_LCM, PRIMEPOW_DIVIDES_ITERATE_LCM_GEN, 
           PRIME_DIVIDES_ITERATE_LCM_GEN, PRIME_DIVIDES_ITERATE_LCM, 
           ITERATE_LCM_EQ_0_GEN, ITERATE_LCM_EQ_0, ITERATE_LCM_EQ_1_GEN, 
           ITERATE_LCM_EQ_1, ITERATE_GCD_EQ_0_GEN, ITERATE_GCD_EQ_0 }

/- ------------------------------------------------------------------------- -/
/- Induction principle for multiplicative functions (prime.ml 2288-2356)     -/
/- ------------------------------------------------------------------------- -/

structure Induct where
  INDUCT_COPRIME : thm
  INDUCT_COPRIME_STRONG : thm
  INDUCT_COPRIME_ALT : thm
  deriving Inhabited

@[nospecialize]
def setupInduct [HolBase] (D : PrimeDeps) (PCoprime : Coprime) (PPrimes : Primes) : ExceptT String IO Induct := do
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, .. } := D
  let { EQ_MULT_LCANCEL, EXP, EXP_1, EXP_ADD, EXP_EQ_0, EXP_EQ_1, 
        LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, LT_MULT_RCANCEL, LT_REFL, .. } := D.core1
  let { MULT_ASSOC, MULT_CLAUSES, MULT_EQ_0, MULT_EQ_1, divides, num_WF, .. } := D.core2
  let { COPRIME_SYM, COPRIME_EXP, .. } := PCoprime
  let { PRIME_2, PRIME_COPRIME, PRIME_GE_2, PRIME_FACTOR, PRIME_IMP_NZ, 
        FACTORIZATION_INDEX, .. } := PPrimes

  let INDUCT_COPRIME ← prove
   r"!P. (!a b. 1 < a /\ 1 < b /\ coprime(a,b) /\ P a /\ P b ==> P(a * b)) /\
       (!p k. prime p ==> P(p EXP k))
       ==> !n. 1 < n ==> P n"
   (GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC num_WF THEN
    X_GEN_TAC (← q r"n:num") THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP (← ARITH_RULE (← q r"1 < n ==> ~(n = 1)"))) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"p:num") o MATCH_MP PRIME_FACTOR) THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"p:num"] FACTORIZATION_INDEX) THEN
    ASM_SIMP_TAC [PRIME_GE_2, ← ARITH_RULE (← q r"1 < n ==> ~(n = 0)")] THEN
    REWRITE_TAC [divides, LEFT_IMP_EXISTS_THM, LEFT_AND_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"k:num", ← q r"m:num"] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_CASES_TAC (← q r"m = 1") THEN ASM_SIMP_TAC [MULT_CLAUSES] THEN
    FIRST_X_ASSUM (CONJUNCTS_THEN2 MATCH_MP_TAC MP_TAC) THEN
    ASM_SIMP_TAC [] THEN DISCH_THEN (K ALL_TAC) THEN
    MATCH_MP_TAC (← TAUT
     (← q r"!p. (a /\ b /\ ~p) /\ c /\ (a /\ ~p ==> b ==> d)
          ==> a /\ b /\ c /\ d")) THEN
    EXISTS_TAC (← q r"m = 0") THEN
    SUBGOAL_THEN (← q r"~(k = 0)") ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM (MP_TAC o C MATCH_MP (← ARITH_RULE (← q r"0 < 1"))) THEN
      FIRST_X_ASSUM (MP_TAC o CONJUNCT2) THEN
      REWRITE_TAC [EXP, EXP_1, MULT_CLAUSES, divides],
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC (← q r"1 < p EXP k * m") THEN
      ASM_REWRITE_TAC [← ARITH_RULE (← q r"1 < x <=> ~(x = 0) /\ ~(x = 1)")] THEN
      ASM_REWRITE_TAC [EXP_EQ_0, EXP_EQ_1, MULT_EQ_0, MULT_EQ_1] THEN
      FIRST_X_ASSUM (MP_TAC o MATCH_MP PRIME_GE_2 o CONJUNCT1) THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o C MATCH_MP (← ARITH_RULE (← q r"k < k + 1"))) THEN
      REWRITE_TAC [EXP_ADD, EXP_1, ← GSYM MULT_ASSOC, EQ_MULT_LCANCEL] THEN
      ASM_SIMP_TAC [EXP_EQ_0, PRIME_IMP_NZ, ← GSYM divides] THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC [COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_EXP THEN
      ASM_MESON_TAC [PRIME_COPRIME, COPRIME_SYM],
      DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [← ARITH_RULE (← q r"m = 1 * m")] THEN
      ASM_REWRITE_TAC [LT_MULT_RCANCEL]])

  let INDUCT_COPRIME_STRONG ← prove
   r"!P. (!a b. 1 < a /\ 1 < b /\ coprime(a,b) /\ P a /\ P b ==> P(a * b)) /\
       (!p k. prime p /\ ~(k = 0) ==> P(p EXP k))
       ==> !n. 1 < n ==> P n"
   (GEN_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC [← TAUT (← q r"a ==> b <=> a ==> a ==> b")] THEN
    MATCH_MP_TAC INDUCT_COPRIME THEN CONJ_TAC THENL
     [ASM_MESON_TAC [],
      MAP_EVERY X_GEN_TAC [← q r"p:num", ← q r"k:num"] THEN ASM_CASES_TAC (← q r"k = 0") THEN
      ASM_REWRITE_TAC [LT_REFL, EXP] THEN ASM_MESON_TAC []])

  let INDUCT_COPRIME_ALT ← prove
   r"!P. P 0 /\
       (!a b. 1 < a /\ 1 < b /\ coprime(a,b) /\ P a /\ P b ==> P(a * b)) /\
       (!p k. prime p ==> P(p EXP k))
       ==> !n. P n"
   (GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC (← MESON []
     (← q r"(!n. 1 < n ==> P n) /\ (!n. ~(1 < n) ==> P n) ==> !n. P n")) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INDUCT_COPRIME THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [← ARITH_RULE (← q r"~(1 < n) <=> n = 0 \/ n = 1")] THEN
      REPEAT STRIP_TAC THEN ASM_MESON_TAC [PRIME_2, EXP]])
  return { INDUCT_COPRIME, INDUCT_COPRIME_STRONG, INDUCT_COPRIME_ALT }

/- ------------------------------------------------------------------------- -/
/- A conversion for divisibility. (prime.ml 2358-2376)                       -/
/- A conversion for coprimality. (prime.ml 2378-2424)                        -/
/- More general GCD_CONV, and LCM_CONV. (prime.ml 2426-2472)                 -/
/- ------------------------------------------------------------------------- -/

/-- What the four conversions compute ONCE, when prime.ml defines them: each
    `let ... and ... in fun tm -> ...` evaluates its bindings at load time,
    left to right. -/
structure Convs where
  -- DIVIDES_CONV (2361-2366)
  divides_pth_0 : thm
  divides_pth_1 : thm
  divides_a_tm : term
  divides_b_tm : term
  divides_zero_tm : term
  divides_op : term
  -- COPRIME_CONV (2381-2395)
  coprime_pth_yes_l : thm
  coprime_pth_yes_r : thm
  coprime_pth_no : thm
  coprime_pth_oo : thm
  coprime_m_tm : term
  coprime_n_tm : term
  coprime_x_tm : term
  coprime_y_tm : term
  coprime_d_tm : term
  coprime_tm : term
  -- GCD_CONV (2429-2441)
  gcd_pth0 : thm
  gcd_pth1 : thm
  gcd_pth2 : thm
  gcd_tm : term
  -- LCM_CONV (2467-2472): its GEN_REWRITE_CONVs' theorems
  lcm_cond1 : thm
  lcm_cond2 : thm
  deriving Inhabited

@[nospecialize]
def setupConvs [HolBase] (D : PrimeDeps) (PDivides : Divides) (PGcd : Gcd) : ExceptT String IO Convs := do
  let { MESON_TAC, ASM_MESON_TAC, NUM_REDUCE_CONV, .. } := D
  let { COND_CLAUSES, DIVIDES_MOD, DIVIDES_ONE, .. } := D.core1
  let { MULT_AC, coprime, divides, .. } := D.core2
  let { DIVIDES_ZERO, DIVIDES_RMUL, DIVIDES_ADD_REVR, DIVIDES_REFL, DIVIDES_LMUL, .. } := PDivides
  let { GCD_0, GCD_UNIQUE, GCD_SYM, .. } := PGcd

  -- let DIVIDES_CONV =
  let divides_pth_0 ← SPEC (← q r"b:num") DIVIDES_ZERO
  let divides_pth_1 ← prove
     r"~(a = 0) ==> (a divides b <=> (b MOD a = 0))"
     (REWRITE_TAC [DIVIDES_MOD])
  let divides_a_tm ← q r"a:num"
  let divides_b_tm ← q r"b:num"
  let divides_zero_tm ← q r"0"
  let divides_op ← q r"(divides)"     -- dest_divides = dest_binop `(divides)`

  -- let COPRIME_CONV =
  let coprime_pth_yes_l ← prove
     r"(m * x = n * y + 1) ==> (coprime(m,n) <=> T)"
     (MESON_TAC [coprime, DIVIDES_RMUL, DIVIDES_ADD_REVR, DIVIDES_ONE])
  let coprime_pth_yes_r ← prove
     r"(m * x = n * y + 1) ==> (coprime(n,m) <=> T)"
     (MESON_TAC [coprime, DIVIDES_RMUL, DIVIDES_ADD_REVR, DIVIDES_ONE])
  let coprime_pth_no ← prove
     r"(m = x * d) /\ (n = y * d) /\ ~(d = 1) ==> (coprime(m,n) <=> F)"
     (REWRITE_TAC [coprime, divides] THEN MESON_TAC [MULT_AC])
  let coprime_pth_oo ← prove
     r"coprime(0,0) <=> F"
     (MESON_TAC [coprime, DIVIDES_REFL, ← NUM_REDUCE_CONV (← q r"1 = 0")])
  let coprime_m_tm ← q r"m:num"
  let coprime_n_tm ← q r"n:num"
  let coprime_x_tm ← q r"x:num"
  let coprime_y_tm ← q r"y:num"
  let coprime_d_tm ← q r"d:num"
  let coprime_tm ← q r"coprime"

  -- let GCD_CONV =
  let gcd_pth0 ← prove r"gcd(0,0) = 0" (REWRITE_TAC [GCD_0])
  let gcd_pth1 ← prove
     r"!m n x y d m' n'.
      (m * x = n * y + d) /\ (m = m' * d) /\ (n = n' * d) ==> (gcd(m,n) = d)"
     (REPEAT GEN_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      CONV_TAC (RAND_CONV SYM_CONV) THEN ASM_REWRITE_TAC [← GSYM GCD_UNIQUE] THEN
      ASM_MESON_TAC [DIVIDES_LMUL, DIVIDES_RMUL,
                     DIVIDES_ADD_REVR, DIVIDES_REFL])
  let gcd_pth2 ← prove
     r"!m n x y d m' n'.
       (n * y = m * x + d) /\ (m = m' * d) /\ (n = n' * d) ==> (gcd(m,n) = d)"
     (MESON_TAC [gcd_pth1, GCD_SYM])
  let gcd_tm ← q r"gcd"

  -- let LCM_CONV = ... CONJUNCT1(SPEC_ALL COND_CLAUSES) ... CONJUNCT2(...)
  let lcm_cond1 ← CONJUNCT1 (← SPEC_ALL COND_CLAUSES)
  let lcm_cond2 ← CONJUNCT2 (← SPEC_ALL COND_CLAUSES)

  return { divides_pth_0, divides_pth_1, divides_a_tm, divides_b_tm, divides_zero_tm,
           divides_op, coprime_pth_yes_l, coprime_pth_yes_r, coprime_pth_no,
           coprime_pth_oo, coprime_m_tm, coprime_n_tm, coprime_x_tm, coprime_y_tm,
           coprime_d_tm, coprime_tm, gcd_pth0, gcd_pth1, gcd_pth2, gcd_tm,
           lcm_cond1, lcm_cond2 }

/-- `DIVIDES_CONV` (prime.ml 2361). -/
def DIVIDES_CONV [HolBase] (D : PrimeDeps) (P : Convs) : ioconv := fun tm => ExceptT.run do
  let { NUM_EQ_CONV, NUM_MOD_CONV, .. } := D
  let (a, b) ← liftExcept (HolCore.Basics.dest_binop P.divides_op tm)
  if a == P.divides_zero_tm then
    CONV_RULE (RAND_CONV NUM_EQ_CONV) (← INST [(b, P.divides_b_tm)] P.divides_pth_0)
  else
    let th1 ← INST [(a, P.divides_a_tm), (b, P.divides_b_tm)] P.divides_pth_1
    let th2 ← MP th1 (← EQF_ELIM (← ExceptT.mk (NUM_EQ_CONV (← liftExcept (rand (← liftExcept (lhand (concl th1))))))))
    CONV_RULE (RAND_CONV (LAND_CONV NUM_MOD_CONV THENC NUM_EQ_CONV)) th2

/-- The `bezout` of COPRIME_CONV (2396) and GCD_CONV (2443):
    `x`, `y` with `x * m + y * n = gcd(m,n)`. -/
partial def bezout (m n : Rat) : Rat × Rat :=
  if m == 0 then (0, 1) else if n == 0 then (1, 0)
  else if m ≤ n then
    let q := quo_num n m
    let r := mod_num n m
    let (x, y) := bezout m r
    (x - q * y, y)
  else
    let (x, y) := bezout n m
    (y, x)

/-- `COPRIME_CONV` (prime.ml 2381). -/
def COPRIME_CONV [HolBase] (D : PrimeDeps) (P : Convs) : ioconv := fun tm => ExceptT.run do
  let { NUM_REDUCE_CONV, mk_numeral, .. } := D
  let num (n : Rat) := liftExcept (mk_numeral n)
  let (pop, ptm) ← liftExcept (dest_comb tm)
  if pop != P.coprime_tm then throw "COPRIME_CONV"
  let (l, r) ← liftExcept (HolMath.Pair.dest_pair ptm)
  let m ← liftExcept (HolCore.Basics.dest_numeral l)
  let n ← liftExcept (HolCore.Basics.dest_numeral r)
  if m == 0 && n == 0 then return P.coprime_pth_oo
  let (x, y) := bezout m n
  let d := x * m + y * n
  let th ←
    if d == 1 then
      if x > 0 then
        INST [(l, P.coprime_m_tm), (r, P.coprime_n_tm), (← num x, P.coprime_x_tm),
              (← num (-y), P.coprime_y_tm)] P.coprime_pth_yes_l
      else
        INST [(r, P.coprime_m_tm), (l, P.coprime_n_tm), (← num (-x), P.coprime_y_tm),
              (← num y, P.coprime_x_tm)] P.coprime_pth_yes_r
    else
      INST [(l, P.coprime_m_tm), (r, P.coprime_n_tm), (← num d, P.coprime_d_tm),
            (← num (m / d), P.coprime_x_tm), (← num (n / d), P.coprime_y_tm)] P.coprime_pth_no
  MP th (← EQT_ELIM (← ExceptT.mk (NUM_REDUCE_CONV (← liftExcept (lhand (concl th))))))

/-- `GCD_CONV` (prime.ml 2429). -/
def GCD_CONV [HolBase] (D : PrimeDeps) (P : Convs) : ioconv := fun tm => ExceptT.run do
  let { NUM_REDUCE_CONV, mk_numeral, .. } := D
  let num (n : Rat) := liftExcept (mk_numeral n)
  let (gt, lr) ← liftExcept (dest_comb tm)
  if gt != P.gcd_tm then throw "GCD_CONV"
  let (mtm, ntm) ← liftExcept (HolMath.Pair.dest_pair lr)
  let m ← liftExcept (HolCore.Basics.dest_numeral mtm)
  let n ← liftExcept (HolCore.Basics.dest_numeral ntm)
  if m == 0 && n == 0 then return P.gcd_pth0
  let (x0, y0) := bezout m n
  let x := abs_num x0
  let y := abs_num y0
  let xtm ← num x
  let ytm ← num y
  let d := abs_num (x * m - y * n)
  let dtm ← num d
  let m' := m / d
  let n' := n / d
  let mtm' ← num m'
  let ntm' ← num n'
  let th ← SPECL [mtm, ntm, xtm, ytm, dtm, mtm', ntm']
            (if m * x == n * y + d then P.gcd_pth1 else P.gcd_pth2)
  MP th (← EQT_ELIM (← ExceptT.mk (NUM_REDUCE_CONV (← liftExcept (lhand (concl th))))))

/-- `LCM_CONV` (prime.ml 2467), with its nets built once, as OCaml builds
    them when prime.ml defines it. -/
def LCM_CONV [HolBase] (D : PrimeDeps) (P : Convs) (lcm : thm) :
    ExceptT String IO ioconv := do
  let { NUM_EQ_CONV, NUM_MULT_CONV, NUM_DIV_CONV, .. } := D
  pure ((← GEN_REWRITE_CONV_NET I [lcm]) THENC
    RATOR_CONV (LAND_CONV (LAND_CONV NUM_MULT_CONV THENC NUM_EQ_CONV)) THENC
    ((← GEN_REWRITE_CONV_NET I [P.lcm_cond1]) ORELSEC
     ((← GEN_REWRITE_CONV_NET I [P.lcm_cond2]) THENC
      COMB2_CONV (RAND_CONV NUM_MULT_CONV) (GCD_CONV D P) THENC NUM_DIV_CONV)))

end HolLibrary.Prime
