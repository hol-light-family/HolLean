/- ========================================================================= -/
/- HOL primality proving via Pocklington-optimized Pratt certificates.       -/
/- ========================================================================= -/
/- File: HolLibrary/Pocklington.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/pocklington.ml`, by hand, in file
  order, in the style of HolLibrary/Card.lean and HolLibrary/BitMatch.lean
  (see there and HolMath/Base.lean for the conventions).  pocklington.ml
  begins with `needs "Library/iter.ml"` and `needs "Library/prime.ml"`;
  the theorems it uses from them come through CoreThms1-4 (filled from
  SessionLibrary.Iter / SessionLibrary.Prime), and prime.ml's DIVIDES_CONV
  and COPRIME_CONV through `PocklingtonDeps`.  Each section group of
  pocklington.ml is a bundle (a `structure`) built by a `setup` function;
  SessionLibrary/Pocklington.lean builds the bundles in order and exports
  every name under its HOL Light name.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, NUMBER_RULE, INTEGER_RULE, INT_ARITH,
  SET_RULE, TAUT) they are bound first, in OCaml's order.  `let ... and ...`
  is left to right.
-/

import HolMath

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB BETA ABS INST_TYPE EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.Pocklington

/- ------------------------------------------------------------------------- -/
/- What pocklington.ml uses from the core library, iter.ml and prime.ml.     -/
/- ------------------------------------------------------------------------- -/

/-- Theorems pocklington.ml uses from the core library, prime.ml and iter.ml
    (part 1 of 4). -/
structure CoreThms1 where
  (ADD1 ADD_AC ADD_ASSOC ADD_CLAUSES ADD_EQ_0 ADD_SUB ADD_SYM ALL
   AND_FORALL_THM ARITH ARITH_EQ BETA_THM BEZOUT_GCD_STRONG CARD_CLAUSES
   CARD_DIFF CARD_IMAGE_INJ CARD_IMAGE_INJ_EQ CARD_NUMSEG_LE CARD_NUMSEG_LT
   CARD_PRODUCT CARD_SUBSET CARD_SUBSET_EQ CHINESE_REMAINDER
   COMPLETE_FACTOR_INDUCT COND_CLAUSES COND_ID CONG CONG_DIV2 CONG_LMOD
   CONG_RMOD CONJ_ASSOC CONTRAPOS_THM COPRIME_0 COPRIME_1 COPRIME_EXP
   COPRIME_GCD COPRIME_LEXP COPRIME_LMOD COPRIME_LMUL COPRIME_LMUL2
   COPRIME_MUL COPRIME_NPRODUCT COPRIME_NPRODUCT_EQ COPRIME_PRIMEPOW
   COPRIME_PRIME_PRIME COPRIME_REFL COPRIME_REXP COPRIME_RMOD COPRIME_RMUL
   COPRIME_RMUL2 COPRIME_SYM CROSS_EMPTY DE_MORGAN_THM DIVIDES_0 DIVIDES_1
   DIVIDES_ADD DIVIDES_ADD_REVL DIVIDES_ADD_REVR DIVIDES_ANTISYM
   DIVIDES_DIV_MULT DIVIDES_EXP_LE DIVIDES_EXP_LE_IMP DIVIDES_GCD
   DIVIDES_GCD_RIGHT DIVIDES_INDEX DIVIDES_LCM_RIGHT DIVIDES_LE
   DIVIDES_LE_IMP DIVIDES_LE_STRONG DIVIDES_LMUL DIVIDES_LMUL2_EQ DIVIDES_MOD
   DIVIDES_MUL : thm)
  deriving Inhabited

/-- Theorems pocklington.ml uses from the core library, prime.ml and iter.ml
    (part 2 of 4). -/
structure CoreThms2 where
  (DIVIDES_MUL2 DIVIDES_ONE DIVIDES_PRIME_PRIME DIVIDES_REFL DIVIDES_REXP
   DIVIDES_RMUL DIVIDES_RMUL2_EQ DIVIDES_SUB DIVIDES_TRANS DIVIDES_ZERO
   DIVISION DIVISION_0 DIVISION_SIMP DIV_0 DIV_EQ_0 DIV_MONO DIV_MULT
   DIV_UNIQ EMPTY_GSPEC EQ_ADD_RCANCEL EQ_IMP EQ_MULT_LCANCEL EQ_MULT_RCANCEL
   EQ_TRANS EVEN EVEN_EXISTS EVEN_EXP EVEN_MULT EVEN_SUB EXISTS_IN_IMAGE
   EXISTS_PAIR_THM EXISTS_REFL EXISTS_UNIQUE EXISTS_UNIQUE_THM EXP EXP_1
   EXP_2 EXP_ADD EXP_EQ_0 EXP_EQ_1 EXP_EXP EXP_MONO_LE EXP_MULT EXP_ONE
   EXTENSION FINITE_DIVISORS FINITE_EMPTY FINITE_IMAGE FINITE_INDUCT_STRONG
   FINITE_NUMSEG FINITE_NUMSEG_LE FINITE_NUMSEG_LT FINITE_RULES
   FINITE_SPECIAL_DIVISORS FINITE_SUBSET FORALL_AND_THM FORALL_IN_IMAGE
   FORALL_IN_INSERT FORALL_PAIR_THM FORALL_UNWIND_THM1 FUN_EQ_THM GCD GCD_0
   GCD_SYM GCD_ZERO HAS_SIZE HAS_SIZE_0 HAS_SIZE_CROSS HAS_SIZE_IMAGE_INJ
   HAS_SIZE_IMAGE_INJ_EQ HAS_SIZE_NUMSEG_LT IMAGE_CLAUSES IMAGE_EQ_EMPTY : thm)
  deriving Inhabited

/-- Theorems pocklington.ml uses from the core library, prime.ml and iter.ml
    (part 3 of 4). -/
structure CoreThms3 where
  (IMP_CONJ IMP_IMP IN INDEX_EQ_0 INDEX_EXP INDEX_GCD INDEX_PRIME
   INDUCT_COPRIME_ALT INDUCT_COPRIME_STRONG INT_IMAGE INT_MUL_RZERO
   INT_OF_NUM_ADD INT_OF_NUM_EQ INT_OF_NUM_LT INT_OF_NUM_MUL INT_OF_NUM_POW
   INT_OF_NUM_SUB IN_CROSS IN_ELIM_PAIR_THM IN_ELIM_THM IN_IMAGE IN_INSERT
   IN_NUMSEG IN_SING ITER ITERATE_CLAUSES ITERATE_EQ
   ITERATE_EQ_GENERAL_INVERSES ITERATE_ITERATE_PRODUCT ITERATE_RELATED ITLIST
   LCM_0 LCM_COPRIME_DECOMP LCM_DIVIDES LE LEFT_ADD_DISTRIB
   LEFT_AND_EXISTS_THM LEFT_IMP_EXISTS_THM LEFT_SUB_DISTRIB LE_0 LE_1
   LE_ANTISYM LE_CASES LE_EXISTS LE_EXP LE_LCM LE_LT LE_MULT2 LE_MULT_LCANCEL
   LE_MULT_RCANCEL LE_RDIV_EQ LE_REFL LE_TRANS LT LT_LE LT_MULT_LCANCEL LT_NZ
   LT_REFL LT_TRANS MEM MEMBER_NOT_EMPTY MOD_2_CASES MOD_EQ_0 MOD_EQ_SELF
   MOD_EXP_MOD MOD_LT MOD_LT_EQ MOD_MOD_REFL MOD_UNIQ MOD_ZERO MONOIDAL_MUL
   MONO_AND MONO_EXISTS : thm)
  deriving Inhabited

/-- Theorems pocklington.ml uses from the core library, prime.ml and iter.ml
    (part 4 of 4). -/
structure CoreThms4 where
  (MULT_AC MULT_ASSOC MULT_CLAUSES MULT_EQ_0 MULT_EQ_1 MULT_EXP MULT_SYM
   NEUTRAL_MUL NOT_EVEN NOT_EXISTS_THM NOT_FORALL_THM NOT_IMP NOT_IN_EMPTY
   NOT_LT NOT_ODD NOT_SUC NPRODUCT_CLAUSES ODD_EXISTS ORDER_EXISTENCE_ITER
   OR_EXISTS_THM PAIRWISE_EMPTY PAIRWISE_INSERT PAIR_EQ PRIME
   PRIMEPOW_DIVIDES_INDEX PRIME_0 PRIME_1 PRIME_2 PRIME_COPRIME
   PRIME_COPRIME_EQ PRIME_DIVEXP_EQ PRIME_DIVPROD_POW_EQ
   PRIME_DIVPROD_POW_GEN_EQ PRIME_EXP PRIME_FACTOR PRIME_FACTORIZATION
   PRIME_GE_2 PRIME_IMP_NZ PRIME_ODD RDIV_LT_EQ RIGHT_AND_EXISTS_THM
   RIGHT_FORALL_IMP_THM RIGHT_IMP_FORALL_THM RIGHT_SUB_DISTRIB SUBSET
   SUBSET_ANTISYM SUBSET_ANTISYM_EQ SUB_0 SUB_ADD SUB_REFL
   SURJECTIVE_IFF_INJECTIVE_GEN SWAP_EXISTS_THM SWAP_FORALL_THM
   UNIQUE_SKOLEM_THM UNWIND_THM2 cong coprime divides index_def int_congruent
   int_of_num nproduct num_FINITE num_INDUCTION num_MAX num_WOP num_congruent
   num_divides pairwise prime
   MOD_LE MOD_MULT PRIME_DIVPROD ALL_IMP ALL_MEM num_WF LT_MULT_RCANCEL : thm)
  deriving Inhabited

/-- What pocklington.ml uses from Session and prime.ml besides theorems. -/
structure PocklingtonDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  prioritize_num : IO Unit
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  ASM_MESON_TAC : List thm → tactic
  INDUCT_TAC : tactic
  INTEGER_RULE : term → ExceptT String IO thm
  INT_ARITH : term → ExceptT String IO thm
  INT_ARITH_TAC : tactic
  LIST_INDUCT_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  NUMBER_RULE : term → ExceptT String IO thm
  NUMBER_TAC : tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  -- conversions (prime.ml's DIVIDES_CONV and COPRIME_CONV among them)
  DIVIDES_CONV : ioconv
  COPRIME_CONV : ioconv
  EXP_MOD_CONV : ioconv
  NUM_DIV_CONV : ioconv
  NUM_EQ_CONV : ioconv
  NUM_LE_CONV : ioconv
  NUM_MULT_CONV : ioconv
  NUM_REDUCE_CONV : ioconv
  NUM_SUB_CONV : ioconv
  SELECT_CONV : ioconv
  num_CONV : ioconv
  -- syntax
  mk_numeral : Rat → Except String term
  mk_small_numeral : Int → Except String term
  mk_flist : List term → IO (Except String term)
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  core4 : CoreThms4

/-- `num_0`, `num_1`, `num_2` (pocklington.ml 10-12; lib.ml's `num_0` is
    rebound to the same value). -/
def num_0 : Rat := 0
def num_1 : Rat := 1
def num_2 : Rat := 2

/- ------------------------------------------------------------------------- -/
/- Compatibility lemmas, lemmas, congruences, order cases, CONG_CONV.         -/
/- (pocklington.ml 14-423)                                                    -/
/- ------------------------------------------------------------------------- -/

structure Basics where
  -- @@FIELDS
  nat_mod_lemma : thm
  nat_mod : thm
  FINITE_NUMBER_SEGMENT : thm
  CONG_MOD_0 : thm
  CONG_MOD_1 : thm
  CONG_MOD_2 : thm
  CONG_MOD_2_ALT : thm
  CONG_0 : thm
  CONG_SUB_CASES : thm
  CONG_MINUS1 : thm
  CONG_MINUS1_SQUARED : thm
  CONG_CASES : thm
  CONG_CASE : thm
  CONG_MULT_LCANCEL : thm
  CONG_MULT_RCANCEL : thm
  CONG_REFL : thm
  EQ_IMP_CONG : thm
  CONG_SYM : thm
  CONG_TRANS : thm
  CONG_ADD : thm
  CONG_MULT : thm
  CONG_MULT_1 : thm
  CONG_EXP : thm
  CONG_EXP_1 : thm
  CONG_SUB : thm
  CONG_MULT_LCANCEL_EQ : thm
  CONG_MULT_RCANCEL_EQ : thm
  CONG_ADD_LCANCEL_EQ : thm
  CONG_ADD_RCANCEL_EQ : thm
  CONG_ADD_RCANCEL : thm
  CONG_ADD_LCANCEL : thm
  CONG_ADD_LCANCEL_EQ_0 : thm
  CONG_ADD_RCANCEL_EQ_0 : thm
  CONG_MULT_LCANCEL_ALL : thm
  CONG_LMUL : thm
  CONG_RMUL : thm
  CONG_IMP_EQ : thm
  CONG_DIVIDES_MODULUS : thm
  CONG_0_DIVIDES : thm
  CONG_1_DIVIDES : thm
  CONG_1_DIVIDES_EQ : thm
  CONG_DIVIDES : thm
  CONG_COPRIME : thm
  CONG_GCD_RIGHT : thm
  CONG_GCD_LEFT : thm
  CONG_MOD : thm
  MOD_MULT_CONG : thm
  CONG_MOD_LT : thm
  MOD_UNIQUE : thm
  CONG_DIV : thm
  CONG_DIV_COPRIME : thm
  CONG_SQUARE_1_PRIME_POWER : thm
  CONG_LT : thm
  CONG_LE : thm
  CONG_TO_1 : thm
  EVEN_MOD_2 : thm
  ODD_MOD_2 : thm
  CONG_CONV : term → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupBasics [HolBase] (D : PocklingtonDeps) :
    ExceptT String IO Basics := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, DIVIDES_CONV, INDUCT_TAC,
        INTEGER_RULE, INT_ARITH, INT_ARITH_TAC, MESON_TAC, NUMBER_RULE, NUMBER_TAC,
        NUM_LE_CONV, NUM_REDUCE_CONV, NUM_SUB_CONV, prioritize_num, .. } := D
  let { ADD1, ADD_AC, ADD_CLAUSES, ADD_SYM, ARITH, CARD_CLAUSES, COND_CLAUSES, CONG,
        CONG_DIV2, COPRIME_0, DIVIDES_0, DIVIDES_GCD, .. } := D.core1
  let { DIVIDES_ONE, DIVIDES_PRIME_PRIME, DIVIDES_REFL, DIVIDES_RMUL, DIVIDES_SUB,
        DIVIDES_ZERO, DIVISION, DIVISION_0, DIV_MULT, EVEN_EXISTS, EXP, EXP_EQ_0,
        EXP_EQ_1, EXP_ONE, EXTENSION, FINITE_RULES, GCD_SYM, HAS_SIZE, HAS_SIZE_0, .. } := D.core2
  let { INT_IMAGE, INT_MUL_RZERO, INT_OF_NUM_ADD, INT_OF_NUM_EQ, INT_OF_NUM_LT,
        INT_OF_NUM_MUL, INT_OF_NUM_POW, INT_OF_NUM_SUB, IN_ELIM_THM, IN_INSERT,
        LEFT_ADD_DISTRIB, LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, LEFT_SUB_DISTRIB,
        LE_1, LE_CASES, LE_EXISTS, LT, LT_REFL, MOD_2_CASES, MOD_LT, MOD_ZERO,
        MONO_EXISTS, .. } := D.core3
  let { MULT_AC, MULT_CLAUSES, MULT_EQ_0, MULT_SYM, NOT_IN_EMPTY, NOT_ODD, ODD_EXISTS,
        OR_EXISTS_THM, PRIME_0, PRIME_1, PRIME_2, PRIME_DIVPROD_POW_GEN_EQ,
        RIGHT_AND_EXISTS_THM, SUB_0, SUB_ADD, SWAP_EXISTS_THM, cong, divides,
        int_congruent, num_INDUCTION, num_congruent, num_divides, .. } := D.core4
  -- @@SCOPE END

  prioritize_num

  let nat_mod_lemma ← prove
   r"!x y n:num. (x == y) (mod n) /\ y <= x ==> ?q. x = y + n * q"
   (← do
    let a ← ARITH_RULE (← q r"x <= y ==> (y:num = x + d <=> y - x = d)")
    let i ← INTEGER_RULE (← q r"(x == y) (mod &n) <=> &n divides (x - y)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [num_congruent] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      ONCE_REWRITE_TAC [i] THEN
      ASM_SIMP_TAC [INT_OF_NUM_SUB, a] THEN
      REWRITE_TAC [← GSYM num_divides, divides]))

  let nat_mod ← prove
   r"!x y n:num. (mod n) x y <=> ?q1 q2. x + n * q1 = y + n * q2"
   (← do
    let a ← ARITH_RULE (← q "x + y * 0 = x")
    let n ← NUMBER_RULE (← q r"(x:num == y) (mod n) <=> (y == x) (mod n)")
    let t ← TAUT (← q r"a \/ b ==> c ==> d <=> (c /\ b) \/ (c /\ a) ==> d")
    pure (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM cong] THEN
      EQ_TAC THENL [ALL_TAC, NUMBER_TAC] THEN
      MP_TAC (← SPECL [← q "x:num", ← q "y:num"] LE_CASES) THEN
      REWRITE_TAC [t] THEN
      DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
       [ALL_TAC,
        ONCE_REWRITE_TAC [n]] THEN
      MESON_TAC [nat_mod_lemma, a]))

  let FINITE_NUMBER_SEGMENT ← prove
   r"!n. { m | 0 < m /\ m < n } HAS_SIZE (n - 1)"
   (INDUCT_TAC THENL
     [SUBGOAL_THEN (← q r"{m | 0 < m /\ m < 0} = EMPTY") SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY, LT], ALL_TAC] THEN
      REWRITE_TAC [HAS_SIZE, FINITE_RULES, CARD_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV,
      ASM_CASES_TAC (← q "n = 0") THENL
       [SUBGOAL_THEN (← q r"{m | 0 < m /\ m < SUC n} = EMPTY") SUBST1_TAC THENL
         [ASM_REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY] THEN
          ARITH_TAC, ALL_TAC] THEN
        ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC [HAS_SIZE_0],
        SUBGOAL_THEN (← q r"{m | 0 < m /\ m < SUC n} = n INSERT {m | 0 < m /\ m < n}")
        SUBST1_TAC THENL
         [REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_INSERT] THEN
          UNDISCH_TAC (← q "~(n = 0)") THEN ARITH_TAC, ALL_TAC] THEN
        UNDISCH_TAC (← q "~(n = 0)") THEN
        POP_ASSUM MP_TAC THEN
        SIMP_TAC [FINITE_RULES, HAS_SIZE, CARD_CLAUSES] THEN
        DISCH_TAC THEN REWRITE_TAC [IN_ELIM_THM, LT_REFL] THEN
        ARITH_TAC]])

  let CONG_MOD_0 ← prove
   r"!x y. (x == y) (mod 0) <=> (x = y)"
   (NUMBER_TAC)

  let CONG_MOD_1 ← prove
   r"!x y. (x == y) (mod 1)"
   (NUMBER_TAC)

  let CONG_MOD_2 ← prove
   r"!a b. (a == b) (mod 2) <=> (EVEN a <=> EVEN b)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [CONG, MOD_2_CASES] THEN
    ASM_CASES_TAC (← q "EVEN a") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q "EVEN b") THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC NUM_REDUCE_CONV)

  let CONG_MOD_2_ALT ← prove
   r"!a b. (a == b) (mod 2) <=> (ODD a <=> ODD b)"
   (REWRITE_TAC [CONG_MOD_2, ← GSYM NOT_ODD] THEN MESON_TAC [])

  let CONG_0 ← prove
   r"!x n. ((x == 0) (mod n) <=> n divides x)"
   (NUMBER_TAC)

  let CONG_SUB_CASES ← prove
   r"!x y n. (x == y) (mod n) <=>
           if x <= y then (y - x == 0) (mod n)
           else (x - y == 0) (mod n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [cong, nat_mod] THEN
    COND_CASES_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [SWAP_EXISTS_THM], ALL_TAC] THEN
    REPEAT (AP_TERM_TAC THEN ABS_TAC) THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC)

  let CONG_MINUS1 ← prove
   r"!a n. (a == n - 1) (mod n) <=> n = 0 /\ a = 0 \/ n divides (a + 1)"
   (← do
    let n ← NUMBER_RULE (← q r"(a == b) (mod n) <=> (a + 1 == b + 1) (mod n)")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "n = 0") THENL
     [ASM_REWRITE_TAC [SUB_0, CONG_MOD_0, DIVIDES_ZERO] THEN ARITH_TAC,
      ONCE_REWRITE_TAC [n] THEN
      ASM_SIMP_TAC [SUB_ADD, LE_1] THEN CONV_TAC NUMBER_RULE]))

  let CONG_MINUS1_SQUARED ← prove
   r"!p. ((p - 1) EXP 2 == 1) (mod p) <=> ~(p = 0)"
   (← do
    let n2 ← NUMBER_RULE (← q r"(p EXP 2 == 1 + 2 * n + 1) (mod p) <=> p divides (2 * (n + 1))")
    let n ← NUMBER_RULE (← q r"(n EXP 2 == m) (mod p) <=> ((n + 1) EXP 2 == m + 2 * n + 1) (mod p)")
    pure (GEN_TAC THEN ASM_CASES_TAC (← q "p = 0") THEN
      ASM_REWRITE_TAC [CONG_MOD_0, ARITH] THEN
      ONCE_REWRITE_TAC [n] THEN
      ASM_SIMP_TAC [SUB_ADD, LE_1, n2] THEN
      CONV_TAC NUMBER_RULE))

  let CONG_CASES ← prove
   r"!x y n. (x == y) (mod n) <=> (?q. x = q * n + y) \/ (?q. y = q * n + x)"
   (← do
    let a ← ARITH_RULE (← q r"x + a = y + b ==> x = (b - a) + y \/ y = (a - b) + x")
    pure (REPEAT GEN_TAC THEN EQ_TAC THENL
     [ALL_TAC, STRIP_TAC THEN ASM_REWRITE_TAC [] THEN NUMBER_TAC] THEN
    REWRITE_TAC [cong, nat_mod, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q "q1:num", ← q "q2:num"] THEN
    DISCH_THEN (MP_TAC o MATCH_MP a) THEN
    REWRITE_TAC [← GSYM LEFT_SUB_DISTRIB] THEN MESON_TAC [MULT_SYM]))

  let CONG_CASE ← prove
   r"!n a x:num. a < n ==> ((x == a) (mod n) <=> ?q. x = q * n + a)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [CONG_CASES, OR_EXISTS_THM] THEN
    EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [] THEN
    MATCH_MP_TAC num_INDUCTION THEN SIMP_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN
    ASM_ARITH_TAC)

  let CONG_MULT_LCANCEL ← prove
   r"!a n x y. coprime(a,n) /\ (a * x == a * y) (mod n) ==> (x == y) (mod n)"
   (NUMBER_TAC)

  let CONG_MULT_RCANCEL ← prove
   r"!a n x y. coprime(a,n) /\ (x * a == y * a) (mod n) ==> (x == y) (mod n)"
   (NUMBER_TAC)

  let CONG_REFL ← prove
   r"!x n. (x == x) (mod n)"
   (NUMBER_TAC)

  let EQ_IMP_CONG ← prove
   r"!a b n. a = b ==> (a == b) (mod n)"
   (SIMP_TAC [CONG_REFL])

  let CONG_SYM ← prove
   r"!x y n. (x == y) (mod n) <=> (y == x) (mod n)"
   (NUMBER_TAC)

  let CONG_TRANS ← prove
   r"!x y z n. (x == y) (mod n) /\ (y == z) (mod n) ==> (x == z) (mod n)"
   (NUMBER_TAC)

  let CONG_ADD ← prove
   r"!x x' y y'.
     (x == x') (mod n) /\ (y == y') (mod n) ==> (x + y == x' + y') (mod n)"
   (NUMBER_TAC)

  let CONG_MULT ← prove
   r"!x x' y y'.
     (x == x') (mod n) /\ (y == y') (mod n) ==> (x * y == x' * y') (mod n)"
   (NUMBER_TAC)

  let CONG_MULT_1 ← prove
   r"!n x y. (x == 1) (mod n) /\ (y == 1) (mod n) ==> (x * y == 1) (mod n)"
   (NUMBER_TAC)

  let CONG_EXP ← prove
   r"!n k x y. (x == y) (mod n) ==> (x EXP k == y EXP k) (mod n)"
   (GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC [CONG_MULT, EXP, CONG_REFL])

  let CONG_EXP_1 ← prove
   r"!x n k. (x == 1) (mod n) ==> (x EXP k == 1) (mod n)"
   (REPEAT GEN_TAC THEN
    DISCH_THEN (MP_TAC o SPEC (← q "k:num") o MATCH_MP CONG_EXP) THEN
    REWRITE_TAC [EXP_ONE])

  let CONG_SUB ← prove
   r"!x x' y y'.
     (x == x') (mod n) /\ (y == y') (mod n) /\ y <= x /\ y' <= x'
     ==> (x - y == x' - y') (mod n)"
   (← do
    let a ← ARITH_RULE (← q r"(x + a = x' + a') /\ (y + b = y' + b') /\ y <= x /\ y' <= x'
    ==> ((x - y) + (a + b') = (x' - y') + (a' + b))")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [cong, nat_mod] THEN
      REWRITE_TAC [LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
      DISCH_THEN (MP_TAC o MATCH_MP a) THEN
      REWRITE_TAC [← GSYM LEFT_ADD_DISTRIB] THEN MESON_TAC []))

  let CONG_MULT_LCANCEL_EQ ← prove
   r"!a n x y. coprime(a,n) ==> ((a * x == a * y) (mod n) <=> (x == y) (mod n))"
   (NUMBER_TAC)

  let CONG_MULT_RCANCEL_EQ ← prove
   r"!a n x y. coprime(a,n) ==> ((x * a == y * a) (mod n) <=> (x == y) (mod n))"
   (NUMBER_TAC)

  let CONG_ADD_LCANCEL_EQ ← prove
   r"!a n x y. (a + x == a + y) (mod n) <=> (x == y) (mod n)"
   (NUMBER_TAC)

  let CONG_ADD_RCANCEL_EQ ← prove
   r"!a n x y. (x + a == y + a) (mod n) <=> (x == y) (mod n)"
   (NUMBER_TAC)

  let CONG_ADD_RCANCEL ← prove
   r"!a n x y. (x + a == y + a) (mod n) ==> (x == y) (mod n)"
   (NUMBER_TAC)

  let CONG_ADD_LCANCEL ← prove
   r"!a n x y. (a + x == a + y) (mod n) ==> (x == y) (mod n)"
   (NUMBER_TAC)

  let CONG_ADD_LCANCEL_EQ_0 ← prove
   r"!a n x. (a + x == a) (mod n) <=> (x == 0) (mod n)"
   (NUMBER_TAC)

  let CONG_ADD_RCANCEL_EQ_0 ← prove
   r"!a n x. (x + a == a) (mod n) <=> (x == 0) (mod n)"
   (NUMBER_TAC)

  let CONG_MULT_LCANCEL_ALL ← prove
   r"!a x y n. (a * x == a * y) (mod (a * n)) <=> a = 0 \/ (x == y) (mod n)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "a = 0") THEN ASM_REWRITE_TAC [] THEN
    POP_ASSUM MP_TAC THEN NUMBER_TAC)

  let CONG_LMUL ← NUMBER_RULE (← q
   r"!a x y n:num. (x == y) (mod n) ==> (a * x == a * y) (mod n)")

  let CONG_RMUL ← NUMBER_RULE (← q
   r"!x y a n:num. (x == y) (mod n) ==> (x * a == y * a) (mod n)")

  let CONG_IMP_EQ ← prove
   r"!x y n. x < n /\ y < n /\ (x == y) (mod n) ==> x = y"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "n = 0") THEN ASM_REWRITE_TAC [LT] THEN
    ASM_MESON_TAC [CONG, MOD_LT])

  let CONG_DIVIDES_MODULUS ← prove
   r"!x y m n. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)"
   (NUMBER_TAC)

  let CONG_0_DIVIDES ← prove
   r"!n x. (x == 0) (mod n) <=> n divides x"
   (NUMBER_TAC)

  let CONG_1_DIVIDES ← prove
   r"!n x. (x == 1) (mod n) ==> n divides (x - 1)"
   (← do
    let a ← ARITH_RULE (← q r"(x + q1 = 1 + q2) ==> ~(x = 0) ==> (x - 1 = q2 - q1)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [divides, cong, nat_mod] THEN
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
      DISCH_THEN (MP_TAC o MATCH_MP a) THEN
      ASM_CASES_TAC (← q "x = 0") THEN
      ASM_REWRITE_TAC [ARITH, ← GSYM LEFT_SUB_DISTRIB] THEN
      ASM_MESON_TAC [MULT_CLAUSES]))

  let CONG_1_DIVIDES_EQ ← prove
   r"!n x. (x == 1) (mod n) <=> (x = 0 ==> n = 1) /\ n divides (x - 1)"
   (← do
    let n ← NUMBER_RULE (← q r"(0 == a) (mod n) <=> n divides a")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "x = 0") THEN ASM_REWRITE_TAC [] THENL
     [REWRITE_TAC [n] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [DIVIDES_ONE, DIVIDES_0],
      ONCE_REWRITE_TAC [CONG_SYM] THEN ONCE_REWRITE_TAC [CONG_SUB_CASES] THEN
      ASM_SIMP_TAC [LE_1] THEN CONV_TAC NUMBER_RULE]))

  let CONG_DIVIDES ← prove
   r"!x y n. (x == y) (mod n) ==> (n divides x <=> n divides y)"
   (NUMBER_TAC)

  let CONG_COPRIME ← prove
   r"!x y n. (x == y) (mod n) ==> (coprime(n,x) <=> coprime(n,y))"
   (NUMBER_TAC)

  let CONG_GCD_RIGHT ← prove
   r"!x y n. (x == y) (mod n) ==> gcd(n,x) = gcd(n,y)"
   (NUMBER_TAC)

  let CONG_GCD_LEFT ← prove
   r"!x y n. (x == y) (mod n) ==> gcd(x,n) = gcd(y,n)"
   (NUMBER_TAC)

  let CONG_MOD ← prove
   r"!a n. (a MOD n == a) (mod n)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "n = 0") THEN
    ASM_REWRITE_TAC [CONG_REFL, MOD_ZERO] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP DIVISION) THEN
    DISCH_THEN (MP_TAC o SPEC (← q "a:num")) THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN (fun th => GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC [cong, nat_mod] THEN
    MAP_EVERY EXISTS_TAC [← q "a DIV n", ← q "0"] THEN
    REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES, ADD_AC, MULT_AC])

  let MOD_MULT_CONG ← prove
   r"!a b x y. ((x MOD (a * b) == y) (mod a) <=> (x == y) (mod a))"
   (REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q r"(x MOD (a * b) == x) (mod a)")
     (fun th => MESON_TAC [th, CONG_TRANS, CONG_SYM]) THEN
    MATCH_MP_TAC CONG_DIVIDES_MODULUS THEN EXISTS_TAC (← q "a * b") THEN
    ASM_SIMP_TAC [CONG_MOD, MULT_EQ_0, DIVIDES_RMUL, DIVIDES_REFL])

  let CONG_MOD_LT ← prove
   r"!y. y < n ==> (x MOD n = y <=> (x == y) (mod n))"
   (MESON_TAC [MOD_LT, CONG, LT])

  let MOD_UNIQUE ← prove
   r"!m n p. m MOD n = p <=> ((n = 0 /\ m = p) \/ p < n) /\ (m == p) (mod n)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "n = 0") THEN
    ASM_REWRITE_TAC [CONG_MOD_0, LT] THENL
     [ASM_MESON_TAC [DIVISION_0], ALL_TAC] THEN
    ASM_SIMP_TAC [CONG] THEN ASM_MESON_TAC [DIVISION, MOD_LT])

  let CONG_DIV ← prove
   r"!m n a b.
        ~(m = 0) /\ (a == m * b) (mod (m * n)) ==> (a DIV m == b) (mod n)"
   (MESON_TAC [CONG_DIV2, DIV_MULT])

  let CONG_DIV_COPRIME ← prove
   r"!m n a b.
        coprime(m,n) /\ m divides a /\ (a == m * b) (mod n)
        ==> (a DIV m == b) (mod n)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "m = 0") THEN
    ASM_SIMP_TAC [COPRIME_0, CONG_MOD_1] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC CONG_DIV THEN
    REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC NUMBER_RULE)

  let CONG_SQUARE_1_PRIME_POWER ← prove
   r"!p k x.
        prime p /\ ~(p = 2)
        ==> ((x EXP 2 == 1) (mod (p EXP k)) <=>
             (x == 1) (mod (p EXP k)) \/ (x == p EXP k - 1) (mod (p EXP k)))"
   (← do
    let a ← ARITH_RULE (← q r"~(x = 0) ==> (x + 1) - (x - 1) = 2")
    pure (REPEAT GEN_TAC THEN
      ASM_CASES_TAC (← q "k = 0") THEN ASM_REWRITE_TAC [EXP, CONG_MOD_1] THEN
      ASM_CASES_TAC (← q "p = 0") THEN ASM_REWRITE_TAC [PRIME_0] THEN
      ASM_CASES_TAC (← q "p = 1") THEN ASM_REWRITE_TAC [PRIME_1] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [CONG_MINUS1, CONG_1_DIVIDES_EQ] THEN
      ASM_REWRITE_TAC [EXP_EQ_0, EXP_EQ_1] THEN
      ASM_CASES_TAC (← q "x = 0") THEN
      ASM_REWRITE_TAC [ADD_CLAUSES, DIVIDES_ONE, EXP_EQ_1, ARITH] THEN
      SUBGOAL_THEN (← q "x EXP 2 - 1 = (x - 1) * (x + 1)") SUBST1_TAC THENL
       [REWRITE_TAC [← GSYM INT_OF_NUM_EQ, ← GSYM INT_OF_NUM_MUL] THEN
        ASM_SIMP_TAC [← GSYM INT_OF_NUM_SUB, EXP_EQ_0, LE_1] THEN
        REWRITE_TAC [← GSYM INT_OF_NUM_ADD, ← GSYM INT_OF_NUM_POW] THEN
        INT_ARITH_TAC,
        MATCH_MP_TAC PRIME_DIVPROD_POW_GEN_EQ THEN ASM_REWRITE_TAC [] THEN
        ONCE_REWRITE_TAC [GCD_SYM] THEN REWRITE_TAC [DIVIDES_GCD] THEN
        DISCH_THEN (MP_TAC o MATCH_MP DIVIDES_SUB) THEN
        ASM_SIMP_TAC [a] THEN
        ASM_SIMP_TAC [DIVIDES_PRIME_PRIME, PRIME_2]]))

  let CONG_LT ← prove
   r"!x y n. y < n ==> ((x == y) (mod n) <=> ?d. x = d * n + y)"
   (← do
    let a4 ← INT_ARITH (← q r"x - (x + a):int = --a")
    let a3 ← ARITH_RULE (← q r"m = 0 \/ 1 <= m")
    let a2 ← INT_ARITH (← q r"x - y:int = n * --m ==> y = x + n * m")
    let a ← INT_ARITH (← q r"x = m * n + y <=> x - y:int = n * m")
    pure (REWRITE_TAC [← GSYM INT_OF_NUM_EQ, ← GSYM INT_OF_NUM_LT,
                ← GSYM INT_OF_NUM_ADD, ← GSYM INT_OF_NUM_MUL] THEN
      REWRITE_TAC [num_congruent, int_congruent] THEN
      REWRITE_TAC [a] THEN
      REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC, MESON_TAC []] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "d:int")) THEN
      DISJ_CASES_TAC (← SPEC (← q "d:int") INT_IMAGE) THENL [ASM_MESON_TAC [], ALL_TAC] THEN
      FIRST_X_ASSUM (X_CHOOSE_THEN (← q "m:num") SUBST_ALL_TAC) THEN
      FIRST_X_ASSUM (SUBST_ALL_TAC o MATCH_MP a2) THEN
      POP_ASSUM MP_TAC THEN DISJ_CASES_TAC a3 THEN
      ASM_REWRITE_TAC [INT_MUL_RZERO, a4] THENL
       [STRIP_TAC THEN EXISTS_TAC (← q "0") THEN INT_ARITH_TAC,
        FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [LE_EXISTS]) THEN
        DISCH_THEN (X_CHOOSE_THEN (← q "p:num") SUBST1_TAC) THEN
        REWRITE_TAC [INT_OF_NUM_ADD, INT_OF_NUM_MUL, INT_OF_NUM_LT] THEN
        ARITH_TAC]))

  let CONG_LE ← prove
   r"!x y n. y <= x ==> ((x == y) (mod n) <=> ?q. x = q * n + y)"
   (← do
    let a ← ARITH_RULE (← q r"y <= x ==> (x = a + y <=> x - y = a)")
    pure (ONCE_REWRITE_TAC [CONG_SYM] THEN ONCE_REWRITE_TAC [CONG_SUB_CASES] THEN
      SIMP_TAC [a] THEN
      REWRITE_TAC [CONG_0, divides] THEN MESON_TAC [MULT_SYM]))

  let CONG_TO_1 ← prove
   r"!a n. (a == 1) (mod n) <=> a = 0 /\ n = 1 \/ ?m. a = 1 + m * n"
   (← do
    let a3 ← ARITH_RULE (← q r"~(0 = 1 + a)")
    let a2 ← ARITH_RULE (← q r"a = 0 \/ ~(a = 0) /\ 1 <= a")
    let a ← ARITH_RULE (← q r"n = 0 \/ n = 1 + (n - 1) * 1")
    pure (REPEAT STRIP_TAC THEN
      ASM_CASES_TAC (← q "n = 1") THEN ASM_REWRITE_TAC [CONG_MOD_1] THENL
       [MESON_TAC [a], ALL_TAC] THEN
      DISJ_CASES_TAC a2 THEN
      ASM_SIMP_TAC [CONG_LE] THENL [ALL_TAC, MESON_TAC [ADD_SYM, MULT_SYM]] THEN
      ASM_MESON_TAC [CONG_SYM, CONG_0, DIVIDES_ONE, a3]))

  let EVEN_MOD_2 ← prove
   r"EVEN n <=> (n == 0) (mod 2)"
   (SIMP_TAC [EVEN_EXISTS, CONG_LT, ARITH, ADD_CLAUSES, MULT_AC])

  let ODD_MOD_2 ← prove
   r"ODD n <=> (n == 1) (mod 2)"
   (SIMP_TAC [ODD_EXISTS, CONG_LT, ARITH, ADD_CLAUSES, ADD1, MULT_AC])

  let CONG_CONV : term → ExceptT String IO thm ← do
    let pth ← prove
     r"(x == y) (mod n) <=>
     if x <= y then n divides (y - x) else n divides (x - y)"
     (ONCE_REWRITE_TAC [CONG_SUB_CASES] THEN REWRITE_TAC [CONG_0_DIVIDES])
    pure (fun tm => ExceptT.mk ((GEN_REWRITE_CONV id [pth] THENC
      RATOR_CONV (LAND_CONV NUM_LE_CONV) THENC
      GEN_REWRITE_CONV id [COND_CLAUSES] THENC
      RAND_CONV NUM_SUB_CONV THENC
      DIVIDES_CONV) tm))

  -- @@RETURN BEGIN
  return { nat_mod_lemma, nat_mod, FINITE_NUMBER_SEGMENT, CONG_MOD_0, CONG_MOD_1,
           CONG_MOD_2, CONG_MOD_2_ALT, CONG_0, CONG_SUB_CASES, CONG_MINUS1,
           CONG_MINUS1_SQUARED, CONG_CASES, CONG_CASE, CONG_MULT_LCANCEL,
           CONG_MULT_RCANCEL, CONG_REFL, EQ_IMP_CONG, CONG_SYM, CONG_TRANS, CONG_ADD,
           CONG_MULT, CONG_MULT_1, CONG_EXP, CONG_EXP_1, CONG_SUB, CONG_MULT_LCANCEL_EQ,
           CONG_MULT_RCANCEL_EQ, CONG_ADD_LCANCEL_EQ, CONG_ADD_RCANCEL_EQ,
           CONG_ADD_RCANCEL, CONG_ADD_LCANCEL, CONG_ADD_LCANCEL_EQ_0,
           CONG_ADD_RCANCEL_EQ_0, CONG_MULT_LCANCEL_ALL, CONG_LMUL, CONG_RMUL,
           CONG_IMP_EQ, CONG_DIVIDES_MODULUS, CONG_0_DIVIDES, CONG_1_DIVIDES,
           CONG_1_DIVIDES_EQ, CONG_DIVIDES, CONG_COPRIME, CONG_GCD_RIGHT, CONG_GCD_LEFT,
           CONG_MOD, MOD_MULT_CONG, CONG_MOD_LT, MOD_UNIQUE, CONG_DIV, CONG_DIV_COPRIME,
           CONG_SQUARE_1_PRIME_POWER, CONG_LT, CONG_LE, CONG_TO_1, EVEN_MOD_2, ODD_MOD_2,
           CONG_CONV }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Solving congruences, Chinese remainder, inverse_mod, INVERSE_MOD_CONV.     -/
/- (pocklington.ml 424-873)                                                   -/
/- ------------------------------------------------------------------------- -/

/-- `INVERSE_MOD_CONV`'s `gcdex` (pocklington.ml 851-856), on OCaml `num`
    (here `Rat`): `x`, `y` with `x * m + y * n = gcd(m,n)` (up to sign). -/
partial def gcdex (m n : Rat) : Rat × Rat :=
  if n < m then let (x, y) := gcdex n m; (y, x)
  else if m == 0 then (0, 1)
  else
    let q := quo_num n m
    let r := n - q * m
    let (x, y) := gcdex r m
    (y - q * x, x)

structure Solve where
  -- @@FIELDS
  CONG_SOLVE_EQ : thm
  CONG_SOLVE_LT_EQ : thm
  CONG_SOLVE : thm
  CONG_SOLVE_UNIQUE : thm
  CONG_SOLVE_UNIQUE_NONTRIVIAL : thm
  CONG_UNIQUE_INVERSE_PRIME : thm
  COUNT_CONG_SOLVE_SIMPLE : thm
  COUNT_CONG_SOLVE_GEN : thm
  COUNT_CONG_SOLVE : thm
  CONG_CHINESE : thm
  CHINESE_REMAINDER_UNIQUE : thm
  CHINESE_REMAINDER_COPRIME_UNIQUE : thm
  CHINESE_REMAINDER_USUAL : thm
  CONG_CHINESE_EQ : thm
  CHINESE_REMAINDER_COUNT : thm
  CHINESE_REMAINDER_COPRIME_COUNT : thm
  COUNT_ROOTS_MODULO_COPRIME : thm
  inverse_mod : thm
  INVERSE_MOD_BOUND : thm
  INVERSE_MOD_RMUL_GEN : thm
  INVERSE_MOD_LMUL_GEN : thm
  INVERSE_MOD_RMUL_EQ : thm
  INVERSE_MOD_LMUL_EQ : thm
  INVERSE_MOD_LMUL : thm
  INVERSE_MOD_RMUL : thm
  INVERSE_MOD_UNIQUE : thm
  INVERSE_MOD_1 : thm
  INVERSE_MOD_CONG : thm
  INVERSE_MOD_INVERSE_MOD_CONG : thm
  INVERSE_MOD_INVERSE_MOD : thm
  INVERSE_MOD_NONZERO_ALT : thm
  INVERSE_MOD_NONZERO : thm
  INVERSE_MOD_BOUND_LE : thm
  INVERSE_MOD_INVERSION : thm
  INVERSE_MOD_CONV : term → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupSolve [HolBase] (D : PocklingtonDeps) (BBasics : Basics) :
    ExceptT String IO Solve := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC,
        NUMBER_RULE, NUMBER_TAC, NUM_REDUCE_CONV, SELECT_CONV, SET_RULE, mk_numeral,
        new_definition, .. } := D
  let { ADD_ASSOC, ADD_CLAUSES, ADD_EQ_0, AND_FORALL_THM, ARITH, ARITH_EQ,
        BEZOUT_GCD_STRONG, CARD_CLAUSES, CHINESE_REMAINDER, COND_ID, CONG, CONG_LMOD,
        CONG_RMOD, CONTRAPOS_THM, COPRIME_0, COPRIME_1, COPRIME_GCD, COPRIME_MUL,
        COPRIME_RMOD, COPRIME_SYM, CROSS_EMPTY, DIVIDES_GCD, DIVIDES_LE, DIVIDES_MUL, .. } := D.core1
  let { DIVIDES_ONE, DIVIDES_REFL, DIVISION, DIVISION_SIMP, EMPTY_GSPEC,
        EQ_ADD_RCANCEL, EQ_IMP, EQ_MULT_RCANCEL, EQ_TRANS, EXISTS_PAIR_THM,
        EXISTS_REFL, EXISTS_UNIQUE, EXISTS_UNIQUE_THM, FINITE_EMPTY, FORALL_IN_IMAGE,
        FORALL_PAIR_THM, FUN_EQ_THM, GCD_0, GCD_SYM, HAS_SIZE, HAS_SIZE_0,
        HAS_SIZE_CROSS, HAS_SIZE_IMAGE_INJ, HAS_SIZE_IMAGE_INJ_EQ, HAS_SIZE_NUMSEG_LT, .. } := D.core2
  let { IMP_CONJ, IN_CROSS, IN_ELIM_THM, IN_IMAGE, LEFT_ADD_DISTRIB,
        LEFT_IMP_EXISTS_THM, LE_1, LE_LT, LE_MULT_LCANCEL, LE_MULT_RCANCEL, LE_REFL,
        LT, LT_REFL, MOD_EQ_SELF, MOD_EXP_MOD, MOD_LT, MOD_LT_EQ, MOD_MOD_REFL,
        MONO_AND, MONO_EXISTS, .. } := D.core3
  let { MULT_ASSOC, MULT_CLAUSES, MULT_EQ_0, MULT_EQ_1, MULT_SYM, NOT_LT, PAIR_EQ,
        PRIME_0, PRIME_1, PRIME_COPRIME, RDIV_LT_EQ, SUBSET, SUBSET_ANTISYM_EQ,
        UNIQUE_SKOLEM_THM, cong, coprime, divides, .. } := D.core4
  let { CONG_0, CONG_COPRIME, CONG_GCD_RIGHT, CONG_IMP_EQ, CONG_MOD_0, CONG_MOD_1,
        CONG_MULT, CONG_MULT_LCANCEL, CONG_REFL, CONG_SUB_CASES, CONG_SYM, CONG_TO_1,
        CONG_TRANS, MOD_MULT_CONG, nat_mod, .. } := BBasics
  -- @@SCOPE END

  let CONG_SOLVE_EQ ← prove
   r"!n a b. (?x. (a * x == b) (mod n)) <=> gcd(a,n) divides b"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [NUMBER_TAC, ALL_TAC] THEN
    ASM_CASES_TAC (← q "a = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES, GCD_0]
    THENL [NUMBER_TAC, REWRITE_TAC [divides, LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC (← q "c:num") THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q "n:num") o MATCH_MP BEZOUT_GCD_STRONG) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q "x:num", ← q "y:num"] THEN STRIP_TAC THEN
    EXISTS_TAC (← q "c * x:num") THEN POP_ASSUM MP_TAC THEN CONV_TAC NUMBER_RULE)

  let CONG_SOLVE_LT_EQ ← prove
   r"!n a b. (?x. x < n /\ (a * x == b) (mod n)) <=>
           ~(n = 0) /\ gcd(a,n) divides b"
   (← do
    let n ← NUMBER_RULE
      (← q r"(x == y) (mod n) ==> (a * x == b) (mod n) ==> (a * y == b) (mod n)")
    let m ← MESON [DIVISION]
      (← q r"~(n = 0) /\ (!y. P y ==> P(y MOD n))
    ==> ((?y. y < n /\ P y) <=> (?y. P y))")
    pure (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q "n = 0") THEN
      ASM_REWRITE_TAC [← CONJUNCT1 LT] THEN REWRITE_TAC [← GSYM CONG_SOLVE_EQ] THEN
      MATCH_MP_TAC m THEN
      ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q "x:num") THEN MATCH_MP_TAC n THEN
      ASM_SIMP_TAC [CONG_RMOD, CONG_REFL]))

  let CONG_SOLVE ← prove
   r"!a b n. coprime(a,n) ==> ?x. (a * x == b) (mod n)"
   (REWRITE_TAC [CONG_SOLVE_EQ] THEN CONV_TAC NUMBER_RULE)

  let CONG_SOLVE_UNIQUE ← prove
   r"!a b n. coprime(a,n) /\ ~(n = 0) ==> ?!x. x < n /\ (a * x == b) (mod n)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [EXISTS_UNIQUE] THEN
    MP_TAC (← SPECL [← q "a:num", ← q "b:num", ← q "n:num"] CONG_SOLVE) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (X_CHOOSE_TAC (← q "x:num")) THEN
    EXISTS_TAC (← q "x MOD n") THEN
    MATCH_MP_TAC (← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")) THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [DIVISION] THEN MATCH_MP_TAC CONG_TRANS THEN
      EXISTS_TAC (← q "a * x:num") THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC CONG_MULT THEN REWRITE_TAC [CONG_REFL] THEN
      ASM_SIMP_TAC [CONG, MOD_MOD_REFL],
      ALL_TAC] THEN
    STRIP_TAC THEN X_GEN_TAC (← q "y:num") THEN STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q "y MOD n") THEN CONJ_TAC THENL
     [ASM_SIMP_TAC [MOD_LT], ALL_TAC] THEN
    ASM_SIMP_TAC [← GSYM CONG] THEN MATCH_MP_TAC CONG_MULT_LCANCEL THEN
    EXISTS_TAC (← q "a:num") THEN ASM_MESON_TAC [CONG_TRANS, CONG_SYM])

  let CONG_SOLVE_UNIQUE_NONTRIVIAL ← prove
   r"!a p x. prime p /\ coprime(p,a) /\ 0 < x /\ x < p
           ==> ?!y. 0 < y /\ y < p /\ (x * y == a) (mod p)"
   (← do
    -- right to left: the three ARITH_RULEs, last first
    let r3 ← ARITH_RULE (← q r"~(p = 0) ==> 0 < p")
    let r2 ← ARITH_RULE (← q r"0 < r <=> ~(r = 0)")
    let r1 ← ARITH_RULE (← q r"1 < p <=> ~(p = 0) /\ ~(p = 1)")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "p = 0") THEN ASM_REWRITE_TAC [PRIME_0] THEN
    REPEAT STRIP_TAC THEN SUBGOAL_THEN (← q "1 < p") ASSUME_TAC THENL
     [REWRITE_TAC [r1] THEN
      ASM_MESON_TAC [PRIME_1],
      ALL_TAC] THEN
    MP_TAC (← SPECL [← q "x:num", ← q "a:num", ← q "p:num"] CONG_SOLVE_UNIQUE) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [PRIME_0]] THEN
      ONCE_REWRITE_TAC [COPRIME_SYM] THEN
      MP_TAC (← SPECL [← q "x:num", ← q "p:num"] PRIME_COPRIME) THEN
      ASM_CASES_TAC (← q "x = 1") THEN ASM_REWRITE_TAC [COPRIME_1] THEN
      ASM_MESON_TAC [COPRIME_SYM, NOT_LT, DIVIDES_LE, LT_REFL],
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
    X_GEN_TAC (← q "r:num") THEN REWRITE_TAC [] THEN
    REWRITE_TAC [r2] THEN
    ASM_CASES_TAC (← q "r = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN
    ASM_SIMP_TAC [r3] THEN
    ONCE_REWRITE_TAC [CONG_SYM] THEN REWRITE_TAC [CONG_0] THEN
    ASM_MESON_TAC [DIVIDES_REFL, PRIME_1, coprime]))

  let CONG_UNIQUE_INVERSE_PRIME ← prove
   r"!p x. prime p /\ 0 < x /\ x < p
         ==> ?!y. 0 < y /\ y < p /\ (x * y == 1) (mod p)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_SOLVE_UNIQUE_NONTRIVIAL THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [COPRIME_1, COPRIME_SYM])

  let COUNT_CONG_SOLVE_SIMPLE ← prove
   r"!m n b. {x | x < m * n /\ (x == b) (mod n)} HAS_SIZE
           (if n = 0 then 0 else m)"
   (← do
    let a ← ARITH_RULE
      (← q r"b < n /\ (i + 1) * n <= m * n ==> i * n + b < m * n")
    let n ← NUMBER_RULE (← q r"(x * n + c:num == b) (mod n) <=> (c == b) (mod n)")
    pure (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC [MULT_CLAUSES, LT, HAS_SIZE_0, EMPTY_GSPEC] THEN
      SUBGOAL_THEN
       (← q r"{x | x < m * n /\ (x == b) (mod n)} =
    IMAGE (\i. i * n + b MOD n) {i | i < m}")
      SUBST1_TAC THENL
       [REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET, FORALL_IN_IMAGE] THEN
        REWRITE_TAC [IN_ELIM_THM, IN_IMAGE] THEN CONJ_TAC THENL
         [X_GEN_TAC (← q "x:num") THEN REWRITE_TAC [CONG] THEN
          DISCH_THEN (STRIP_ASSUME_TAC o GSYM) THEN EXISTS_TAC (← q "x DIV n") THEN
          ASM_SIMP_TAC [RDIV_LT_EQ, DIVISION_SIMP] THEN ASM_MESON_TAC [MULT_SYM],
          X_GEN_TAC (← q "i:num") THEN DISCH_TAC THEN
          REWRITE_TAC [CONG_LMOD, CONG_REFL, n] THEN
          MATCH_MP_TAC a THEN
          ASM_REWRITE_TAC [MOD_LT_EQ, LE_MULT_RCANCEL] THEN ASM_ARITH_TAC],
        MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
        REWRITE_TAC [IN_ELIM_THM, HAS_SIZE_NUMSEG_LT] THEN
        ASM_SIMP_TAC [EQ_ADD_RCANCEL, EQ_MULT_RCANCEL]]))

  let COUNT_CONG_SOLVE_GEN ← prove
   r"!m n a b.
        {x | x < m * n /\ (a * x == b) (mod n)} HAS_SIZE
        (if ~(n = 0) /\ gcd(n,a) divides b then m * gcd(n,a) else 0)"
   (← do
    let n ← NUMBER_RULE (← q "gcd(n:num,a) divides n")
    pure (REPEAT GEN_TAC THEN
      MAP_EVERY ASM_CASES_TAC [← q "m = 0", ← q "n = 0"] THEN
      ASM_REWRITE_TAC [LT, EMPTY_GSPEC, HAS_SIZE_0, MULT_CLAUSES, COND_ID] THEN
      COND_CASES_TAC THENL
       [ALL_TAC,
        REWRITE_TAC [HAS_SIZE_0, ← SET_RULE (← q r"{x | P x} = {} <=> ~(?x. P x)")] THEN
        ASM_MESON_TAC [CONG_SOLVE_EQ, GCD_SYM]] THEN
      MP_TAC (← SPECL [← q "n:num", ← q "a:num", ← q "b:num"] CONG_SOLVE_EQ) THEN
      DISCH_THEN (fun th => tactic_of do
        let p ← EQ_IMP_RULE th; pure (MP_TAC p.2)) THEN
      ANTS_TAC THENL [ASM_MESON_TAC [GCD_SYM], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "z:num") MP_TAC) THEN REWRITE_TAC [CONG] THEN
      DISCH_THEN (fun th => tactic_of do
        pure (REWRITE_TAC [← SYM th])) THEN REWRITE_TAC [← GSYM CONG] THEN
      MP_TAC n THEN
      REWRITE_TAC [divides, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q "d:num") THEN DISCH_THEN (ASSUME_TAC o SYM) THEN
      SUBGOAL_THEN (← q r"!x:num. (a * x == a * z) (mod n) <=> (x == z) (mod d)")
       (fun th => REWRITE_TAC [th])
      THENL [REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC NUMBER_RULE, ALL_TAC] THEN
      EXPAND_TAC "n" THEN REWRITE_TAC [MULT_ASSOC, HAS_SIZE] THEN
      REWRITE_TAC [← REWRITE_RULE [HAS_SIZE] COUNT_CONG_SOLVE_SIMPLE] THEN
      ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [MULT_CLAUSES]))

  let COUNT_CONG_SOLVE ← prove
   r"!n a b. {x | x < n /\ (a * x == b) (mod n)} HAS_SIZE
           (if ~(n = 0) /\ gcd(n,a) divides b then gcd(n,a) else 0)"
   (MP_TAC (← SPEC (← q "1") COUNT_CONG_SOLVE_GEN) THEN
    REWRITE_TAC [MULT_CLAUSES, ARITH_EQ])

  let CONG_CHINESE ← prove
   r"coprime(a,b) /\ (x == y) (mod a) /\ (x == y) (mod b)
   ==> (x == y) (mod (a * b))"
   (ONCE_REWRITE_TAC [CONG_SUB_CASES] THEN MESON_TAC [CONG_0, DIVIDES_MUL])

  let CHINESE_REMAINDER_UNIQUE ← prove
   r"!a b m n.
        coprime(a,b) /\ ~(a = 0) /\ ~(b = 0)
        ==> ?!x. x < a * b /\ (x == m) (mod a) /\ (x == n) (mod b)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
     [MP_TAC (← SPECL [← q "a:num", ← q "b:num", ← q "m:num", ← q "n:num"] CHINESE_REMAINDER) THEN
      ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [← q "x:num", ← q "q1:num", ← q "q2:num"] THEN
      DISCH_TAC THEN EXISTS_TAC (← q "x MOD (a * b)") THEN
      CONJ_TAC THENL [ASM_MESON_TAC [DIVISION, MULT_EQ_0], ALL_TAC] THEN
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM (SUBST1_TAC o CONJUNCT1),
        FIRST_X_ASSUM (SUBST1_TAC o CONJUNCT2)] THEN
      ASM_SIMP_TAC [MOD_MULT_CONG] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
      REWRITE_TAC [cong, nat_mod, ← GSYM ADD_ASSOC, ← GSYM LEFT_ADD_DISTRIB] THEN
      MESON_TAC [],
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN
      EXISTS_TAC (← q "a * b") THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [CONG_CHINESE, CONG_SYM, CONG_TRANS]])

  let CHINESE_REMAINDER_COPRIME_UNIQUE ← prove
   r"!a b m n.
        coprime(a,b) /\ ~(a = 0) /\ ~(b = 0) /\ coprime(m,a) /\ coprime(n,b)
        ==> ?!x. coprime(x,a * b) /\ x < a * b /\
                 (x == m) (mod a) /\ (x == n) (mod b)"
   (← do
    let m ← MESON []
      (← q r"(!x. P(x) ==> Q(x)) ==> (?!x. P x) ==> ?!x. Q(x) /\ P(x)")
    pure (REPEAT STRIP_TAC THEN MP_TAC
     (← SPECL [← q "a:num", ← q "b:num", ← q "m:num", ← q "n:num"] CHINESE_REMAINDER_UNIQUE) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC m THEN
    ASM_SIMP_TAC [CHINESE_REMAINDER_UNIQUE] THEN
    ASM_MESON_TAC [CONG_COPRIME, COPRIME_SYM, COPRIME_MUL]))

  let CHINESE_REMAINDER_USUAL ← prove
   r"!a b u v:num. coprime(a,b) ==> ?x. (x == u) (mod a) /\ (x == v) (mod b)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "a = 0") THEN
    ASM_SIMP_TAC [CONG_MOD_1, COPRIME_0, CONG_MOD_0, EXISTS_REFL] THEN
    ASM_CASES_TAC (← q "b = 0") THEN
    ASM_SIMP_TAC [CONG_MOD_1, COPRIME_0, CONG_MOD_0, EXISTS_REFL] THEN
    DISCH_TAC THEN
    MP_TAC (← ISPECL [← q "a:num", ← q "b:num", ← q "u:num", ← q "v:num"] CHINESE_REMAINDER) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    MATCH_MP_TAC MONO_AND THEN SIMP_TAC [] THEN CONV_TAC NUMBER_RULE)

  let CONG_CHINESE_EQ ← prove
   r"!a b x y.
     coprime(a,b)
     ==> ((x == y) (mod (a * b)) <=> (x == y) (mod a) /\ (x == y) (mod b))"
   (NUMBER_TAC)

  let CHINESE_REMAINDER_COUNT ← prove
   r"!P Q R a b m n.
        coprime(a,b) /\
        (!x. x < a * b ==> (R x <=> P (x MOD a) /\ Q (x MOD b))) /\
        {x | x < a /\ P x} HAS_SIZE m /\ {x | x < b /\ Q x} HAS_SIZE n
        ==> {x | x < a * b /\ R x} HAS_SIZE (m * n)"
   (← do
    let n ← NUMBER_RULE
      (← q r"coprime(a,b)
       ==> ((x == y) (mod (a * b)) <=>
            (x == y) (mod a) /\ (x == y) (mod b))")
    let m ← MESON [HAS_SIZE_IMAGE_INJ_EQ]
      (← q r"!f. (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        IMAGE f s = t
        ==> s HAS_SIZE p ==> t HAS_SIZE p")
    pure (REPEAT GEN_TAC THEN
      REPLICATE_TAC 2 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (MP_TAC o MATCH_MP HAS_SIZE_CROSS) THEN
      ASM_CASES_TAC (← q "a = 0") THENL
       [ASM_REWRITE_TAC [LT, EMPTY_GSPEC, CROSS_EMPTY, MULT_CLAUSES,
                        HAS_SIZE, CARD_CLAUSES, FINITE_EMPTY],
        ALL_TAC] THEN
      ASM_CASES_TAC (← q "b = 0") THENL
       [ASM_REWRITE_TAC [LT, EMPTY_GSPEC, CROSS_EMPTY, MULT_CLAUSES,
                        HAS_SIZE, CARD_CLAUSES, FINITE_EMPTY],
        ALL_TAC] THEN
      MP_TAC (← ISPECL [← q "a:num", ← q "b:num"] CHINESE_REMAINDER_UNIQUE) THEN
      ASM_REWRITE_TAC [UNIQUE_SKOLEM_THM] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "f:num->num->num") o EXISTENCE) THEN
      MATCH_MP_TAC m THEN
      EXISTS_TAC (← q r"\(m,n). (f:num->num->num) m n") THEN
      REWRITE_TAC [← GSYM SUBSET_ANTISYM_EQ, SUBSET, FORALL_IN_IMAGE] THEN
      REWRITE_TAC [FORALL_PAIR_THM, IN_CROSS, IN_ELIM_THM] THEN
      REWRITE_TAC [EXISTS_PAIR_THM, IN_IMAGE, IN_CROSS] THEN
      REWRITE_TAC [IN_ELIM_THM, PAIR_EQ] THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC [CONG_IMP_EQ, CONG_SYM, CONG_TRANS],
        RULE_ASSUM_TAC (REWRITE_RULE [CONG]) THEN ASM_SIMP_TAC [MOD_LT],
        X_GEN_TAC (← q "x:num") THEN ASM_SIMP_TAC [IMP_CONJ] THEN REPEAT STRIP_TAC THEN
        MAP_EVERY EXISTS_TAC [← q "x MOD a", ← q "x MOD b"] THEN
        CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [MOD_LT, MOD_LT_EQ]] THEN
        MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC (← q "a * b:num") THEN
        ASM_REWRITE_TAC [] THEN
        ASM_SIMP_TAC [n] THEN
         ASM_MESON_TAC [MOD_LT, MOD_LT_EQ, CONG]]))

  let CHINESE_REMAINDER_COPRIME_COUNT ← prove
   r"!P Q R a b m n.
        coprime(a,b) /\
        (!x. x < a * b ==> (R x <=> P (x MOD a) /\ Q (x MOD b))) /\
        {x | x < a /\ coprime(a,x) /\ P x} HAS_SIZE m /\
        {x | x < b /\ coprime(b,x) /\ Q x} HAS_SIZE n
        ==> {x | x < a * b /\ coprime(a * b,x) /\ R x} HAS_SIZE (m * n)"
   (← do
    let n ← NUMBER_RULE
      (← q r"coprime(a:num,b)
    ==> (coprime(a * b,x) <=> coprime(a,x) /\ coprime(b,x))")
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC CHINESE_REMAINDER_COUNT THEN
      EXISTS_TAC (← q r"\x:num. coprime(a,x) /\ P x") THEN
      EXISTS_TAC (← q r"\x:num. coprime(b,x) /\ Q x") THEN
      ASM_SIMP_TAC [COPRIME_RMOD, n] THEN
      MESON_TAC []))

  let COUNT_ROOTS_MODULO_COPRIME ← prove
   r"!a b k m n.
        coprime(a,b) /\
        {x | x < a /\ (x EXP k == 1) (mod a)} HAS_SIZE m /\
        {x | x < b /\ (x EXP k == 1) (mod b)} HAS_SIZE n
        ==> {x | x < a * b /\ (x EXP k == 1) (mod (a * b))} HAS_SIZE (m * n)"
   (← do
    let n ← NUMBER_RULE
      (← q r"coprime(a,b)
       ==> ((x == y) (mod (a * b)) <=>
            (x == y) (mod a) /\ (x == y) (mod b))")
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC CHINESE_REMAINDER_COUNT THEN
      EXISTS_TAC (← q r"\x. (x EXP k == 1) (mod a)") THEN
      EXISTS_TAC (← q r"\x. (x EXP k == 1) (mod b)") THEN
      ASM_SIMP_TAC [n] THEN
      REWRITE_TAC [CONG, MOD_EXP_MOD]))

  let inverse_mod ← new_definition
   r"inverse_mod n x =
    if n <= 1 then 1
    else @y. y < n /\ (x * y == gcd(n,x)) (mod n)"

  let (INVERSE_MOD_BOUND, INVERSE_MOD_RMUL_GEN) ← CONJ_PAIR (← prove
   r"(!n x. inverse_mod n x < n <=> 2 <= n) /\
   (!n x. (x * inverse_mod n x == gcd(n,x)) (mod n))"
   (← do
    let a2 ← ARITH_RULE (← q r"2 <= n <=> ~(n <= 1)")
    let a ← ARITH_RULE (← q r"n <= 1 ==> n = 0 \/ n = 1")
    pure (REWRITE_TAC [AND_FORALL_THM] THEN REWRITE_TAC [inverse_mod] THEN
      MAP_EVERY X_GEN_TAC [← q "n:num", ← q "x:num"] THEN ASM_CASES_TAC (← q "n <= 1") THENL
       [FIRST_X_ASSUM (DISJ_CASES_TAC o MATCH_MP a) THEN
        ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC [CONG_MOD_0, CONG_MOD_1, GCD_0, MULT_CLAUSES],
        ASM_REWRITE_TAC [a2] THEN
        CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC [CONG_SOLVE_LT_EQ] THEN
        REWRITE_TAC [GCD_SYM, DIVIDES_REFL] THEN ASM_ARITH_TAC])))

  let INVERSE_MOD_LMUL_GEN ← prove
   r"!n x. (inverse_mod n x * x == gcd(n,x)) (mod n)"
   (ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [INVERSE_MOD_RMUL_GEN])

  let INVERSE_MOD_RMUL_EQ ← prove
   r"!n x. (x * inverse_mod n x == 1) (mod n) <=> coprime(n,x)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [NUMBER_TAC, ALL_TAC] THEN
    REWRITE_TAC [COPRIME_GCD] THEN DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [INVERSE_MOD_RMUL_GEN])

  let INVERSE_MOD_LMUL_EQ ← prove
   r"!n x. (inverse_mod n x * x == 1) (mod n) <=> coprime(n,x)"
   (ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [INVERSE_MOD_RMUL_EQ])

  let INVERSE_MOD_LMUL ← prove
   r"!n x. coprime(n,x) ==> (inverse_mod n x * x == 1) (mod n)"
   (REWRITE_TAC [INVERSE_MOD_LMUL_EQ])

  let INVERSE_MOD_RMUL ← prove
   r"!n x. coprime(n,x) ==> (x * inverse_mod n x == 1) (mod n)"
   (REWRITE_TAC [INVERSE_MOD_RMUL_EQ])

  let INVERSE_MOD_UNIQUE ← prove
   r"!n a x.
        (a * x == 1) (mod n) /\ x <= n /\ ~(n = 1 /\ x = 0)
        ==> inverse_mod n a = x"
   (← do
    let n2 ← NUMBER_RULE
      (← q r"(a * x == 1) (mod n) /\ (a * y == 1) (mod n) ==> (x == y) (mod n)")
    let a ← ARITH_RULE
      (← q r"~(n = 1 /\ x = 0) ==> ~(x = n) /\ x <= n ==> ~(n = 1)")
    let n ← NUMBER_RULE (← q r"(a * n == z) (mod n) <=> n divides z")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "n = 0") THENL
     [ASM_REWRITE_TAC [CONG_MOD_0, MULT_EQ_1] THEN ARITH_TAC,
      ALL_TAC] THEN
    ASM_CASES_TAC (← q "x:num = n") THENL
     [ASM_REWRITE_TAC [n] THEN
      REWRITE_TAC [DIVIDES_ONE] THEN SIMP_TAC [inverse_mod, LE_REFL],
      REPEAT STRIP_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP a) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC (← q "n:num") THEN
    ASM_REWRITE_TAC [INVERSE_MOD_BOUND] THEN
    REPEAT (CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC]) THEN
    MATCH_MP_TAC n2 THEN
    ASM_REWRITE_TAC [INVERSE_MOD_RMUL_EQ] THEN
    UNDISCH_TAC (← q r"(a * x == 1) (mod n)") THEN CONV_TAC NUMBER_RULE))

  let INVERSE_MOD_1 ← prove
   r"!n. inverse_mod n 1 = 1"
   (GEN_TAC THEN ASM_CASES_TAC (← q "n <= 1") THENL
     [ASM_REWRITE_TAC [inverse_mod], MATCH_MP_TAC INVERSE_MOD_UNIQUE] THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"~(n <= 1) ==> 1 <= n"), ARITH_EQ] THEN
    NUMBER_TAC)

  let INVERSE_MOD_CONG ← prove
   r"!n x y. (x == y) (mod n) ==> inverse_mod n x = inverse_mod n y"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [inverse_mod] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP CONG_GCD_RIGHT) THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC (← q r"(x:num == y) (mod n)") THEN CONV_TAC NUMBER_RULE)

  let INVERSE_MOD_INVERSE_MOD_CONG ← prove
   r"!n x. coprime(n,x) ==> (inverse_mod n (inverse_mod n x) == x) (mod n)"
   (← do
    let t ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    let n ← NUMBER_RULE
      (← q r"!x'. (x * x' == 1) (mod n) /\ (x' * x'' == 1) (mod n)
         ==> (x'' == x) (mod n)")
    pure (REPEAT STRIP_TAC THEN
      MATCH_MP_TAC n THEN
      EXISTS_TAC (← q "inverse_mod n x") THEN
      MATCH_MP_TAC t THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC [INVERSE_MOD_RMUL_EQ],
        GEN_REWRITE_TAC RAND_CONV [INVERSE_MOD_RMUL_EQ] THEN
        CONV_TAC NUMBER_RULE]))

  let INVERSE_MOD_INVERSE_MOD ← prove
   r"!n x. coprime(n,x) /\ 1 <= x /\ x <= n
         ==> inverse_mod n (inverse_mod n x) = x"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC INVERSE_MOD_UNIQUE THEN
    ASM_SIMP_TAC [INVERSE_MOD_LMUL_EQ, LE_1])

  let INVERSE_MOD_NONZERO_ALT ← prove
   r"!n a. ~(n divides a) ==> ~(inverse_mod n a = 0)"
   (← do
    let n ← NUMBER_RULE (← q r"(a * 0 == b) (mod n) <=> n divides b")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [CONTRAPOS_THM] THEN DISCH_TAC THEN
      MP_TAC (← SPECL [← q "n:num", ← q "a:num"] INVERSE_MOD_RMUL_GEN) THEN
      ASM_REWRITE_TAC [n] THEN
      SIMP_TAC [DIVIDES_GCD]))

  let INVERSE_MOD_NONZERO ← prove
   r"!n a. coprime(n,a) ==> ~(inverse_mod n a = 0)"
   (← do
    let n ← NUMBER_RULE (← q r"coprime(n,a) ==> (n divides a <=> n divides 1)")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "n = 1") THENL
     [ASM_REWRITE_TAC [inverse_mod, ARITH],
      DISCH_TAC THEN MATCH_MP_TAC INVERSE_MOD_NONZERO_ALT THEN
      ASM_SIMP_TAC [DIVIDES_ONE, n]]))

  let INVERSE_MOD_BOUND_LE ← prove
   r"!n a. inverse_mod n a <= n <=> ~(n = 0)"
   (GEN_TAC THEN REWRITE_TAC [LE_LT, INVERSE_MOD_BOUND] THEN
    REWRITE_TAC [inverse_mod] THEN ARITH_TAC)

  let INVERSE_MOD_INVERSION ← prove
   r"!m n. coprime(m,n)
         ==> m * inverse_mod n m + n * inverse_mod m n = m * n + 1"
   (← do
    let a2 ← ARITH_RULE
      (← q r"m * x <= m * n /\ n * y <= n * m /\ 2 * m * n <= q * m * n
    ==> m * x + n * y = 1 + q * m * n ==> u:num = v")
    let a ← ARITH_RULE
      (← q r"a + b = 1 <=> a = 0 /\ b = 1 \/ a = 1 /\ b = 0")
    let n2 ← NUMBER_RULE (← q r"(a + m * x == 1) (mod m) <=> (a == 1) (mod m)")
    let n1 ← NUMBER_RULE (← q r"(m * x + a == 1) (mod m) <=> (a == 1) (mod m)")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "m = 0") THENL
     [ASM_SIMP_TAC [COPRIME_0, inverse_mod, MULT_CLAUSES, ADD_CLAUSES, ARITH],
      ALL_TAC] THEN
    REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "n = 0") THENL
     [ASM_SIMP_TAC [COPRIME_0, inverse_mod, MULT_CLAUSES, ADD_CLAUSES, ARITH],
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"(m * inverse_mod n m + n * inverse_mod m n == 1) (mod (m * n))")
    MP_TAC THENL
     [MATCH_MP_TAC CONG_CHINESE THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [n1, n2,
                  INVERSE_MOD_RMUL_EQ, INVERSE_MOD_LMUL_EQ] THEN
      ASM_MESON_TAC [COPRIME_SYM],
      REWRITE_TAC [CONG_TO_1, ADD_EQ_0, MULT_EQ_0, MULT_EQ_1]] THEN
    DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
     [ASM_CASES_TAC (← q "m = 1") THEN ASM_REWRITE_TAC [inverse_mod, ARITH] THEN
      ASM_CASES_TAC (← q "n = 1") THEN ASM_REWRITE_TAC [inverse_mod, ARITH],
      DISCH_THEN (X_CHOOSE_THEN (← q "q:num") MP_TAC)] THEN
    ASM_CASES_TAC (← q "q = 0") THENL
     [ASM_REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES, MULT_EQ_0, MULT_EQ_1, a] THEN
      MAP_EVERY ASM_CASES_TAC [← q "m = 1", ← q "n = 1"] THEN
      ASM_REWRITE_TAC [COPRIME_0, inverse_mod, ARITH],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q "q = 1") THENL [ASM_REWRITE_TAC [] THEN ARITH_TAC, ALL_TAC] THEN
    MATCH_MP_TAC a2 THEN
    ASM_REWRITE_TAC [LE_MULT_LCANCEL, INVERSE_MOD_BOUND_LE] THEN
    REWRITE_TAC [LE_MULT_RCANCEL] THEN ASM_ARITH_TAC))

  let INVERSE_MOD_CONV : term → ExceptT String IO thm ← do
    -- `let pth_01,pth = ... and dest_iterm = ... and m_tm ... and n_tm ...
    -- and p_tm = ...`, left to right.
    let (pth_01, pth) ← CONJ_PAIR (← prove
     r"(inverse_mod 0 n = 1 /\ inverse_mod 1 n = 1) /\
     (MAX 2 p <= n /\ (m * p) MOD n = 1 ==> inverse_mod n m = p)"
     (CONJ_TAC THENL [REWRITE_TAC [inverse_mod, ARITH], STRIP_TAC] THEN
      MATCH_MP_TAC INVERSE_MOD_UNIQUE THEN ONCE_REWRITE_TAC [CONG_SYM] THEN
      ASM_REWRITE_TAC [CONG, MOD_EQ_SELF] THEN ASM_ARITH_TAC))
    let iterm_op ← q "inverse_mod"
    let dest_iterm (tm : term) : Except String (term × term) :=
      HolCore.Basics.dest_binop iterm_op tm
    let m_tm ← q "m:num"
    let n_tm ← q "n:num"
    let p_tm ← q "p:num"
    let baseconv ← pure (GEN_REWRITE_CONV id [pth_01])
    pure (fun tm => do
      let (ntm, mtm) ← liftExcept (dest_iterm tm)
      let n ← liftExcept (dest_numeral ntm)
      let m ← liftExcept (dest_numeral mtm)
      if n ≤ num_1 then ExceptT.mk (baseconv tm) else do
        let (x, y) := gcdex m n
        let d := x * m + y * n
        if d != num_1 then throw "INVERSE_MOD_CONV: not coprime" else do
          let p := mod_num x n
          let th ← INST [(mtm, m_tm), (ntm, n_tm), (← liftExcept (mk_numeral p), p_tm)] pth
          MP th (← EQT_ELIM (← ExceptT.mk (NUM_REDUCE_CONV (← liftExcept (lhand (concl th)))))))

  -- @@RETURN BEGIN
  return { CONG_SOLVE_EQ, CONG_SOLVE_LT_EQ, CONG_SOLVE, CONG_SOLVE_UNIQUE,
           CONG_SOLVE_UNIQUE_NONTRIVIAL, CONG_UNIQUE_INVERSE_PRIME,
           COUNT_CONG_SOLVE_SIMPLE, COUNT_CONG_SOLVE_GEN, COUNT_CONG_SOLVE, CONG_CHINESE,
           CHINESE_REMAINDER_UNIQUE, CHINESE_REMAINDER_COPRIME_UNIQUE,
           CHINESE_REMAINDER_USUAL, CONG_CHINESE_EQ, CHINESE_REMAINDER_COUNT,
           CHINESE_REMAINDER_COPRIME_COUNT, COUNT_ROOTS_MODULO_COPRIME, inverse_mod,
           INVERSE_MOD_BOUND, INVERSE_MOD_RMUL_GEN, INVERSE_MOD_LMUL_GEN,
           INVERSE_MOD_RMUL_EQ, INVERSE_MOD_LMUL_EQ, INVERSE_MOD_LMUL, INVERSE_MOD_RMUL,
           INVERSE_MOD_UNIQUE, INVERSE_MOD_1, INVERSE_MOD_CONG,
           INVERSE_MOD_INVERSE_MOD_CONG, INVERSE_MOD_INVERSE_MOD,
           INVERSE_MOD_NONZERO_ALT, INVERSE_MOD_NONZERO, INVERSE_MOD_BOUND_LE,
           INVERSE_MOD_INVERSION, INVERSE_MOD_CONV }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Square-free numbers (pocklington.ml 874-1109).                            -/
/- ------------------------------------------------------------------------- -/

structure Squarefree where
  -- @@FIELDS
  squarefree : thm
  SQUAREFREE_0 : thm
  SQUAREFREE_1 : thm
  SQUAREFREE_IMP_NZ : thm
  SQUAREFREE_PRIME : thm
  SQUAREFREE_PRIME_DIVISOR : thm
  SQUAREFREE_INDEX : thm
  SQUAREFREE_PRIME_INDEX : thm
  SQUAREFREE_COPRIME : thm
  SQUAREFREE_COPRIME_DIVISORS : thm
  SQUAREFREE_DIVISOR : thm
  PRIME_IMP_SQUAREFREE : thm
  SQUAREFREE_MUL : thm
  SQUAREFREE_EXP : thm
  SQUAREFREE_DIVIDES : thm
  SQUAREFREE_DIVEXP : thm
  SQUAREFREE_DIVEXP_EQ : thm
  SQUAREFREE : thm
  SQUAREFREE_ALT : thm
  SQUAREFREE_GCD : thm
  SQUAREFREE_GCD_SQUARE : thm
  SQUAREFREE_NPRODUCT : thm
  SQUAREFREE_EXPAND : thm
  SQUAREFREE_EXPAND_EQ : thm
  SQUAREFREE_DECOMPOSITION : thm
  CONG_MOD_SQUAREFREE : thm
  CONG_MOD_SQUAREFREE_EQ : thm
  deriving Inhabited

@[nospecialize]
def setupSquarefree [HolBase] (D : PocklingtonDeps) (BBasics : Basics) :
    ExceptT String IO Squarefree := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC,
        NUMBER_RULE, NUM_REDUCE_CONV, new_definition, .. } := D
  let { AND_FORALL_THM, ARITH_EQ, COMPLETE_FACTOR_INDUCT, COPRIME_LMUL,
        COPRIME_NPRODUCT_EQ, COPRIME_PRIME_PRIME, COPRIME_REFL, COPRIME_RMUL,
        COPRIME_SYM, DE_MORGAN_THM, DIVIDES_0, DIVIDES_EXP_LE, DIVIDES_EXP_LE_IMP,
        DIVIDES_INDEX, DIVIDES_LMUL, DIVIDES_LMUL2_EQ, DIVIDES_MOD, .. } := D.core1
  let { DIVIDES_MUL2, DIVIDES_ONE, DIVIDES_PRIME_PRIME, DIVIDES_REXP, DIVIDES_RMUL,
        DIVIDES_RMUL2_EQ, EQ_TRANS, EXP, EXP_1, EXP_2, EXP_ADD, EXP_EQ_0, EXP_EQ_1,
        EXP_EXP, EXP_ONE, FINITE_INDUCT_STRONG, FINITE_SPECIAL_DIVISORS,
        FORALL_IN_INSERT, FORALL_UNWIND_THM1, FUN_EQ_THM, GCD, GCD_0, GCD_ZERO, .. } := D.core2
  let { IMP_CONJ, INDEX_EQ_0, INDEX_EXP, INDEX_GCD, INDEX_PRIME, INDUCT_COPRIME_ALT,
        IN_ELIM_THM, ITERATE_EQ, LEFT_IMP_EXISTS_THM, LE_0, MONOIDAL_MUL, .. } := D.core3
  let { MULT_ASSOC, MULT_EQ_0, NOT_IMP, NOT_IN_EMPTY, NPRODUCT_CLAUSES, PAIRWISE_EMPTY,
        PAIRWISE_INSERT, PRIMEPOW_DIVIDES_INDEX, PRIME_1, PRIME_2, PRIME_DIVEXP_EQ,
        PRIME_DIVPROD_POW_EQ, PRIME_FACTOR, PRIME_FACTORIZATION, PRIME_GE_2,
        PRIME_IMP_NZ, RIGHT_IMP_FORALL_THM, SWAP_FORALL_THM, coprime, divides,
        index_def, nproduct, pairwise, .. } := D.core4
  let { CONG_MOD_1, .. } := BBasics
  -- @@SCOPE END

  let squarefree ← new_definition
   r"squarefree n <=> !m. m EXP 2 divides n ==> m = 1"

  let SQUAREFREE_0 ← prove
   r"~squarefree 0"
   (REWRITE_TAC [squarefree, DIVIDES_0] THEN
    MESON_TAC [← ARITH_RULE (← q r"~(1 = 0)")])

  let SQUAREFREE_1 ← prove
   r"squarefree 1"
   (REWRITE_TAC [squarefree, DIVIDES_ONE, EXP_EQ_1, ARITH_EQ])

  let SQUAREFREE_IMP_NZ ← prove
   r"!n. squarefree n ==> ~(n = 0)"
   (MESON_TAC [SQUAREFREE_0])

  let (SQUAREFREE_PRIME, SQUAREFREE_PRIME_DIVISOR) ← CONJ_PAIR (← prove
   r"(!n. squarefree n <=> !p. prime p ==> ~(p EXP 2 divides n)) /\
     (!n. squarefree n <=> !p. prime p /\ p divides n ==> ~(p EXP 2 divides n))"
   (REWRITE_TAC [AND_FORALL_THM, squarefree] THEN X_GEN_TAC (← q r"n:num") THEN
    MATCH_MP_TAC (← TAUT (← q r"(q ==> r) /\ (p ==> q) /\ (r ==> p)
      ==> (p <=> q) /\ (p <=> r)")) THEN
    CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
    CONJ_TAC THENL [MESON_TAC [PRIME_1], ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN
    ASM_CASES_TAC (← q r"m = 1") THEN ASM_REWRITE_TAC [] THEN
    MP_TAC (← SPEC (← q r"m:num") PRIME_FACTOR) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"p:num") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"p:num")) THEN ASM_REWRITE_TAC [NOT_IMP] THEN
    MAP_EVERY UNDISCH_TAC [← q r"m EXP 2 divides n", ← q r"(p:num) divides m"] THEN
    CONV_TAC NUMBER_RULE))

  let SQUAREFREE_INDEX ← prove
   r"!n. squarefree n <=> ~(n = 0) /\ !m. index m n <= 1"
   (← do
    let loc_arith2 ← ARITH_RULE (← q r"~(2 <= n) <=> n <= 1")
    let loc_taut1 ← TAUT (← q r"p \/ q ==> p <=> q ==> p")
    let loc_arith1 ← ARITH_RULE (← q r"~(1 = 0)")
    pure (GEN_TAC THEN REWRITE_TAC [squarefree, PRIMEPOW_DIVIDES_INDEX] THEN
     ASM_CASES_TAC (← q r"n = 0") THENL
      [ASM_MESON_TAC [loc_arith1],
       ASM_REWRITE_TAC [loc_taut1]] THEN
     AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
     X_GEN_TAC (← q r"m:num") THEN ASM_CASES_TAC (← q r"m = 1") THEN
     ASM_REWRITE_TAC [loc_arith2] THEN
     ASM_REWRITE_TAC [index_def] THEN CONV_TAC NUM_REDUCE_CONV))

  let SQUAREFREE_PRIME_INDEX ← prove
   r"!n. squarefree n <=>
         ~(n = 0) /\ !p. prime p ==> index p n <= 1"
   (GEN_TAC THEN REWRITE_TAC [SQUAREFREE_PRIME] THEN
    REWRITE_TAC [PRIMEPOW_DIVIDES_INDEX] THEN
    ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [DE_MORGAN_THM, ← ARITH_RULE (← q r"~(2 <= n) <=> n <= 1")] THEN
    ASM_MESON_TAC [PRIME_1, PRIME_2])

  let (SQUAREFREE_COPRIME, SQUAREFREE_COPRIME_DIVISORS) ← CONJ_PAIR (← prove
   r"(!n. squarefree n <=> !a b. a * b = n ==> coprime(a,b)) /\
     (!n. squarefree n <=> !a b. a * b divides n ==> coprime(a,b))"
   (REWRITE_TAC [squarefree, AND_FORALL_THM] THEN X_GEN_TAC (← q r"n:num") THEN
    MATCH_MP_TAC (← TAUT (← q r"(r ==> p) /\ (q ==> r) /\ (p ==> q)
      ==> (p <=> q) /\ (p <=> r)")) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [EXP_2] THEN MESON_TAC [COPRIME_REFL],
      REWRITE_TAC [divides, ← GSYM MULT_ASSOC] THEN MESON_TAC [COPRIME_RMUL],
      REWRITE_TAC [coprime, EXP_2] THEN MESON_TAC [DIVIDES_MUL2]]))

  let SQUAREFREE_DIVISOR ← prove
   r"!m n. squarefree n /\ m divides n ==> squarefree m"
   (REWRITE_TAC [squarefree] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC NUMBER_RULE)

  let PRIME_IMP_SQUAREFREE ← prove
   r"!p. prime p ==> squarefree p"
   (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [SQUAREFREE_PRIME_DIVISOR, DIVIDES_PRIME_PRIME, IMP_CONJ] THEN
    GEN_TAC THEN REPLICATE_TAC 2 (DISCH_THEN (K ALL_TAC)) THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [← GSYM EXP_1] THEN
    ASM_SIMP_TAC [DIVIDES_EXP_LE, PRIME_GE_2] THEN
    CONV_TAC NUM_REDUCE_CONV)

  let SQUAREFREE_MUL ← prove
   r"!m n. squarefree(m * n) <=> coprime(m,n) /\ squarefree m /\ squarefree n"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"coprime(m:num,n)") THENL
     [ASM_REWRITE_TAC [], ASM_MESON_TAC [SQUAREFREE_COPRIME]] THEN
    EQ_TAC THENL
     [REWRITE_TAC [squarefree] THEN MESON_TAC [DIVIDES_LMUL, DIVIDES_RMUL],
      ASM_SIMP_TAC [SQUAREFREE_PRIME, PRIME_DIVPROD_POW_EQ]])

  let SQUAREFREE_EXP ← prove
   r"!n k. squarefree(n EXP k) <=> n = 1 \/ k = 0 \/ squarefree n /\ k = 1"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"n = 1") THEN ASM_REWRITE_TAC [EXP_ONE, SQUAREFREE_1] THEN
    ASM_CASES_TAC (← q r"k = 0") THEN ASM_REWRITE_TAC [EXP, SQUAREFREE_1] THEN
    ASM_CASES_TAC (← q r"k = 1") THEN ASM_REWRITE_TAC [EXP_1] THEN
    REWRITE_TAC [squarefree] THEN DISCH_THEN (MP_TAC o SPEC (← q r"n:num")) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN
    ASM_ARITH_TAC)

  let SQUAREFREE_DIVIDES ← prove
   r"!q n. squarefree q
           ==> (q divides n <=> !p. prime p /\ p divides q ==> p divides n)"
   (← do
    let loc_taut ← TAUT (← q r"p ==> q ==> r <=> q ==> p ==> r")
    let loc_meson ← MESON [LE_0]
      (← q r"(if p then 1 else 0) <= x <=> p ==> 1 <= x")
    pure (REWRITE_TAC [SQUAREFREE_PRIME_INDEX] THEN REPEAT STRIP_TAC THEN
     ASM_SIMP_TAC [IMP_CONJ, DIVIDES_INDEX, PRIME_IMP_NZ] THEN
     ASM_CASES_TAC (← q r"n = 0") THEN ASM_SIMP_TAC [INDEX_PRIME] THEN
     AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
     X_GEN_TAC (← q r"p:num") THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q r"p:num")) THEN
     ASM_CASES_TAC (← q r"prime p") THEN ASM_REWRITE_TAC [loc_meson] THEN
     ONCE_REWRITE_TAC [loc_taut] THEN
     ASM_REWRITE_TAC [FORALL_UNWIND_THM1] THEN ARITH_TAC))

  let SQUAREFREE_DIVEXP ← prove
   r"!n q x. squarefree q /\ q divides x EXP n ==> q divides x"
   (SIMP_TAC [IMP_CONJ, SQUAREFREE_DIVIDES, PRIME_DIVEXP_EQ])

  let SQUAREFREE_DIVEXP_EQ ← prove
   r"!n q x. squarefree q /\ ~(n = 0) ==> (q divides x EXP n <=> q divides x)"
   (MESON_TAC [DIVIDES_REXP, SQUAREFREE_DIVEXP])

  let (SQUAREFREE, SQUAREFREE_ALT) ← CONJ_PAIR (← prove
   r"(!n. squarefree n <=> ~(n = 0) /\ !m k. n divides m EXP k ==> n divides m) /\
     (!n. squarefree n <=> ~(n = 0) /\ !m. n divides m EXP 2 ==> n divides m)"
   (← do
    let loc_arith ← ARITH_RULE (← q r"r = 1 * r")
    let loc_taut ← TAUT (← q r"((p ==> q) /\ (q ==> r)) /\ (r ==> p) ==> (p <=> q) /\ (p <=> r)")
    pure (REWRITE_TAC [AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC loc_taut THEN
     CONJ_TAC THENL [MESON_TAC [SQUAREFREE_DIVEXP, SQUAREFREE_0], STRIP_TAC] THEN
     REWRITE_TAC [SQUAREFREE_PRIME] THEN
     X_GEN_TAC (← q r"p:num") THEN REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"r:num") SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [divides]) THEN
     FIRST_X_ASSUM (MP_TAC o SPEC (← q r"p * r:num")) THEN RULE_ASSUM_TAC
       (REWRITE_RULE [MULT_EQ_0, EXP_EQ_0, ARITH_EQ, DE_MORGAN_THM]) THEN
     ASM_SIMP_TAC [EXP_2, ← GSYM MULT_ASSOC, DIVIDES_LMUL2_EQ, NOT_IMP] THEN
     CONJ_TAC THENL [CONV_TAC NUMBER_RULE, ALL_TAC] THEN
     GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [loc_arith] THEN
     ASM_SIMP_TAC [DIVIDES_RMUL2_EQ, DIVIDES_ONE] THEN ASM_MESON_TAC [PRIME_1])))

  let SQUAREFREE_GCD ← prove
   r"!m n. squarefree m \/ squarefree n ==> squarefree(gcd(m,n))"
   (MESON_TAC [SQUAREFREE_DIVISOR, GCD])

  let SQUAREFREE_GCD_SQUARE ← prove
   r"!n. squarefree n <=> !x. gcd(x EXP 2,n) divides x"
   (← do
    let loc_taut2 ← TAUT (← q r"p \/ q <=> ~p ==> q")
    let loc_taut1 ← TAUT (← q r"p \/ q <=> ~p ==> q")
    pure (GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THENL
      [ASM_REWRITE_TAC [SQUAREFREE_0, GCD_0] THEN
       DISCH_THEN (MP_TAC o SPEC (← q r"2")) THEN REWRITE_TAC [DIVIDES_MOD] THEN ARITH_TAC,
       ASM_REWRITE_TAC [DIVIDES_INDEX, SQUAREFREE_PRIME_INDEX]] THEN
     ASM_SIMP_TAC [GCD_ZERO, INDEX_GCD, INDEX_EXP, EXP_EQ_0,
                  RIGHT_IMP_FORALL_THM, loc_taut1] THEN
     SIMP_TAC [GCD_ZERO, EXP_EQ_0, loc_taut2] THEN
     ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN AP_TERM_TAC THEN
     GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC (← q r"p:num") THEN
     ASM_CASES_TAC (← q r"prime p") THEN ASM_REWRITE_TAC [] THEN
     EQ_TAC THENL [ARITH_TAC, DISCH_THEN (MP_TAC o SPEC (← q r"p:num"))] THEN
     ASM_SIMP_TAC [INDEX_PRIME, PRIME_IMP_NZ] THEN ARITH_TAC))

  let SQUAREFREE_NPRODUCT ← prove
   r"!s. FINITE s
         ==> (squarefree(nproduct s (\n. n)) <=>
              pairwise (\a b. coprime(a,b)) s /\ !n. n IN s ==> squarefree n)"
   (MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [NPRODUCT_CLAUSES, PAIRWISE_EMPTY, NOT_IN_EMPTY, SQUAREFREE_1] THEN
    REWRITE_TAC [PAIRWISE_INSERT, SQUAREFREE_MUL, FORALL_IN_INSERT] THEN
    SIMP_TAC [pairwise, COPRIME_NPRODUCT_EQ] THEN MESON_TAC [COPRIME_SYM])

  let SQUAREFREE_EXPAND ← prove
   r"!n. squarefree n
         ==> nproduct {p | prime p /\ p divides n} (\p. p) = n"
   (REWRITE_TAC [SQUAREFREE_INDEX] THEN REPEAT STRIP_TAC THEN
    W (MP_TAC o PART_MATCH (rand o rand) PRIME_FACTORIZATION o rand o snd) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ] EQ_TRANS) THEN REWRITE_TAC [nproduct] THEN
    MATCH_MP_TAC (← MATCH_MP ITERATE_EQ MONOIDAL_MUL) THEN
    REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"p:num") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"p:num") o REWRITE_RULE [SQUAREFREE_INDEX]) THEN
    ASM_REWRITE_TAC [← ARITH_RULE (← q r"n <= 1 <=> n = 0 \/ n = 1"), INDEX_EQ_0] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [EXP_1] THEN ASM_MESON_TAC [PRIME_1])

  let SQUAREFREE_EXPAND_EQ ← prove
   r"!n. squarefree n <=>
         ~(n = 0) /\ nproduct {p | prime p /\ p divides n} (\p. p) = n"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THENL
     [ASM_MESON_TAC [SQUAREFREE_0], ASM_REWRITE_TAC []] THEN
    EQ_TAC THEN REWRITE_TAC [SQUAREFREE_EXPAND] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC [SQUAREFREE_NPRODUCT, FINITE_SPECIAL_DIVISORS] THEN
    SIMP_TAC [IN_ELIM_THM, PRIME_IMP_SQUAREFREE, pairwise] THEN
    MESON_TAC [COPRIME_PRIME_PRIME])

  let SQUAREFREE_DECOMPOSITION ← prove
   r"!n. ?m r. squarefree m /\ m * r EXP 2 = n"
   (MATCH_MP_TAC INDUCT_COPRIME_ALT THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [← q r"1", ← q r"0"] THEN
      REWRITE_TAC [SQUAREFREE_1] THEN CONV_TAC NUM_REDUCE_CONV,
      REWRITE_TAC [IMP_CONJ, RIGHT_IMP_FORALL_THM, LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC
       [← q r"a:num", ← q r"b:num", ← q r"ma:num", ← q r"na:num", ← q r"mb:num", ← q r"nb:num"] THEN
      REPEAT STRIP_TAC THEN UNDISCH_TAC (← q r"coprime(a:num,b)") THEN
      REPEAT (FIRST_X_ASSUM (SUBST1_TAC o SYM)) THEN
      REWRITE_TAC [COPRIME_LMUL, COPRIME_RMUL] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [← q r"ma * mb:num", ← q r"na * nb:num"] THEN
      ASM_REWRITE_TAC [SQUAREFREE_MUL] THEN ARITH_TAC,
      MAP_EVERY X_GEN_TAC [← q r"p:num", ← q r"k:num"] THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [← q r"p EXP (k MOD 2)", ← q r"p EXP (k DIV 2)"] THEN
      ASM_SIMP_TAC [SQUAREFREE_EXP, PRIME_IMP_SQUAREFREE] THEN
      CONJ_TAC THENL [ARITH_TAC, ALL_TAC] THEN
      REWRITE_TAC [EXP_EXP, ← GSYM EXP_ADD] THEN AP_TERM_TAC THEN ARITH_TAC])

  let CONG_MOD_SQUAREFREE ← prove
   r"!n a b. squarefree n /\
             (!p. prime p /\ p divides n ==> (a == b) (mod p))
             ==> (a == b) (mod n)"
   (REPLICATE_TAC 2 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
    MATCH_MP_TAC COMPLETE_FACTOR_INDUCT THEN
    REWRITE_TAC [CONG_MOD_1, SQUAREFREE_0] THEN
    CONJ_TAC THENL [MESON_TAC [DIVIDES_PRIME_PRIME], ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q r"m:num", ← q r"n:num"] THEN
    ASM_CASES_TAC (← q r"squarefree m") THEN ASM_REWRITE_TAC [SQUAREFREE_MUL] THEN
    ASM_CASES_TAC (← q r"squarefree n") THEN ASM_REWRITE_TAC [] THEN
    SIMP_TAC [← NUMBER_RULE (← q r"coprime(m:num,n)
      ==> ((a == b) (mod (m * n)) <=>
           (a == b) (mod m) /\ (a == b) (mod n))")] THEN
    STRIP_TAC THEN DISCH_TAC THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_MESON_TAC [DIVIDES_LMUL, DIVIDES_RMUL])

  let CONG_MOD_SQUAREFREE_EQ ← prove
   r"!n a b. squarefree n
             ==> ((a == b) (mod n) <=>
                 !p. prime p /\ p divides n ==> (a == b) (mod p))"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL [CONV_TAC NUMBER_RULE, ALL_TAC] THEN
    ASM_MESON_TAC [CONG_MOD_SQUAREFREE])

  -- @@RETURN BEGIN
  return { squarefree, SQUAREFREE_0, SQUAREFREE_1, SQUAREFREE_IMP_NZ, SQUAREFREE_PRIME,
           SQUAREFREE_PRIME_DIVISOR, SQUAREFREE_INDEX, SQUAREFREE_PRIME_INDEX,
           SQUAREFREE_COPRIME, SQUAREFREE_COPRIME_DIVISORS, SQUAREFREE_DIVISOR,
           PRIME_IMP_SQUAREFREE, SQUAREFREE_MUL, SQUAREFREE_EXP, SQUAREFREE_DIVIDES,
           SQUAREFREE_DIVEXP, SQUAREFREE_DIVEXP_EQ, SQUAREFREE, SQUAREFREE_ALT,
           SQUAREFREE_GCD, SQUAREFREE_GCD_SQUARE, SQUAREFREE_NPRODUCT, SQUAREFREE_EXPAND,
           SQUAREFREE_EXPAND_EQ, SQUAREFREE_DECOMPOSITION, CONG_MOD_SQUAREFREE,
           CONG_MOD_SQUAREFREE_EQ }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Euler totient function (pocklington.ml 1110-1463).                        -/
/- ------------------------------------------------------------------------- -/

structure Phi where
  -- @@FIELDS
  phi : thm
  PHI_ALT : thm
  PHI_FINITE_LEMMA : thm
  PHI_ANOTHER : thm
  PHI_LIMIT : thm
  PHI_LIMIT_STRONG : thm
  PHI_0 : thm
  PHI_1 : thm
  PHI_LOWERBOUND_1_STRONG : thm
  PHI_LOWERBOUND_1 : thm
  PHI_LOWERBOUND_2 : thm
  PHI_EQ_0 : thm
  PHI_PRIME_EQ : thm
  PHI_PRIME : thm
  PHI_PRIMEPOW_SUC : thm
  PHI_PRIMEPOW : thm
  PHI_PRIMEPOW_ALT : thm
  PHI_2 : thm
  PHI_MULTIPLICATIVE : thm
  EVEN_PHI : thm
  EVEN_PHI_EQ : thm
  ODD_PHI_EQ : thm
  PHI_EQ_PRIME : thm
  PHI_LIMIT_COMPOSITE : thm
  NPRODUCT_MOD : thm
  NPRODUCT_CMUL : thm
  ITERATE_OVER_COPRIME : thm
  ITERATE_ITERATE_DIVISORS : thm
  FERMAT_LITTLE : thm
  FERMAT_LITTLE_PRIME : thm
  deriving Inhabited

@[nospecialize]
def setupPhi [HolBase] (D : PocklingtonDeps) (BBasics : Basics) (BSolve : Solve) :
    ExceptT String IO Phi := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC,
        NUMBER_RULE, NUMBER_TAC, NUM_REDUCE_CONV, SET_RULE, new_definition, .. } := D
  let { ADD1, ADD_EQ_0, ADD_SUB, ARITH, CARD_CLAUSES, CARD_DIFF, CARD_IMAGE_INJ,
        CARD_IMAGE_INJ_EQ, CARD_NUMSEG_LE, CARD_NUMSEG_LT, CARD_PRODUCT, CARD_SUBSET,
        CARD_SUBSET_EQ, CONG, CONG_LMOD, CONJ_ASSOC, CONTRAPOS_THM, COPRIME_0,
        COPRIME_1, COPRIME_LMOD, COPRIME_LMUL, COPRIME_LMUL2, COPRIME_NPRODUCT,
        COPRIME_PRIMEPOW, COPRIME_REFL, COPRIME_RMUL2, COPRIME_SYM, DIVIDES_DIV_MULT,
        DIVIDES_LE, .. } := D.core1
  let { DIVIDES_SUB, DIVIDES_ZERO, DIVISION, DIV_EQ_0, DIV_MONO, DIV_MULT,
        EQ_MULT_LCANCEL, EQ_TRANS, EVEN, EVEN_EXP, EVEN_MULT, EVEN_SUB, EXP, EXP_EQ_0,
        EXP_EQ_1, EXTENSION, FINITE_DIVISORS, FINITE_INDUCT_STRONG, FINITE_NUMSEG,
        FINITE_NUMSEG_LE, FINITE_NUMSEG_LT, FINITE_RULES, FINITE_SUBSET,
        FORALL_AND_THM, FORALL_IN_IMAGE, FORALL_PAIR_THM, HAS_SIZE, .. } := D.core2
  let { IMP_CONJ, IMP_IMP, INDUCT_COPRIME_STRONG, IN_ELIM_PAIR_THM, IN_ELIM_THM,
        IN_IMAGE, IN_INSERT, IN_NUMSEG, IN_SING, ITERATE_CLAUSES,
        ITERATE_EQ_GENERAL_INVERSES, ITERATE_ITERATE_PRODUCT, ITERATE_RELATED,
        LEFT_IMP_EXISTS_THM, LE_1, LE_EXP, LE_LT, LE_MULT2, LE_RDIV_EQ, LE_TRANS, LT,
        LT_LE, LT_MULT_LCANCEL, LT_NZ, MOD_LT, MONOIDAL_MUL, .. } := D.core3
  let { MULT_AC, MULT_CLAUSES, MULT_EQ_0, MULT_SYM, NEUTRAL_MUL, NOT_EVEN,
        NOT_IN_EMPTY, NOT_LT, NOT_ODD, NOT_SUC, PAIR_EQ, PRIME, PRIME_0, PRIME_1,
        PRIME_2, PRIME_EXP, PRIME_IMP_NZ, PRIME_ODD, RIGHT_FORALL_IMP_THM,
        RIGHT_IMP_FORALL_THM, RIGHT_SUB_DISTRIB, SUBSET, coprime, divides, nproduct, .. } := D.core4
  let { CONG_MOD, CONG_MOD_0, CONG_MOD_LT, CONG_MULT, CONG_MULT_LCANCEL, CONG_REFL,
        CONG_SYM, CONG_TRANS, FINITE_NUMBER_SEGMENT, .. } := BBasics
  let { CHINESE_REMAINDER_COPRIME_UNIQUE, CONG_SOLVE, .. } := BSolve
  -- @@SCOPE END

  let phi ← new_definition
   r"phi(n) = CARD { m | 0 < m /\ m <= n /\ coprime(m,n) }"

  let PHI_ALT ← prove
   r"phi(n) = CARD { m | coprime(m,n) /\ m < n}"
   (REWRITE_TAC [phi] THEN
    ASM_CASES_TAC (← q r"n = 0") THENL
     [AP_TERM_TAC THEN
      ASM_REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
      MESON_TAC [LT, NOT_LT],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"n = 1") THENL
     [SUBGOAL_THEN
       (← q r"({m | 0 < m /\ m <= n /\ coprime (m,n)} = {1}) /\
        ({m | coprime (m,n) /\ m < n} = {0})")
       (CONJUNCTS_THEN SUBST1_TAC)
      THENL [ALL_TAC, SIMP_TAC [CARD_CLAUSES, FINITE_RULES, NOT_IN_EMPTY]] THEN
      ASM_REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_SING] THEN
      REWRITE_TAC [COPRIME_1] THEN REPEAT STRIP_TAC THEN ARITH_TAC,
      ALL_TAC] THEN
    AP_TERM_TAC THEN ASM_REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    X_GEN_TAC (← q r"m:num") THEN ASM_CASES_TAC (← q r"m = 0") THEN
    ASM_REWRITE_TAC [LT] THENL
     [ASM_MESON_TAC [COPRIME_0, COPRIME_SYM],
      ASM_MESON_TAC [LE_LT, COPRIME_REFL, LT_NZ]])

  let PHI_FINITE_LEMMA ← prove
   r"!n. FINITE {m | coprime(m,n) /\ m < n}"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"0..n") THEN
    REWRITE_TAC [FINITE_NUMSEG, SUBSET, IN_NUMSEG, IN_ELIM_THM] THEN ARITH_TAC)

  let PHI_ANOTHER ← prove
   r"!n. ~(n = 1) ==> (phi(n) = CARD {m | 0 < m /\ m < n /\ coprime(m,n)})"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [phi] THEN
    AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    ASM_MESON_TAC [LE_LT, COPRIME_REFL, COPRIME_1, LT_NZ])

  let PHI_LIMIT ← prove
   r"!n. phi(n) <= n"
   (GEN_TAC THEN REWRITE_TAC [PHI_ALT] THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM CARD_NUMSEG_LT] THEN
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC [FINITE_NUMSEG_LT] THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM])

  let PHI_LIMIT_STRONG ← prove
   r"!n. ~(n = 1) ==> phi(n) <= n - 1"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"n:num") FINITE_NUMBER_SEGMENT) THEN
    ASM_SIMP_TAC [PHI_ANOTHER, HAS_SIZE] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC [] THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM])

  let PHI_0 ← prove
   r"phi 0 = 0"
   (MP_TAC (← SPEC (← q r"0") PHI_LIMIT) THEN REWRITE_TAC [ARITH] THEN ARITH_TAC)

  let PHI_1 ← prove
   r"phi 1 = 1"
   (REWRITE_TAC [PHI_ALT, COPRIME_1, CARD_NUMSEG_LT])

  let PHI_LOWERBOUND_1_STRONG ← prove
   r"!n. 1 <= n ==> 1 <= phi(n)"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"1 = CARD {1}") SUBST1_TAC THENL
     [SIMP_TAC [CARD_CLAUSES, NOT_IN_EMPTY, FINITE_RULES, ARITH], ALL_TAC] THEN
    REWRITE_TAC [phi] THEN MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [SIMP_TAC [SUBSET, IN_INSERT, NOT_IN_EMPTY, IN_ELIM_THM] THEN
      REWRITE_TAC [← ONCE_REWRITE_RULE [COPRIME_SYM] COPRIME_1] THEN
      GEN_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC,
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{b | b <= n}") THEN
      REWRITE_TAC [CARD_NUMSEG_LE, FINITE_NUMSEG_LE] THEN
      SIMP_TAC [SUBSET, IN_ELIM_THM]])

  let PHI_LOWERBOUND_1 ← prove
   r"!n. 2 <= n ==> 1 <= phi(n)"
   (MESON_TAC [PHI_LOWERBOUND_1_STRONG, LE_TRANS, ← ARITH_RULE (← q r"1 <= 2")])

  let PHI_LOWERBOUND_2 ← prove
   r"!n. 3 <= n ==> 2 <= phi(n)"
   (← do
    let loc_arith2 ← ARITH_RULE (← q r"3 <= n ==> 0 < n - 1 /\ n - 1 <= n /\ 1 <= n")
    let loc_arith1 ← ARITH_RULE (← q r"3 <= n ==> ~(1 = n - 1)")
    pure (REPEAT STRIP_TAC THEN
     SUBGOAL_THEN (← q r"2 = CARD {1,(n-1)}") SUBST1_TAC THENL
      [SIMP_TAC [CARD_CLAUSES, IN_INSERT, NOT_IN_EMPTY, FINITE_RULES, ARITH] THEN
       ASM_SIMP_TAC [loc_arith1], ALL_TAC] THEN
     REWRITE_TAC [phi] THEN MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
      [SIMP_TAC [SUBSET, IN_INSERT, NOT_IN_EMPTY, IN_ELIM_THM] THEN
       GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [COPRIME_1] THEN
       ASM_SIMP_TAC [ARITH, loc_arith2] THEN
       REWRITE_TAC [coprime] THEN X_GEN_TAC (← q r"d:num") THEN STRIP_TAC THEN
       MP_TAC (← SPEC (← q r"n:num") (← CONJUNCT1 COPRIME_1)) THEN REWRITE_TAC [coprime] THEN
       DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
       SUBGOAL_THEN (← q r"1 = n - (n - 1)") SUBST1_TAC THENL
        [UNDISCH_TAC (← q r"3 <= n") THEN ARITH_TAC,
         ASM_SIMP_TAC [DIVIDES_SUB]],
       MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{b | b <= n}") THEN
       REWRITE_TAC [CARD_NUMSEG_LE, FINITE_NUMSEG_LE] THEN
       SIMP_TAC [SUBSET, IN_ELIM_THM]]))

  let PHI_EQ_0 ← prove
   r"!n. phi n = 0 <=> n = 0"
   (GEN_TAC THEN EQ_TAC THEN SIMP_TAC [PHI_0] THEN
    MP_TAC (← SPEC (← q r"n:num") PHI_LOWERBOUND_1_STRONG) THEN ARITH_TAC)

  let PHI_PRIME_EQ ← prove
   r"!n. (phi n = n - 1) /\ ~(n = 0) /\ ~(n = 1) <=> prime n"
   (GEN_TAC THEN REWRITE_TAC [PRIME] THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"n = 1") THEN ASM_REWRITE_TAC [PHI_1, ARITH] THEN
    MP_TAC (← SPEC (← q r"n:num") FINITE_NUMBER_SEGMENT) THEN
    ASM_SIMP_TAC [PHI_ANOTHER, HAS_SIZE] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     (← q r"{m | 0 < m /\ m < n /\ coprime (m,n)} = {m | 0 < m /\ m < n}") THEN
    CONJ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
      AP_TERM_TAC THEN ABS_TAC THEN
      REWRITE_TAC [COPRIME_SYM] THEN CONV_TAC TAUT] THEN
    EQ_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN
    MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC [] THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM])

  let PHI_PRIME ← prove
   r"!p. prime p ==> phi p = p - 1"
   (MESON_TAC [PHI_PRIME_EQ])

  let PHI_PRIMEPOW_SUC ← prove
   r"!p k. prime(p) ==> phi(p EXP (k + 1)) = p EXP (k + 1) - p EXP k"
   (← do
    let loc_taut ← TAUT (← q r"(a <=> b) <=> (a ==> b) /\ (b ==> a)")
    let loc_set ← SET_RULE (← q r"{n | ~(P n) /\ Q n} = {n | Q n} DIFF {n | P n /\ Q n}")
    pure (REPEAT STRIP_TAC THEN
     ASM_SIMP_TAC [PHI_ALT, COPRIME_PRIMEPOW, ADD_EQ_0, ARITH] THEN
     REWRITE_TAC [loc_set] THEN
     SIMP_TAC [FINITE_NUMSEG_LT, SUBSET, IN_ELIM_THM, CARD_DIFF] THEN
     REWRITE_TAC [CARD_NUMSEG_LT] THEN AP_TERM_TAC THEN
     SUBGOAL_THEN (← q r"{m | p divides m /\ m < p EXP (k + 1)} =
                   IMAGE (\x. p * x) {m | m < p EXP k}")
      (fun th => ASM_SIMP_TAC [th, CARD_IMAGE_INJ, EQ_MULT_LCANCEL, PRIME_IMP_NZ,
                              FINITE_NUMSEG_LT, CARD_NUMSEG_LT]) THEN
     REWRITE_TAC [EXTENSION, loc_taut,
                 FORALL_AND_THM, FORALL_IN_IMAGE] THEN
     ASM_SIMP_TAC [IN_ELIM_THM, ← GSYM ADD1, EXP, LT_MULT_LCANCEL, PRIME_IMP_NZ] THEN
     CONJ_TAC THENL [ALL_TAC, NUMBER_TAC] THEN
     X_GEN_TAC (← q r"x:num") THEN REWRITE_TAC [divides] THEN
     DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
     DISCH_THEN (X_CHOOSE_THEN (← q r"n:num") SUBST_ALL_TAC) THEN
     REWRITE_TAC [IN_IMAGE, IN_ELIM_THM] THEN EXISTS_TAC (← q r"n:num") THEN
     UNDISCH_TAC (← q r"p * n < p * p EXP k") THEN
     ASM_SIMP_TAC [LT_MULT_LCANCEL, PRIME_IMP_NZ]))

  let PHI_PRIMEPOW ← prove
   r"!p k. prime p
           ==> phi(p EXP k) = if k = 0 then 1 else p EXP k - p EXP (k - 1)"
   (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC [NOT_SUC, ← CONJUNCT1 EXP, PHI_1] THEN
    ASM_SIMP_TAC [ADD1, PHI_PRIMEPOW_SUC, ADD_SUB])

  let PHI_PRIMEPOW_ALT ← prove
   r"!p k. prime p
           ==> phi(p EXP k) = if k = 0 then 1 else p EXP (k - 1) * (p - 1)"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [PHI_PRIMEPOW] THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [RIGHT_SUB_DISTRIB] THEN
    REWRITE_TAC [MULT_CLAUSES, ← GSYM (← CONJUNCT2 EXP)] THEN
    ASM_SIMP_TAC [← ARITH_RULE (← q r"~(k = 0) ==> SUC(k - 1) = k")])

  let PHI_2 ← prove
   r"phi 2 = 1"
   (SIMP_TAC [PHI_PRIME, PRIME_2] THEN CONV_TAC NUM_REDUCE_CONV)

  let PHI_MULTIPLICATIVE ← prove
   r"!a b. coprime(a,b) ==> phi(a * b) = phi(a) * phi(b)"
   (REPEAT STRIP_TAC THEN
    MAP_EVERY ASM_CASES_TAC [← q r"a = 0", ← q r"b = 0"] THEN
    ASM_REWRITE_TAC [PHI_0, MULT_CLAUSES] THEN
    SIMP_TAC [PHI_ALT, ← GSYM CARD_PRODUCT, PHI_FINITE_LEMMA] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN
    EXISTS_TAC (← q r"\p. p MOD a,p MOD b") THEN
    REWRITE_TAC [PHI_FINITE_LEMMA, IN_ELIM_PAIR_THM] THEN
    ASM_SIMP_TAC [IN_ELIM_THM, COPRIME_LMOD, DIVISION] THEN CONJ_TAC THENL
     [MESON_TAC [COPRIME_LMUL2, COPRIME_RMUL2], ALL_TAC] THEN
    X_GEN_TAC (← q r"pp:num#num") THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"m:num", ← q r"n:num"] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [PAIR_EQ, ← GSYM CONJ_ASSOC] THEN MP_TAC (← SPECL
     [← q r"a:num", ← q r"b:num", ← q r"m:num", ← q r"n:num"] CHINESE_REMAINDER_COPRIME_UNIQUE) THEN
    ASM_SIMP_TAC [CONG, MOD_LT])

  let EVEN_PHI ← prove
   r"!n. 3 <= n ==> EVEN(phi n)"
   (← do
    let loc_arith2 ← ARITH_RULE (← q r"~(2 = 1)")
    let loc_arith1 ← ARITH_RULE (← q r"3 <= n <=> 1 < n /\ ~(n = 2)")
    pure (REWRITE_TAC [loc_arith1, IMP_CONJ] THEN
     MATCH_MP_TAC INDUCT_COPRIME_STRONG THEN
     SIMP_TAC [PHI_PRIMEPOW, PHI_MULTIPLICATIVE, EVEN_MULT, EVEN_SUB] THEN
     CONJ_TAC THENL [MESON_TAC [COPRIME_REFL, loc_arith2], ALL_TAC] THEN
     REWRITE_TAC [EVEN_EXP] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
     FIRST_ASSUM (DISJ_CASES_TAC o MATCH_MP PRIME_ODD) THEN ASM_REWRITE_TAC [] THENL
      [ASM_CASES_TAC (← q r"k = 1") THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
       ASM_REWRITE_TAC [← GSYM NOT_ODD]]))

  let EVEN_PHI_EQ ← prove
   r"!n. EVEN(phi n) <=> n = 0 \/ 3 <= n"
   (GEN_TAC THEN EQ_TAC THENL
     [ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC [← ARITH_RULE (← q r"~(n = 0 \/ 3 <= n) <=> n = 1 \/ n = 2")] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [PHI_1, PHI_2] THEN CONV_TAC NUM_REDUCE_CONV,
      STRIP_TAC THEN ASM_SIMP_TAC [PHI_0, EVEN_PHI, EVEN]])

  let ODD_PHI_EQ ← prove
   r"!n. ODD(phi n) <=> n = 1 \/ n = 2"
   (REWRITE_TAC [← GSYM NOT_EVEN, EVEN_PHI_EQ] THEN ARITH_TAC)

  let PHI_EQ_PRIME ← prove
   r"!p. phi p = p - 1 <=> p = 0 \/ prime p"
   (← do
    let loc_arith7 ← ARITH_RULE (← q r"k - 1 = 0 <=> k = 0 \/ k = 1")
    let loc_arith6 ← ARITH_RULE (← q r"k - 1 <= k")
    let loc_arith5 ← ARITH_RULE (← q r"p EXP k - p EXP k1 = p EXP k - 1
       ==> ~(p EXP k = 0) /\ p EXP k1 <= p EXP k ==> p EXP k1 = 1")
    let loc_arith4 ← ARITH_RULE (← q r"~(n = 0) /\ m <= n - 1 ==> m + 1 <= n")
    let loc_arith3 ← ARITH_RULE (← q r"1 < n ==> ~(n = 0)")
    let loc_arith2 ← ARITH_RULE (← q r"~(m = 0 /\ n = 0) /\ (m + 1) * (n + 1) <= k ==> ~(m * n = k - 1)")
    let loc_taut ← TAUT (← q r"~p ==> p ==> q")
    pure (GEN_TAC THEN ASM_CASES_TAC (← q r"p = 0") THEN ASM_REWRITE_TAC [PHI_0, ARITH] THEN
     ASM_CASES_TAC (← q r"p = 1") THEN ASM_REWRITE_TAC [PHI_1, PRIME_1, ARITH] THEN
     EQ_TAC THEN REWRITE_TAC [PHI_PRIME] THEN
     SUBGOAL_THEN (← q r"1 < p") MP_TAC THENL
      [ASM_ARITH_TAC, POP_ASSUM_LIST (K ALL_TAC)] THEN
     SPEC_TAC (← q r"p:num", ← q r"n:num") THEN
     MATCH_MP_TAC INDUCT_COPRIME_STRONG THEN CONJ_TAC THENL
      [MAP_EVERY X_GEN_TAC [← q r"m:num", ← q r"n:num"] THEN
       STRIP_TAC THEN ASM_SIMP_TAC [PHI_MULTIPLICATIVE] THEN
       MATCH_MP_TAC loc_taut THEN
       MATCH_MP_TAC loc_arith2 THEN
       ASM_SIMP_TAC [PHI_EQ_0, loc_arith3] THEN
       MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THEN MATCH_MP_TAC loc_arith4 THEN
       (CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC PHI_LIMIT_STRONG]) THEN
       ASM_ARITH_TAC,
       MAP_EVERY X_GEN_TAC [← q r"p:num", ← q r"k:num"] THEN
       SIMP_TAC [PHI_PRIMEPOW, PRIME_EXP] THEN REPEAT STRIP_TAC THEN
       FIRST_X_ASSUM (MP_TAC o MATCH_MP loc_arith5) THEN
       REWRITE_TAC [EXP_EQ_0, LE_EXP, EXP_EQ_1, loc_arith6] THEN
       ASM_REWRITE_TAC [loc_arith7] THEN
       ASM_MESON_TAC [PRIME_0, PRIME_1]]))

  let PHI_LIMIT_COMPOSITE ← prove
   r"!n. ~prime n /\ ~(n = 0) /\ ~(n = 1) ==> phi n < n - 1"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [LT_LE, PHI_LIMIT_STRONG, PHI_EQ_PRIME])

  let NPRODUCT_MOD ← prove
   r"!s a:A->num n.
          FINITE s /\ ~(n = 0)
          ==> (nproduct s (\m. a(m) MOD n) == nproduct s a) (mod n)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [nproduct] THEN
    MP_TAC (← ISPEC (← q r"\x y. (x == y) (mod n)")
     (← MATCH_MP ITERATE_RELATED MONOIDAL_MUL)) THEN
    SIMP_TAC [NEUTRAL_MUL, CONG_MULT, CONG_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC [CONG_MOD])

  let NPRODUCT_CMUL ← prove
   r"!s a c.
          FINITE s
          ==> nproduct s (\m. c * a(m)) = c EXP (CARD s) * nproduct s a"
   (REWRITE_TAC [nproduct, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [ITERATE_CLAUSES, MONOIDAL_MUL, NEUTRAL_MUL, CARD_CLAUSES,
                 EXP, MULT_CLAUSES] THEN
    REWRITE_TAC [MULT_AC])

  let ITERATE_OVER_COPRIME ← (← do
    let loc_lemma ← prove
     r"~(n = 0) ==> ((a * x MOD n == b) (mod n) <=> (a * x == b) (mod n))"
     (MESON_TAC [CONG_REFL, CONG_SYM, CONG_TRANS, CONG_MULT, CONG_MOD])
    let loc_setF ← SET_RULE (← q r"{x | F} = {}")
    pure (prove
     r"!op f n k.
            monoidal(op) /\ coprime(k,n) /\
            (!x y. (x == y) (mod n) ==> f x = f y)
            ==> iterate op {d | coprime(d,n) /\ d < n} (\m. f(k * m)) =
                iterate op {d | coprime(d,n) /\ d < n} f"
     (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THENL
       [ASM_SIMP_TAC [LT, loc_setF, ITERATE_CLAUSES], ALL_TAC] THEN
      STRIP_TAC THEN SUBGOAL_THEN (← q r"?m. (k * m == 1) (mod n)") CHOOSE_TAC THENL
       [ASM_MESON_TAC [CONG_SOLVE, MULT_SYM, CONG_SYM], ALL_TAC] THEN
      FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP ITERATE_EQ_GENERAL_INVERSES) THEN
      MAP_EVERY EXISTS_TAC [← q r"\x. (k * x) MOD n", ← q r"\x. (m * x) MOD n"] THEN
      REWRITE_TAC [IN_ELIM_THM] THEN
      ASM_SIMP_TAC [COPRIME_LMOD, CONG_MOD_LT, CONG_LMOD, DIVISION, loc_lemma,
                   COPRIME_LMUL] THEN
      REPEAT STRIP_TAC THEN
      TRY (FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC [CONG_LMOD]) THEN
      UNDISCH_TAC (← q r"(k * m == 1) (mod n)") THEN CONV_TAC NUMBER_RULE)))

  let ITERATE_ITERATE_DIVISORS ← prove
   r"!op:A->A->A f x.
          monoidal op
          ==> iterate op (1..x) (\n. iterate op {d | d divides n} (f n)) =
              iterate op (1..x)
                         (\n. iterate op (1..(x DIV n)) (\k. f (k * n) n))"
   (← do
    let loc_arith2 ← ARITH_RULE (← q r"1 <= x <=> ~(x = 0)")
    let loc_arith1 ← ARITH_RULE (← q r"1 <= x <=> ~(x = 0)")
    pure (REPEAT STRIP_TAC THEN
     ASM_SIMP_TAC [ITERATE_ITERATE_PRODUCT, FINITE_NUMSEG, FINITE_DIVISORS,
                  IN_NUMSEG, LE_1] THEN
     MATCH_MP_TAC (← REWRITE_RULE [RIGHT_IMP_FORALL_THM, IMP_IMP]
         ITERATE_EQ_GENERAL_INVERSES) THEN
     MAP_EVERY EXISTS_TAC [← q r"\(n,d). d,n DIV d", ← q r"\(n:num,k). n * k,n"] THEN
     ASM_SIMP_TAC [FORALL_PAIR_THM, IN_ELIM_PAIR_THM, PAIR_EQ] THEN CONJ_TAC THEN
     REWRITE_TAC [IN_ELIM_THM] THEN X_GEN_TAC (← q r"n:num") THENL
      [X_GEN_TAC (← q r"k:num") THEN SIMP_TAC [DIV_MULT, LE_1, ← GSYM LE_RDIV_EQ] THEN
       SIMP_TAC [MULT_EQ_0, loc_arith1] THEN
       DISCH_THEN (K ALL_TAC) THEN NUMBER_TAC,
       X_GEN_TAC (← q r"d:num") THEN ASM_CASES_TAC (← q r"d = 0") THEN
       ASM_REWRITE_TAC [DIVIDES_ZERO] THENL [ARITH_TAC, ALL_TAC] THEN
       STRIP_TAC THEN ASM_SIMP_TAC [DIV_MONO] THEN CONJ_TAC THENL
        [ALL_TAC, ASM_MESON_TAC [DIVIDES_DIV_MULT, MULT_SYM]] THEN
       FIRST_X_ASSUM (MP_TAC o MATCH_MP DIVIDES_LE) THEN
       ASM_SIMP_TAC [DIV_EQ_0, loc_arith2] THEN
       ASM_ARITH_TAC]))

  let FERMAT_LITTLE ← prove
   r"!a n. coprime(a,n) ==> (a EXP (phi n) == 1) (mod n)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_SIMP_TAC [COPRIME_0, PHI_0, CONG_MOD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_TAC THEN MATCH_MP_TAC CONG_MULT_LCANCEL THEN
    EXISTS_TAC (← q r"nproduct {m | coprime (m,n) /\ m < n} (\m. m)") THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [PHI_ALT, MULT_CLAUSES] THEN
    SIMP_TAC [IN_ELIM_THM, ← ONCE_REWRITE_RULE [COPRIME_SYM] COPRIME_NPRODUCT,
             PHI_FINITE_LEMMA, ← GSYM NPRODUCT_CMUL] THEN
    ONCE_REWRITE_TAC [CONG_SYM] THEN MATCH_MP_TAC CONG_TRANS THEN
    EXISTS_TAC (← q r"nproduct {m | coprime(m,n) /\ m < n} (\m. (a * m) MOD n)") THEN
    ASM_SIMP_TAC [NPRODUCT_MOD, PHI_FINITE_LEMMA] THEN
    MP_TAC (← ISPECL [← q r"( * ):num->num->num", ← q r"\x. x MOD n", ← q r"n:num", ← q r"a:num"]
                  ITERATE_OVER_COPRIME) THEN
    ASM_SIMP_TAC [MONOIDAL_MUL, ← GSYM CONG, ← GSYM nproduct] THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC [CONG_SYM] THEN
    MATCH_MP_TAC NPRODUCT_MOD THEN ASM_SIMP_TAC [PHI_FINITE_LEMMA])

  let FERMAT_LITTLE_PRIME ← prove
   r"!a p. prime p /\ coprime(a,p) ==> (a EXP (p - 1) == 1) (mod p)"
   (MESON_TAC [FERMAT_LITTLE, PHI_PRIME_EQ])

  -- @@RETURN BEGIN
  return { phi, PHI_ALT, PHI_FINITE_LEMMA, PHI_ANOTHER, PHI_LIMIT, PHI_LIMIT_STRONG,
           PHI_0, PHI_1, PHI_LOWERBOUND_1_STRONG, PHI_LOWERBOUND_1, PHI_LOWERBOUND_2,
           PHI_EQ_0, PHI_PRIME_EQ, PHI_PRIME, PHI_PRIMEPOW_SUC, PHI_PRIMEPOW,
           PHI_PRIMEPOW_ALT, PHI_2, PHI_MULTIPLICATIVE, EVEN_PHI, EVEN_PHI_EQ,
           ODD_PHI_EQ, PHI_EQ_PRIME, PHI_LIMIT_COMPOSITE, NPRODUCT_MOD, NPRODUCT_CMUL,
           ITERATE_OVER_COPRIME, ITERATE_ITERATE_DIVISORS, FERMAT_LITTLE,
           FERMAT_LITTLE_PRIME }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Lucas's theorem, the order of a number mod n, primitive roots, another     -/
/- primality characterization.  (pocklington.ml 1464-2020)                   -/
/- ------------------------------------------------------------------------- -/

/-- `W(MP_TAC o PART_MATCH f th o snd)` -/
def mpPartSnd [HolBase] (f : term → Except String term) (th : thm) : tactic := fun gl =>
  ExceptT.run do
    ExceptT.mk (MP_TAC (← PART_MATCH f th gl.2) gl)

structure Order where
  -- @@FIELDS
  LUCAS_COPRIME_LEMMA : thm
  LUCAS_WEAK : thm
  LUCAS : thm
  order : thm
  EXP_ITER : thm
  ORDER_DIVIDES : thm
  ORDER : thm
  ORDER_UNIQUE_ALT : thm
  ORDER_MINIMAL : thm
  ORDER_WORKS : thm
  ORDER_1 : thm
  ORDER_EQ_0 : thm
  ORDER_EQ_1 : thm
  ORDER_UNIQUE_PRIME : thm
  ORDER_CONG : thm
  ORDER_MOD : thm
  COPRIME_ORDER : thm
  ORDER_DIVIDES_PHI : thm
  ORDER_LE_PHI : thm
  ORDER_DIVIDES_EXPDIFF : thm
  ORDER_UNIQUE : thm
  ORDER_MUL_LCM : thm
  ORDER_EXP_GEN : thm
  ORDER_EXP : thm
  ORDER_INVERSE_MOD : thm
  ORDER_MUL_DIVIDES : thm
  ORDER_MUL_EQ : thm
  ORDER_LCM_EXISTS : thm
  ORDER_DIVIDES_MAXIMAL : thm
  POWER_RESIDUE_MODULO_COPRIME : thm
  POWER_RESIDUE_MODULO_PRIME : thm
  INJECTIVE_EXP_MODULO : thm
  PRIMITIVE_ROOT_IMP_COPRIME : thm
  PRIMITIVE_ROOT_IMP_PRIME : thm
  PRIMITIVE_ROOT_IMAGE : thm
  PRIMITIVE_ROOT_IMAGE_PRIME : thm
  PRIMITIVE_ROOT_SURJECTIVE : thm
  PRIMITIVE_ROOT_SURJECTIVE_ALT : thm
  PRIMITIVE_ROOT_SURJECTIVE_PRIME : thm
  PRIMITIVE_ROOT_SURJECTIVE_PRIME_ALT : thm
  PRIME_DIVISOR_SQRT : thm
  PRIME_PRIME_FACTOR_SQRT : thm
  deriving Inhabited

@[nospecialize]
def setupOrder [HolBase] (D : PocklingtonDeps) (BBasics : Basics) (BSolve : Solve) (BPhi : Phi) :
    ExceptT String IO Order := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON,
        MESON_TAC, NUMBER_RULE, NUMBER_TAC, SELECT_CONV, SET_RULE, SET_TAC,
        new_definition, num_CONV, .. } := D
  let { ADD_CLAUSES, ARITH, ARITH_EQ, CARD_NUMSEG_LT, CONG, CONG_LMOD, COPRIME_0,
        COPRIME_1, COPRIME_EXP, COPRIME_LEXP, COPRIME_LMOD, COPRIME_REXP, COPRIME_SYM,
        DIVIDES_0, DIVIDES_1, DIVIDES_ADD_REVR, DIVIDES_ANTISYM, DIVIDES_GCD_RIGHT,
        DIVIDES_LCM_RIGHT, DIVIDES_LE, DIVIDES_LE_IMP, DIVIDES_LE_STRONG, DIVIDES_LMUL,
        DIVIDES_MOD, .. } := D.core1
  let { DIVIDES_ONE, DIVIDES_REFL, DIVIDES_RMUL, DIVIDES_TRANS, DIVIDES_ZERO, DIVISION,
        DIV_0, DIV_MULT, DIV_UNIQ, EMPTY_GSPEC, EQ_TRANS, EXISTS_IN_IMAGE, EXP, EXP_1,
        EXP_2, EXP_ADD, EXP_EQ_0, EXP_EQ_1, EXP_EXP, EXP_MONO_LE, EXP_ONE, EXTENSION,
        FINITE_IMAGE, FINITE_NUMSEG_LT, FINITE_SUBSET, FORALL_IN_IMAGE, FUN_EQ_THM,
        GCD_ZERO, IMAGE_CLAUSES, IMAGE_EQ_EMPTY, .. } := D.core2
  let { IMP_CONJ, IN, IN_ELIM_THM, ITER, LCM_0, LCM_COPRIME_DECOMP, LCM_DIVIDES, LE,
        LEFT_IMP_EXISTS_THM, LE_0, LE_1, LE_ANTISYM, LE_CASES, LE_EXISTS, LE_LCM,
        LE_MULT_LCANCEL, LE_MULT_RCANCEL, LE_TRANS, LT, LT_MULT_LCANCEL, LT_REFL,
        LT_TRANS, MEMBER_NOT_EMPTY, MOD_EQ_0, MOD_EXP_MOD, MOD_LT_EQ, MOD_UNIQ,
        MONO_EXISTS, .. } := D.core3
  let { MULT_AC, MULT_ASSOC, MULT_CLAUSES, MULT_EXP, MULT_SYM, NOT_EXISTS_THM, NOT_LT,
        NOT_SUC, ORDER_EXISTENCE_ITER, PRIME_0, PRIME_1, PRIME_COPRIME_EQ,
        PRIME_FACTOR, SUBSET, SUBSET_ANTISYM, SUB_REFL, SURJECTIVE_IFF_INJECTIVE_GEN,
        UNWIND_THM2, coprime, divides, num_FINITE, num_MAX, num_WOP, prime, .. } := D.core4
  let { CONG_0_DIVIDES, CONG_ADD_LCANCEL_EQ, CONG_EXP, CONG_EXP_1, CONG_IMP_EQ,
        CONG_MOD_0, CONG_MULT_1, CONG_MULT_LCANCEL, CONG_MULT_LCANCEL_EQ, CONG_REFL,
        CONG_SYM, CONG_TRANS, .. } := BBasics
  let { CONG_SOLVE, INVERSE_MOD_LMUL_EQ, .. } := BSolve
  let { FERMAT_LITTLE, PHI_0, PHI_ALT, PHI_EQ_0, PHI_EQ_PRIME, PHI_LIMIT_STRONG,
        PHI_LOWERBOUND_1, PHI_PRIME, PHI_PRIME_EQ, .. } := BPhi
  -- @@SCOPE END

  let LUCAS_COPRIME_LEMMA ← prove
   r"!m n a. ~(m = 0) /\ (a EXP m == 1) (mod n) ==> coprime(a,n)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THENL
     [ASM_REWRITE_TAC [CONG_MOD_0, EXP_EQ_1] THEN
      ASM_CASES_TAC (← q r"m = 0") THEN ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [COPRIME_SYM] THEN SIMP_TAC [COPRIME_1],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"n = 1") THEN ASM_REWRITE_TAC [COPRIME_1] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [coprime] THEN X_GEN_TAC (← q r"d:num") THEN STRIP_TAC THEN
    UNDISCH_TAC (← q r"(a EXP m == 1) (mod n)") THEN
    ASM_SIMP_TAC [CONG] THEN
    SUBGOAL_THEN (← q r"1 MOD n = 1") SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC (← q r"0") THEN
      REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN
      MAP_EVERY UNDISCH_TAC [← q r"~(n = 0)", ← q r"~(n = 1)"] THEN ARITH_TAC,
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN (← q r"d divides (a EXP m) MOD n") MP_TAC THENL
     [ALL_TAC, ASM_SIMP_TAC [DIVIDES_ONE]] THEN
    MATCH_MP_TAC DIVIDES_ADD_REVR THEN
    EXISTS_TAC (← q r"a EXP m DIV n * n") THEN
    ASM_SIMP_TAC [← GSYM DIVISION, DIVIDES_LMUL] THEN
    SUBGOAL_THEN (← q r"m = SUC(m - 1)") SUBST1_TAC THENL
     [UNDISCH_TAC (← q r"~(m = 0)") THEN ARITH_TAC,
      ASM_SIMP_TAC [EXP, DIVIDES_RMUL]])

  let LUCAS_WEAK ← prove
   r"!a n. 2 <= n /\
           (a EXP (n - 1) == 1) (mod n) /\
           (!m. 0 < m /\ m < n - 1 ==> ~(a EXP m == 1) (mod n))
           ==> prime(n)"
   (← do
    let a2 ← ARITH_RULE (← q r"1 <= n ==> 0 < n")
    let t ← TAUT (← q r"a ==> ~(a /\ b) ==> ~b")
    let a1 ← ARITH_RULE (← q r"2 <= n ==> ~(n - 1 = 0)")
    let a0 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0) /\ ~(n = 1)")
    pure (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [← GSYM PHI_PRIME_EQ, PHI_LIMIT_STRONG, ← GSYM LE_ANTISYM, a0] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"phi n")) THEN
    SUBGOAL_THEN (← q r"coprime(a,n)") (fun th => SIMP_TAC [FERMAT_LITTLE, th]) THENL
     [MATCH_MP_TAC LUCAS_COPRIME_LEMMA THEN EXISTS_TAC (← q r"n - 1") THEN
      ASM_SIMP_TAC [a1], ALL_TAC] THEN
    REWRITE_TAC [← GSYM NOT_LT] THEN
    MATCH_MP_TAC t THEN
    ASM_SIMP_TAC [PHI_LOWERBOUND_1, a2]))

  let LUCAS ← prove
   r"!a n. 2 <= n /\
           (a EXP (n - 1) == 1) (mod n) /\
           (!p. prime(p) /\ p divides (n - 1)
                ==> ~(a EXP ((n - 1) DIV p) == 1) (mod n))
           ==> prime(n)"
   (← do
    let a5 ← ARITH_RULE (← q r"~(p = 0) ==> 0 < p")
    let a4 ← ARITH_RULE (← q r"~(0 < n) ==> (n = 0)")
    let a3 ← ARITH_RULE (← q r"0 < n ==> ~(n = 0)")
    let t2 ← TAUT (← q r"a ==> ~b <=> ~(a /\ b)")
    let a1 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0)")
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP a1) THEN
    MATCH_MP_TAC LUCAS_WEAK THEN EXISTS_TAC (← q r"a:num") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [t2, ← GSYM NOT_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [num_WOP] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"m:num") STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP a3) THEN
    SUBGOAL_THEN (← q r"m divides (n - 1)") MP_TAC THENL
     [REWRITE_TAC [divides] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
      ASM_SIMP_TAC [← GSYM MOD_EQ_0] THEN
      MATCH_MP_TAC a4 THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(n - 1) MOD m")) THEN
      ASM_SIMP_TAC [DIVISION] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC (← q r"m:num") THEN
        ASM_SIMP_TAC [DIVISION], ALL_TAC] THEN
      MATCH_MP_TAC CONG_MULT_LCANCEL THEN
      EXISTS_TAC (← q r"a EXP ((n - 1) DIV m * m)") THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC [COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_EXP THEN
        ONCE_REWRITE_TAC [COPRIME_SYM] THEN MATCH_MP_TAC LUCAS_COPRIME_LEMMA THEN
        EXISTS_TAC (← q r"m:num") THEN ASM_SIMP_TAC [], ALL_TAC] THEN
      REWRITE_TAC [← GSYM EXP_ADD] THEN
      ASM_SIMP_TAC [← GSYM DIVISION] THEN REWRITE_TAC [MULT_CLAUSES] THEN
      ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [← GSYM EXP_EXP] THEN
      UNDISCH_TAC (← q r"(a EXP (n - 1) == 1) (mod n)") THEN
      UNDISCH_TAC (← q r"(a EXP m == 1) (mod n)") THEN
      ASM_SIMP_TAC [CONG] THEN REPEAT DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC (← q r"((a EXP m) MOD n) EXP ((n - 1) DIV m) MOD n") THEN
      CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC [MOD_EXP_MOD]] THEN
      ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [MOD_EXP_MOD] THEN
      REWRITE_TAC [EXP_ONE], ALL_TAC] THEN
    REWRITE_TAC [divides] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"r:num") SUBST_ALL_TAC) THEN
    SUBGOAL_THEN (← q r"~(r = 1)") MP_TAC THENL
     [UNDISCH_TAC (← q r"m < m * r") THEN CONV_TAC CONTRAPOS_CONV THEN
      SIMP_TAC [MULT_CLAUSES, LT_REFL], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o MATCH_MP PRIME_FACTOR) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"p:num") MP_TAC) THEN STRIP_TAC THEN
    UNDISCH_TAC (← q r"!p. prime p /\ p divides m * r
                     ==> ~(a EXP ((m * r) DIV p) == 1) (mod n)") THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"p:num")) THEN ASM_SIMP_TAC [DIVIDES_LMUL] THEN
    SUBGOAL_THEN (← q r"(m * r) DIV p = m * (r DIV p)") SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC (← q r"0") THEN
      UNDISCH_TAC (← q r"prime p") THEN
      ASM_CASES_TAC (← q r"p = 0") THEN ASM_REWRITE_TAC [PRIME_0] THEN
      ASM_SIMP_TAC [a5] THEN
      DISCH_TAC THEN REWRITE_TAC [ADD_CLAUSES, ← GSYM MULT_ASSOC] THEN
      AP_TERM_TAC THEN UNDISCH_TAC (← q r"p divides r") THEN
      REWRITE_TAC [divides] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [DIV_MULT] THEN REWRITE_TAC [MULT_AC], ALL_TAC] THEN
    UNDISCH_TAC (← q r"(a EXP m == 1) (mod n)") THEN
    ASM_SIMP_TAC [CONG] THEN
    DISCH_THEN (MP_TAC o C AP_THM (← q r"r DIV p") o AP_TERM (← q r"(EXP)")) THEN
    DISCH_THEN (MP_TAC o C AP_THM (← q r"n:num") o AP_TERM (← q r"(MOD)")) THEN
    ASM_SIMP_TAC [MOD_EXP_MOD] THEN
    REWRITE_TAC [EXP_EXP, EXP_ONE]))

  let order ← new_definition
   r"order n a = @d. !k. (a EXP k == 1) (mod n) <=> d divides k"

  let EXP_ITER ← prove
   r"!x n. x EXP n = ITER n (\y. x * y) (1)"
   (GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ITER, EXP])

  let ORDER_DIVIDES ← prove
   r"!n a d. (a EXP d == 1) (mod n) <=> order(n) a divides d"
   (GEN_TAC THEN GEN_TAC THEN REWRITE_TAC [order] THEN CONV_TAC SELECT_CONV THEN
    MP_TAC (← ISPECL [← q r"\x y:num. (x == y) (mod n)", ← q r"\x:num. a * x", ← q r"1"]
          ORDER_EXISTENCE_ITER) THEN
    REWRITE_TAC [← GSYM EXP_ITER] THEN DISCH_THEN MATCH_MP_TAC THEN
    NUMBER_TAC)

  let ORDER ← prove
   r"!n a. (a EXP (order(n) a) == 1) (mod n)"
   (REWRITE_TAC [ORDER_DIVIDES, DIVIDES_REFL])

  let ORDER_UNIQUE_ALT ← prove
   r"!n a d. order n a = d <=> !k. (a EXP k == 1) (mod n) <=> d divides k"
   (REWRITE_TAC [ORDER_DIVIDES, ← GSYM DIVIDES_ANTISYM] THEN
    MESON_TAC [DIVIDES_REFL, DIVIDES_TRANS])

  let ORDER_MINIMAL ← prove
   r"!n a m. 0 < m /\ m < order(n) a ==> ~((a EXP m == 1) (mod n))"
   (REWRITE_TAC [ORDER_DIVIDES] THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC)

  let ORDER_WORKS ← prove
   r"!n a. (a EXP (order(n) a) == 1) (mod n) /\
           !m. 0 < m /\ m < order(n) a ==> ~((a EXP m == 1) (mod n))"
   (MESON_TAC [ORDER, ORDER_MINIMAL])

  let ORDER_1 ← prove
   r"!n. order n 1 = 1"
   (REWRITE_TAC [← GSYM DIVIDES_ONE, ← GSYM ORDER_DIVIDES, EXP_1, CONG_REFL])

  let ORDER_EQ_0 ← prove
   r"!n a. order(n) a = 0 <=> ~coprime(n,a)"
   (← do
    let t ← TAUT (← q r"~p ==> (q ==> p) ==> q ==> r")
    let a0 ← ARITH_RULE (← q r"~(1 = 0)")
    pure (REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [ONCE_REWRITE_TAC [COPRIME_SYM] THEN DISCH_TAC THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP FERMAT_LITTLE) THEN
      ASM_REWRITE_TAC [ORDER_DIVIDES, DIVIDES_ZERO, PHI_EQ_0] THEN
      ASM_MESON_TAC [COPRIME_0, ORDER_1, a0],
      MP_TAC (← SPECL [← q r"n:num", ← q r"a:num"] ORDER) THEN
      SPEC_TAC (← q r"order n a", ← q r"m:num") THEN INDUCT_TAC THEN REWRITE_TAC [] THEN
      FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP t) THEN
      REWRITE_TAC [EXP] THEN CONV_TAC NUMBER_RULE]))

  let ORDER_EQ_1 ← prove
   r"!n a. order n a = 1 <=> (a == 1) (mod n)"
   (REWRITE_TAC [ORDER_UNIQUE_ALT, DIVIDES_1] THEN
    MESON_TAC [CONG_EXP_1, EXP_1])

  let ORDER_UNIQUE_PRIME ← prove
   r"!n a p.
          prime p
          ==> (order n a = p <=> ~((a == 1) (mod n)) /\ (a EXP p == 1) (mod n))"
   (← do
    let m0 ← NUMBER_RULE (← q r"1 divides n /\ n divides n")
    pure (SIMP_TAC [ORDER_DIVIDES] THEN REWRITE_TAC [← GSYM ORDER_EQ_1] THEN
    REWRITE_TAC [prime] THEN
    MESON_TAC [m0]))

  let ORDER_CONG ← prove
   r"!n a b. (a == b) (mod n) ==> order n a = order n b"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [order] THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    ASM_MESON_TAC [CONG_EXP, CONG_REFL, CONG_SYM, CONG_TRANS])

  let ORDER_MOD ← prove
   r"!p n. order p (n MOD p) = order p n"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC ORDER_CONG THEN
    REWRITE_TAC [CONG_LMOD, CONG_REFL])

  let COPRIME_ORDER ← prove
   r"!n a. coprime(n,a)
           ==> order(n) a > 0 /\
              (a EXP (order(n) a) == 1) (mod n) /\
              !m. 0 < m /\ m < order(n) a ==> ~((a EXP m == 1) (mod n))"
   (← do
    let a0 ← ARITH_RULE (← q r"n > 0 <=> ~(n = 0)")
    pure (SIMP_TAC [a0, ORDER_EQ_0] THEN
    MESON_TAC [ORDER, ORDER_MINIMAL]))

  let ORDER_DIVIDES_PHI ← prove
   r"!a n. coprime(n,a) ==> (order n a) divides (phi n)"
   (MESON_TAC [ORDER_DIVIDES, FERMAT_LITTLE, COPRIME_SYM])

  let ORDER_LE_PHI ← prove
   r"!n. ~(n = 0) ==> order n a <= phi n"
   (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"order n a = 0") THEN ASM_REWRITE_TAC [LE_0] THEN
    MATCH_MP_TAC DIVIDES_LE_IMP THEN ASM_REWRITE_TAC [PHI_EQ_0] THEN
    MATCH_MP_TAC ORDER_DIVIDES_PHI THEN
    ASM_MESON_TAC [ORDER_EQ_0])

  let ORDER_DIVIDES_EXPDIFF ← prove
   r"!a n d e. coprime(n,a)
               ==> ((a EXP d == a EXP e) (mod n) <=> (d == e) (mod (order n a)))"
   (← do
    let a1 ← ARITH_RULE (← q r"(e + 0) + c = e + c")
    let a0 ← ARITH_RULE (← q r"e = e + 0")
    pure (SUBGOAL_THEN
     (← q r"!a n d e. coprime(n,a) /\ e <= d
                ==> ((a EXP d == a EXP e) (mod n) <=> (d == e) (mod (order n a)))")
     (fun th => MESON_TAC [th, LE_CASES, CONG_SYM]) THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"c:num") SUBST1_TAC) THEN
    SUBST1_TAC a0 THEN
    REWRITE_TAC [a1] THEN
    REWRITE_TAC [EXP_ADD] THEN
    ASM_SIMP_TAC [CONG_ADD_LCANCEL_EQ, COPRIME_EXP,
      ← ONCE_REWRITE_RULE [COPRIME_SYM] CONG_MULT_LCANCEL_EQ] THEN
    REWRITE_TAC [EXP, CONG_0_DIVIDES, ORDER_DIVIDES]))

  let ORDER_UNIQUE ← prove
   r"!n a k. 0 < k /\
             (a EXP k == 1) (mod n) /\
             (!m. 0 < m /\ m < k ==> ~(a EXP m == 1) (mod n))
             ==> order n a = k"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"order n a")) THEN
    MP_TAC (← ISPECL [← q r"n:num", ← q r"a:num"] ORDER_WORKS) THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC (← q r"k:num"))) THEN
    ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"order n a = 0") THEN
    ASM_REWRITE_TAC [] THENL [ALL_TAC, ASM_ARITH_TAC] THEN
    FIRST_X_ASSUM (ASSUME_TAC o GEN_REWRITE_RULE I [ORDER_EQ_0]) THEN
    MP_TAC (← ISPECL [← q r"n:num", ← q r"a:num", ← q r"k:num"] COPRIME_REXP) THEN
    ASM_SIMP_TAC [LE_1, LT] THEN
    UNDISCH_TAC (← q r"(a EXP k == 1) (mod n)") THEN CONV_TAC NUMBER_RULE)

  let ORDER_MUL_LCM ← prove
   r"!m n a. coprime(m,n) ==> order (m * n) a = lcm(order m a,order n a)"
   (← do
    let n0 ← NUMBER_RULE (← q r"coprime(m,n)
      ==> ((x == y) (mod (m * n)) <=>
           (x == y) (mod m) /\ (x == y) (mod n))")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [ORDER_UNIQUE_ALT] THEN
    ASM_SIMP_TAC [n0] THEN
    REWRITE_TAC [ORDER_DIVIDES, LCM_DIVIDES]))

  let ORDER_EXP_GEN ← prove
   r"!p a k. order p (a EXP k) =
             if k = 0 then 1 else order p a DIV gcd(order p a,k)"
   (← do
    let n0 ← NUMBER_RULE (← q r"gcd(order p a,k) divides order p a")
    pure (REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [ORDER_1, EXP] THEN
    ASM_CASES_TAC (← q r"order p a = 0") THENL
     [ASM_REWRITE_TAC [DIV_0, ORDER_EQ_0, COPRIME_REXP] THEN
      ASM_REWRITE_TAC [← GSYM ORDER_EQ_0],
      ALL_TAC] THEN
    REWRITE_TAC [ORDER_UNIQUE_ALT, EXP_EXP] THEN
    X_GEN_TAC (← q r"j:num") THEN REWRITE_TAC [ORDER_DIVIDES] THEN
    MP_TAC n0 THEN
    GEN_REWRITE_TAC LAND_CONV [divides] THEN
    ABBREV_TAC (← q r"d = gcd(order p a,k)") THEN
    ASM_CASES_TAC (← q r"d = 0") THENL [ASM_MESON_TAC [GCD_ZERO], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"e:num")) THEN ASM_SIMP_TAC [DIV_MULT] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC NUMBER_RULE))

  let ORDER_EXP ← prove
   r"!p a k. ~(k = 0) /\ k divides order p a
             ==> order p (a EXP k) = order p a DIV k"
   (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [ORDER_EXP_GEN] THEN
    AP_TERM_TAC THEN ASM_REWRITE_TAC [← GSYM DIVIDES_GCD_RIGHT])

  let ORDER_INVERSE_MOD ← prove
   r"!n a. coprime(n,a) ==> order n (inverse_mod n a) = order n a"
   (← do
    let n0 ← NUMBER_RULE (← q r"(a * b == 1) (mod n) ==> ((a == 1) (mod n) <=> (b == 1) (mod n))")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [order] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"d:num") THEN REWRITE_TAC [] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC (← q r"k:num") THEN REWRITE_TAC [] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC n0 THEN
    REWRITE_TAC [← GSYM MULT_EXP] THEN MATCH_MP_TAC CONG_EXP_1 THEN
    ASM_REWRITE_TAC [INVERSE_MOD_LMUL_EQ]))

  let ORDER_MUL_DIVIDES ← prove
   r"!p a b. order p (a * b) divides order p a * order p b"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM ORDER_DIVIDES] THEN
    REWRITE_TAC [MULT_EXP] THEN MATCH_MP_TAC CONG_MULT_1 THEN
    REWRITE_TAC [ORDER_DIVIDES] THEN NUMBER_TAC)

  let ORDER_MUL_EQ ← prove
   r"!p a b. coprime(order p a,order p b)
             ==> order p (a * b) = order p a * order p b"
   (← do
    let n2 ← NUMBER_RULE (← q r"(a == 1) (mod n) ==> (b == a * b) (mod n)")
    let n1 ← NUMBER_RULE (← q r"(b == 1) (mod n) ==> (a == a * b) (mod n)")
    let n0 ← NUMBER_RULE (← q r"(a:num) divides (b * c) /\ b divides (a * c) /\ coprime(a,b)
      ==> (a * b) divides c")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM DIVIDES_ANTISYM] THEN
    ASM_SIMP_TAC [ORDER_MUL_DIVIDES] THEN
    MATCH_MP_TAC n0 THEN
    ASM_REWRITE_TAC [← GSYM ORDER_DIVIDES] THEN CONJ_TAC THEN
    MATCH_MP_TAC CONG_TRANS THENL
     [EXISTS_TAC (← q r"(a * b) EXP (order p b * order p (a * b))"),
      EXISTS_TAC (← q r"(a * b) EXP (order p a * order p (a * b))")] THEN
    (CONJ_TAC THENL
      [ALL_TAC,
       GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o RAND_CONV) [MULT_SYM] THEN
       REWRITE_TAC [← GSYM EXP_EXP] THEN MATCH_MP_TAC CONG_EXP_1 THEN
       REWRITE_TAC [ORDER_WORKS]]) THEN
    REWRITE_TAC [← GSYM EXP_EXP] THEN MATCH_MP_TAC CONG_EXP THEN
    REWRITE_TAC [MULT_EXP] THENL
     [MATCH_MP_TAC n1,
      MATCH_MP_TAC n2] THEN
    REWRITE_TAC [ORDER_WORKS]))

  let ORDER_LCM_EXISTS ← prove
   r"!p a b. ?c. order p c = lcm(order p a,order p b)"
   (← do
    let n0 ← NUMBER_RULE (← q r"gcd(a * b:num,a) = a /\ gcd(a * b,b) = b")
    pure (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"order p a = 0") THENL
     [ASM_MESON_TAC [LCM_0], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"order p b = 0") THENL
     [ASM_MESON_TAC [LCM_0], ALL_TAC] THEN
    MP_TAC (← SPECL [← q r"order p a", ← q r"order p b"]
          LCM_COPRIME_DECOMP) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"m:num", ← q r"n:num"] THEN
    REWRITE_TAC [divides, IMP_CONJ, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"m':num") THEN DISCH_TAC THEN
    X_GEN_TAC (← q r"n':num") THEN DISCH_TAC THEN DISCH_TAC THEN
    DISCH_THEN (fun th => tactic_of do
      pure (SUBST1_TAC (← SYM th) THEN ASSUME_TAC (← SYM th))) THEN
    EXISTS_TAC (← q r"a EXP m' * b EXP n'") THEN
    SUBGOAL_THEN
     (← q r"order p (a EXP m') = m /\ order p (b EXP n') = n")
     (fun th => ASM_SIMP_TAC [th, ORDER_MUL_EQ]) THEN
    ASM_SIMP_TAC [ORDER_EXP_GEN] THEN CONJ_TAC THEN
    (COND_CASES_TAC THENL [ASM_MESON_TAC [MULT_CLAUSES], ALL_TAC]) THEN
    REWRITE_TAC [n0] THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN ASM_SIMP_TAC [DIV_MULT]))

  let ORDER_DIVIDES_MAXIMAL ← prove
   r"!p. ~(p = 1)
         ==> ?n. coprime(p,n) /\
                 !m. coprime(p,m) ==> order p m divides order p n"
   (← do
    let a2 ← ARITH_RULE (← q r"a:num <= b ==> b <= a ==> a = b")
    let a1 ← ARITH_RULE (← q r"a <= b ==> ~(a = 0) ==> ~(b = 0)")
    let m0 ← MESON [IN] (← q r"IMAGE f s x <=> x IN IMAGE f s")
    let loc_mxp ← EQ_IMP_RULE (← ISPEC (← q r"IMAGE (order p) {k | k < p}") num_MAX)
    pure (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"p = 0") THEN
    ASM_SIMP_TAC [COPRIME_0, DIVIDES_REFL, UNWIND_THM2] THEN
    MP_TAC loc_mxp.1 THEN
    REWRITE_TAC [m0] THEN
    SIMP_TAC [← GSYM num_FINITE, FINITE_IMAGE, FINITE_NUMSEG_LT] THEN
    REWRITE_TAC [MEMBER_NOT_EMPTY, IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, IN_ELIM_THM] THEN
    ANTS_TAC THENL [ASM_MESON_TAC [LE_1], ALL_TAC] THEN
    REWRITE_TAC [EXISTS_IN_IMAGE, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"n:num") THEN STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"1")) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (MP_TAC o MATCH_MP a1) THEN
    REWRITE_TAC [ORDER_EQ_0, COPRIME_1] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN
    MP_TAC (← SPECL [← q r"p:num", ← q r"m:num", ← q r"n:num"] ORDER_LCM_EXISTS) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"q:num")) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"q MOD p")) THEN
    ASM_REWRITE_TAC [ORDER_MOD, MOD_LT_EQ] THEN
    DISCH_THEN (MP_TAC o MATCH_MP a2) THEN
    ASM_REWRITE_TAC [LE_LCM, ← GSYM DIVIDES_LCM_RIGHT, ORDER_EQ_0]))

  let POWER_RESIDUE_MODULO_COPRIME ← prove
   r"!n a k. coprime(n,a) /\ coprime(k,phi n)
             ==> ?x. (x EXP k == a) (mod n)"
   (REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"1") o MATCH_MP CONG_SOLVE) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q r"l:num")) THEN EXISTS_TAC (← q r"a EXP l") THEN
    REWRITE_TAC [EXP_EXP] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM EXP_1] THEN
    ASM_SIMP_TAC [ORDER_DIVIDES_EXPDIFF] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP ORDER_DIVIDES_PHI) THEN
    POP_ASSUM MP_TAC THEN NUMBER_TAC)

  let POWER_RESIDUE_MODULO_PRIME ← prove
   r"!p a k. prime p /\ ~(p divides a) /\ coprime(k,p - 1)
             ==> ?x. (x EXP k == a) (mod p)"
   (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC POWER_RESIDUE_MODULO_COPRIME THEN
    ASM_SIMP_TAC [PHI_PRIME, PRIME_COPRIME_EQ])

  let INJECTIVE_EXP_MODULO ← prove
   r"!n a b k.
          coprime(k,phi n) /\
          coprime(n,a) /\ coprime(n,b) /\
          (a EXP k == b EXP k) (mod n)
          ==> (a == b) (mod n)"
   (← do
    let n1 ← NUMBER_RULE (← q r"(a:num == b) (mod d) ==> e divides d ==> (a == b) (mod e)")
    let n0 ← NUMBER_RULE (← q r"(a':num == a) (mod n) /\ (b' == b) (mod n)
      ==> (a' == b') (mod n) ==> (a == b) (mod n)")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"?l. (k * l == 1) (mod phi n)") STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC [CONG_SOLVE], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"(a EXP k EXP l == b EXP k EXP l) (mod n)") MP_TAC THENL
     [ASM_MESON_TAC [CONG_EXP], ALL_TAC] THEN
    MATCH_MP_TAC n0 THEN
    CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM EXP_1] THEN
    ASM_SIMP_TAC [ORDER_DIVIDES_EXPDIFF, EXP_EXP] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP n1) THEN
    ASM_SIMP_TAC [ORDER_DIVIDES_PHI]))

  let PRIMITIVE_ROOT_IMP_COPRIME ← prove
   r"!n g. order n g = phi n ==> n = 0 \/ coprime(n,g)"
   (MESON_TAC [ORDER_EQ_0, PHI_EQ_0])

  let PRIMITIVE_ROOT_IMP_PRIME ← prove
   r"!p g. order p g = p - 1 ==> p = 0 \/ prime p"
   (← do
    let a0 ← ARITH_RULE (← q r"h <= p - 1 /\ g <= h ==> g = p - 1 ==> h = p - 1")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"p = 0") THENL
     [ASM_REWRITE_TAC [], REWRITE_TAC [← GSYM PHI_EQ_PRIME]] THEN
    ASM_CASES_TAC (← q r"p = 1") THEN
    ASM_REWRITE_TAC [SUB_REFL, ORDER_EQ_0, COPRIME_1] THEN
    MATCH_MP_TAC a0 THEN
    ASM_SIMP_TAC [PHI_LIMIT_STRONG, ORDER_LE_PHI]))

  let PRIMITIVE_ROOT_IMAGE ← prove
   r"!n g. order n g = phi n
           ==> IMAGE (\i. (g EXP i) MOD n) {i | i < phi n} =
               {a | coprime(a,n) /\ a < n}"
   (← do
    let s1 ← SET_RULE (← q r"t SUBSET IMAGE f s <=> !y. y IN t ==> ?x. x IN s /\ f x = y")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [PHI_0, ← CONJUNCT1 LT, EMPTY_GSPEC, IMAGE_CLAUSES] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN (← q r"coprime(n:num,g)") ASSUME_TAC THENL
     [ASM_MESON_TAC [ORDER_EQ_0, PHI_EQ_0],
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    MATCH_MP_TAC (← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")) THEN CONJ_TAC THENL
     [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
      ASM_REWRITE_TAC [COPRIME_LMOD, COPRIME_LEXP, MOD_LT_EQ] THEN
      ASM_MESON_TAC [COPRIME_SYM],
      DISCH_TAC] THEN
    REWRITE_TAC [s1] THEN
    mpPartSnd (fun c => do lhand (← rand c)) SURJECTIVE_IFF_INJECTIVE_GEN THEN
    ASM_REWRITE_TAC [FINITE_NUMSEG_LT, ← GSYM PHI_ALT, CARD_NUMSEG_LT] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{i:num | i < n}") THEN
      REWRITE_TAC [FINITE_NUMSEG_LT] THEN SET_TAC [],
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC [IN_ELIM_THM, ← GSYM CONG, ORDER_DIVIDES_EXPDIFF] THEN
    MESON_TAC [CONG_IMP_EQ]))

  let PRIMITIVE_ROOT_IMAGE_PRIME ← prove
   r"!p g. order p g = p - 1
           ==> IMAGE (\i. (g EXP i) MOD p) {i | i < p - 1} =
               {a | 0 < a /\ a < p}"
   (← do
    let a0 ← ARITH_RULE (← q r"0 < a <=> ~(a = 0)")
    pure (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"p = 0") THEN
    ASM_REWRITE_TAC [ARITH, ← CONJUNCT1 LT, EMPTY_GSPEC, IMAGE_CLAUSES] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP PRIMITIVE_ROOT_IMP_PRIME) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    MP_TAC (← SPECL [← q r"p:num", ← q r"g:num"] PRIMITIVE_ROOT_IMAGE) THEN
    ASM_SIMP_TAC [PHI_PRIME] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"a:num") THEN
    ASM_CASES_TAC (← q r"a:num < p") THEN ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_SIMP_TAC [PRIME_COPRIME_EQ] THEN
    ASM_CASES_TAC (← q r"a = 0") THEN ASM_REWRITE_TAC [LT_REFL, DIVIDES_0] THEN
    ASM_REWRITE_TAC [a0] THEN
    DISCH_THEN (MP_TAC o MATCH_MP DIVIDES_LE_STRONG) THEN
    ASM_ARITH_TAC))

  let PRIMITIVE_ROOT_SURJECTIVE ← prove
   r"!n g a. ~(n = 0) /\ order n g = phi n /\ coprime(a,n)
             ==> ?m. m < phi n /\ (a == g EXP m) (mod n)"
   (← do
    let s0 ← SET_RULE (← q r"IMAGE f s = t ==> !y. y IN t ==> ?x. x IN s /\ f x = y")
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP PRIMITIVE_ROOT_IMAGE) THEN
    DISCH_THEN (MP_TAC o MATCH_MP s0) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"a MOD n")) THEN
    ASM_REWRITE_TAC [IN_ELIM_THM, COPRIME_LMOD, MOD_LT_EQ] THEN
    MESON_TAC [CONG]))

  let PRIMITIVE_ROOT_SURJECTIVE_ALT ← prove
   r"!n g a. order n g = phi n /\ coprime(a,n)
             ==> ?m. (a == g EXP m) (mod n)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THENL
     [ALL_TAC, ASM_MESON_TAC [PRIMITIVE_ROOT_SURJECTIVE]] THEN
    ASM_SIMP_TAC [COPRIME_0, CONG_MOD_0] THEN MESON_TAC [EXP])

  let PRIMITIVE_ROOT_SURJECTIVE_PRIME ← prove
   r"!p g a. ~(p = 0) /\ order p g = p - 1 /\ coprime(a,p)
             ==> ?m. m < p - 1 /\ (a == g EXP m) (mod p)"
   (← do
    let a0 ← ARITH_RULE (← q r"0 < n <=> ~(n = 0)")
    let s0 ← SET_RULE (← q r"IMAGE f s = t ==> !y. y IN t ==> ?x. x IN s /\ f x = y")
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP PRIMITIVE_ROOT_IMAGE_PRIME) THEN
    DISCH_THEN (MP_TAC o MATCH_MP s0) THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"a MOD p")) THEN
    ASM_REWRITE_TAC [IN_ELIM_THM, COPRIME_LMOD, MOD_LT_EQ] THEN
    REWRITE_TAC [CONG, a0, ← GSYM DIVIDES_MOD] THEN
    ASM_MESON_TAC [PRIME_COPRIME_EQ, COPRIME_SYM, PRIMITIVE_ROOT_IMP_PRIME]))

  let PRIMITIVE_ROOT_SURJECTIVE_PRIME_ALT ← prove
   r"!p g a. order p g = p - 1 /\ coprime(a,p)
             ==> ?m. (a == g EXP m) (mod p)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"p = 0") THENL
     [ALL_TAC, ASM_MESON_TAC [PRIMITIVE_ROOT_SURJECTIVE_PRIME]] THEN
    ASM_SIMP_TAC [COPRIME_0, CONG_MOD_0] THEN MESON_TAC [EXP])

  let PRIME_DIVISOR_SQRT ← prove
   r"!n. prime(n) <=> ~(n = 1) /\ !d. d divides n /\ d EXP 2 <= n ==> (d = 1)"
   (← do
    let a1 ← ARITH_RULE (← q r"~(n * n <= n) <=> n * 1 < n * n")
    pure (GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [prime] THEN
    ASM_CASES_TAC (← q r"n = 1") THEN ASM_SIMP_TAC [DIVIDES_ONE] THEN
    ASM_CASES_TAC (← q r"n = 0") THENL
     [ASM_REWRITE_TAC [DIVIDES_0, LE, EXP_EQ_0, ARITH_EQ] THEN
      MATCH_MP_TAC (← TAUT (← q r"~a /\ ~b ==> (a <=> b)")) THEN CONJ_TAC THENL
       [DISCH_THEN (MP_TAC o SPEC (← q r"2")) THEN REWRITE_TAC [ARITH],
        DISCH_THEN (MP_TAC o SPEC (← q r"0")) THEN REWRITE_TAC [ARITH]],
      ALL_TAC] THEN
    EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC (← q r"d:num") THEN STRIP_TAC THENL
     [ASM_CASES_TAC (← q r"d = n:num") THENL
       [ALL_TAC, ASM_MESON_TAC []] THEN
      UNDISCH_TAC (← q r"d EXP 2 <= n") THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [EXP_2, a1] THEN
      ASM_REWRITE_TAC [LT_MULT_LCANCEL] THEN
      MAP_EVERY UNDISCH_TAC [← q r"~(n = 0)", ← q r"~(n = 1)"] THEN ARITH_TAC,
      ALL_TAC] THEN
    UNDISCH_TAC (← q r"d divides n") THEN REWRITE_TAC [divides] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"e:num") SUBST_ALL_TAC) THEN
    SUBGOAL_THEN (← q r"d EXP 2 <= d * e \/ e EXP 2 <= d * e") MP_TAC THENL
     [REWRITE_TAC [EXP_2, LE_MULT_LCANCEL, LE_MULT_RCANCEL] THEN ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"d:num")),
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"e:num"))] THEN
    ASM_SIMP_TAC [DIVIDES_RMUL, DIVIDES_LMUL, DIVIDES_REFL, MULT_CLAUSES]))

  let PRIME_PRIME_FACTOR_SQRT ← prove
   r"!n. prime n <=>
         ~(n = 0) /\ ~(n = 1) /\ ~(?p. prime p /\ p divides n /\ p EXP 2 <= n)"
   (GEN_TAC THEN ASM_CASES_TAC (← q r"n = 1") THEN ASM_REWRITE_TAC [PRIME_1] THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [PRIME_0] THEN
    GEN_REWRITE_TAC LAND_CONV [PRIME_DIVISOR_SQRT] THEN
    EQ_TAC THENL [MESON_TAC [PRIME_1], ALL_TAC] THEN
    REWRITE_TAC [NOT_EXISTS_THM] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC [] THEN X_GEN_TAC (← q r"d:num") THEN STRIP_TAC THEN
    ASM_CASES_TAC (← q r"d = 1") THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP PRIME_FACTOR) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"p:num") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"p:num")) THEN ASM_REWRITE_TAC [] THEN
    CONJ_TAC THENL [ASM_MESON_TAC [DIVIDES_TRANS], ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"d EXP 2") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [← ExceptT.mk (num_CONV (← q r"2")), EXP_MONO_LE, NOT_SUC] THEN
    ASM_MESON_TAC [DIVIDES_LE, DIVIDES_ZERO])

  -- @@RETURN BEGIN
  return { LUCAS_COPRIME_LEMMA, LUCAS_WEAK, LUCAS, order, EXP_ITER, ORDER_DIVIDES, ORDER,
           ORDER_UNIQUE_ALT, ORDER_MINIMAL, ORDER_WORKS, ORDER_1, ORDER_EQ_0, ORDER_EQ_1,
           ORDER_UNIQUE_PRIME, ORDER_CONG, ORDER_MOD, COPRIME_ORDER, ORDER_DIVIDES_PHI,
           ORDER_LE_PHI, ORDER_DIVIDES_EXPDIFF, ORDER_UNIQUE, ORDER_MUL_LCM,
           ORDER_EXP_GEN, ORDER_EXP, ORDER_INVERSE_MOD, ORDER_MUL_DIVIDES, ORDER_MUL_EQ,
           ORDER_LCM_EXISTS, ORDER_DIVIDES_MAXIMAL, POWER_RESIDUE_MODULO_COPRIME,
           POWER_RESIDUE_MODULO_PRIME, INJECTIVE_EXP_MODULO, PRIMITIVE_ROOT_IMP_COPRIME,
           PRIMITIVE_ROOT_IMP_PRIME, PRIMITIVE_ROOT_IMAGE, PRIMITIVE_ROOT_IMAGE_PRIME,
           PRIMITIVE_ROOT_SURJECTIVE, PRIMITIVE_ROOT_SURJECTIVE_ALT,
           PRIMITIVE_ROOT_SURJECTIVE_PRIME, PRIMITIVE_ROOT_SURJECTIVE_PRIME_ALT,
           PRIME_DIVISOR_SQRT, PRIME_PRIME_FACTOR_SQRT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Pocklington theorem and its variants, prime factorizations, the Lucas and  -/
/- Pocklington variants.  (pocklington.ml 2021-2311)                          -/
/- ------------------------------------------------------------------------- -/

structure Pock where
  -- @@FIELDS
  POCKLINGTON_LEMMA : thm
  POCKLINGTON : thm
  POCKLINGTON_ALT : thm
  primefact : thm
  PRIMEFACT : thm
  PRIMAFACT_CONTAINS : thm
  PRIMEFACT_VARIANT : thm
  LUCAS_PRIMEFACT : thm
  POCKLINGTON_PRIMEFACT : thm
  deriving Inhabited

@[nospecialize]
def setupPock [HolBase] (D : PocklingtonDeps) (BBasics : Basics) (BPhi : Phi) (BOrder : Order) :
    ExceptT String IO Pock := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, LIST_INDUCT_TAC, MESON_TAC,
        new_definition, num_CONV, .. } := D
  let { ALL, ARITH_EQ, CONTRAPOS_THM, COPRIME_EXP, COPRIME_SYM, DIVIDES_ADD,
        DIVIDES_ADD_REVL, DIVIDES_LE, DIVIDES_LMUL, .. } := D.core1
  let { DIVIDES_ONE, DIVIDES_RMUL, DIVISION, DIV_MULT, EQ_MULT_LCANCEL, EXP, EXP_2,
        EXP_EQ_0, EXP_EXP, EXP_MONO_LE, EXP_MULT, EXP_ONE, .. } := D.core2
  let { ITLIST, LEFT_IMP_EXISTS_THM, LE_TRANS, MEM, MOD_EQ_0, MOD_EXP_MOD, .. } := D.core3
  let { ALL_IMP, ALL_MEM, LT_MULT_RCANCEL, MOD_LE, MOD_MULT, MULT_AC, MULT_ASSOC,
        MULT_CLAUSES, MULT_SYM, NOT_FORALL_THM, NOT_IMP, NOT_SUC, PRIME_0, PRIME_1,
        PRIME_DIVPROD, PRIME_FACTOR, PRIME_GE_2, cong, coprime, divides, num_WF, prime, .. } := D.core4
  let { CONG_0_DIVIDES, CONG_1_DIVIDES, CONG_COPRIME, CONG_DIVIDES, CONG_EXP, CONG_MOD,
        CONG_REFL, CONG_SUB, CONG_SYM, CONG_TRANS, nat_mod, .. } := BBasics
  let { FERMAT_LITTLE, PHI_PRIME_EQ, .. } := BPhi
  let { LUCAS, ORDER, ORDER_DIVIDES, PRIME_PRIME_FACTOR_SQRT, .. } := BOrder
  -- @@SCOPE END

  let POCKLINGTON_LEMMA ← prove
   r"!a n q r.
          2 <= n /\ (n - 1 = q * r) /\
          (a EXP (n - 1) == 1) (mod n) /\
          (!p. prime(p) /\ p divides q
               ==> coprime(a EXP ((n - 1) DIV p) - 1,n))
          ==> !p. prime p /\ p divides n ==> (p == 1) (mod q)"
   (← do
    let a2 ← ARITH_RULE (← q r"(a * p * b = p * c) <=> (p * a * b = p * c)")
    let t ← TAUT (← q r"~a ==> a ==> b")
    let a1 ← ARITH_RULE (← q r"2 <= n ==> (n - 1 = SUC(n - 2))")
    let a0 ← ARITH_RULE (← q r"(p - 1 = q * d) ==> ~(p = 0) ==> (p + q * 0 = 1 + q * d)")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"order p (a EXP r) = q") ASSUME_TAC THENL
     [ALL_TAC,
      SUBGOAL_THEN (← q r"coprime(a EXP r,p)") (MP_TAC o MATCH_MP FERMAT_LITTLE) THENL
       [ALL_TAC,
        ASM_REWRITE_TAC [ORDER_DIVIDES] THEN
        SUBGOAL_THEN (← q r"phi p = p - 1") SUBST1_TAC THENL
         [ASM_MESON_TAC [PHI_PRIME_EQ], ALL_TAC] THEN
        REWRITE_TAC [divides, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"d:num") THEN
        DISCH_THEN (MP_TAC o MATCH_MP a0) THEN
        REWRITE_TAC [nat_mod, cong] THEN ASM_MESON_TAC [PRIME_0]] THEN
      ONCE_REWRITE_TAC [COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_EXP THEN
      UNDISCH_TAC (← q r"(a EXP (n - 1) == 1) (mod n)") THEN
      ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC [coprime, NOT_FORALL_THM, NOT_IMP] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"d:num") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"d = p:num") SUBST_ALL_TAC THENL
       [ASM_MESON_TAC [prime], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"p divides (a EXP (n - 1))") ASSUME_TAC THENL
       [FIRST_ASSUM (SUBST1_TAC o MATCH_MP a1) THEN
        REWRITE_TAC [EXP] THEN ASM_SIMP_TAC [DIVIDES_RMUL],
        ALL_TAC] THEN
      REWRITE_TAC [cong, nat_mod] THEN
      SUBGOAL_THEN (← q r"~(p divides 1)") MP_TAC THENL
       [ASM_MESON_TAC [DIVIDES_ONE, PRIME_1], ALL_TAC] THEN
      ASM_MESON_TAC [DIVIDES_RMUL, DIVIDES_ADD, DIVIDES_ADD_REVL]] THEN
    SUBGOAL_THEN (← q r"(order p (a EXP r)) divides q") MP_TAC THENL
     [REWRITE_TAC [← GSYM ORDER_DIVIDES, EXP_EXP] THEN
      ONCE_REWRITE_TAC [MULT_SYM] THEN
      UNDISCH_TAC (← q r"(a EXP (n - 1) == 1) (mod n)") THEN
      ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC (← q r"p divides n") THEN REWRITE_TAC [divides] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"b:num") SUBST_ALL_TAC) THEN
      REWRITE_TAC [cong, nat_mod] THEN MESON_TAC [MULT_AC],
      ALL_TAC] THEN
    REWRITE_TAC [divides, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q r"d:num") THEN
    ASM_CASES_TAC (← q r"d = 1") THEN ASM_SIMP_TAC [MULT_CLAUSES] THEN
    DISCH_THEN (ASSUME_TAC o SYM) THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP PRIME_FACTOR) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"P:num") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"P divides q") ASSUME_TAC THENL
     [ASM_MESON_TAC [DIVIDES_LMUL], ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"P:num")) THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC t THEN
    UNDISCH_TAC (← q r"P divides q") THEN REWRITE_TAC [divides] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"s:num") SUBST_ALL_TAC) THEN
    REWRITE_TAC [← GSYM MULT_ASSOC] THEN
    SUBGOAL_THEN (← q r"~(P = 0)") ASSUME_TAC THENL
     [ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN
    ASM_SIMP_TAC [DIV_MULT] THEN
    UNDISCH_TAC (← q r"P divides d") THEN REWRITE_TAC [divides] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:num") SUBST_ALL_TAC) THEN
    UNDISCH_TAC (← q r"order p (a EXP r) * P * t = P * s") THEN
    ONCE_REWRITE_TAC [a2] THEN
    REWRITE_TAC [EQ_MULT_LCANCEL] THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (SUBST_ALL_TAC o SYM) THEN REWRITE_TAC [coprime] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"p:num")) THEN REWRITE_TAC [NOT_IMP] THEN
    CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [PRIME_1]] THEN
    ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [← AC MULT_AC (← q r"(d * t) * r = r * d * t")] THEN
    REWRITE_TAC [EXP_MULT] THEN
    MATCH_MP_TAC CONG_1_DIVIDES THEN
    MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC (← q r"1 EXP t") THEN
    SIMP_TAC [CONG_EXP, ORDER] THEN REWRITE_TAC [EXP_ONE, CONG_REFL]))

  let POCKLINGTON ← prove
   r"!a n q r.
          2 <= n /\ (n - 1 = q * r) /\ n <= q EXP 2 /\
          (a EXP (n - 1) == 1) (mod n) /\
          (!p. prime(p) /\ p divides q
               ==> coprime(a EXP ((n - 1) DIV p) - 1,n))
          ==> prime(n)"
   (← do
    let a0 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0) /\ ~(n = 1)")
    pure (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [PRIME_PRIME_FACTOR_SQRT] THEN
    ASM_SIMP_TAC [a0] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"p:num") STRIP_ASSUME_TAC) THEN
    MP_TAC (← SPECL [← q r"a:num", ← q r"n:num", ← q r"q:num", ← q r"r:num"] POCKLINGTON_LEMMA) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o SPEC (← q r"p:num")) THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"p EXP 2 <= q EXP 2") MP_TAC THENL
     [ASM_MESON_TAC [LE_TRANS], ALL_TAC] THEN
    REWRITE_TAC [← ExceptT.mk (num_CONV (← q r"2")), EXP_MONO_LE, NOT_SUC] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o MATCH_MP CONG_1_DIVIDES) THEN
    DISCH_THEN (MP_TAC o MATCH_MP DIVIDES_LE) THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC))

  let POCKLINGTON_ALT ← prove
   r"!a n q r.
          2 <= n /\ (n - 1 = q * r) /\ n <= q EXP 2 /\
          (a EXP (n - 1) == 1) (mod n) /\
          (!p. prime(p) /\ p divides q
               ==> ?b. (a EXP ((n - 1) DIV p) == b) (mod n) /\
                       coprime(b - 1,n))
          ==> prime(n)"
   (← do
    let a2 ← ARITH_RULE (← q r"~(2 <= 1)")
    let a0 ← ARITH_RULE (← q r"2 <= n ==> (n - 1 = SUC(n - 2))")
    let a1 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC POCKLINGTON THEN
    MAP_EVERY EXISTS_TAC [← q r"a:num", ← q r"q:num", ← q r"r:num"] THEN
    ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"p:num") THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"p:num")) THEN ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"b:num") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"(a EXP ((q * r) DIV p) - 1 == b - 1) (mod n)")
     (fun th => ASM_MESON_TAC [CONG_COPRIME, COPRIME_SYM, th]) THEN
    MATCH_MP_TAC CONG_SUB THEN ASM_REWRITE_TAC [CONG_REFL] THEN
    REWRITE_TAC [a1, EXP_EQ_0] THEN
    SUBGOAL_THEN (← q r"~(a = 0)") ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC (← q r"(a EXP (n - 1) == 1) (mod n)") THEN
      SIMP_TAC [a0, ← ASSUME (← q r"a = 0"), ← ASSUME (← q r"2 <= n")] THEN
      REWRITE_TAC [MULT_CLAUSES, EXP] THEN
      ONCE_REWRITE_TAC [CONG_SYM] THEN
      REWRITE_TAC [CONG_0_DIVIDES, DIVIDES_ONE] THEN
      UNDISCH_TAC (← q r"2 <= n") THEN ARITH_TAC,
      ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC (← q r"(a EXP ((q * r) DIV p) == b) (mod n)") THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [CONG_0_DIVIDES] THEN
    SUBGOAL_THEN (← q r"~(n divides (a EXP (n - 1)))") MP_TAC THENL
     [ASM_MESON_TAC [CONG_DIVIDES, DIVIDES_ONE, a2],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [CONTRAPOS_THM] THEN UNDISCH_TAC (← q r"p divides q") THEN
    GEN_REWRITE_TAC LAND_CONV [divides] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"d:num") SUBST1_TAC) THEN
    REWRITE_TAC [← GSYM MULT_ASSOC] THEN
    SUBGOAL_THEN (← q r"~(p = 0)") ASSUME_TAC THENL
     [ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN
    ASM_SIMP_TAC [DIV_MULT] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EXP_MULT] THEN
    SUBGOAL_THEN (← q r"p = SUC(p - 1)") SUBST1_TAC THENL
     [UNDISCH_TAC (← q r"~(p = 0)") THEN ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [EXP, DIVIDES_RMUL]))

  let primefact ← new_definition
   r"primefact ps n <=> (ITLIST (*) ps 1 = n) /\ !p. MEM p ps ==> prime(p)"

  let PRIMEFACT ← prove
   r"!n. ~(n = 0) ==> ?ps. primefact ps n"
   (← do
    let a1 ← ARITH_RULE (← q r"~(p = 0) /\ ~(p = 1) ==> 1 < p")
    let a0 ← ARITH_RULE (← q r"n = 1 * n")
    pure (MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q r"n:num") THEN
    ASM_CASES_TAC (← q r"n = 1") THEN ASM_REWRITE_TAC [] THENL
     [REPEAT DISCH_TAC THEN EXISTS_TAC (← q r"[]:num list") THEN
      REWRITE_TAC [primefact, ITLIST, MEM], ALL_TAC] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q r"p:num") STRIP_ASSUME_TAC o
      MATCH_MP PRIME_FACTOR) THEN
    UNDISCH_TAC (← q r"p divides n") THEN REWRITE_TAC [divides] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"m:num") SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"m:num")) THEN
    UNDISCH_TAC (← q r"~(p * m = 0)") THEN
    ASM_CASES_TAC (← q r"m = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN DISCH_TAC THEN
    GEN_REWRITE_TAC (funpow 3 LAND_CONV) [a0] THEN
    ASM_REWRITE_TAC [LT_MULT_RCANCEL] THEN
    SUBGOAL_THEN (← q r"1 < p") (fun th => REWRITE_TAC [th]) THENL
     [MATCH_MP_TAC a1 THEN
      REPEAT STRIP_TAC THEN UNDISCH_TAC (← q r"prime p") THEN
      ASM_REWRITE_TAC [PRIME_0, PRIME_1], ALL_TAC] THEN
    REWRITE_TAC [primefact] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"ps:num list") ASSUME_TAC) THEN
    EXISTS_TAC (← q r"CONS (p:num) ps") THEN
    ASM_REWRITE_TAC [MEM, ITLIST] THEN ASM_MESON_TAC []))

  let PRIMAFACT_CONTAINS ← prove
   r"!ps n. primefact ps n ==> !p. prime p /\ p divides n ==> MEM p ps"
   (REPEAT GEN_TAC THEN REWRITE_TAC [primefact] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    POP_ASSUM (SUBST1_TAC o SYM) THEN
    SPEC_TAC (← q r"ps:num list", ← q r"ps:num list") THEN LIST_INDUCT_TAC THEN
    REWRITE_TAC [ITLIST, MEM] THENL
     [ASM_MESON_TAC [DIVIDES_ONE, PRIME_1], ALL_TAC] THEN
    STRIP_TAC THEN GEN_TAC THEN
    DISCH_THEN (fun th => tactic_of do
      pure (ASSUME_TAC (← CONJUNCT1 th) THEN MP_TAC th)) THEN
    DISCH_THEN (DISJ_CASES_TAC o MATCH_MP PRIME_DIVPROD) THEN
    ASM_MESON_TAC [prime, PRIME_1])

  let PRIMEFACT_VARIANT ← prove
   r"!ps n. primefact ps n <=> (ITLIST (*) ps 1 = n) /\ ALL prime ps"
   (REPEAT GEN_TAC THEN REWRITE_TAC [primefact] THEN AP_TERM_TAC THEN
    SPEC_TAC (← q r"ps:num list", ← q r"ps:num list") THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [MEM, ALL] THEN ASM_MESON_TAC [])

  let LUCAS_PRIMEFACT ← prove
   r"2 <= n /\
     (a EXP (n - 1) == 1) (mod n) /\
     (ITLIST (*) ps 1 = n - 1) /\
     ALL (\p. prime p /\ ~(a EXP ((n - 1) DIV p) == 1) (mod n)) ps
     ==> prime n"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC LUCAS THEN
    EXISTS_TAC (← q r"a:num") THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"primefact ps (n - 1)") MP_TAC THENL
     [ASM_REWRITE_TAC [PRIMEFACT_VARIANT] THEN MATCH_MP_TAC ALL_IMP THEN
      EXISTS_TAC (← q r"\p. prime p /\ ~(a EXP ((n - 1) DIV p) == 1) (mod n)") THEN
      ASM_SIMP_TAC [], ALL_TAC] THEN
    DISCH_THEN (ASSUME_TAC o MATCH_MP PRIMAFACT_CONTAINS) THEN
    X_GEN_TAC (← q r"p:num") THEN DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN UNDISCH_TAC
     (← q r"ALL (\p. prime p /\ ~(a EXP ((n - 1) DIV p) == 1) (mod n)) ps") THEN
    SPEC_TAC (← q r"ps:num list", ← q r"ps:num list") THEN LIST_INDUCT_TAC THEN
    SIMP_TAC [ALL, MEM] THEN ASM_MESON_TAC [])

  let POCKLINGTON_PRIMEFACT ← prove
   r"2 <= n /\ (q * r = n - 1) /\ n <= q * q
     ==> ((a EXP r) MOD n = b)
         ==> (ITLIST (*) ps 1 = q)
             ==> ((b EXP q) MOD n = 1)
                 ==> ALL (\p. prime p /\
                              coprime((b EXP (q DIV p)) MOD n - 1,n)) ps
                     ==> prime n"
   (← do
    let b8 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0)")
    let b7 ← ARITH_RULE (← q r"~(p = 0) ==> (p = SUC(p - 1))")
    let b6 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0)")
    let b5 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0)")
    let b4 ← ARITH_RULE (← q r"a <= b /\ ~(a = 0) ==> 1 <= a /\ 1 <= b")
    let b3 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0)")
    let t ← TAUT (← q r"(a ==> (b <=> c)) ==> a /\ b ==> c")
    let b2 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0)")
    let b1 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0)")
    pure (DISCH_THEN (fun th => DISCH_THEN (SUBST1_TAC o SYM) THEN MP_TAC th) THEN
    SIMP_TAC [MOD_EXP_MOD, b1] THEN
    SIMP_TAC [← ONCE_REWRITE_RULE [MULT_SYM] EXP_EXP] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC POCKLINGTON THEN
    MAP_EVERY EXISTS_TAC [← q r"a:num", ← q r"q:num", ← q r"r:num"] THEN
    ASM_REWRITE_TAC [EXP_2] THEN CONJ_TAC THENL
     [MP_TAC (← SPECL [← q r"a EXP (n - 1)", ← q r"n:num"] DIVISION) THEN
      ASM_SIMP_TAC [b2] THEN
      STRIP_TAC THEN ABBREV_TAC (← q r"Q = a EXP (n - 1) DIV n") THEN
      ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [cong, nat_mod] THEN
      MAP_EVERY EXISTS_TAC [← q r"0", ← q r"Q:num"] THEN ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"primefact ps q") MP_TAC THENL
     [ASM_REWRITE_TAC [PRIMEFACT_VARIANT] THEN MATCH_MP_TAC ALL_IMP THEN
      EXISTS_TAC (← q r"\p. prime p /\ coprime(a EXP (q DIV p * r) MOD n - 1,n)") THEN
      ASM_SIMP_TAC [], ALL_TAC] THEN
    DISCH_THEN (ASSUME_TAC o MATCH_MP PRIMAFACT_CONTAINS) THEN
    X_GEN_TAC (← q r"p:num") THEN
    DISCH_THEN (fun th => STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [← GSYM ALL_MEM]) THEN
    DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN
    MATCH_MP_TAC t THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC [COPRIME_SYM] THEN
    SUBGOAL_THEN (← q r"~(p = 0)") ASSUME_TAC THENL
     [ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"q DIV p * r = (n - 1) DIV p") SUBST1_TAC THENL
     [UNDISCH_TAC (← q r"p divides q") THEN REWRITE_TAC [divides] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"d:num") SUBST_ALL_TAC) THEN
      UNDISCH_THEN (← q r"(p * d) * r = n - 1") (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC [DIV_MULT, ← GSYM MULT_ASSOC],
      ALL_TAC] THEN
    MATCH_MP_TAC CONG_COPRIME THEN MATCH_MP_TAC CONG_SUB THEN
    ASM_SIMP_TAC [CONG_MOD, b3, CONG_REFL] THEN
    MATCH_MP_TAC b4 THEN
    ASM_SIMP_TAC [MOD_LE, b5] THEN
    ASM_SIMP_TAC [MOD_EQ_0, b6] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"s:num") MP_TAC) THEN
    DISCH_THEN (MP_TAC o C AP_THM (← q r"p:num") o AP_TERM (← q r"(EXP)")) THEN
    REWRITE_TAC [EXP_EXP] THEN
    SUBGOAL_THEN (← q r"(n - 1) DIV p * p = n - 1") SUBST1_TAC THENL
     [SUBST1_TAC (← SYM (← ASSUME (← q r"q * r = n - 1"))) THEN
      UNDISCH_TAC (← q r"p divides q") THEN REWRITE_TAC [divides] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"d:num") SUBST1_TAC) THEN
      REWRITE_TAC [← GSYM MULT_ASSOC] THEN
      ASM_MESON_TAC [DIV_MULT, MULT_AC, PRIME_0],
      ALL_TAC] THEN
    DISCH_THEN (MP_TAC o C AP_THM (← q r"n:num") o AP_TERM (← q r"(MOD)")) THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP b7) THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [EXP, ← GSYM MULT_ASSOC] THEN
    ASM_SIMP_TAC [MOD_MULT, b8] THEN
    REWRITE_TAC [ARITH_EQ]))

  -- @@RETURN BEGIN
  return { POCKLINGTON_LEMMA, POCKLINGTON, POCKLINGTON_ALT, primefact, PRIMEFACT,
           PRIMAFACT_CONTAINS, PRIMEFACT_VARIANT, LUCAS_PRIMEFACT, POCKLINGTON_PRIMEFACT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Utility functions, PARI/GP factoring, Pratt certificates and the          -/
/- primality-proving rules.  (pocklington.ml 2312-2623)                      -/
/- ------------------------------------------------------------------------- -/

/-- `even_num n` (pocklington.ml 2316). -/
def even_num (n : Rat) : Bool := mod_num n num_2 == num_0

/-- `odd_num = not o even_num` (pocklington.ml 2318). -/
def odd_num (n : Rat) : Bool := !(even_num n)

/-- Least `p >= 0` with `x <= 2^p`: the inner recursion (pocklington.ml 2324). -/
partial def log2Aux (x y : Rat) : Rat :=
  if x < num_1 then y else log2Aux (quo_num x num_2) (y + num_1)

/-- `log2 x` (pocklington.ml 2324). -/
def log2 (x : Rat) : Rat := log2Aux (x - num_1) num_0

/-- `powermod x m n = x^m mod n` (pocklington.ml 2332). -/
partial def powermod (x m n : Rat) : Rat :=
  if m == num_0 then num_1
  else
    let y := powermod x (quo_num m num_2) n
    let z := mod_num (y * y) n
    if even_num m then z else mod_num (x * z) n

/-- OCaml's `Invalid_argument`, kept apart from `Failure`. -/
def invalidArgPrefix : String := "Invalid_argument "

/-- Whether an error is an `Invalid_argument` (so a `Failure` handler skips it). -/
def isInvalidArg (e : String) : Bool := e.startsWith invalidArgPrefix

/-- `try x with Failure _ -> h ()`: OCaml's `Invalid_argument` and
    `Match_failure` are not caught. -/
def tryFailure {α : Type} (x : ExceptT String IO α) (h : Unit → ExceptT String IO α) :
    ExceptT String IO α :=
  tryCatch x (fun e => if isInvalidArg e || e == "Match_failure" then throw e else h ())

/-- `factor n`: factor `n` into (probable) primes with multiplicities, by a
    call to PARI/GP through the shell (pocklington.ml 2338-2362).  Fails with
    `factor: Call to GP/PARI failed` when the shell command's exit code is
    non-zero (so always, when `gp` is not installed). -/
def factor (n : Rat) : ExceptT String IO (List (Rat × Rat)) := do
  if n == num_1 then pure []
  else
    -- `Filename.temp_file "pocklington" ".out"`
    let (handle, filename) ← IO.FS.createTempFile
    let _ := handle
    let s := "echo 'print(factorint(" ++ string_of_num n ++
             "))  \n quit' | gp >" ++ filename.toString ++ " 2>/dev/null"
    let out ← IO.Process.output { cmd := "sh", args := #["-c", s] }
    if out.exitCode == 0 then
      -- suck_file: read then remove
      let data ← IO.FS.readFile filename
      IO.FS.removeFile filename
      -- extract_output
      let l0 := explode data
      let l0' := l0.reverse
      let i1 ← liftExcept (index "]" l0')
      let l1 := (← liftExcept (chop_list i1 l0')).2
      let i2 ← liftExcept (index "[" l1)
      let l2 := "[" :: ((← liftExcept (chop_list i2 l1)).1).reverse
      let tm ← ExceptT.mk (HolCore.Parser.parse_term (implode l2))
      let lst ← liftExcept (dest_list tm)
      lst.mapM (fun t => do
        let (l, r) ← liftExcept (HolMath.Pair.dest_pair t)
        pure ((← liftExcept (dest_numeral l)), (← liftExcept (dest_numeral r))))
    else throw "factor: Call to GP/PARI failed"

/-- `PARI_THRESHOLD = pow2 25` (pocklington.ml 2370). -/
def PARI_THRESHOLD : Rat := pow2 25

/-- `multifactor`'s `findfactor` (pocklington.ml 2373). -/
partial def findfactor (m n : Rat) : Rat :=
  if mod_num n m == num_0 then m
  else if m * m > n then n
  else findfactor (m + num_1) n

/-- `multifactor`'s `stupidfactor` (pocklington.ml 2377). -/
partial def stupidfactor (n : Rat) : List Rat :=
  let p := findfactor num_2 n
  if p == n then [n] else p :: stupidfactor (quo_num n p)

/-- `multifactor`'s `multilist` (pocklington.ml 2380). -/
def multilist : List (Rat × Rat) → List Rat
  | [] => []
  | (x, n) :: t => replicate x n.num.toNat ++ multilist t

/-- `multifactor n` (pocklington.ml 2372-2386): the multiset of prime factors
    of `n`.  Falls back to `stupidfactor` for small numbers or when PARI/GP is
    unavailable. -/
def multifactor (n : Rat) : ExceptT String IO (List Rat) :=
  tryFailure
    (do if n < PARI_THRESHOLD then throw "" else pure (multilist (← factor n)))
    (fun _ => pure (sort (· < ·) (stupidfactor n)))

/-- Pratt primality certificates (pocklington.ml 2392-2395). -/
inductive certificate where
  | Prime_2
  | Primroot_and_factors : ((Rat × List Rat) × Rat × List (Rat × certificate)) → certificate
  deriving Inhabited

/-- `find_primitive_root`'s inner recursion (pocklington.ml 2398). -/
partial def findPrimitiveRootAux (a m : Rat) (ms : List Rat) (n : Rat) : Rat :=
  if gcd_num a n == num_1 && powermod a m n == num_1 &&
     forall' (fun k => powermod a k n != num_1) ms
  then a
  else findPrimitiveRootAux (a + num_1) m ms n

/-- `find_primitive_root m ms n` (pocklington.ml 2398-2408). -/
def find_primitive_root (m : Rat) (ms : List Rat) (n : Rat) : Except String Rat :=
  if n < num_2 then failwith "find_primitive_root: input too small"
  else pure (findPrimitiveRootAux num_2 m ms n)

/-- `uniq_num`'s inner `uniq` (pocklington.ml 2411): `none` models the
    `Unchanged` exception. -/
partial def uniqAux (x : Rat) : List Rat → Option (List Rat)
  | [] => none
  | h :: t =>
    if x == h then
      match uniqAux x t with
      | none => some (h :: t)
      | some r => some r
    else
      match uniqAux h t with
      | none => none
      | some r => some (x :: r)

/-- `uniq_num l` (pocklington.ml 2410-2419): `none` models `Unchanged`. -/
def uniq_num : List Rat → Option (List Rat)
  | [] => some []
  | h :: t => uniqAux h t

/-- `setify_num s` (pocklington.ml 2421). -/
def setify_num (s : List Rat) : List Rat :=
  let s' := sort (· ≤ ·) s
  match uniq_num s' with
  | none => s'
  | some r => r

/-- `general_certify_prime`'s `cert_prime` (pocklington.ml 2425-2436). -/
partial def certPrime (factorizer : Rat → ExceptT String IO (List Rat)) :
    Rat → ExceptT String IO certificate := fun n => do
  if n ≤ num_2 then
    if n == num_2 then pure .Prime_2
    else throw "certify_prime: not a prime!"
  else do
    let m := n - num_1
    let pfact ← factorizer m
    let primes := setify_num pfact
    let ms := primes.map (fun d => divide_num m d)
    let a ← liftExcept (find_primitive_root m ms n)
    let sub ← primes.mapM (fun p => do pure (p, ← certPrime factorizer p))
    pure (.Primroot_and_factors ((n, pfact), a, sub))

/-- `general_certify_prime factorizer` (pocklington.ml 2424-2438). -/
partial def generalCertifyPrime (factorizer : Rat → ExceptT String IO (List Rat)) :
    Rat → ExceptT String IO certificate := fun n => do
  if (← factorizer n).length == 1 then certPrime factorizer n
  else throw "guided_certify_prime: input is not a prime"

/-- `certify_prime = general_certify_prime multifactor` (pocklington.ml 2440). -/
def certify_prime : Rat → ExceptT String IO certificate := generalCertifyPrime multifactor

/-- `lookup_under_num n l` (pocklington.ml 2448-2452). -/
partial def lookup_under_num {α : Type} (n : Rat) : List (Rat × α) → Except String α
  | [] => failwith "lookup_under_num"
  | h :: t => if h.1 == n then pure h.2 else lookup_under_num n t

/-- `split_factors q qs ps n` (pocklington.ml 2454-2456). -/
partial def split_factors (q : Rat) (qs ps : List Rat) (n : Rat) :
    Except String (List Rat × List Rat) :=
  if q * q ≥ n then pure (qs.reverse, ps)
  else match ps with
    | h :: t => split_factors (q * h) (h :: qs) t n
    | [] => failwith "hd"

/-- The constants, conversions, theorems and cache `check_certificate` closes
    over (pocklington.ml 2458-2498). -/
structure CheckCtx where
  (n_tm a_tm q_tm r_tm b_tm ps_tm : term)
  (conv_itlist conv_all subarith_conv EXP_MOD_CONV NUM_REDUCE_CONV : ioconv)
  (POCKLINGTON_PRIMEFACT PRIME_2 : thm)
  mk_numeral : Rat → Except String term
  mk_flist : List term → IO (Except String term)
  cache : IO.Ref (List (Rat × thm))

/-- `check_certificate`'s recursion (pocklington.ml 2493-2520). -/
partial def checkCertificate [HolBase] (C : CheckCtx) :
    certificate → ExceptT String IO thm
  | .Prime_2 => pure C.PRIME_2
  | .Primroot_and_factors ((n, ps), a, ncerts) => do
    match lookup_under_num n (← C.cache.get) with
    | .ok th => pure th
    | .error _ => do
      let (qs, rs) ← liftExcept (split_factors num_1 [] ps.reverse n)
      let q := HolCore.Lib.itlist (· * ·) qs num_1
      let r := HolCore.Lib.itlist (· * ·) rs num_1
      let qsNums ← liftExcept (qs.mapM C.mk_numeral)
      let psList ← ExceptT.mk (C.mk_flist qsNums)
      let nNum ← liftExcept (C.mk_numeral n)
      let qNum ← liftExcept (C.mk_numeral q)
      let rNum ← liftExcept (C.mk_numeral r)
      let aNum ← liftExcept (C.mk_numeral a)
      let th1 ← INST [(nNum, C.n_tm), (psList, C.ps_tm), (qNum, C.q_tm),
                      (rNum, C.r_tm), (aNum, C.a_tm)] C.POCKLINGTON_PRIMEFACT
      let th2 ← MP th1 (← EQT_ELIM (← ExceptT.mk (C.NUM_REDUCE_CONV
        (← liftExcept (lhand (concl th1))))))
      let tha ← ExceptT.mk (C.EXP_MOD_CONV (← liftExcept (do lhand (← lhand (concl th2)))))
      let thb ← MP (← INST [((← liftExcept (rand (concl tha))), C.b_tm)] th2) tha
      let th3 ← MP thb (← EQT_ELIM (← ExceptT.mk (C.conv_itlist
        (← liftExcept (lhand (concl thb))))))
      let th4 ← MP th3 (← ExceptT.mk (C.EXP_MOD_CONV
        (← liftExcept (do lhand (← lhand (concl th3))))))
      let th5 ← ExceptT.mk (C.conv_all (← liftExcept (lhand (concl th4))))
      let th6 ← TRANS th5 (← ExceptT.mk (C.subarith_conv (← liftExcept (rand (concl th5)))))
      let (_, imp) ← EQ_IMP_RULE th6
      let th7 ← IMP_TRANS imp th4
      let ants := conjuncts (← liftExcept (lhand (concl th7)))
      let certs ← ants.mapM (fun t => do
        let num ← liftExcept (do dest_numeral (← rand t))
        liftExcept (lookup_under_num num ncerts))
      let ths ← certs.mapM (checkCertificate C)
      let fth ← MP th7 (← HolLight.end_itlist CONJ ths)
      C.cache.modify (fun l => (n, fth) :: l)
      pure fth

/-- `extract_primes_from_certificate`'s `extr` (pocklington.ml 2538-2542). -/
partial def extr : certificate → List Rat → List Rat
  | .Prime_2, acc => num_2 :: acc
  | .Primroot_and_factors ((p, _), _, l), acc =>
    HolCore.Lib.itlist (fun (qd : Rat × certificate) a => extr qd.2 (qd.1 :: a)) l (p :: acc)

/-- `extract_primes_from_certificate n` (pocklington.ml 2537-2544). -/
def extract_primes_from_certificate (n : Rat) : ExceptT String IO (List String) := do
  let c ← certify_prime n
  pure (uniq ((sort (· < ·) (extr c [])).map string_of_num))

/-- `guided_certify_prime`'s `guidedfactor` (pocklington.ml 2547-2550). -/
partial def guidedfactor (hints : List Rat) (n : Rat) : Except String (List Rat) :=
  if exists' (fun p => p == n) hints then pure [n]
  else do
    let p ← find (fun p => mod_num n p == num_0) hints
    pure (p :: (← guidedfactor hints (quo_num n p)))

/-- `guided_certify_prime hints` (pocklington.ml 2546-2551). -/
def guided_certify_prime (hints : List Rat) : Rat → ExceptT String IO certificate :=
  generalCertifyPrime (fun n => liftExcept (guidedfactor hints n))

/-- lib.ml's `time` for a rule, as the load-time examples use it
    (`time PRIME_TEST`, `time PROVE_PRIMEFACT`). -/
def timeThm {α : Type} (f : α → ExceptT String IO thm) (x : α) : ExceptT String IO thm :=
  ExceptT.mk (HolCore.Lib.time (fun t => (f t).run) x)

/- ------------------------------------------------------------------------- -/
/- The primality-proving rules, as one bundle.                               -/
/- ------------------------------------------------------------------------- -/

/-- A rule taking a number (`PROVE_PRIME`, `PROVE_PRIMEFACT`). -/
abbrev RatRule := Rat → ExceptT String IO thm
/-- A rule taking a term (`PRIME_TEST`, `PRIME_CONV`). -/
abbrev TermRule := term → ExceptT String IO thm
/-- `check_certificate`. -/
abbrev CertRule := certificate → ExceptT String IO thm
/-- `GUIDED_PROVE_PRIME`. -/
abbrev GuidedRule := List Rat → Rat → ExceptT String IO thm
/-- `PRIME_RULE`. -/
abbrev PrimeRuleTy := List String → term → ExceptT String IO thm
/-- `prime_theorem_cache`. -/
abbrev ThmCache := IO.Ref (List (Rat × thm))

structure Certify where
  -- @@FIELDS
  prime_theorem_cache : Option ThmCache
  check_certificate : CertRule
  PROVE_PRIME : RatRule
  PROVE_PRIMEFACT : RatRule
  PRIME_TEST : TermRule
  PRIME_CONV : TermRule
  GUIDED_PROVE_PRIME : GuidedRule
  PRIME_RULE : PrimeRuleTy
  deriving Inhabited

@[nospecialize]
def setupCertify [HolBase] (D : PocklingtonDeps) (BPock : Pock) :
    ExceptT String IO Certify := do
  -- @@SCOPE BEGIN
  let { COPRIME_CONV, EXP_MOD_CONV, MESON_TAC, NUM_DIV_CONV, NUM_EQ_CONV,
        NUM_MULT_CONV, NUM_REDUCE_CONV, NUM_SUB_CONV, mk_flist, mk_numeral,
        mk_small_numeral, .. } := D
  let { ALL, BETA_THM, .. } := D.core1
  let { ITLIST, .. } := D.core3
  let { PRIME_0, PRIME_1, PRIME_2, divides, prime, .. } := D.core4
  let { POCKLINGTON_PRIMEFACT, PRIMEFACT_VARIANT, .. } := BPock
  -- @@SCOPE END

  -- `prime_theorem_cache = ref []` (pocklington.ml 2446): created once, when
  -- this (cached) setup runs at load, and closed over by the rules below.
  let loc_prime_theorem_cache : ThmCache ← IO.mkRef []
  -- Exported as `some ref`: a structure with an `IO.Ref` field cannot derive
  -- `Inhabited` computably, so the field is an `Option`.
  let prime_theorem_cache : Option ThmCache ← pure (some loc_prime_theorem_cache)

  -- `check_certificate` (pocklington.ml 2458-2521): its nets are built once.
  let check_certificate : CertRule ← do
    let loc_n_tm ← q r"n:num"
    let loc_a_tm ← q r"a:num"
    let loc_q_tm ← q r"q:num"
    let loc_r_tm ← q r"r:num"
    let loc_b_tm ← q r"b:num"
    let loc_ps_tm ← q r"ps:num list"
    let loc_conv_itlist : ioconv ← do
      let c ← GEN_REWRITE_CONV_NET TOP_DEPTH_CONV [ITLIST]
      pure (c THENC NUM_REDUCE_CONV)
    let loc_conv_all : ioconv ← do
      -- arguments right to left: the second GEN_REWRITE_CONV's TAUT first.
      let taut2 ← TAUT (← q r"(a /\ a /\ b <=> a /\ b) /\ (a /\ a <=> a)")
      let taut1 ← TAUT (← q r"a /\ T <=> a")
      let c1 ← GEN_REWRITE_CONV_NET TOP_DEPTH_CONV [ALL, BETA_THM, taut1]
      let c2 ← GEN_REWRITE_CONV_NET DEPTH_CONV [taut2]
      pure (c1 THENC c2)
    let loc_subarith_conv : ioconv ← do
      -- `itlist (uncurry net_of_conv) [...] empty_net`: the list is built
      -- right to left, so the last pair's TAUT is evaluated first and the
      -- last pair is entered into the net first.
      let taut4 ← TAUT (← q r"T /\ p <=> p")
      let taut3 ← TAUT (← q r"p /\ T <=> p")
      let pat1 ← q r"a - b"
      let pat2 ← q r"a DIV b"
      let pat3 ← q r"(a EXP b) MOD c"
      let pat4 ← q r"coprime(a,b)"
      let pat5 ← q r"p /\ T"
      let pat6 ← q r"T /\ p"
      let pairs :=
        [(pat1, NUM_SUB_CONV), (pat2, NUM_DIV_CONV), (pat3, EXP_MOD_CONV),
         (pat4, COPRIME_CONV), (pat5, REWR_CONV taut3), (pat6, REWR_CONV taut4)]
      let mut net := HolCore.Nets.empty_net
      for (pat, cv) in pairs.reverse do
        net ← ExceptT.mk (HolCore.Simp.net_of_conv pat cv net)
      pure (DEPTH_CONV (REWRITES_CONV net))
    let C : CheckCtx :=
      ⟨loc_n_tm, loc_a_tm, loc_q_tm, loc_r_tm, loc_b_tm, loc_ps_tm,
       loc_conv_itlist, loc_conv_all, loc_subarith_conv, EXP_MOD_CONV, NUM_REDUCE_CONV,
       POCKLINGTON_PRIMEFACT, PRIME_2, mk_numeral, mk_flist, loc_prime_theorem_cache⟩
    pure (checkCertificate C)

  -- `PROVE_PRIME = check_certificate o certify_prime` (pocklington.ml 2527).
  let PROVE_PRIME : RatRule ←
    pure (fun n => do check_certificate (← certify_prime n))

  -- `PROVE_PRIMEFACT` (pocklington.ml 2533-2543).
  let PROVE_PRIMEFACT : RatRule ← do
    let loc_pth ← SPEC_ALL PRIMEFACT_VARIANT
    let loc_start_CONV : ioconv ← do
      let c ← PURE_REWRITE_CONV_NET [ITLIST, ALL]
      pure (c THENC NUM_REDUCE_CONV)
    let loc_ps_tm ← q r"ps:num list"
    let loc_n_tm ← q r"n:num"
    pure (fun n => do
      let pfact ← multifactor n
      let pfactNums ← liftExcept (pfact.mapM mk_numeral)
      let flist ← ExceptT.mk (mk_flist pfactNums)
      let nNum ← liftExcept (mk_numeral n)
      let th1 ← INST [(flist, loc_ps_tm), (nNum, loc_n_tm)] loc_pth
      let th2 ← TRANS th1 (← ExceptT.mk (loc_start_CONV (← liftExcept (rand (concl th1)))))
      let ths ← pfact.mapM PROVE_PRIME
      EQ_MP (← SYM th2) (← HolLight.end_itlist CONJ ths))

  -- `PRIME_TEST` (pocklington.ml 2549-2576).
  let PRIME_TEST : TermRule ← do
    let loc_NOT_PRIME_THM ← prove
      r"((m = 1) <=> F) ==> ((m = p) <=> F) ==> (m * n = p) ==> (prime(p) <=> F)"
      (MESON_TAC [prime, divides])
    let loc_m_tm ← q r"m:num"
    let loc_n_tm ← q r"n:num"
    let loc_p_tm ← q r"p:num"
    pure (fun tm => do
      let p ← liftExcept (dest_numeral tm)
      if p == num_0 then EQF_INTRO PRIME_0
      else if p == num_1 then EQF_INTRO PRIME_1
      else do
        let pfact ← multifactor p
        if pfact.length == 1 then do
          remark ("proving that " ++ string_of_num p ++ " is prime")
          EQT_INTRO (← PROVE_PRIME p)
        else do
          remark ("proving that " ++ string_of_num p ++ " is composite")
          let m ← liftExcept (hd pfact)
          let nn ← liftExcept (HolCore.Lib.end_itlist (· * ·) (← liftExcept (tl pfact)))
          let mNum ← liftExcept (mk_numeral m)
          let nNum ← liftExcept (mk_numeral nn)
          let pNum ← liftExcept (mk_numeral p)
          let th0 ← INST [(mNum, loc_m_tm), (nNum, loc_n_tm), (pNum, loc_p_tm)] loc_NOT_PRIME_THM
          let th1 ← MP th0 (← ExceptT.mk (NUM_EQ_CONV
            (← liftExcept (do lhand (← lhand (concl th0))))))
          let th2 ← MP th1 (← ExceptT.mk (NUM_EQ_CONV
            (← liftExcept (do lhand (← lhand (concl th1))))))
          MP th2 (← ExceptT.mk (NUM_MULT_CONV
            (← liftExcept (do lhand (← lhand (concl th2)))))))

  -- `PRIME_CONV` (pocklington.ml 2578-2583).
  let PRIME_CONV : TermRule ← do
    let loc_prime_tm ← q r"prime"
    pure (fun tm0 => do
      let (ptm, tm) ← liftExcept (dest_comb tm0)
      if ptm != loc_prime_tm then throw "expected term of form prime(n)"
      else PRIME_TEST tm)

  -- `GUIDED_PROVE_PRIME hints = check_certificate o guided_certify_prime hints`
  -- (pocklington.ml 2553).
  let GUIDED_PROVE_PRIME : GuidedRule ←
    pure (fun hints n => do check_certificate (← guided_certify_prime hints n))

  -- `PRIME_RULE` (pocklington.ml 2555-2563).
  let PRIME_RULE : PrimeRuleTy ← do
    let loc_prime_tm ← q r"prime"
    pure (fun hints tm0 => do
      let (ptm, tm) ← liftExcept (dest_comb tm0)
      if ptm != loc_prime_tm then throw "expected term of form prime(n)"
      else do
        let n ← liftExcept (dest_numeral tm)
        let hintNums ← liftExcept (hints.mapM num_of_string)
        GUIDED_PROVE_PRIME (hintNums ++ [n]) n)

  -- Examples (pocklington.ml 2603-2623): run at load, as OCaml runs them.
  -- `map (...) (...)`: HOL Light's `map` (lib.ml) processes elements in order.
  _ ← (upto 0 50).mapM (fun i => do
    let tm ← liftExcept (mk_small_numeral i)
    timeThm PRIME_TEST tm)
  _ ← timeThm PRIME_TEST (← q r"65535")
  _ ← timeThm PRIME_TEST (← q r"65536")
  _ ← timeThm PRIME_TEST (← q r"65537")
  _ ← timeThm PROVE_PRIMEFACT (222 : Rat)
  _ ← timeThm PROVE_PRIMEFACT (151 : Rat)
  _ ← ([3, 5, 7, 13, 23, 43, 83, 163, 317, 631, 1259, 2503, 4001] : List Int).mapM
    (fun i => do
      let tm ← liftExcept (mk_small_numeral i)
      timeThm PRIME_TEST tm)

  -- @@RETURN BEGIN
  return { prime_theorem_cache, check_certificate, PROVE_PRIME, PROVE_PRIMEFACT,
           PRIME_TEST, PRIME_CONV, GUIDED_PROVE_PRIME, PRIME_RULE }
  -- @@RETURN END

end HolLibrary.Pocklington
