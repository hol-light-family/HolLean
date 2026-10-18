/- ========================================================================= -/
/- HOL primality proving procedure, based on Pratt certificates.             -/
/- ========================================================================= -/
/- File: HolLibrary/Pratt.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/pratt.ml`, by hand, in file order,
  in the style of HolLibrary/Pocklington.lean (see there and HolMath/Base.lean
  for the conventions).  pratt.ml begins with `needs "Library/prime.ml"`;
  prime.ml's theorems it uses are supplied via the CoreThms structures
  (SessionLibrary.Pratt fills them from SessionLibrary.Prime).  Each section
  is a bundle (a `structure`) built by a `setup` function;
  SessionLibrary/Pratt.lean builds the bundles in order and exports every
  name under its HOL Light name.

  pratt.ml rebinds several names that the core library or prime.ml already
  define (PRIME, CONG_0, phi, ...: "mostly for compatibility"); they are new
  bindings of this file, as in OCaml.  The computational part (the
  certificate type, `factor` through PARI/GP, the certificate checker with
  its theorem cache, PROVE_PRIME, PRIME_CONV and the load-time examples)
  follows Pocklington.lean, keeping pratt.ml's own algorithm and messages.

  REQUIRES PARI/GP.  `factor` runs PARI/GP's `gp` (through `sh -c`), and
  pratt.ml's load-time examples call it, so `gp` must be on the `PATH` (for
  example `brew install pari`).  Unlike pocklington.ml there is no
  trial-division fallback: without `gp`, loading fails with HOL Light's
  message "factor: Call to GP/PARI failed".

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, NUMBER_RULE, TAUT) they are bound first,
  in OCaml's order.
-/

import HolLibrary.Prime

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.Pratt

-- @@COREFILL BEGIN
/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD_AC ADD_ASSOC ADD_CLAUSES ALL ALL_IMP ARITH BEZOUT BIT0 BIT1
   CARD_CLAUSES CARD_NUMSEG_LE CARD_NUMSEG_LT CARD_SUBSET CARD_SUBSET_EQ CONG
   CONJ_ASSOC COPRIME_0 COPRIME_1 COPRIME_DIVPROD COPRIME_EXP COPRIME_LMOD
   COPRIME_MUL COPRIME_REFL COPRIME_SYM DE_MORGAN_THM DIVIDES_ADD
   DIVIDES_ADD_REVR DIVIDES_EXP DIVIDES_EXP2 DIVIDES_LE DIVIDES_LMUL
   DIVIDES_ONE DIVIDES_REFL DIVIDES_RMUL DIVIDES_SUB DIVIDES_ZERO DIVISION
   DIV_MULT DIV_UNIQ EQ_TRANS EXP EXP_ADD EXP_EQ_1 EXP_EXP EXP_ONE EXTENSION
   FINITE_IMAGE FINITE_INDUCT_STRONG FINITE_NUMSEG_LE FINITE_NUMSEG_LT
   FINITE_RECURSION FINITE_RULES FINITE_SUBSET FORALL_AND_THM HAS_SIZE
   HAS_SIZE_0 IMAGE IMAGE_CLAUSES IMP_CONJ IMP_IMP INT_OF_NUM_SUB IN_ELIM_THM
   IN_IMAGE IN_INSERT IN_SING ITLIST LEFT_ADD_DISTRIB LEFT_SUB_DISTRIB LE_0
   LE_ANTISYM : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (LE_CASES LE_LT LE_MULT_LCANCEL LE_TRANS LT LT_IMP_LE LT_LE LT_MULT_RCANCEL
   LT_NZ LT_REFL LT_TRANS MEM MOD_EQ_0 MOD_EXP_MOD MOD_LT MOD_MOD_REFL
   MOD_MULT_LMOD MOD_MULT_RMOD MOD_UNIQ MULT_AC MULT_ASSOC MULT_CLAUSES
   MULT_EQ_0 MULT_SYM NOT_EXISTS_THM NOT_FORALL_THM NOT_IN_EMPTY NOT_LE
   NOT_LT NUMERAL PRIME_0 PRIME_1 PRIME_2 PRIME_COPRIME PRIME_DIVPROD
   PRIME_FACTOR RIGHT_ADD_DISTRIB RIGHT_SUB_DISTRIB SUBSET SUB_EQ_0
   SWAP_EXISTS_THM cong coprime divides num_WF num_WOP num_congruent
   num_divides prime : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms3 where
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms4 where
  deriving Inhabited

-- @@COREFILL END

/-- What pratt.ml uses from Session besides theorems. -/
structure PrattDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  prioritize_num : IO Unit
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  INTEGER_RULE : term → ExceptT String IO thm
  NUMBER_RULE : term → ExceptT String IO thm
  NUMBER_TAC : tactic
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  INDUCT_TAC : tactic
  LIST_INDUCT_TAC : tactic
  -- conversions (Session / core)
  NUM_REDUCE_CONV : ioconv
  -- check_certificate, PROVE_PRIMEFACT, PRIME_TEST)
  let_CONV : ioconv
  NUM_EQ_CONV : ioconv
  NUM_LE_CONV : ioconv
  NUM_SUB_CONV : ioconv
  NUM_MULT_CONV : ioconv
  NUM_DIV_CONV : ioconv
  -- syntax
  mk_numeral : Rat → Except String term
  mk_small_numeral : Int → Except String term
  mk_flist : List term → IO (Except String term)
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  core4 : CoreThms4

/-- `num_0`, `num_1`, `num_2` (pratt.ml 7-9): `num` values used by the
    certificate arithmetic, as `Rat` (as in HolLibrary/Pocklington.lean). -/
def num_0 : Rat := 0
def num_1 : Rat := 1
def num_2 : Rat := 2

/- ------------------------------------------------------------------------- -/
/- Mostly for compatibility. Should eliminate this eventually.               -/
/- Lemmas about previously defined terms.  (pratt.ml 14-89)                  -/
/- ------------------------------------------------------------------------- -/

structure Compat where
  -- @@FIELDS
  nat_mod_lemma : thm
  nat_mod : thm
  PRIME : thm
  FINITE_NUMBER_SEGMENT : thm
  deriving Inhabited

@[nospecialize]
def setupCompat [HolBase] (D : PrattDeps) :
    ExceptT String IO Compat := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, INTEGER_RULE, MESON_TAC,
        NUMBER_RULE, NUMBER_TAC, NUM_REDUCE_CONV, prioritize_num, .. } := D
  let { CARD_CLAUSES, COPRIME_1, DIVIDES_LE, DIVIDES_REFL, DIVIDES_ZERO, EXTENSION,
        FINITE_RULES, HAS_SIZE, HAS_SIZE_0, INT_OF_NUM_SUB, IN_ELIM_THM, IN_INSERT,
        LE_0, .. } := D.core1
  let { LE_CASES, LT, LT_LE, LT_REFL, NOT_FORALL_THM, NOT_IN_EMPTY, NOT_LT, PRIME_0,
        PRIME_1, PRIME_COPRIME, PRIME_FACTOR, cong, coprime, divides, num_congruent,
        num_divides, .. } := D.core2
  -- @@SCOPE END

  prioritize_num

  let nat_mod_lemma ← prove
   r"!x y n:num. (x == y) (mod n) /\ y <= x ==> ?q. x = y + n * q"
   (← do
    let r2 ← ARITH_RULE (← q r"x <= y ==> (y:num = x + d <=> y - x = d)")
    let i1 ← INTEGER_RULE (← q r"(x == y) (mod &n) <=> &n divides (x - y)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [num_congruent] THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    ONCE_REWRITE_TAC [i1] THEN
    ASM_SIMP_TAC [INT_OF_NUM_SUB, r2] THEN
    REWRITE_TAC [← GSYM num_divides, divides]))

  let nat_mod ← prove
   r"!x y n:num. (mod n) x y <=> ?q1 q2. x + n * q1 = y + n * q2"
   (← do
    let r3 ← ARITH_RULE (← q r"x + y * 0 = x")
    let r2 ← NUMBER_RULE (← q r"(x:num == y) (mod n) <=> (y == x) (mod n)")
    let r1 ← TAUT (← q r"a \/ b ==> c ==> d <=> (c /\ b) \/ (c /\ a) ==> d")
    pure (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [← GSYM cong] THEN
    EQ_TAC THENL [ALL_TAC, NUMBER_TAC] THEN
    MP_TAC (← SPECL [← q "x:num", ← q "y:num"] LE_CASES) THEN
    REWRITE_TAC [r1] THEN
    DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
     [ALL_TAC,
      ONCE_REWRITE_TAC [r2]] THEN
    MESON_TAC [nat_mod_lemma, r3]))

  let PRIME ← prove
   r"!p. prime p <=>
       ~(p = 0) /\ ~(p = 1) /\ !m. 0 < m /\ m < p ==> coprime(p,m)"
   (GEN_TAC THEN ASM_CASES_TAC (← q "p = 0") THEN ASM_REWRITE_TAC [PRIME_0] THEN
    ASM_CASES_TAC (← q "p = 1") THEN ASM_REWRITE_TAC [PRIME_1] THEN
    EQ_TAC THENL
     [DISCH_THEN (MP_TAC o MATCH_MP PRIME_COPRIME) THEN
      DISCH_TAC THEN X_GEN_TAC (← q "m:num") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q "m:num")) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [COPRIME_1] THEN
      ASM_MESON_TAC [NOT_LT, LT_REFL, DIVIDES_LE], ALL_TAC] THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q "q:num") MP_TAC o MATCH_MP PRIME_FACTOR) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q "q:num")) THEN
    SUBGOAL_THEN (← q r"~(coprime(p,q))") (fun th => REWRITE_TAC [th]) THENL
     [REWRITE_TAC [coprime, NOT_FORALL_THM] THEN
      EXISTS_TAC (← q "q:num") THEN ASM_REWRITE_TAC [DIVIDES_REFL] THEN
      ASM_MESON_TAC [PRIME_1], ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_REWRITE_TAC [LT_LE, LE_0] THEN
    ASM_CASES_TAC (← q "p:num = q") THEN ASM_REWRITE_TAC [] THEN
    SIMP_TAC [] THEN DISCH_TAC THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
    ASM_MESON_TAC [DIVIDES_ZERO])

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

  -- @@RETURN BEGIN
  return { nat_mod_lemma, nat_mod, PRIME, FINITE_NUMBER_SEGMENT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Congruences.  (pratt.ml 90-143)                                           -/
/- ------------------------------------------------------------------------- -/

structure Cong where
  -- @@FIELDS
  CONG_MOD_0 : thm
  CONG_MOD_1 : thm
  CONG_0 : thm
  CONG_SUB_CASES : thm
  CONG_MULT_LCANCEL : thm
  CONG_REFL : thm
  CONG_SYM : thm
  CONG_TRANS : thm
  deriving Inhabited

@[nospecialize]
def setupCong [HolBase] (D : PrattDeps) (BCompat : Compat) :
    ExceptT String IO Cong := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, MESON_TAC, NUMBER_TAC, .. } := D
  let { ADD_CLAUSES, COPRIME_0, COPRIME_DIVPROD, COPRIME_SYM, LEFT_SUB_DISTRIB, .. } := D.core1
  let { LE_MULT_LCANCEL, MULT_CLAUSES, SWAP_EXISTS_THM, cong, .. } := D.core2
  let { nat_mod, .. } := BCompat
  -- @@SCOPE END

  let CONG_MOD_0 ← prove
   r"!x y. (x == y) (mod 0) <=> (x = y)"
   (NUMBER_TAC)

  let CONG_MOD_1 ← prove
   r"!x y. (x == y) (mod 1)"
   (NUMBER_TAC)

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

  let CONG_MULT_LCANCEL ← prove
   r"!a n x y. coprime(a,n) /\ (a * x == a * y) (mod n) ==> (x == y) (mod n)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "a = 0") THENL
     [ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_REWRITE_TAC [COPRIME_0] THEN
      SIMP_TAC [CONG_MOD_1], ALL_TAC] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ONCE_REWRITE_TAC [CONG_SUB_CASES] THEN
    ASM_REWRITE_TAC [LE_MULT_LCANCEL] THEN
    REWRITE_TAC [← GSYM LEFT_SUB_DISTRIB, CONG_0] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [COPRIME_DIVPROD, COPRIME_SYM])

  let CONG_REFL ← prove
   r"!x n. (x == x) (mod n)"
   (MESON_TAC [cong, nat_mod, ADD_CLAUSES, MULT_CLAUSES])

  let CONG_SYM ← prove
   r"!x y n. (x == y) (mod n) <=> (y == x) (mod n)"
   (REWRITE_TAC [cong, nat_mod] THEN MESON_TAC [])

  let CONG_TRANS ← prove
   r"!x y z n. (x == y) (mod n) /\ (y == z) (mod n) ==> (x == z) (mod n)"
   (← do
    let r1 ← ARITH_RULE
      (← q r"(x + n * q1 = y + n * q2) /\
    (y + n * q3 = z + n * q4)
    ==> (x + n * (q1 + q3) = z + n * (q2 + q4))")
    pure (REWRITE_TAC [cong, nat_mod] THEN
    MESON_TAC [r1]))

  -- @@RETURN BEGIN
  return { CONG_MOD_0, CONG_MOD_1, CONG_0, CONG_SUB_CASES, CONG_MULT_LCANCEL, CONG_REFL,
           CONG_SYM, CONG_TRANS }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Euler totient function.  (pratt.ml 144-264)                               -/
/- ------------------------------------------------------------------------- -/

structure Phi where
  -- @@FIELDS
  phi : thm
  PHI_ALT : thm
  PHI_ANOTHER : thm
  PHI_LIMIT : thm
  PHI_LIMIT_STRONG : thm
  PHI_0 : thm
  PHI_1 : thm
  PHI_LOWERBOUND_1_STRONG : thm
  PHI_LOWERBOUND_1 : thm
  PHI_LOWERBOUND_2 : thm
  PHI_PRIME_EQ : thm
  PHI_PRIME : thm
  deriving Inhabited

@[nospecialize]
def setupPhi [HolBase] (D : PrattDeps) (BCompat : Compat) :
    ExceptT String IO Phi := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, MESON_TAC, new_definition, .. } := D
  let { ARITH, CARD_CLAUSES, CARD_NUMSEG_LE, CARD_NUMSEG_LT, CARD_SUBSET,
        CARD_SUBSET_EQ, COPRIME_0, COPRIME_1, COPRIME_REFL, COPRIME_SYM, DIVIDES_SUB,
        EQ_TRANS, EXTENSION, FINITE_NUMSEG_LE, FINITE_NUMSEG_LT, FINITE_RULES,
        FINITE_SUBSET, HAS_SIZE, IN_ELIM_THM, IN_INSERT, IN_SING, .. } := D.core1
  let { LE_LT, LE_TRANS, LT, LT_NZ, NOT_IN_EMPTY, NOT_LT, SUBSET, coprime, .. } := D.core2
  let { FINITE_NUMBER_SEGMENT, PRIME, .. } := BCompat
  -- @@SCOPE END

  let phi ← new_definition
   r"phi(n) = CARD { m | 0 < m /\ m <= n /\ coprime(m,n) }"

  let PHI_ALT ← prove
   r"phi(n) = CARD { m | coprime(m,n) /\ m < n}"
   (REWRITE_TAC [phi] THEN
    ASM_CASES_TAC (← q "n = 0") THENL
     [AP_TERM_TAC THEN
      ASM_REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
      MESON_TAC [LT, NOT_LT],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q "n = 1") THENL
     [SUBGOAL_THEN
       (← q r"({m | 0 < m /\ m <= n /\ coprime (m,n)} = {1}) /\
      ({m | coprime (m,n) /\ m < n} = {0})")
       (CONJUNCTS_THEN SUBST1_TAC)
      THENL [ALL_TAC, SIMP_TAC [CARD_CLAUSES, FINITE_RULES, NOT_IN_EMPTY]] THEN
      ASM_REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_SING] THEN
      REWRITE_TAC [COPRIME_1] THEN REPEAT STRIP_TAC THEN ARITH_TAC,
      ALL_TAC] THEN
    AP_TERM_TAC THEN ASM_REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    X_GEN_TAC (← q "m:num") THEN ASM_CASES_TAC (← q "m = 0") THEN
    ASM_REWRITE_TAC [LT] THENL
     [ASM_MESON_TAC [COPRIME_0, COPRIME_SYM],
      ASM_MESON_TAC [LE_LT, COPRIME_REFL, LT_NZ]])

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
    MP_TAC (← SPEC (← q "n:num") FINITE_NUMBER_SEGMENT) THEN
    ASM_SIMP_TAC [PHI_ANOTHER, HAS_SIZE] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC [] THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM])

  let PHI_0 ← prove
   r"phi 0 = 0"
   (MP_TAC (← SPEC (← q "0") PHI_LIMIT) THEN REWRITE_TAC [ARITH] THEN ARITH_TAC)

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
   (← do
    let r1 ← ARITH_RULE (← q r"1 <= 2")
    pure (MESON_TAC [PHI_LOWERBOUND_1_STRONG, LE_TRANS, r1]))

  let PHI_LOWERBOUND_2 ← prove
   r"!n. 3 <= n ==> 2 <= phi(n)"
   (← do
    let r3 ← ARITH_RULE (← q r"3 <= n ==> 0 < n - 1 /\ n - 1 <= n /\ 1 <= n")
    let r2 ← ARITH_RULE (← q r"3 <= n ==> ~(1 = n - 1)")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"2 = CARD {1,(n-1)}") SUBST1_TAC THENL
     [SIMP_TAC [CARD_CLAUSES, IN_INSERT, NOT_IN_EMPTY, FINITE_RULES, ARITH] THEN
      ASM_SIMP_TAC [r2], ALL_TAC] THEN
    REWRITE_TAC [phi] THEN MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [SIMP_TAC [SUBSET, IN_INSERT, NOT_IN_EMPTY, IN_ELIM_THM] THEN
      GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [COPRIME_1] THEN
      ASM_SIMP_TAC [ARITH, r3] THEN
      REWRITE_TAC [coprime] THEN X_GEN_TAC (← q "d:num") THEN STRIP_TAC THEN
      MP_TAC (← SPEC (← q "n:num") (← CONJUNCT1 COPRIME_1)) THEN REWRITE_TAC [coprime] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"1 = n - (n - 1)") SUBST1_TAC THENL
       [UNDISCH_TAC (← q "3 <= n") THEN ARITH_TAC,
        ASM_SIMP_TAC [DIVIDES_SUB]],
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{b | b <= n}") THEN
      REWRITE_TAC [CARD_NUMSEG_LE, FINITE_NUMSEG_LE] THEN
      SIMP_TAC [SUBSET, IN_ELIM_THM]]))

  let PHI_PRIME_EQ ← prove
   r"!n. (phi n = n - 1) /\ ~(n = 0) /\ ~(n = 1) <=> prime n"
   (GEN_TAC THEN REWRITE_TAC [PRIME] THEN
    ASM_CASES_TAC (← q "n = 0") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q "n = 1") THEN ASM_REWRITE_TAC [PHI_1, ARITH] THEN
    MP_TAC (← SPEC (← q "n:num") FINITE_NUMBER_SEGMENT) THEN
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

  -- @@RETURN BEGIN
  return { phi, PHI_ALT, PHI_ANOTHER, PHI_LIMIT, PHI_LIMIT_STRONG, PHI_0, PHI_1,
           PHI_LOWERBOUND_1_STRONG, PHI_LOWERBOUND_1, PHI_LOWERBOUND_2, PHI_PRIME_EQ,
           PHI_PRIME }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Fermat's Little theorem.  (pratt.ml 265-514)                              -/
/- ------------------------------------------------------------------------- -/

structure Fermat where
  -- @@FIELDS
  DIFFERENCE_POS_LEMMA : thm
  ITSET_MODMULT : thm
  ITSET_MODMULT_COPRIME : thm
  FERMAT_LITTLE : thm
  FERMAT_LITTLE_PRIME : thm
  deriving Inhabited

@[nospecialize]
def setupFermat [HolBase] (D : PrattDeps) (BCompat : Compat) (BCong : Cong) (BPhi : Phi) :
    ExceptT String IO Fermat := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, NUM_REDUCE_CONV, .. } := D
  let { ADD_AC, ADD_ASSOC, ADD_CLAUSES, BEZOUT, CARD_CLAUSES, CONG, CONJ_ASSOC,
        COPRIME_0, COPRIME_1, COPRIME_LMOD, COPRIME_MUL, COPRIME_SYM, DE_MORGAN_THM,
        DIVIDES_ADD, DIVIDES_ADD_REVR, DIVIDES_EXP, DIVIDES_EXP2, DIVIDES_LMUL,
        DIVIDES_ONE, DIVIDES_REFL, DIVIDES_RMUL, DIVIDES_SUB, DIVISION, EXP, EXP_ONE,
        EXTENSION, FINITE_IMAGE, FINITE_INDUCT_STRONG, FINITE_RECURSION, FINITE_SUBSET,
        FORALL_AND_THM, HAS_SIZE, IMAGE, IMAGE_CLAUSES, IMP_CONJ, IMP_IMP, IN_ELIM_THM,
        IN_IMAGE, IN_INSERT, LEFT_ADD_DISTRIB, LEFT_SUB_DISTRIB, .. } := D.core1
  let { LE_MULT_LCANCEL, LT_IMP_LE, MOD_LT, MOD_MOD_REFL, MOD_MULT_LMOD, MOD_MULT_RMOD,
        MOD_UNIQ, MULT_AC, MULT_ASSOC, MULT_CLAUSES, MULT_EQ_0, MULT_SYM, NOT_LE,
        PRIME_0, PRIME_COPRIME, RIGHT_ADD_DISTRIB, RIGHT_SUB_DISTRIB, SUBSET, SUB_EQ_0,
        cong, coprime, .. } := D.core2
  let { FINITE_NUMBER_SEGMENT, nat_mod, .. } := BCompat
  let { CONG_0, CONG_MOD_0, CONG_MOD_1, CONG_MULT_LCANCEL, CONG_REFL, CONG_SYM,
        CONG_TRANS, .. } := BCong
  let { PHI_0, PHI_ANOTHER, PHI_PRIME_EQ, .. } := BPhi
  -- @@SCOPE END

  let DIFFERENCE_POS_LEMMA ← prove
   r"b <= a /\
   (?x1 x2. x1 * n + a = x2 * n + b)
   ==> ?x. a = x * n + b"
   (STRIP_TAC THEN EXISTS_TAC (← q "x2 - x1") THEN
    POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC [RIGHT_SUB_DISTRIB] THEN ARITH_TAC)

  -- `W(C SUBGOAL_THEN ttac o funpow 2 lhand o snd)`
  let loc_subgoalLhand2 (ttac : thm_tactic) : tactic := fun gl => ExceptT.run do
    let t ← liftExcept (funpow 2 (fun (m : Except String term) => do lhand (← m)) (pure gl.2))
    ExceptT.mk (SUBGOAL_THEN t ttac gl)

  let ITSET_MODMULT ← prove
   r"!n s. FINITE s /\ ~(n = 0) /\ ~(n = 1) /\ coprime(a,n)
       ==> (!b. b IN s ==> b < n)
           ==> (ITSET (\x y. (x * y) MOD n) (IMAGE (\b. (a * b) MOD n) s) 1 =
                (a EXP (CARD s) * ITSET (\x y. (x * y) MOD n) s 1) MOD n)"
   (GEN_TAC THEN ASM_CASES_TAC (← q "n = 0") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q "n = 1") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"coprime(a,n)") THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    MP_TAC (← ISPECL [← q r"\x y. (x * y) MOD n", ← q "1"] FINITE_RECURSION) THEN
    loc_subgoalLhand2 (fun th => REWRITE_TAC [th]) THENL
     [ASM_SIMP_TAC [MOD_MULT_RMOD] THEN REWRITE_TAC [MULT_AC], ALL_TAC] THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC [IMAGE_CLAUSES, CARD_CLAUSES, FINITE_IMAGE] THEN CONJ_TAC THENL
     [REWRITE_TAC [EXP, MULT_CLAUSES] THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC (← q "0") THEN
      REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES] THEN
      MAP_EVERY UNDISCH_TAC [← q "~(n = 0)", ← q "~(n = 1)"] THEN ARITH_TAC,
      ALL_TAC] THEN
    X_GEN_TAC (← q "b:num") THEN X_GEN_TAC (← q r"s:num->bool") THEN
    DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    REWRITE_TAC [IN_INSERT] THEN
    REWRITE_TAC [← TAUT (← q r"(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)")] THEN
    REWRITE_TAC [FORALL_AND_THM] THEN
    ASM_CASES_TAC (← q r"!b. b IN s ==> b < n") THEN ASM_REWRITE_TAC [] THEN
    DISCH_TAC THEN SIMP_TAC [] THEN
    DISCH_THEN (MP_TAC o SPEC (← q "b:num")) THEN REWRITE_TAC [] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"~((a * b) MOD n IN IMAGE (\b. (a * b) MOD n) s)")
     (fun th => REWRITE_TAC [th])
    THENL
     [REWRITE_TAC [IN_IMAGE] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "c:num") MP_TAC) THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      ASM_SIMP_TAC [← GSYM CONG] THEN DISCH_TAC THEN
      UNDISCH_TAC (← q r"~(b:num IN s)") THEN REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"b:num = c") (fun th => ASM_REWRITE_TAC [th]) THEN
      SUBGOAL_THEN (← q r"b MOD n = c MOD n") MP_TAC THENL
       [ASM_SIMP_TAC [← GSYM CONG] THEN
        MATCH_MP_TAC CONG_MULT_LCANCEL THEN
        EXISTS_TAC (← q "a:num") THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
      ASM_SIMP_TAC [MOD_LT], ALL_TAC] THEN
    REWRITE_TAC [EXP] THEN
    ASM_SIMP_TAC [MOD_MULT_LMOD, MOD_MULT_RMOD] THEN
    REWRITE_TAC [MULT_AC])

  let ITSET_MODMULT_COPRIME ← prove
   r"!n s. FINITE s /\ (!b. b IN s ==> coprime(b,n)) /\ ~(n = 0)
         ==> coprime(ITSET (\x y. (x * y) MOD n) s 1,n)"
   (GEN_TAC THEN ASM_CASES_TAC (← q "n = 0") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    MP_TAC (← ISPECL [← q r"\x y. (x * y) MOD n", ← q "1"] FINITE_RECURSION) THEN
    loc_subgoalLhand2 (fun th => REWRITE_TAC [th]) THENL
     [ASM_SIMP_TAC [MOD_MULT_RMOD] THEN REWRITE_TAC [MULT_AC], ALL_TAC] THEN
    STRIP_TAC THEN
    ASM_SIMP_TAC [IMAGE_CLAUSES, CARD_CLAUSES, FINITE_IMAGE] THEN
    REWRITE_TAC [← ONCE_REWRITE_RULE [COPRIME_SYM] COPRIME_1] THEN
    REWRITE_TAC [IN_INSERT] THEN
    REWRITE_TAC [← TAUT (← q r"(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)")] THEN
    REWRITE_TAC [FORALL_AND_THM] THEN
    MAP_EVERY X_GEN_TAC [← q "x:num", ← q r"s:num->bool"] THEN
    ASM_CASES_TAC (← q r"!b. b IN s ==> coprime(b,n)") THEN ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN DISCH_THEN (MP_TAC o SPEC (← q "x:num")) THEN
    ASM_SIMP_TAC [COPRIME_LMOD, ← ONCE_REWRITE_RULE [COPRIME_SYM] COPRIME_MUL])

  let FERMAT_LITTLE ← prove
   r"!a n. coprime(a,n) ==> (a EXP (phi n) == 1) (mod n)"
   (← do
    -- counter/printing rules bound in reverse text order (t15 .. t1)
    let t15 ← ARITH_RULE (← q r"x = x * 1")
    let t14 ← ARITH_RULE (← q r"(n * x - a * y = 1) ==> (x * n = a * y + 1)")
    let t13 ← ARITH_RULE (← q r"(x + a * c * n = c * a * n + y) <=> (x = y)")
    let t12 ← ARITH_RULE (← q r"y <= n /\ (a + n = x + y) ==> (a + (n - y) = x)")
    let t11 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    let t10 ← ARITH_RULE (← q r"c <= a * c * x <=> c * 1 <= c * a * x")
    let t9 ← ARITH_RULE (← q r"m < n ==> ((n - m) + m = n:num)")
    let t8 ← ARITH_RULE (← q r"~(0 < n) <=> (n = 0)")
    let t7 ← TAUT (← q r"(~a ==> ~c) /\ b /\ c /\ d ==> a /\ b /\ c /\ d")
    let t6 ← ARITH_RULE (← q r"(a - b = 1) ==> (a = b + 1)")
    let t5 ← ARITH_RULE (← q r"(a * c * x = b:num) <=> (c * a * x = b)")
    let t4 ← ARITH_RULE (← q r"~(0 < n) <=> (n = 0)")
    let t3 ← TAUT (← q r"(~a ==> ~c) /\ b /\ c /\ d ==> a /\ b /\ c /\ d")
    let t2 ← ARITH_RULE (← q r"~(0 < n) <=> (n = 0)")
    let t1 ← TAUT (← q r"b /\ (~a ==> ~b) ==> a /\ b")
    pure (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q "n = 0") THEN
    ASM_SIMP_TAC [COPRIME_0, PHI_0, CONG_MOD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_CASES_TAC (← q "n = 1") THEN ASM_REWRITE_TAC [CONG_MOD_1] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"{ c | ?b. 0 < b /\ b < n /\ coprime(b,n) /\ (c = (a * b) MOD n) } =
    { b | 0 < b /\ b < n /\ coprime(b,n) }")
    MP_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
      X_GEN_TAC (← q "c:num") THEN EQ_TAC THENL
       [DISCH_THEN (X_CHOOSE_THEN (← q "b:num") MP_TAC) THEN
        REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC [DIVISION] THEN
        MATCH_MP_TAC t1 THEN
        SIMP_TAC [t2] THEN
        ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_SIMP_TAC [COPRIME_0] THEN
        SUBGOAL_THEN (← q r"coprime(n,a * b)") MP_TAC THENL
         [MATCH_MP_TAC COPRIME_MUL THEN
          ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_REWRITE_TAC [], ALL_TAC] THEN
        SUBGOAL_THEN (← q r"a * b = (a * b) DIV n * n + (a * b) MOD n")
         (fun th => GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
        THENL [ASM_SIMP_TAC [DIVISION], ALL_TAC] THEN
        REWRITE_TAC [coprime] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC [DIVIDES_ADD, DIVIDES_LMUL, DIVIDES_REFL], ALL_TAC] THEN
      STRIP_TAC THEN MP_TAC (← SPECL [← q "a:num", ← q "n:num"] BEZOUT) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d:num")
       (X_CHOOSE_THEN (← q "x:num") (X_CHOOSE_THEN (← q "y:num")
          (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)))) THEN
      SUBGOAL_THEN (← q r"d = 1") SUBST_ALL_TAC THENL
       [ASM_MESON_TAC [coprime], ALL_TAC] THEN
      STRIP_TAC THENL
       [EXISTS_TAC (← q r"(c * x) MOD n") THEN
        MATCH_MP_TAC t3 THEN
        CONJ_TAC THENL
         [SIMP_TAC [t4] THEN
          ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_SIMP_TAC [COPRIME_0],
          ALL_TAC] THEN
        ASM_SIMP_TAC [DIVISION] THEN CONJ_TAC THENL
         [SUBGOAL_THEN (← q r"coprime(n,c * x)") MP_TAC THENL
           [MATCH_MP_TAC COPRIME_MUL THEN
            ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_REWRITE_TAC [] THEN
            REWRITE_TAC [coprime, ← GSYM DIVIDES_ONE] THEN
            FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
            SIMP_TAC [DIVIDES_SUB, DIVIDES_LMUL, DIVIDES_RMUL, DIVIDES_REFL],
            ALL_TAC] THEN
          SUBGOAL_THEN (← q r"c * x = (c * x) DIV n * n + (c * x) MOD n")
           (fun th => GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
          THENL [ASM_SIMP_TAC [DIVISION], ALL_TAC] THEN
          REWRITE_TAC [coprime] THEN REPEAT STRIP_TAC THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_SIMP_TAC [DIVIDES_ADD, DIVIDES_LMUL, DIVIDES_REFL], ALL_TAC] THEN
        ASM_SIMP_TAC [MOD_MULT_RMOD] THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC (← q r"c * y:num") THEN
        ASM_REWRITE_TAC [← GSYM MULT_ASSOC] THEN
        ONCE_REWRITE_TAC [t5] THEN
        FIRST_ASSUM (SUBST1_TAC o MATCH_MP t6) THEN
        REWRITE_TAC [LEFT_ADD_DISTRIB, MULT_CLAUSES, MULT_AC],

        EXISTS_TAC (← q r"(c * (n - y MOD n)) MOD n") THEN
        MATCH_MP_TAC t7 THEN
        CONJ_TAC THENL
         [SIMP_TAC [t8] THEN
          ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_SIMP_TAC [COPRIME_0],
          ALL_TAC] THEN
        ASM_SIMP_TAC [DIVISION] THEN CONJ_TAC THENL
         [SUBGOAL_THEN (← q r"coprime(n,c * (n - y MOD n))") MP_TAC THENL
           [MATCH_MP_TAC COPRIME_MUL THEN
            ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_REWRITE_TAC [] THEN
            REWRITE_TAC [coprime, ← GSYM DIVIDES_ONE] THEN
            FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
            X_GEN_TAC (← q "e:num") THEN STRIP_TAC THEN MATCH_MP_TAC DIVIDES_SUB THEN
            ASM_SIMP_TAC [DIVIDES_RMUL, DIVIDES_REFL] THEN
            MATCH_MP_TAC DIVIDES_LMUL THEN
            SUBGOAL_THEN (← q r"y = (y DIV n) * n + y MOD n") SUBST1_TAC THENL
             [ASM_SIMP_TAC [DIVISION], ALL_TAC] THEN
            MATCH_MP_TAC DIVIDES_ADD THEN
            ASM_SIMP_TAC [DIVIDES_LMUL, DIVIDES_REFL] THEN
            MATCH_MP_TAC DIVIDES_ADD_REVR THEN
            EXISTS_TAC (← q r"n - y MOD n") THEN ASM_REWRITE_TAC [] THEN
            ASM_SIMP_TAC [t9, DIVISION],
            ALL_TAC] THEN
          SUBGOAL_THEN (← q r"!x. c * x = (c * x) DIV n * n + (c * x) MOD n")
           (fun th => GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
          THENL [ASM_SIMP_TAC [DIVISION], ALL_TAC] THEN
          REWRITE_TAC [coprime] THEN REPEAT STRIP_TAC THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_SIMP_TAC [DIVIDES_ADD, DIVIDES_LMUL, DIVIDES_REFL], ALL_TAC] THEN
        ASM_SIMP_TAC [MOD_MULT_RMOD] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ THEN
        ASM_REWRITE_TAC [] THEN MATCH_MP_TAC DIFFERENCE_POS_LEMMA THEN
        CONJ_TAC THENL
         [ONCE_REWRITE_TAC [t10] THEN
          REWRITE_TAC [LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
          REWRITE_TAC [t11, MULT_EQ_0,
                      SUB_EQ_0, DE_MORGAN_THM] THEN
          UNDISCH_TAC (← q r"coprime(a,n)") THEN ONCE_REWRITE_TAC [COPRIME_SYM] THEN
          ASM_CASES_TAC (← q "a = 0") THEN ASM_REWRITE_TAC [COPRIME_0] THEN
          DISCH_TAC THEN ASM_SIMP_TAC [DIVISION, NOT_LE], ALL_TAC] THEN
        MAP_EVERY EXISTS_TAC [← q r"c * x", ← q r"c * a * (1 + y DIV n)"] THEN
        REWRITE_TAC [LEFT_ADD_DISTRIB, LEFT_SUB_DISTRIB] THEN
        MATCH_MP_TAC t12 THEN
        CONJ_TAC THENL
         [REWRITE_TAC [MULT_ASSOC] THEN REWRITE_TAC [LE_MULT_LCANCEL] THEN
          ASM_SIMP_TAC [LT_IMP_LE, DIVISION], ALL_TAC] THEN
        REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES] THEN
        REWRITE_TAC [← GSYM ADD_ASSOC, ← GSYM MULT_ASSOC] THEN
        REWRITE_TAC [t13] THEN
        FIRST_ASSUM (SUBST1_TAC o MATCH_MP t14) THEN
        SUBGOAL_THEN (← q r"y = (y DIV n) * n + y MOD n")
         (fun th => GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
        THENL [ASM_SIMP_TAC [DIVISION], ALL_TAC] THEN
        REWRITE_TAC [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES] THEN
        REWRITE_TAC [MULT_AC, ADD_AC]],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"{c | ?b. 0 < b /\ b < n /\ coprime (b,n) /\ (c = (a * b) MOD n)} =
    IMAGE (\b. (a * b) MOD n) {b | 0 < b /\ b < n /\ coprime (b,n)}")
    SUBST1_TAC THENL
     [REWRITE_TAC [IMAGE, EXTENSION, IN_ELIM_THM, CONJ_ASSOC], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"ITSET (\x y. (x * y) MOD n)")) THEN
    DISCH_THEN (MP_TAC o C AP_THM (← q "1")) THEN
    SUBGOAL_THEN (← q r"FINITE {b | 0 < b /\ b < n /\ coprime (b,n)} /\
                !b. b IN {b | 0 < b /\ b < n /\ coprime (b,n)} ==> b < n")
    ASSUME_TAC THENL
     [CONJ_TAC THENL [ALL_TAC, SIMP_TAC [IN_ELIM_THM]] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{b | 0 < b /\ b < n}") THEN
      REWRITE_TAC [← REWRITE_RULE [HAS_SIZE] FINITE_NUMBER_SEGMENT] THEN
      SIMP_TAC [SUBSET, IN_ELIM_THM], ALL_TAC] THEN
    ASM_SIMP_TAC [← REWRITE_RULE [IMP_IMP]
      ITSET_MODMULT] THEN
    ASM_SIMP_TAC [← GSYM PHI_ANOTHER] THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"(MOD)")) THEN
    DISCH_THEN (MP_TAC o C AP_THM (← q "n:num")) THEN
    ASM_SIMP_TAC [MOD_MOD_REFL] THEN ASM_SIMP_TAC [← GSYM CONG] THEN
    GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV)
     [t15] THEN
    GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o LAND_CONV) [MULT_SYM] THEN
    DISCH_TAC THEN MATCH_MP_TAC CONG_MULT_LCANCEL THEN
    EXISTS_TAC (← q r"ITSET (\x y. (x * y) MOD n)
                    {b | 0 < b /\ b < n /\ coprime (b,n)} 1") THEN
    ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [ITSET_MODMULT_COPRIME, IN_ELIM_THM]))

  let FERMAT_LITTLE_PRIME ← prove
   r"!p a. prime p ==> (a EXP p == a) (mod p)"
   (← do
    let loc_phith ← do
      let s ← SPEC_ALL PHI_PRIME_EQ
      let p ← EQ_IMP_RULE s
      pure p.2
    let r1 ← ARITH_RULE (← q r"~(p = 0) ==> (SUC(p - 1) = p)")
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q "a:num") o MATCH_MP PRIME_COPRIME) THEN
    ONCE_REWRITE_TAC [COPRIME_SYM] THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC [EXP_ONE, CONG_REFL],
      MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC (← q "0") THEN
      GEN_REWRITE_TAC RAND_CONV [CONG_SYM] THEN ASM_REWRITE_TAC [CONG_0] THEN
      ASM_MESON_TAC [DIVIDES_EXP, DIVIDES_EXP2, PRIME_0],
      ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP FERMAT_LITTLE) THEN
    ASM_SIMP_TAC [loc_phith] THEN
    REWRITE_TAC [cong, nat_mod] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "q1:num") (X_CHOOSE_THEN (← q "q2:num") MP_TAC)) THEN
    DISCH_THEN (MP_TAC o AP_TERM (← q r"( * ) a")) THEN
    REWRITE_TAC [LEFT_ADD_DISTRIB, ← GSYM (← CONJUNCT2 EXP)] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
    REWRITE_TAC [MULT_CLAUSES, ← GSYM MULT_ASSOC] THEN
    ASM_MESON_TAC [r1, PRIME_0]))

  -- @@RETURN BEGIN
  return { DIFFERENCE_POS_LEMMA, ITSET_MODMULT, ITSET_MODMULT_COPRIME, FERMAT_LITTLE,
           FERMAT_LITTLE_PRIME }
  -- @@RETURN END

structure Lucas where
  -- @@FIELDS
  LUCAS_COPRIME_LEMMA : thm
  LUCAS_WEAK : thm
  LUCAS : thm
  deriving Inhabited

@[nospecialize]
def setupLucas [HolBase] (D : PrattDeps) (BCong : Cong) (BPhi : Phi) (BFermat : Fermat) :
    ExceptT String IO Lucas := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, .. } := D
  let { ADD_CLAUSES, CONG, COPRIME_1, COPRIME_EXP, COPRIME_SYM, DIVIDES_ADD_REVR,
        DIVIDES_LMUL, DIVIDES_ONE, DIVIDES_RMUL, DIVISION, DIV_MULT, DIV_UNIQ,
        EQ_TRANS, EXP, EXP_ADD, EXP_EQ_1, EXP_EXP, EXP_ONE, LE_ANTISYM, .. } := D.core1
  let { LT_REFL, LT_TRANS, MOD_EQ_0, MOD_EXP_MOD, MOD_UNIQ, MULT_AC, MULT_ASSOC,
        MULT_CLAUSES, MULT_SYM, NOT_EXISTS_THM, NOT_LT, PRIME_0, PRIME_FACTOR, coprime,
        divides, num_WOP, .. } := D.core2
  let { CONG_MOD_0, CONG_MULT_LCANCEL, .. } := BCong
  let { PHI_LIMIT_STRONG, PHI_LOWERBOUND_1, PHI_PRIME_EQ, .. } := BPhi
  let { FERMAT_LITTLE, .. } := BFermat
  -- @@SCOPE END

  let LUCAS_COPRIME_LEMMA ← prove
   r"!m n a. ~(m = 0) /\ (a EXP m == 1) (mod n) ==> coprime(a,n)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "n = 0") THENL
     [ASM_REWRITE_TAC [CONG_MOD_0, EXP_EQ_1] THEN
      ASM_CASES_TAC (← q "m = 0") THEN ASM_REWRITE_TAC [] THEN
      ONCE_REWRITE_TAC [COPRIME_SYM] THEN SIMP_TAC [COPRIME_1],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q "n = 1") THEN ASM_REWRITE_TAC [COPRIME_1] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [coprime] THEN X_GEN_TAC (← q "d:num") THEN STRIP_TAC THEN
    UNDISCH_TAC (← q r"(a EXP m == 1) (mod n)") THEN
    ASM_SIMP_TAC [CONG] THEN
    SUBGOAL_THEN (← q "1 MOD n = 1") SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC (← q "0") THEN
      REWRITE_TAC [MULT_CLAUSES, ADD_CLAUSES] THEN
      MAP_EVERY UNDISCH_TAC [← q "~(n = 0)", ← q "~(n = 1)"] THEN ARITH_TAC,
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN (← q "d divides (a EXP m) MOD n") MP_TAC THENL
     [ALL_TAC, ASM_SIMP_TAC [DIVIDES_ONE]] THEN
    MATCH_MP_TAC DIVIDES_ADD_REVR THEN
    EXISTS_TAC (← q "a EXP m DIV n * n") THEN
    ASM_SIMP_TAC [← GSYM DIVISION, DIVIDES_LMUL] THEN
    SUBGOAL_THEN (← q "m = SUC(m - 1)") SUBST1_TAC THENL
     [UNDISCH_TAC (← q "~(m = 0)") THEN ARITH_TAC,
      ASM_SIMP_TAC [EXP, DIVIDES_RMUL]])

  let LUCAS_WEAK ← prove
   r"!a n. 2 <= n /\
           (a EXP (n - 1) == 1) (mod n) /\
           (!m. 0 < m /\ m < n - 1 ==> ~(a EXP m == 1) (mod n))
           ==> prime(n)"
   (← do
    let a1 ← ARITH_RULE (← q r"1 <= n ==> 0 < n")
    let t ← TAUT (← q r"a ==> ~(a /\ b) ==> ~b")
    let a2 ← ARITH_RULE (← q r"2 <= n ==> ~(n - 1 = 0)")
    let a0 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0) /\ ~(n = 1)")
    pure (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [← GSYM PHI_PRIME_EQ, PHI_LIMIT_STRONG, ← GSYM LE_ANTISYM, a0] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q "phi n")) THEN
    SUBGOAL_THEN (← q "coprime(a,n)") (fun th => SIMP_TAC [FERMAT_LITTLE, th]) THENL
     [MATCH_MP_TAC LUCAS_COPRIME_LEMMA THEN EXISTS_TAC (← q "n - 1") THEN
      ASM_SIMP_TAC [a2], ALL_TAC] THEN
    REWRITE_TAC [← GSYM NOT_LT] THEN
    MATCH_MP_TAC t THEN
    ASM_SIMP_TAC [PHI_LOWERBOUND_1, a1]))

  let LUCAS ← prove
   r"!a n. 2 <= n /\
           (a EXP (n - 1) == 1) (mod n) /\
           (!p. prime(p) /\ p divides (n - 1)
                ==> ~(a EXP ((n - 1) DIV p) == 1) (mod n))
           ==> prime(n)"
   (← do
    let a3 ← ARITH_RULE (← q r"~(p = 0) ==> 0 < p")
    let a2 ← ARITH_RULE (← q r"~(0 < n) ==> (n = 0)")
    let a1 ← ARITH_RULE (← q r"0 < n ==> ~(n = 0)")
    let t ← TAUT (← q r"a ==> ~b <=> ~(a /\ b)")
    let a0 ← ARITH_RULE (← q r"2 <= n ==> ~(n = 0)")
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP a0) THEN
    MATCH_MP_TAC LUCAS_WEAK THEN EXISTS_TAC (← q "a:num") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [t, ← GSYM NOT_EXISTS_THM] THEN
    ONCE_REWRITE_TAC [num_WOP] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "m:num") STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP a1) THEN
    SUBGOAL_THEN (← q "m divides (n - 1)") MP_TAC THENL
     [REWRITE_TAC [divides] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
      ASM_SIMP_TAC [← GSYM MOD_EQ_0] THEN
      MATCH_MP_TAC a2 THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q "(n - 1) MOD m")) THEN
      ASM_SIMP_TAC [DIVISION] THEN CONJ_TAC THENL
       [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC (← q "m:num") THEN
        ASM_SIMP_TAC [DIVISION], ALL_TAC] THEN
      MATCH_MP_TAC CONG_MULT_LCANCEL THEN
      EXISTS_TAC (← q "a EXP ((n - 1) DIV m * m)") THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC [COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_EXP THEN
        ONCE_REWRITE_TAC [COPRIME_SYM] THEN MATCH_MP_TAC LUCAS_COPRIME_LEMMA THEN
        EXISTS_TAC (← q "m:num") THEN ASM_SIMP_TAC [], ALL_TAC] THEN
      REWRITE_TAC [← GSYM EXP_ADD] THEN
      ASM_SIMP_TAC [← GSYM DIVISION] THEN REWRITE_TAC [MULT_CLAUSES] THEN
      ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [← GSYM EXP_EXP] THEN
      UNDISCH_TAC (← q r"(a EXP (n - 1) == 1) (mod n)") THEN
      UNDISCH_TAC (← q r"(a EXP m == 1) (mod n)") THEN
      ASM_SIMP_TAC [CONG] THEN REPEAT DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC (← q "((a EXP m) MOD n) EXP ((n - 1) DIV m) MOD n") THEN
      CONJ_TAC THENL [ALL_TAC, ASM_SIMP_TAC [MOD_EXP_MOD]] THEN
      ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [MOD_EXP_MOD] THEN
      REWRITE_TAC [EXP_ONE], ALL_TAC] THEN
    REWRITE_TAC [divides] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "r:num") SUBST_ALL_TAC) THEN
    SUBGOAL_THEN (← q "~(r = 1)") MP_TAC THENL
     [UNDISCH_TAC (← q "m < m * r") THEN CONV_TAC CONTRAPOS_CONV THEN
      SIMP_TAC [MULT_CLAUSES, LT_REFL], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o MATCH_MP PRIME_FACTOR) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "p:num") MP_TAC) THEN STRIP_TAC THEN
    UNDISCH_TAC (← q r"!p. prime p /\ p divides m * r
                     ==> ~(a EXP ((m * r) DIV p) == 1) (mod n)") THEN
    DISCH_THEN (MP_TAC o SPEC (← q "p:num")) THEN ASM_SIMP_TAC [DIVIDES_LMUL] THEN
    SUBGOAL_THEN (← q "(m * r) DIV p = m * (r DIV p)") SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC (← q "0") THEN
      UNDISCH_TAC (← q "prime p") THEN
      ASM_CASES_TAC (← q "p = 0") THEN ASM_REWRITE_TAC [PRIME_0] THEN
      ASM_SIMP_TAC [a3] THEN
      DISCH_TAC THEN REWRITE_TAC [ADD_CLAUSES, ← GSYM MULT_ASSOC] THEN
      AP_TERM_TAC THEN UNDISCH_TAC (← q "p divides r") THEN
      REWRITE_TAC [divides] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [DIV_MULT] THEN REWRITE_TAC [MULT_AC], ALL_TAC] THEN
    UNDISCH_TAC (← q r"(a EXP m == 1) (mod n)") THEN
    ASM_SIMP_TAC [CONG] THEN
    DISCH_THEN (MP_TAC o C AP_THM (← q "r DIV p") o AP_TERM (← q "(EXP)")) THEN
    DISCH_THEN (MP_TAC o C AP_THM (← q "n:num") o AP_TERM (← q "(MOD)")) THEN
    ASM_SIMP_TAC [MOD_EXP_MOD] THEN
    REWRITE_TAC [EXP_EXP, EXP_ONE]))

  -- @@RETURN BEGIN
  return { LUCAS_COPRIME_LEMMA, LUCAS_WEAK, LUCAS }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Prime factorizations.                                                     -/
/- ------------------------------------------------------------------------- -/

structure Primefact where
  -- @@FIELDS
  primefact : thm
  PRIMEFACT : thm
  PRIMAFACT_CONTAINS : thm
  PRIMEFACT_VARIANT : thm
  LUCAS_PRIMEFACT : thm
  deriving Inhabited

@[nospecialize]
def setupPrimefact [HolBase] (D : PrattDeps) (BLucas : Lucas) :
    ExceptT String IO Primefact := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, LIST_INDUCT_TAC, new_definition, .. } := D
  let { ALL, ALL_IMP, DIVIDES_ONE, ITLIST, .. } := D.core1
  let { LT_MULT_RCANCEL, MEM, MULT_CLAUSES, PRIME_0, PRIME_1, PRIME_DIVPROD,
        PRIME_FACTOR, divides, num_WF, prime, .. } := D.core2
  let { LUCAS, .. } := BLucas
  -- @@SCOPE END

  let primefact ← new_definition
   r"primefact ps n <=> (ITLIST (*) ps 1 = n) /\ !p. MEM p ps ==> prime(p)"

  let PRIMEFACT ← prove
   r"!n. ~(n = 0) ==> ?ps. primefact ps n"
   (← do
    let a1 ← ARITH_RULE (← q r"~(p = 0) /\ ~(p = 1) ==> 1 < p")
    let a0 ← ARITH_RULE (← q r"n = 1 * n")
    pure (MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q "n:num") THEN
    ASM_CASES_TAC (← q "n = 1") THEN ASM_REWRITE_TAC [] THENL
     [REPEAT DISCH_TAC THEN EXISTS_TAC (← q "[]:num list") THEN
      REWRITE_TAC [primefact, ITLIST, MEM], ALL_TAC] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q "p:num") STRIP_ASSUME_TAC o
      MATCH_MP PRIME_FACTOR) THEN
    UNDISCH_TAC (← q "p divides n") THEN REWRITE_TAC [divides] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "m:num") SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q "m:num")) THEN
    UNDISCH_TAC (← q "~(p * m = 0)") THEN
    ASM_CASES_TAC (← q "m = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN DISCH_TAC THEN
    GEN_REWRITE_TAC (funpow 3 LAND_CONV) [a0] THEN
    ASM_REWRITE_TAC [LT_MULT_RCANCEL] THEN
    SUBGOAL_THEN (← q "1 < p") (fun th => REWRITE_TAC [th]) THENL
     [MATCH_MP_TAC a1 THEN
      REPEAT STRIP_TAC THEN UNDISCH_TAC (← q "prime p") THEN
      ASM_REWRITE_TAC [PRIME_0, PRIME_1], ALL_TAC] THEN
    REWRITE_TAC [primefact] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "ps:num list") ASSUME_TAC) THEN
    EXISTS_TAC (← q "CONS (p:num) ps") THEN
    ASM_REWRITE_TAC [MEM, ITLIST] THEN ASM_MESON_TAC []))

  let PRIMAFACT_CONTAINS ← prove
   r"!ps n. primefact ps n ==> !p. prime p /\ p divides n ==> MEM p ps"
   (REPEAT GEN_TAC THEN REWRITE_TAC [primefact] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    POP_ASSUM (SUBST1_TAC o SYM) THEN
    SPEC_TAC (← q "ps:num list", ← q "ps:num list") THEN LIST_INDUCT_TAC THEN
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
    SPEC_TAC (← q "ps:num list", ← q "ps:num list") THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC [MEM, ALL] THEN ASM_MESON_TAC [])

  /- --------------------------------------------------------------------- -/
  /- Variant of Lucas theorem.                                             -/
  /- --------------------------------------------------------------------- -/

  let LUCAS_PRIMEFACT ← prove
   r"2 <= n /\
     (a EXP (n - 1) == 1) (mod n) /\
     (ITLIST (*) ps 1 = n - 1) /\
     ALL (\p. prime p /\ ~(a EXP ((n - 1) DIV p) == 1) (mod n)) ps
     ==> prime n"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC LUCAS THEN
    EXISTS_TAC (← q "a:num") THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q "primefact ps (n - 1)") MP_TAC THENL
     [ASM_REWRITE_TAC [PRIMEFACT_VARIANT] THEN MATCH_MP_TAC ALL_IMP THEN
      EXISTS_TAC (← q r"\p. prime p /\ ~(a EXP ((n - 1) DIV p) == 1) (mod n)") THEN
      ASM_SIMP_TAC [], ALL_TAC] THEN
    DISCH_THEN (ASSUME_TAC o MATCH_MP PRIMAFACT_CONTAINS) THEN
    X_GEN_TAC (← q "p:num") THEN DISCH_THEN (ANTE_RES_THEN MP_TAC) THEN UNDISCH_TAC
     (← q r"ALL (\p. prime p /\ ~(a EXP ((n - 1) DIV p) == 1) (mod n)) ps") THEN
    SPEC_TAC (← q "ps:num list", ← q "ps:num list") THEN LIST_INDUCT_TAC THEN
    SIMP_TAC [ALL, MEM] THEN ASM_MESON_TAC [])

  -- @@RETURN BEGIN
  return { primefact, PRIMEFACT, PRIMAFACT_CONTAINS, PRIMEFACT_VARIANT, LUCAS_PRIMEFACT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Utility functions.                                                        -/
/- ------------------------------------------------------------------------- -/

/-- `even_num n` (pratt.ml 678-679). -/
def even_num (n : Rat) : Bool := mod_num n num_2 == num_0

/-- `odd_num = not o even_num` (pratt.ml 681). -/
def odd_num (n : Rat) : Bool := !(even_num n)

/- ------------------------------------------------------------------------- -/
/- Least p >= 0 with x <= 2^p.                                               -/
/- ------------------------------------------------------------------------- -/

/-- `log2`'s inner recursion (pratt.ml 687-688). -/
partial def log2Aux (x y : Rat) : Rat :=
  if x < num_1 then y else log2Aux (quo_num x num_2) (y + num_1)

/-- `log2 x` (pratt.ml 686-690). -/
def log2 (x : Rat) : Rat := log2Aux (x - num_1) num_0

/- ------------------------------------------------------------------------- -/
/- Raise number to power (x^m) modulo n.                                     -/
/- ------------------------------------------------------------------------- -/

/-- `powermod x m n = x^m mod n` (pratt.ml 696-700). -/
partial def powermod (x m n : Rat) : Rat :=
  if m == num_0 then num_1
  else
    let y := powermod x (quo_num m num_2) n
    let z := mod_num (y * y) n
    if even_num m then z else mod_num (x * z) n

/- ------------------------------------------------------------------------- -/
/- Make a call to PARI/GP to factor a number into (probable) primes.         -/
/- ------------------------------------------------------------------------- -/

/-- `factor n`: factor `n` into (probable) primes with multiplicities, by a
    call to PARI/GP through the shell (pratt.ml 706-726).  Fails with
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

/- ------------------------------------------------------------------------- -/
/- Alternative giving multiset instead of set plus indices.                  -/
/- ------------------------------------------------------------------------- -/

/-- `multifactor`'s `multilist` (pratt.ml 732-735). -/
def multilist : List (Rat × Rat) → List Rat
  | [] => []
  | (x, n) :: t => replicate x n.num.toNat ++ multilist t

/-- `multifactor n` (pratt.ml 731-736): the multiset of prime factors of `n`. -/
def multifactor (n : Rat) : ExceptT String IO (List Rat) := do
  pure (multilist (← factor n))

/- ------------------------------------------------------------------------- -/
/- Recursive creation of Pratt primality certificates.                       -/
/- ------------------------------------------------------------------------- -/

/-- Pratt primality certificates (pratt.ml 742-745). -/
inductive certificate where
  | Prime_2
  | Primroot_and_factors : ((Rat × List Rat) × Rat × List (Rat × certificate)) → certificate
  deriving Inhabited

/-- `find_primitive_root`'s inner recursion (pratt.ml 748-753). -/
partial def findPrimitiveRootAux (a m : Rat) (ms : List Rat) (n : Rat) : Rat :=
  if gcd_num a n == num_1 && powermod a m n == num_1 &&
     forall' (fun k => powermod a k n != num_1) ms
  then a
  else findPrimitiveRootAux (a + num_1) m ms n

/-- `find_primitive_root m ms n` (pratt.ml 747-758): `find_primitive_root_from_2`
    is `find_primitive_root num_2`. -/
def find_primitive_root (m : Rat) (ms : List Rat) (n : Rat) : Except String Rat :=
  if n < num_2 then failwith "find_primitive_root: input too small"
  else pure (findPrimitiveRootAux num_2 m ms n)

/-- `uniq_num`'s inner `uniq` (pratt.ml 761-769): `none` models the
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

/-- `uniq_num l` (pratt.ml 760-770): `none` models `Unchanged`. -/
def uniq_num : List Rat → Option (List Rat)
  | [] => some []
  | h :: t => uniqAux h t

/-- `setify_num s` (pratt.ml 772-774). -/
def setify_num (s : List Rat) : List Rat :=
  let s' := sort (· ≤ ·) s
  match uniq_num s' with
  | none => s'
  | some r => r

/-- `certify_prime`'s `cert_prime` (pratt.ml 777-787). -/
partial def certPrime : Rat → ExceptT String IO certificate := fun n => do
  if n ≤ num_2 then
    if n == num_2 then pure .Prime_2
    else throw "certify_prime: not a prime!"
  else do
    let m := n - num_1
    let pfact ← multifactor m
    let primes := setify_num pfact
    let ms := primes.map (fun d => divide_num m d)
    let a ← liftExcept (find_primitive_root m ms n)
    let sub ← primes.mapM (fun p => do pure (p, ← certPrime p))
    pure (.Primroot_and_factors ((n, pfact), a, sub))

/-- `certify_prime n` (pratt.ml 776-789). -/
def certify_prime (n : Rat) : ExceptT String IO certificate := do
  if (← multifactor n).length == 1 then certPrime n
  else throw "certify_prime: input is not a prime"

/-- lib.ml's `time` for a rule, as the load-time examples use it
    (`time PRIME_TEST`, `time PROVE_PRIMEFACT`). -/
def timeThm {α : Type} (f : α → ExceptT String IO thm) (x : α) : ExceptT String IO thm :=
  ExceptT.mk (HolCore.Lib.time (fun t => (f t).run) x)

/-- `lookup_under_num n l` (pratt.ml 807-811). -/
partial def lookup_under_num {α : Type} (n : Rat) : List (Rat × α) → Except String α
  | [] => failwith "lookup_under_num"
  | h :: t => if h.1 == n then pure h.2 else lookup_under_num n t

/-- `EXP_EQ_MOD_CONV`'s inner `conv` (pratt.ml raw_conv): recurse through the
    binary expansion, falling back from `conv_base` to the stepping path. -/
partial def expEqModConv (conv_base conv_step let_CONV NUM_REDUCE_CONV : ioconv) :
    ioconv := fun tm => ExceptT.run do
  tryCatch (ExceptT.mk (conv_base tm))
    (fun _ => ExceptT.mk ((conv_step THENC
      RAND_CONV (expEqModConv conv_base conv_step let_CONV NUM_REDUCE_CONV) THENC
      let_CONV THENC
      NUM_REDUCE_CONV) tm))

/- ------------------------------------------------------------------------- -/
/- Relatively efficient evaluation of "(a EXP m == 1) (mod n)" and the        -/
/- HOL checking of a certificate, with a cache for efficiency.               -/
/- ------------------------------------------------------------------------- -/

/-- The theorems and conversions `check_certificate` closes over, plus its
    cache (pratt.ml 795-852). -/
structure CheckCtx where
  (n_tm a_tm ps_tm : term)
  (SIMPLE_REWRITE_CONV CLEAN_RULE_CONV EXP_EQ_MOD_CONV NUM_REDUCE_CONV : ioconv)
  (LUCAS_PRIMEFACT PRIME_2 : thm)
  mk_numeral : Rat → Except String term
  mk_flist : List term → IO (Except String term)
  cache : IO.Ref (List (Rat × thm))

/-- `check_certificate`'s recursion (pratt.ml 826-849). -/
partial def checkCertificate [HolBase] (C : CheckCtx) :
    certificate → ExceptT String IO thm
  | .Prime_2 => pure C.PRIME_2
  | .Primroot_and_factors ((n, ps), a, ncerts) => do
    match lookup_under_num n (← C.cache.get) with
    | .ok th => pure th
    | .error _ => do
      let psNums ← liftExcept (ps.mapM C.mk_numeral)
      let psList ← ExceptT.mk (C.mk_flist psNums)
      let nNum ← liftExcept (C.mk_numeral n)
      let aNum ← liftExcept (C.mk_numeral a)
      let th1 ← INST [(nNum, C.n_tm), (psList, C.ps_tm), (aNum, C.a_tm)] C.LUCAS_PRIMEFACT
      -- CLEAN_RULE = CONV_RULE (...)
      let th2 ← CONV_RULE C.CLEAN_RULE_CONV th1
      let th3 ← ExceptT.mk (ONCE_DEPTH_CONV C.EXP_EQ_MOD_CONV (concl th2))
      let th4 ← CONV_RULE C.SIMPLE_REWRITE_CONV (← EQ_MP th3 th2)
      let ants := conjuncts (← liftExcept (lhand (concl th4)))
      let certs ← ants.mapM (fun t => do
        let num ← liftExcept (do dest_numeral (← rand t))
        liftExcept (lookup_under_num num ncerts))
      let ths ← certs.mapM (checkCertificate C)
      let fth ← MP th4 (← HolLight.end_itlist CONJ ths)
      C.cache.modify (fun l => (n, fth) :: l)
      pure fth

/- ------------------------------------------------------------------------- -/
/- The conversions, cache and primality-proving rules, as one bundle.        -/
/- ------------------------------------------------------------------------- -/

/-- A rule taking a number (`PROVE_PRIME`, `PROVE_PRIMEFACT`). -/
abbrev RatRule := Rat → ExceptT String IO thm
/-- A rule taking a term (`PRIME_TEST`, `PRIME_CONV`). -/
abbrev TermRule := term → ExceptT String IO thm
/-- `check_certificate`. -/
abbrev CertRule := certificate → ExceptT String IO thm
/-- `prime_theorem_cache`. -/
abbrev ThmCache := IO.Ref (List (Rat × thm))

structure Certify where
  -- @@FIELDS
  EXP_EQ_MOD_CONV : ioconv
  prime_theorem_cache : Option ThmCache
  check_certificate : CertRule
  PROVE_PRIME : RatRule
  PROVE_PRIMEFACT : RatRule
  PRIME_TEST : TermRule
  PRIME_CONV : TermRule
  deriving Inhabited

@[nospecialize]
def setupCertify [HolBase] (D : PrattDeps) (BPrimefact : Primefact) :
    ExceptT String IO Certify := do
  -- @@SCOPE BEGIN
  let { MESON_TAC, NUM_DIV_CONV, NUM_EQ_CONV, NUM_LE_CONV, NUM_MULT_CONV,
        NUM_REDUCE_CONV, NUM_SUB_CONV, let_CONV, mk_flist, mk_numeral,
        mk_small_numeral, .. } := D
  let { ALL, BIT0, BIT1, CONG, EXP, EXP_ADD, ITLIST, .. } := D.core1
  let { MOD_MULT_LMOD, MOD_MULT_RMOD, MULT_ASSOC, MULT_SYM, NUMERAL, PRIME_0, PRIME_1,
        PRIME_2, divides, prime, .. } := D.core2
  let { LUCAS_PRIMEFACT, PRIMEFACT_VARIANT, .. } := BPrimefact
  -- @@SCOPE END

  -- `EXP_EQ_MOD_CONV` (pratt.ml 732-779 of the computational part): built once.
  let EXP_EQ_MOD_CONV : ioconv ← do
    let pth ← prove
     r"~(n = 0)
       ==> ((a EXP 0) MOD n = 1 MOD n) /\
           ((a EXP (NUMERAL (BIT0 m))) MOD n =
                  let b = (a EXP (NUMERAL m)) MOD n in
                  (b * b) MOD n) /\
           ((a EXP (NUMERAL (BIT1 m))) MOD n =
                  let b = (a EXP (NUMERAL m)) MOD n in
                  (a * ((b * b) MOD n)) MOD n)"
     (DISCH_TAC THEN REWRITE_TAC [EXP] THEN
      REWRITE_TAC [NUMERAL, BIT0, BIT1] THEN
      REWRITE_TAC [EXP, EXP_ADD] THEN
      CONV_TAC (ONCE_DEPTH_CONV let_CONV) THEN
      ASM_SIMP_TAC [MOD_MULT_LMOD, MOD_MULT_RMOD] THEN
      REWRITE_TAC [MULT_ASSOC] THEN
      ASM_SIMP_TAC [MOD_MULT_LMOD, MOD_MULT_RMOD] THEN
      ONCE_REWRITE_TAC [MULT_SYM] THEN
      REWRITE_TAC [MULT_ASSOC] THEN
      ASM_SIMP_TAC [MOD_MULT_LMOD, MOD_MULT_RMOD])
    let pth_cong ← prove
     r"~(n = 0) ==> ((x == y) (mod n) <=> x MOD n = y MOD n)"
     (REWRITE_TAC [CONG])
    let n_tm ← q "n:num"
    let raw_conv : ioconv ← pure (fun tm => ExceptT.run do
      let ntm ← liftExcept (do rand (← rand tm))
      let th1 ← INST [(ntm, n_tm)] pth_cong
      let th2 ← EQF_ELIM (← ExceptT.mk (NUM_EQ_CONV (← liftExcept (do rand (← lhand (concl th1))))))
      let th3 ← ExceptT.mk (REWR_CONV (← MP th1 th2) tm)
      let th4 ← MP (← INST [(ntm, n_tm)] pth) th2
      let (th4a, th4b) ← CONJ_PAIR th4
      let conv_base : ioconv ← pure (GEN_REWRITE_CONV id [th4a])
      let conv_step : ioconv ← pure (GEN_REWRITE_CONV id [th4b])
      let conv : ioconv := expEqModConv conv_base conv_step let_CONV NUM_REDUCE_CONV
      let th5 ← ExceptT.mk ((LAND_CONV conv THENC NUM_REDUCE_CONV) (← liftExcept (rand (concl th3))))
      TRANS th3 th5)
    let gconv_net ← ExceptT.mk (HolCore.Simp.net_of_conv (← q r"(a EXP m == 1) (mod n)")
      raw_conv HolCore.Nets.empty_net)
    pure (REWRITES_CONV gconv_net)

  -- `prime_theorem_cache = ref []` (pratt.ml 801): created once, when this
  -- (cached) setup runs at load, and closed over by the rules below.
  let loc_prime_theorem_cache : ThmCache ← IO.mkRef []
  -- Exported as `some ref`: a structure with an `IO.Ref` field cannot derive
  -- `Inhabited` computably, so the field is an `Option`.
  let prime_theorem_cache : Option ThmCache ← pure (some loc_prime_theorem_cache)

  -- `check_certificate` (pratt.ml 813-850): its convs/rule are built once.
  let check_certificate : CertRule ← do
    let loc_n_tm ← q r"n:num"
    let loc_a_tm ← q r"a:num"
    let loc_ps_tm ← q r"ps:num list"
    let loc_SIMPLE_REWRITE_CONV : ioconv ← pure (REWRITE_CONV [])
    let loc_CONJ_AC_SORTED ← TAUT (← q r"(a /\ a /\ b <=> a /\ b) /\ (a /\ a <=> a)")
    -- CLEAN_RULE = CONV_RULE(...): the CONV is built once.
    let loc_CLEAN_RULE_CONV : ioconv ← do
      let c0 ← REWRITE_CONV_NET [ITLIST, ALL, loc_CONJ_AC_SORTED]
      pure (c0 THENC
            ONCE_DEPTH_CONV NUM_SUB_CONV THENC
            DEPTH_CONV NUM_MULT_CONV THENC
            ONCE_DEPTH_CONV NUM_DIV_CONV THENC
            ONCE_DEPTH_CONV (NUM_EQ_CONV ORELSEC NUM_LE_CONV) THENC
            loc_SIMPLE_REWRITE_CONV)
    let C : CheckCtx :=
      ⟨loc_n_tm, loc_a_tm, loc_ps_tm,
       loc_SIMPLE_REWRITE_CONV, loc_CLEAN_RULE_CONV, EXP_EQ_MOD_CONV, NUM_REDUCE_CONV,
       LUCAS_PRIMEFACT, PRIME_2, mk_numeral, mk_flist, loc_prime_theorem_cache⟩
    pure (checkCertificate C)

  -- `PROVE_PRIME = check_certificate o certify_prime` (pratt.ml 856).
  let PROVE_PRIME : RatRule ←
    pure (fun n => do check_certificate (← certify_prime n))

  -- `PROVE_PRIMEFACT` (pratt.ml 862-874).
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

  -- `PRIME_TEST` (pratt.ml 880-901).
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

  -- `PRIME_CONV` (pratt.ml 903-908).
  let PRIME_CONV : TermRule ← do
    let loc_prime_tm ← q r"prime"
    pure (fun tm0 => do
      let (ptm, tm) ← liftExcept (dest_comb tm0)
      if ptm != loc_prime_tm then throw "expected term of form prime(n)"
      else PRIME_TEST tm)

  /- --------------------------------------------------------------------- -/
  /- Example.                                                              -/
  /- --------------------------------------------------------------------- -/

  _ ← (upto 0 50).mapM (fun i => do
    let tm ← liftExcept (mk_small_numeral i)
    timeThm PRIME_TEST tm)
  _ ← timeThm PRIME_TEST (← q r"65535")
  _ ← timeThm PRIME_TEST (← q r"65536")
  _ ← timeThm PRIME_TEST (← q r"65537")
  _ ← timeThm PROVE_PRIMEFACT (222 : Rat)
  _ ← timeThm PROVE_PRIMEFACT (151 : Rat)

  /- --------------------------------------------------------------------- -/
  /- The "Landau trick" in Erdos's proof of Chebyshev-Bertrand theorem.    -/
  /- --------------------------------------------------------------------- -/

  _ ← ([3, 5, 7, 13, 23, 43, 83, 163, 317, 631, 1259, 2503, 4001] : List Int).mapM
    (fun i => do
      let tm ← liftExcept (mk_small_numeral i)
      timeThm PRIME_TEST tm)

  -- @@RETURN BEGIN
  return { EXP_EQ_MOD_CONV, prime_theorem_cache, check_certificate, PROVE_PRIME,
           PROVE_PRIMEFACT, PRIME_TEST, PRIME_CONV }
  -- @@RETURN END

end HolLibrary.Pratt
