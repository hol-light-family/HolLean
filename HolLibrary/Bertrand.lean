/- ========================================================================= -/
/- Bertrand's postulate (BERTRAND): for every n >= 1 there is a prime p      -/
/- with n < p <= 2 n, by Erdos's proof with natural numbers only.            -/
/- ========================================================================= -/
/- File: HolLibrary/Bertrand.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `100/bertrand.ml` (e7fbefd), by hand, in
  file order, in the style of HolLibrary/Cyclotomic.lean (see there and
  HolMath/Base.lean for the conventions).  It is a library module, not a
  Hol100 session, because Library/szemeredi.ml `needs` it; HOL Light loads
  100/ files with `needs` like any other.  Hol100/Bertrand.lean, the 100/
  session, loads this module.  bertrand.ml begins with `needs` of prime.ml,
  binomial.ml and products.ml, then `prioritize_num()` (run at the start of
  the first bundle); the theorems it uses from them and from the core
  library are supplied via the CoreThms structures (SessionLibrary.Bertrand
  fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, TAUT, NUMBER_RULE) they are bound first,
  in OCaml's order.
-/

import HolMath

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.Bertrand

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD1 ADD_CLAUSES ADD_EQ_0 ARITH ARITH_EQ BINOMIAL_THEOREM BINOM_EQ_0
   BINOM_FACT BINOM_SYM CARD_NUMSEG_1 CARD_NUMSEG_LT CARD_SING CARD_SUBSET
   CONTRAPOS_THM COPRIME_NPRODUCT DE_MORGAN_THM DISJOINT DISTINCT_PRIME_COPRIME
   DIVIDES_1 DIVIDES_FACT_PRIME DIVIDES_LE DIVIDES_MOD DIVIDES_MUL DIVISION
   DIV_EQ_0 DIV_UNIQ EQ_IMP_LE EQ_MULT_LCANCEL EVEN_OR_ODD EXISTS_OR_THM EXP
   EXP_1 EXP_2 EXP_ADD EXP_EQ_0 EXP_EQ_1 EXP_EXP EXP_MONO_LE_IMP EXP_ONE
   EXTENSION FACT FACT_NZ FINITE_EMPTY FINITE_EXP_LE FINITE_INDUCT_STRONG
   FINITE_INSERT FINITE_NUMSEG FINITE_NUMSEG_LE FINITE_NUMSEG_LT FINITE_RESTRICT
   FINITE_SING FINITE_SUBSET FORALL_IN_INSERT IMP_CONJ INDEX_FACT_ALT INDEX_MUL
   IN_ELIM_THM IN_INSERT IN_INTER IN_NUMSEG IN_SING IN_UNION LET_TRANS LE_CASES
   LE_EXP LE_MULT2 LE_MULT_LCANCEL LE_MULT_RCANCEL LE_RDIV_EQ LE_REFL LE_TRANS
   LTE_TRANS LT_EXP LT_POW2_REFL MONO_EXISTS MULT_ASSOC MULT_CLAUSES MULT_EQ_0
   MULT_EXP NOT_EVEN NOT_EXISTS_THM NOT_IN_EMPTY NOT_LE NOT_LT NPRODUCT_CLAUSES
   NPRODUCT_CONST NPRODUCT_LE NPRODUCT_MUL NPRODUCT_RESTRICT_SET NPRODUCT_SING
   NPRODUCT_SUPERSET NPRODUCT_UNION NSUM_ADD NSUM_CLAUSES NSUM_CONST NSUM_LE
   NSUM_LMUL NSUM_SING NSUM_SUBSET_SIMPLE NSUM_SUPERSET ODD_EXISTS PRIME_2
   PRIME_DIVPROD_EQ PRIME_FACTORIZATION_ALT PRIME_GE_2 PRIME_ODD RDIV_LT_EQ
   RIGHT_FORALL_IMP_THM RIGHT_OR_DISTRIB SUBSET UNWIND_THM2 binom divides num_WF
   num_WOP prime : thm)
  deriving Inhabited

/-- What bertrand.ml uses from Session besides theorems. -/
structure BertrandDeps where
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  SET_TAC : List thm → tactic
  TAUT : term → ExceptT String IO thm
  INDUCT_TAC : tactic
  NUM_REDUCE_CONV : ioconv  -- calc_num.ml's NUM_REDUCE_CONV
  EXPAND_CASES_CONV : ioconv  -- calc_num.ml's EXPAND_CASES_CONV
  NUM_RING : ioconv  -- grobner.ml's NUM_RING
  NUMBER_RULE : ioconv  -- ints.ml's NUMBER_RULE
  prioritize_num : IO Unit  -- prioritize_num ()
  core1 : CoreThms1

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)

/- ------------------------------------------------------------------------- -/
/- Central binomial coefficients.  (bertrand.ml 24-92)                       -/
/- ------------------------------------------------------------------------- -/

structure CentralBinomial where
  -- @@FIELDS
  BINOM_CENTRAL_STEP : thm
  BINOM_CENTRAL_LOWER : thm
  BINOM_ODD_UPPER : thm
  deriving Inhabited

@[nospecialize]
def setupCentralBinomial [HolBase] (D : BertrandDeps) :
    ExceptT String IO CentralBinomial := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, INDUCT_TAC, MESON, NUM_RING, prioritize_num, .. } := D
  let { ADD1, ADD_CLAUSES, ADD_EQ_0, ARITH, ARITH_EQ, BINOMIAL_THEOREM, BINOM_FACT,
        BINOM_SYM, EQ_MULT_LCANCEL, EXP, EXP_ADD, EXP_EXP, EXP_ONE, FACT, FACT_NZ,
        FINITE_EMPTY, FINITE_INSERT, FINITE_NUMSEG, IN_INSERT, IN_NUMSEG,
        LE_MULT_LCANCEL, LE_MULT_RCANCEL, LE_REFL, LE_TRANS, MULT_ASSOC, MULT_CLAUSES,
        MULT_EQ_0, NOT_IN_EMPTY, NSUM_CLAUSES, NSUM_SUBSET_SIMPLE, SUBSET, binom, .. } := D.core1
  -- @@SCOPE END
  -- prioritize_num() (bertrand.ml 28), after the `needs`, which the
  -- imports have done
  prioritize_num

  let BINOM_CENTRAL_STEP ← prove
   r"!n. (n + 1) * binom(2 * n + 2,n + 1) = 2 * (2 * n + 1) * binom(2 * n,n)"
   (← do
    -- right to left: the MESON, then the ARITH_RULEs from the last
    let m5 ← MESON [EQ_MULT_LCANCEL]
     (← q r"!c x y:num. ~(c = 0) /\ c * x = c * y ==> x = y")
    let a4 ← ARITH_RULE (← q r"n + 1 = SUC n")
    let a3 ← ARITH_RULE (← q r"2 * n + 2 = SUC(SUC(2 * n))")
    let a2 ← ARITH_RULE (← q r"(n + 1) + n + 1 = 2 * n + 2")
    let a1 ← ARITH_RULE (← q r"n + n = 2 * n")
    pure (GEN_TAC THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"n:num"] BINOM_FACT) THEN
    MP_TAC (← SPECL [← q r"n + 1", ← q r"n + 1"] BINOM_FACT) THEN
    REWRITE_TAC [a1, a2] THEN
    REWRITE_TAC [a3, a4, FACT] THEN
    MP_TAC (← SPEC (← q r"n:num") FACT_NZ) THEN
    SPEC_TAC (← q r"FACT n", ← q r"a:num") THEN
    SPEC_TAC (← q r"FACT(2 * n)", ← q r"c:num") THEN
    SPEC_TAC (← q r"binom(2 * n,n)", ← q r"b:num") THEN
    SPEC_TAC (← q r"binom(SUC(SUC(2 * n)),SUC n)", ← q r"d:num") THEN
    REWRITE_TAC [ADD1] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC m5 THEN
    EXISTS_TAC (← q r"(n + 1) * a * a") THEN
    ASM_REWRITE_TAC [MULT_EQ_0, ADD_EQ_0, ARITH_EQ] THEN
    UNDISCH_TAC (← q r"a * a * b = c:num") THEN
    UNDISCH_TAC (← q r"((n + 1) * a) * ((n + 1) * a) * d =
               ((2 * n + 1) + 1) * (2 * n + 1) * c") THEN
    CONV_TAC NUM_RING))

  let BINOM_CENTRAL_LOWER ← prove
   r"!n. 4 EXP n <= (2 * n + 1) * binom(2 * n,n)"
   (← do
    let a3 ← ARITH_RULE
     (← q r"(n + 1) * ((2 * n + 2) + 1) * b = ((2 * n + 2) + 1) * (n + 1) * b")
    let m2 ← MESON [LE_MULT_LCANCEL]
     (← q r"!c x y:num. ~(c = 0) /\ c * x <= c * y ==> x <= y")
    let a1 ← ARITH_RULE (← q r"2 * SUC n = 2 * n + 2")
    pure (INDUCT_TAC THENL
     [REWRITE_TAC [EXP, MULT_CLAUSES, ADD_CLAUSES, binom, LE_REFL], ALL_TAC] THEN
    REWRITE_TAC [EXP] THEN
    REWRITE_TAC [a1, ADD1] THEN
    MATCH_MP_TAC m2 THEN
    EXISTS_TAC (← q r"n + 1") THEN REWRITE_TAC [ADD_EQ_0, ARITH_EQ] THEN
    REWRITE_TAC [a3] THEN
    REWRITE_TAC [BINOM_CENTRAL_STEP] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC (← q r"(n + 1) * 4 * (2 * n + 1) * binom(2 * n,n)") THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC [LE_MULT_LCANCEL],
      REWRITE_TAC [MULT_ASSOC, LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ARITH_TAC]))

  let BINOM_ODD_UPPER ← prove
   r"!k. binom(2 * k + 1,k) <= 4 EXP k"
   (← do
    let a4 ← ARITH_RULE (← q r"(2 * k + 1) - k = k + 1")
    let a3 ← ARITH_RULE (← q r"k <= 2 * k + 1")
    let a2 ← ARITH_RULE (← q r"~(k = k + 1)")
    let a1 ← ARITH_RULE (← q r"1 + 1 = 2")
    pure (GEN_TAC THEN
    MP_TAC (← SPECL [← q r"2 * k + 1", ← q r"1", ← q r"1"] BINOMIAL_THEOREM) THEN
    REWRITE_TAC [EXP_ONE, MULT_CLAUSES, a1] THEN
    DISCH_THEN (ASSUME_TAC o SYM) THEN
    MP_TAC (← ISPECL [← q r"{k,k + 1}", ← q r"0..2 * k + 1", ← q r"\i. binom(2 * k + 1,i)"]
      NSUM_SUBSET_SIMPLE) THEN
    ASM_REWRITE_TAC [FINITE_NUMSEG] THEN ANTS_TAC THENL
     [REWRITE_TAC [SUBSET, IN_INSERT, NOT_IN_EMPTY, IN_NUMSEG] THEN ARITH_TAC,
      ALL_TAC] THEN
    SIMP_TAC [NSUM_CLAUSES, FINITE_INSERT, FINITE_EMPTY, IN_INSERT,
              NOT_IN_EMPTY, a2, ADD_CLAUSES] THEN
    MP_TAC (← SPECL [← q r"2 * k + 1", ← q r"k:num"] BINOM_SYM) THEN
    REWRITE_TAC [a3, a4] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [EXP_ADD, ← GSYM EXP_EXP, ARITH] THEN ARITH_TAC))

  -- @@RETURN BEGIN
  return { BINOM_CENTRAL_STEP, BINOM_CENTRAL_LOWER, BINOM_ODD_UPPER }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- The product of the primes up to m is at most 4^m.  (bertrand.ml 94-198)   -/
/- ------------------------------------------------------------------------- -/

structure Primorial where
  -- @@FIELDS
  PRIME_DIVIDES_BINOM_ODD : thm
  NPRODUCT_PRIMES_DIVIDES : thm
  FINITE_PRIMES_LE : thm
  PRIMORIAL_LE_4_EXP : thm
  deriving Inhabited

@[nospecialize]
def setupPrimorial [HolBase] (D : BertrandDeps) (BCentralBinomial : CentralBinomial) :
    ExceptT String IO Primorial := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC,
        NUM_REDUCE_CONV, SET_TAC, TAUT, .. } := D
  let { ADD1, ARITH_EQ, BINOM_EQ_0, BINOM_FACT, COPRIME_NPRODUCT, DISJOINT,
        DISTINCT_PRIME_COPRIME, DIVIDES_1, DIVIDES_FACT_PRIME, DIVIDES_LE, DIVIDES_MUL,
        EVEN_OR_ODD, EXP_ADD, EXP_EQ_0, EXTENSION, FINITE_INDUCT_STRONG,
        FINITE_NUMSEG_LE, FINITE_SUBSET, FORALL_IN_INSERT, IMP_CONJ, IN_ELIM_THM,
        IN_INTER, IN_SING, IN_UNION, LE_EXP, LE_MULT2, LE_REFL, LE_TRANS, NOT_EVEN,
        NOT_IN_EMPTY, NPRODUCT_CLAUSES, NPRODUCT_SING, NPRODUCT_UNION, ODD_EXISTS,
        PRIME_2, PRIME_DIVPROD_EQ, PRIME_GE_2, PRIME_ODD, RIGHT_FORALL_IMP_THM, num_WF, .. } := D.core1
  let { BINOM_ODD_UPPER, .. } := BCentralBinomial
  -- @@SCOPE END

  let PRIME_DIVIDES_BINOM_ODD ← prove
   r"!k p. prime p /\ k + 2 <= p /\ p <= 2 * k + 1
         ==> p divides binom(2 * k + 1,k)"
   (← do
    let t2 ← TAUT (← q r"~a /\ ~b ==> a \/ b \/ c ==> c")
    let a1 ← ARITH_RULE (← q r"(k + 1) + k = 2 * k + 1")
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"k + 1", ← q r"k:num"] BINOM_FACT) THEN
    REWRITE_TAC [a1] THEN DISCH_TAC THEN
    SUBGOAL_THEN (← q r"p divides FACT(k + 1) * FACT k * binom(2 * k + 1,k)")
    MP_TAC THENL
     [ASM_SIMP_TAC [DIVIDES_FACT_PRIME], ALL_TAC] THEN
    ASM_SIMP_TAC [PRIME_DIVPROD_EQ, DIVIDES_FACT_PRIME] THEN
    MATCH_MP_TAC t2 THEN ASM_ARITH_TAC))

  let NPRODUCT_PRIMES_DIVIDES ← prove
   r"!s x. FINITE s /\ (!p. p IN s ==> prime p /\ p divides x)
         ==> nproduct s (\p. p) divides x"
   (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC [NPRODUCT_CLAUSES, DIVIDES_1, FORALL_IN_INSERT] THEN
    MAP_EVERY X_GEN_TAC [← q r"q:num", ← q r"s:num->bool"] THEN STRIP_TAC THEN
    X_GEN_TAC (← q r"x:num") THEN STRIP_TAC THEN
    MATCH_MP_TAC DIVIDES_MUL THEN ASM_SIMP_TAC [] THEN
    MATCH_MP_TAC COPRIME_NPRODUCT THEN ASM_REWRITE_TAC [] THEN
    X_GEN_TAC (← q r"r:num") THEN DISCH_TAC THEN
    MATCH_MP_TAC DISTINCT_PRIME_COPRIME THEN ASM_MESON_TAC [])

  let FINITE_PRIMES_LE ← prove
   r"!m (P:num->bool). FINITE {p | prime p /\ P p /\ p <= m}"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC (← q r"{p:num | p <= m}") THEN REWRITE_TAC [FINITE_NUMSEG_LE] THEN
    SET_TAC [])

  let PRIMORIAL_LE_4_EXP ← prove
   r"!m. nproduct {p | prime p /\ p <= m} (\p. p) <= 4 EXP m"
   (← do
    let a2 ← ARITH_RULE (← q r"~(p <= k + 1 /\ k + 2 <= p)")
    let a1 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    pure (MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q r"m:num") THEN DISCH_TAC THEN
    ASM_CASES_TAC (← q r"m <= 2") THENL
     [SUBGOAL_THEN (← q r"{p | prime p /\ p <= m} = if m = 2 then {2} else {}")
      SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"p:num") THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC [IN_SING, NOT_IN_EMPTY] THENL
         [EQ_TAC THENL
           [DISCH_THEN (CONJUNCTS_THEN2 (MP_TAC o MATCH_MP PRIME_GE_2) MP_TAC)
            THEN ARITH_TAC,
            DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [PRIME_2, LE_REFL]],
          STRIP_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP PRIME_GE_2) THEN
          ASM_ARITH_TAC],
        COND_CASES_TAC THEN REWRITE_TAC [NPRODUCT_CLAUSES, NPRODUCT_SING] THEN
        ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC [a1, EXP_EQ_0, ARITH_EQ]],
      ALL_TAC] THEN
    DISJ_CASES_TAC (← SPEC (← q r"m:num") EVEN_OR_ODD) THENL
     [SUBGOAL_THEN (← q r"{p | prime p /\ p <= m} = {p | prime p /\ p <= m - 1}")
      SUBST1_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"p:num") THEN
        ASM_CASES_TAC (← q r"p:num = m") THENL
         [FIRST_X_ASSUM SUBST_ALL_TAC THEN
          SUBGOAL_THEN (← q r"~prime m") (fun th => REWRITE_TAC [th]) THEN
          DISCH_THEN (MP_TAC o MATCH_MP PRIME_ODD) THEN
          ASM_REWRITE_TAC [← GSYM NOT_EVEN] THEN ASM_ARITH_TAC,
          AP_TERM_TAC THEN ASM_ARITH_TAC],
        ALL_TAC] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"4 EXP (m - 1)") THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
        REWRITE_TAC [LE_EXP] THEN ARITH_TAC],
      ALL_TAC] THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN (← q r"k:num") SUBST_ALL_TAC o
      REWRITE_RULE [ODD_EXISTS]) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [ADD1]) THEN REWRITE_TAC [ADD1] THEN
    SUBGOAL_THEN
     (← q r"{p | prime p /\ p <= 2 * k + 1} =
    {p | prime p /\ p <= k + 1} UNION
    {p | prime p /\ k + 2 <= p /\ p <= 2 * k + 1}")
    SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION, IN_UNION, IN_ELIM_THM] THEN X_GEN_TAC (← q r"p:num") THEN
      ASM_CASES_TAC (← q r"prime p") THEN ASM_REWRITE_TAC [] THEN ARITH_TAC,
      ALL_TAC] THEN
    wPart lhand (fun t => do lhand (← rand t)) NPRODUCT_UNION THEN
    ANTS_TAC THENL
     [REWRITE_TAC [DISJOINT, EXTENSION, IN_INTER, IN_ELIM_THM, NOT_IN_EMPTY] THEN
      REPEAT CONJ_TAC THENL
       [MP_TAC (← SPECL [← q r"k + 1", ← q r"\p:num. T"] FINITE_PRIMES_LE) THEN
        REWRITE_TAC [],
        REWRITE_TAC [FINITE_PRIMES_LE],
        MESON_TAC [a2]],
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"4 EXP (k + 1) * 4 EXP k") THEN
    CONJ_TAC THENL
     [ALL_TAC, REWRITE_TAC [← GSYM EXP_ADD, LE_EXP] THEN ARITH_TAC] THEN
    MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"binom(2 * k + 1,k)") THEN
    REWRITE_TAC [BINOM_ODD_UPPER] THEN
    MP_TAC (← ISPECL [← q r"{p | prime p /\ k + 2 <= p /\ p <= 2 * k + 1}",
                      ← q r"binom(2 * k + 1,k)"] NPRODUCT_PRIMES_DIVIDES) THEN
    REWRITE_TAC [FINITE_PRIMES_LE, IN_ELIM_THM] THEN ANTS_TAC THENL
     [MESON_TAC [PRIME_DIVIDES_BINOM_ODD], ALL_TAC] THEN
    DISCH_THEN (MP_TAC o MATCH_MP DIVIDES_LE) THEN
    REWRITE_TAC [BINOM_EQ_0] THEN ARITH_TAC))

  -- @@RETURN BEGIN
  return { PRIME_DIVIDES_BINOM_ODD, NPRODUCT_PRIMES_DIVIDES, FINITE_PRIMES_LE,
           PRIMORIAL_LE_4_EXP }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- The index of a prime in binom(2 n,n).  (bertrand.ml 200-314)              -/
/- ------------------------------------------------------------------------- -/

structure IndexBinom where
  -- @@FIELDS
  DIV_DOUBLE_LE : thm
  INDEX_BINOM_CENTRAL : thm
  INDEX_BINOM_CENTRAL_CARD : thm
  INDEX_BINOM_CENTRAL_LE : thm
  INDEX_BINOM_CENTRAL_SQRT : thm
  PRIMEPOW_INDICES_SING : thm
  INDEX_BINOM_CENTRAL_ZERO : thm
  deriving Inhabited

@[nospecialize]
def setupIndexBinom [HolBase] (D : BertrandDeps) :
    ExceptT String IO IndexBinom := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, .. } := D
  let { BINOM_EQ_0, BINOM_FACT, CARD_NUMSEG_1, CARD_SING, CARD_SUBSET, CONTRAPOS_THM,
        DIVISION, DIV_EQ_0, DIV_UNIQ, EXP, EXP_1, EXP_2, EXP_EQ_0, EXTENSION, FACT_NZ,
        FINITE_EXP_LE, FINITE_NUMSEG, FINITE_SING, INDEX_FACT_ALT, INDEX_MUL,
        IN_ELIM_THM, IN_NUMSEG, IN_SING, LET_TRANS, LE_MULT_RCANCEL, LE_REFL, LE_TRANS,
        LT_EXP, MULT_EQ_0, NOT_LE, NSUM_ADD, NSUM_CONST, NSUM_LE, NSUM_LMUL, NSUM_SING,
        NSUM_SUPERSET, PRIME_GE_2, RDIV_LT_EQ, SUBSET, .. } := D.core1
  -- @@SCOPE END

  let DIV_DOUBLE_LE ← prove
   r"!n q. ~(q = 0) ==> (2 * n) DIV q <= 2 * (n DIV q) + 1"
   (← do
    let a1 ← ARITH_RULE (← q r"x <= y + 1 <=> x < y + 2")
    pure (REPEAT STRIP_TAC THEN
    REWRITE_TAC [a1] THEN
    ASM_SIMP_TAC [RDIV_LT_EQ] THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"q:num"] DIVISION) THEN ASM_REWRITE_TAC [] THEN
    ARITH_TAC))

  let INDEX_BINOM_CENTRAL ← prove
   r"!n p. prime p
         ==> index p (FACT n) + index p (FACT n) + index p (binom(2 * n,n)) =
             index p (FACT(2 * n))"
   (← do
    let a2 ← ARITH_RULE (← q r"~(2 * n < n)")
    let a1 ← ARITH_RULE (← q r"n + n = 2 * n")
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"n:num"] BINOM_FACT) THEN
    REWRITE_TAC [a1] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC [INDEX_MUL, FACT_NZ, MULT_EQ_0, BINOM_EQ_0, a2]))

  let INDEX_BINOM_CENTRAL_CARD ← prove
   r"!n p. prime p
         ==> index p (binom(2 * n,n)) <=
             CARD {j | 1 <= j /\ p EXP j <= 2 * n}"
   (← do
    let a1 ← ARITH_RULE (← q r"b <= a + a + c ==> a + a + e = b ==> e:num <= c")
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    SUBGOAL_THEN (← q r"!j. ~(p EXP j = 0)") ASSUME_TAC THENL
     [REWRITE_TAC [EXP_EQ_0] THEN ASM_ARITH_TAC, ALL_TAC] THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"p:num"] INDEX_BINOM_CENTRAL) THEN
    ASM_SIMP_TAC [INDEX_FACT_ALT] THEN
    SUBGOAL_THEN
     (← q r"nsum {j | 1 <= j /\ p EXP j <= n} (\j. n DIV p EXP j) =
    nsum {j | 1 <= j /\ p EXP j <= 2 * n} (\j. n DIV p EXP j)")
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN CONJ_TAC THENL
       [ARITH_TAC,
        X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN
        ASM_SIMP_TAC [DIV_EQ_0] THEN ASM_ARITH_TAC],
      ALL_TAC] THEN
    MATCH_MP_TAC a1 THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC
     (← q r"nsum {j | 1 <= j /\ p EXP j <= 2 * n} (\j. 2 * n DIV p EXP j + 1)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_LE THEN ASM_SIMP_TAC [FINITE_EXP_LE, DIV_DOUBLE_LE],
      ASM_SIMP_TAC [NSUM_ADD, NSUM_LMUL, NSUM_CONST, FINITE_EXP_LE] THEN
      ARITH_TAC]))

  let INDEX_BINOM_CENTRAL_LE ← prove
   r"!n p. prime p /\ 1 <= n ==> p EXP index p (binom(2 * n,n)) <= 2 * n"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"p:num"] INDEX_BINOM_CENTRAL_CARD) THEN
    ASM_REWRITE_TAC [] THEN
    SPEC_TAC (← q r"index p (binom(2 * n,n))", ← q r"e:num") THEN GEN_TAC THEN
    ASM_CASES_TAC (← q r"e = 0") THENL
     [ASM_REWRITE_TAC [EXP] THEN ASM_ARITH_TAC, ALL_TAC] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN REWRITE_TAC [NOT_LE] THEN
    DISCH_TAC THEN MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC (← q r"CARD(1..e-1)") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN
      REWRITE_TAC [FINITE_NUMSEG, SUBSET, IN_ELIM_THM, IN_NUMSEG] THEN
      X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"p EXP j < p EXP e") MP_TAC THENL
       [ASM_ARITH_TAC, ASM_REWRITE_TAC [LT_EXP] THEN ASM_ARITH_TAC],
      REWRITE_TAC [CARD_NUMSEG_1] THEN ASM_ARITH_TAC])

  let INDEX_BINOM_CENTRAL_SQRT ← prove
   r"!n p. prime p /\ 2 * n < p * p ==> index p (binom(2 * n,n)) <= 1"
   (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC (← q r"CARD {j | 1 <= j /\ p EXP j <= 2 * n}") THEN
    ASM_SIMP_TAC [INDEX_BINOM_CENTRAL_CARD] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"CARD {1}") THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN
      REWRITE_TAC [FINITE_SING, SUBSET, IN_ELIM_THM, IN_SING] THEN
      X_GEN_TAC (← q r"j:num") THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"p EXP j < p EXP 2") MP_TAC THENL
       [REWRITE_TAC [EXP_2] THEN ASM_ARITH_TAC,
        ASM_REWRITE_TAC [LT_EXP] THEN ASM_ARITH_TAC],
      REWRITE_TAC [CARD_SING, LE_REFL]])

  let PRIMEPOW_INDICES_SING ← prove
   r"!p m. 2 <= p /\ p <= m /\ m < p * p
         ==> {j | 1 <= j /\ p EXP j <= m} = {1}"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM, IN_SING] THEN
    X_GEN_TAC (← q r"j:num") THEN EQ_TAC THENL
     [STRIP_TAC THEN SUBGOAL_THEN (← q r"p EXP j < p EXP 2") MP_TAC THENL
       [REWRITE_TAC [EXP_2] THEN ASM_ARITH_TAC,
        ASM_REWRITE_TAC [LT_EXP] THEN ASM_ARITH_TAC],
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC [EXP_1, LE_REFL]])

  let INDEX_BINOM_CENTRAL_ZERO ← prove
   r"!n p. prime p /\ 3 <= p /\ p <= n /\ 2 * n < 3 * p
         ==> index p (binom(2 * n,n)) = 0"
   (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"3 * p <= p * p") ASSUME_TAC THENL
     [ASM_REWRITE_TAC [LE_MULT_RCANCEL], ALL_TAC] THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"p:num"] INDEX_BINOM_CENTRAL) THEN
    ASM_SIMP_TAC [INDEX_FACT_ALT] THEN
    MP_TAC (← SPECL [← q r"p:num", ← q r"n:num"] PRIMEPOW_INDICES_SING) THEN
    MP_TAC (← SPECL [← q r"p:num", ← q r"2 * n"] PRIMEPOW_INDICES_SING) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC, DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC [NSUM_SING, EXP_1] THEN
    SUBGOAL_THEN (← q r"n DIV p = 1 /\ (2 * n) DIV p = 2")
     (fun th => REWRITE_TAC [th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC DIV_UNIQ THENL
       [EXISTS_TAC (← q r"n - p:num"), EXISTS_TAC (← q r"2 * n - 2 * p")] THEN
      ASM_ARITH_TAC,
      ARITH_TAC])

  -- @@RETURN BEGIN
  return { DIV_DOUBLE_LE, INDEX_BINOM_CENTRAL, INDEX_BINOM_CENTRAL_CARD,
           INDEX_BINOM_CENTRAL_LE, INDEX_BINOM_CENTRAL_SQRT, PRIMEPOW_INDICES_SING,
           INDEX_BINOM_CENTRAL_ZERO }
  -- @@RETURN END


/- ------------------------------------------------------------------------- -/
/- Bertrand's postulate.  (bertrand.ml 316-533)                              -/
/- ------------------------------------------------------------------------- -/

structure BertrandPostulate where
  -- @@FIELDS
  BINOM_CENTRAL_UPPER : thm
  EXP_4_BRACKET : thm
  BERTRAND_THRESHOLD : thm
  BERTRAND_LARGE : thm
  PRIME_TRIAL_DIVISION : thm
  BERTRAND : thm
  deriving Inhabited

@[nospecialize]
def setupBertrandPostulate [HolBase] (D : BertrandDeps) (BCentralBinomial : CentralBinomial) (BPrimorial : Primorial) (BIndexBinom : IndexBinom) :
    ExceptT String IO BertrandPostulate := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, EXPAND_CASES_CONV,
        INDUCT_TAC, MESON_TAC, NUMBER_RULE, NUM_REDUCE_CONV, TAUT, .. } := D
  let { ARITH_EQ, BINOM_EQ_0, CARD_NUMSEG_LT, CARD_SUBSET, CONTRAPOS_THM,
        DE_MORGAN_THM, DIVIDES_MOD, DIVISION, EQ_IMP_LE, EXISTS_OR_THM, EXP, EXP_1,
        EXP_ADD, EXP_EQ_1, EXP_EXP, EXP_MONO_LE_IMP, EXTENSION, FINITE_NUMSEG_LT,
        FINITE_RESTRICT, FORALL_IN_INSERT, IN_ELIM_THM, IN_INSERT, LE_CASES, LE_EXP,
        LE_MULT2, LE_MULT_LCANCEL, LE_MULT_RCANCEL, LE_RDIV_EQ, LE_REFL, LE_TRANS,
        LTE_TRANS, LT_POW2_REFL, MONO_EXISTS, MULT_CLAUSES, MULT_EQ_0, MULT_EXP,
        NOT_EXISTS_THM, NOT_IN_EMPTY, NOT_LE, NOT_LT, NPRODUCT_CONST, NPRODUCT_LE,
        NPRODUCT_MUL, NPRODUCT_RESTRICT_SET, NPRODUCT_SUPERSET,
        PRIME_FACTORIZATION_ALT, PRIME_GE_2, RIGHT_OR_DISTRIB, SUBSET, UNWIND_THM2,
        divides, num_WOP, prime, .. } := D.core1
  let { BINOM_CENTRAL_LOWER, .. } := BCentralBinomial
  let { FINITE_PRIMES_LE, PRIMORIAL_LE_4_EXP, .. } := BPrimorial
  let { INDEX_BINOM_CENTRAL_LE, INDEX_BINOM_CENTRAL_SQRT, INDEX_BINOM_CENTRAL_ZERO, .. } := BIndexBinom
  -- @@SCOPE END

  let BINOM_CENTRAL_UPPER ← prove
   r"!n s. 3 <= n /\ 2 * n < s * s /\ (!p. prime p /\ n < p ==> 2 * n < p)
         ==> binom(2 * n,n) <=
             (2 * n) EXP s *
             nproduct {p | prime p /\ p <= (2 * n) DIV 3} (\p. p)"
   (← do
    let a1 ← ARITH_RULE (← q r"x <= x * p <=> x * 1 <= x * p")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"~(binom(2 * n,n) = 0)") ASSUME_TAC THENL
     [REWRITE_TAC [BINOM_EQ_0] THEN ARITH_TAC, ALL_TAC] THEN
    FIRST_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC LAND_CONV [← SYM (← MATCH_MP PRIME_FACTORIZATION_ALT th)])) THEN
    ABBREV_TAC (← q r"b = binom(2 * n,n)") THEN
    SUBGOAL_THEN (← q r"FINITE {p | prime p /\ p <= 2 * n}") ASSUME_TAC THENL
     [MP_TAC (← SPECL [← q r"2 * n", ← q r"\p:num. T"] FINITE_PRIMES_LE) THEN REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"nproduct {p | prime p} (\p. p EXP index p b) =
    nproduct {p | prime p /\ p <= 2 * n} (\p. p EXP index p b)")
    SUBST1_TAC THENL
     [MATCH_MP_TAC NPRODUCT_SUPERSET THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN
      CONJ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
      X_GEN_TAC (← q r"p:num") THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"2 * n < p") ASSUME_TAC THENL
       [ASM_MESON_TAC [NOT_LE], ALL_TAC] THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
      REWRITE_TAC [EXP_EQ_1] THEN DISJ2_TAC THEN
      MP_TAC (← SPECL [← q r"n:num", ← q r"p:num"] INDEX_BINOM_CENTRAL_LE) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
      REWRITE_TAC [NOT_LE] THEN MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC (← q r"p EXP 1") THEN CONJ_TAC THENL
       [REWRITE_TAC [EXP_1] THEN ASM_ARITH_TAC,
        ASM_REWRITE_TAC [LE_EXP] THEN ASM_ARITH_TAC],
      ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC
     (← q r"nproduct {p | prime p /\ p <= 2 * n}
      (\p. (if p * p <= 2 * n then 2 * n else 1) *
           (if 3 * p <= 2 * n then p else 1))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NPRODUCT_LE THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"p:num") THEN STRIP_TAC THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
      ASM_CASES_TAC (← q r"p * p <= 2 * n") THEN ASM_REWRITE_TAC [MULT_CLAUSES] THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"2 * n") THEN CONJ_TAC THENL
         [EXPAND_TAC "b" THEN MATCH_MP_TAC INDEX_BINOM_CENTRAL_LE THEN
          ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
          REWRITE_TAC [a1] THEN
          REWRITE_TAC [LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
          COND_CASES_TAC THEN ASM_ARITH_TAC],
        ALL_TAC] THEN
      COND_CASES_TAC THENL
       [SUBGOAL_THEN (← q r"index p b <= 1") ASSUME_TAC THENL
         [EXPAND_TAC "b" THEN MATCH_MP_TAC INDEX_BINOM_CENTRAL_SQRT THEN
          ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
          GEN_REWRITE_TAC RAND_CONV [← GSYM EXP_1] THEN
          REWRITE_TAC [LE_EXP] THEN ASM_ARITH_TAC],
        ALL_TAC] THEN
      SUBGOAL_THEN (← q r"index p b = 0") (fun th => REWRITE_TAC [th, EXP, LE_REFL]) THEN
      EXPAND_TAC "b" THEN MATCH_MP_TAC INDEX_BINOM_CENTRAL_ZERO THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN (← q r"~(n < p)") MP_TAC THENL
       [DISCH_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC (← q r"p:num") o
          check (fun th => is_forall (concl th))) THEN
        ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
        ASM_ARITH_TAC],
      ALL_TAC] THEN
    ASM_SIMP_TAC [NPRODUCT_MUL] THEN MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL
     [REWRITE_TAC [← GSYM NPRODUCT_RESTRICT_SET] THEN
      ASM_SIMP_TAC [NPRODUCT_CONST, FINITE_RESTRICT] THEN
      REWRITE_TAC [LE_EXP] THEN
      COND_CASES_TAC THENL [ASM_ARITH_TAC, DISJ2_TAC] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"CARD {p:num | p < s}") THEN
      CONJ_TAC THENL [ALL_TAC, REWRITE_TAC [CARD_NUMSEG_LT, LE_REFL]] THEN
      MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC [FINITE_NUMSEG_LT] THEN
      REWRITE_TAC [SUBSET, IN_ELIM_THM] THEN X_GEN_TAC (← q r"p:num") THEN
      STRIP_TAC THEN REWRITE_TAC [← GSYM NOT_LE] THEN DISCH_TAC THEN
      MP_TAC (← SPECL [← q r"s:num", ← q r"p:num", ← q r"s:num", ← q r"p:num"] LE_MULT2) THEN
      ASM_ARITH_TAC,
      REWRITE_TAC [← GSYM NPRODUCT_RESTRICT_SET] THEN
      MATCH_MP_TAC EQ_IMP_LE THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
      X_GEN_TAC (← q r"p:num") THEN SIMP_TAC [LE_RDIV_EQ, ARITH_EQ] THEN
      ASM_CASES_TAC (← q r"prime p") THEN ASM_REWRITE_TAC [] THEN ARITH_TAC]))

  let EXP_4_BRACKET ← prove
   r"!m. 1 <= m ==> ?t. 4 EXP t <= m /\ m < 4 EXP (t + 1)"
   (← do
    let a1 ← ARITH_RULE (← q r"~(t = 0) ==> t - 1 < t /\ t - 1 + 1 = t")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"?t. m < 4 EXP (t + 1)") MP_TAC THENL
     [EXISTS_TAC (← q r"m:num") THEN MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC (← q r"2 EXP m") THEN REWRITE_TAC [LT_POW2_REFL] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"4 EXP m") THEN CONJ_TAC THENL
       [MATCH_MP_TAC EXP_MONO_LE_IMP THEN ARITH_TAC,
        REWRITE_TAC [LE_EXP] THEN ARITH_TAC],
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"t:num") THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q r"t = 0") THENL
     [ASM_REWRITE_TAC [EXP],
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"t - 1")) THEN
      ASM_SIMP_TAC [a1] THEN
      REWRITE_TAC [NOT_LT]]))

  let BERTRAND_THRESHOLD ← prove
   r"!t. 7 <= t ==> 6 * (t + 1) * (2 EXP (t + 1) + 1) + 1 < 4 EXP t"
   (← do
    let a3 ← ARITH_RULE (← q r"7 <= t ==> (t - 7) + 8 = t + 1 /\ t - 7 + 7 = t")
    let a2 ← ARITH_RULE (← q r"SUC d + 7 = SUC(d + 7)")
    let a1 ← ARITH_RULE (← q r"SUC d + 8 = SUC(d + 8)")
    pure (SUBGOAL_THEN
     (← q r"!d. 6 * (d + 8) * (2 EXP (d + 8) + 1) + 1 < 4 EXP (d + 7)")
    MP_TAC THENL
     [INDUCT_TAC THENL [CONV_TAC NUM_REDUCE_CONV, ALL_TAC] THEN
      REWRITE_TAC [a1, a2, EXP] THEN
      POP_ASSUM MP_TAC THEN
      SPEC_TAC (← q r"2 EXP (d + 8)", ← q r"a:num") THEN
      SPEC_TAC (← q r"4 EXP (d + 7)", ← q r"b:num") THEN ARITH_TAC,
      DISCH_TAC THEN X_GEN_TAC (← q r"t:num") THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"t - 7")) THEN
      ASM_SIMP_TAC [a3]]))

  let BERTRAND_LARGE ← prove
   r"!n. 8192 <= n ==> ?p. prime p /\ n < p /\ p <= 2 * n"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPEC (← q r"2 * n + 1") EXP_4_BRACKET) THEN
    ANTS_TAC THENL [ARITH_TAC, ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"t:num") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"7 <= t") ASSUME_TAC THENL
     [REWRITE_TAC [← GSYM NOT_LT] THEN DISCH_TAC THEN
      SUBGOAL_THEN (← q r"4 EXP (t + 1) <= 4 EXP 7") MP_TAC THENL
       [REWRITE_TAC [LE_EXP] THEN ASM_ARITH_TAC,
        CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC],
      ALL_TAC] THEN
    MP_TAC (← SPEC (← q r"t:num") BERTRAND_THRESHOLD) THEN ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [NOT_EXISTS_THM, NOT_LT] THEN DISCH_TAC THEN
    ABBREV_TAC (← q r"s = 2 EXP (t + 1)") THEN
    SUBGOAL_THEN (← q r"s * s = 4 EXP (t + 1)") ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN REWRITE_TAC [← GSYM MULT_EXP] THEN
      CONV_TAC NUM_REDUCE_CONV,
      ALL_TAC] THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"s:num"] BINOM_CENTRAL_UPPER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC, ASM_ARITH_TAC, ALL_TAC] THEN
      X_GEN_TAC (← q r"p:num") THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"p:num")) THEN ASM_REWRITE_TAC [NOT_LE],
      ALL_TAC] THEN
    MP_TAC (← SPEC (← q r"(2 * n) DIV 3") PRIMORIAL_LE_4_EXP) THEN
    MP_TAC (← SPEC (← q r"n:num") BINOM_CENTRAL_LOWER) THEN
    SPEC_TAC (← q r"binom(2 * n,n)", ← q r"b:num") THEN
    SPEC_TAC (← q r"nproduct {p | prime p /\ p <= (2 * n) DIV 3} (\p. p)", ← q r"q:num") THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN (← q r"(2 * n) EXP s <= 4 EXP ((t + 1) * s)") ASSUME_TAC THENL
     [REWRITE_TAC [← GSYM EXP_EXP] THEN MATCH_MP_TAC EXP_MONO_LE_IMP THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"4 EXP n <= 4 EXP (t + 1) * 4 EXP ((t + 1) * s) * 4 EXP ((2 * n) DIV 3)")
    MP_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC (← q r"(2 * n + 1) * b") THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"(2 * n) EXP s * q") THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [← GSYM EXP_ADD, LE_EXP, ARITH_EQ]] THEN
    MP_TAC (← SPECL [← q r"2 * n", ← q r"3"] DIVISION) THEN REWRITE_TAC [ARITH_EQ] THEN
    ASM_ARITH_TAC)

  let PRIME_TRIAL_DIVISION ← prove
   r"!p m. 2 <= p /\ p < m * m /\
         (!d. d < m ==> 2 <= d /\ d * d <= p ==> ~(d divides p))
         ==> prime p"
   (← do
    let n2 ← ExceptT.mk (NUMBER_RULE (← q r"y divides x * y"))
    let n1 ← ExceptT.mk (NUMBER_RULE (← q r"x divides x * y"))
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [prime] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    X_GEN_TAC (← q r"x:num") THEN REWRITE_TAC [divides] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"y:num") SUBST_ALL_TAC) THEN
    ASM_CASES_TAC (← q r"x = 1") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"y = 1") THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN
    SUBGOAL_THEN (← q r"~(x = 0) /\ ~(y = 0)") STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [← GSYM DE_MORGAN_THM, ← GSYM MULT_EQ_0] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"?d. 2 <= d /\ d * d <= x * y /\ d divides x * y")
    STRIP_ASSUME_TAC THENL
     [DISJ_CASES_TAC (← SPECL [← q r"x:num", ← q r"y:num"] LE_CASES) THENL
       [EXISTS_TAC (← q r"x:num") THEN ASM_REWRITE_TAC [LE_MULT_LCANCEL] THEN
        REWRITE_TAC [n1] THEN ASM_ARITH_TAC,
        EXISTS_TAC (← q r"y:num") THEN ASM_REWRITE_TAC [LE_MULT_RCANCEL] THEN
        REWRITE_TAC [n2] THEN ASM_ARITH_TAC],
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"d:num")) THEN ASM_REWRITE_TAC [NOT_LT] THEN
      DISCH_TAC THEN
      MP_TAC (← SPECL [← q r"m:num", ← q r"d:num", ← q r"m:num", ← q r"d:num"] LE_MULT2) THEN
      ASM_ARITH_TAC]))

  let BERTRAND ← prove
   r"!n. ~(n = 0) ==> ?p. prime p /\ n < p /\ p <= 2 * n"
   (← do
    -- the TAUT is evaluated once, when the REPEAT is built
    let t1 ← TAUT (← q r"(a ==> b) /\ (~a ==> r) ==> a /\ b \/ r")
    pure (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"8192 <= n") THEN
    ASM_SIMP_TAC [BERTRAND_LARGE] THEN
    SUBGOAL_THEN
     (← q r"?q. q IN {2,3,5,7,13,23,43,83,163,317,631,1259,2503,5003,9973} /\
        n < q /\ q <= 2 * n")
    MP_TAC THENL
     [REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
      REWRITE_TAC [RIGHT_OR_DISTRIB, EXISTS_OR_THM, UNWIND_THM2] THEN
      REPEAT (MATCH_MP_TAC t1 THEN
              CONJ_TAC THENL [ASM_ARITH_TAC, DISCH_TAC]) THEN
      ASM_ARITH_TAC,
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q r"q:num") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      UNDISCH_TAC
       (← q r"q IN {2,3,5,7,13,23,43,83,163,317,631,1259,2503,5003,9973}") THEN
      SPEC_TAC (← q r"q:num", ← q r"q:num") THEN
      REWRITE_TAC [FORALL_IN_INSERT, NOT_IN_EMPTY] THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC PRIME_TRIAL_DIVISION THEN
      EXISTS_TAC (← q r"100") THEN CONV_TAC (ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
      REWRITE_TAC [DIVIDES_MOD] THEN CONV_TAC NUM_REDUCE_CONV]))

  -- @@RETURN BEGIN
  return { BINOM_CENTRAL_UPPER, EXP_4_BRACKET, BERTRAND_THRESHOLD, BERTRAND_LARGE,
           PRIME_TRIAL_DIVISION, BERTRAND }
  -- @@RETURN END

end HolLibrary.Bertrand
