/- ========================================================================= -/
/- Binomial coefficients and the binomial theorem.                           -/
/- ========================================================================= -/
/- File: HolLibrary/Binomial.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/binomial.ml`, by hand, in file order,
  in the style of HolLibrary/Products.lean and HolLibrary/BitMatch.lean (see
  there and HolMath/Base.lean for the conventions).  binomial.ml has no
  `needs`: it runs on the core library.  The whole file is a single bundle (a
  `structure`) built by a `setup` function; SessionLibrary/Binomial.lean
  builds the bundle and exports every name under its HOL Light name.

  binomial.ml defines `binom` with `define` and ends with the numeral
  conversion `NUM_BINOM_CONV`, whose local `pth_0`/`pth_1`/`pth_step`/
  `pth_swap` lemmas are proved once; its recursive worker `BINOM_RULE` is a
  LOCAL function (not an exported name), moved to the top-level `partial def
  binomRule` with a context structure (as BitMatch moves its closures).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof uses two or more printing/counter-using
  rules they are bound first, in OCaml's order.
-/

import HolMath
import HolLibrary.Products

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

set_option maxRecDepth 8000

namespace HolLibrary.Binomial

/- ------------------------------------------------------------------------- -/
/- What binomial.ml uses from the core library (supplied by Session).        -/
/- ------------------------------------------------------------------------- -/

/-- Theorems binomial.ml uses from the core library (part 1 of 3). -/
structure CoreThms1 where
  (ADD1 ADD_0 ADD_AC ADD_ASSOC ADD_CLAUSES ADD ADD_SUB ADD_SUB2 ADD_SUC ADD_SYM
   ARITH ARITH_SUC CARD_CLAUSES CONTRAPOS_THM DISJOINT DIVIDES_LE DIV_UNIQ
   EQ_ADD_RCANCEL EQ_MULT_LCANCEL EXP EXTENSION FACT FACT_LT FACT_NZ
   FINITE_HAS_SIZE FINITE_INSERT FINITE_NUMSEG FORALL_IN_GSPEC HAS_SIZE
   HAS_SIZE_0 HAS_SIZE_CLAUSES HAS_SIZE_IMAGE_INJ HAS_SIZE_SUC HAS_SIZE_UNION
   IN_ELIM_PAIR_THM IN_ELIM_THM IN_IMAGE IN_INTER IN_NUMSEG IN_SING : thm)
  deriving Inhabited

/-- Theorems binomial.ml uses from the core library (part 2 of 3). -/
structure CoreThms2 where
  (LEFT_IMP_EXISTS_THM LE_0 LE_EXISTS LE_REFL LE_SUC LT LT_0 LT_MULT LT_NZ
   LT_REFL LT_SUC MULT_AC MULT_CLAUSES MULT_SYM NOT_IN_EMPTY NOT_LE NOT_LT
   NOT_SUC NSUM_ADD_NUMSEG NSUM_CLAUSES_LEFT NSUM_CLAUSES_NUMSEG NSUM_LMUL
   NSUM_OFFSET NSUM_SING_NUMSEG ONE PAIR_EQ POWERSET_CLAUSES
   PRIME_COPRIME_EQ_NONDIVISIBLE REAL_ADD_RDISTRIB REAL_ADD_RID
   REAL_EQ_RDIV_EQ REAL_LT_MUL REAL_MUL_AC REAL_MUL_LID REAL_MUL_LZERO
   REAL_MUL_RZERO REAL_OF_NUM_ADD REAL_OF_NUM_EQ REAL_OF_NUM_LE
   REAL_OF_NUM_LT REAL_OF_NUM_MUL REAL_OF_NUM_SUB : thm)
  deriving Inhabited

/-- Theorems binomial.ml uses from the core library (part 3 of 3). -/
structure CoreThms3 where
  (RIGHT_ADD_DISTRIB SUBSET_EMPTY SUB_0 SUB_EQ_0 SUB_REFL SUB_SUC SUC_INJ
   SUC_SUB1 SUM_ADD_NUMSEG SUM_CLAUSES_LEFT SUM_CLAUSES_NUMSEG
   SUM_EQ_GENERAL_INVERSES SUM_LMUL SUM_OFFSET SUM_RMUL SUM_SING_NUMSEG
   SUM_SUM_PRODUCT real_pow : thm)
  deriving Inhabited

/-- What binomial.ml uses from Session besides theorems. -/
structure BinomialDeps where
  -- definitions and parser state
  define : String → ExceptT String IO thm
  mk_numeral : Rat → Except String term
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  ASM_MESON_TAC : List thm → tactic
  INDUCT_TAC : tactic
  MESON_TAC : List thm → tactic
  NUMBER_RULE : term → ExceptT String IO thm
  REAL_ARITH : term → ExceptT String IO thm
  REAL_FIELD : term → ExceptT String IO thm
  REAL_RING : term → ExceptT String IO thm
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  -- conversions and rules
  HAS_SIZE_CONV : ioconv
  num_CONV : ioconv
  NUM_REDUCE_CONV : ioconv
  NUM_RING : ioconv
  NUM_LE_CONV : ioconv
  NUM_LT_CONV : ioconv
  NUM_SUB_CONV : ioconv
  NUM_SUC_CONV : ioconv
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3

/- ------------------------------------------------------------------------- -/
/- NUM_BINOM_CONV's recursive worker `BINOM_RULE` (binomial.ml 358-375),     -/
/- a local function moved to top level with a context structure.             -/
/- ------------------------------------------------------------------------- -/

/-- The theorems and constants `NUM_BINOM_CONV`'s `BINOM_RULE` closes over
    (binomial.ml 345-357). -/
structure BinomCtx where
  (pth_step pth_0 pth_1 pth_swap : thm)
  (k_tm n_tm x_tm y_tm : term)
  (NUM_LT_CONV NUM_LE_CONV NUM_SUB_CONV NUM_SUC_CONV NUM_REDUCE_CONV : ioconv)
  mk_numeral : Rat → Except String term

/-- `BINOM_RULE (n, k)` (binomial.ml 358-375): `|- binom(n,k) = p`. -/
partial def binomRule [HolBase] (C : BinomCtx) (n k : Rat) : ExceptT String IO thm := do
  if n < k then do
    let th ← INST [(← liftExcept (C.mk_numeral n), C.n_tm),
                   (← liftExcept (C.mk_numeral k), C.k_tm)] C.pth_0
    MP_CONV C.NUM_LT_CONV th
  else if n == k then
    INST [(← liftExcept (C.mk_numeral n), C.n_tm)] C.pth_1
  else if (2 : Rat) * k < n then do
    let th1 ← INST [(← liftExcept (C.mk_numeral n), C.n_tm),
                    (← liftExcept (C.mk_numeral k), C.k_tm)] C.pth_swap
    let th2 ← MP th1 (← EQT_ELIM (← ExceptT.mk (C.NUM_LE_CONV (← liftExcept (lhand (concl th1))))))
    let th3 ← CONV_RULE (funpow 3 RAND_CONV C.NUM_SUB_CONV) th2
    TRANS th3 (← binomRule C n (n - k))
  else do
    let th1 ← binomRule C (n - 1) k
    let y ← liftExcept (dest_numeral (← liftExcept (rand (concl th1))))
    let x := (n / (n - k)) * y
    let th2 ← INST [(← liftExcept (C.mk_numeral (n - 1)), C.n_tm),
                    (← liftExcept (C.mk_numeral k), C.k_tm),
                    (← liftExcept (C.mk_numeral x), C.x_tm),
                    (← liftExcept (C.mk_numeral y), C.y_tm)] C.pth_step
    let th3 ← MP_CONV C.NUM_REDUCE_CONV (← MP_CONV C.NUM_LE_CONV (← MP th2 th1))
    CONV_RULE (LAND_CONV (RAND_CONV (LAND_CONV C.NUM_SUC_CONV))) th3

/- ------------------------------------------------------------------------- -/
/- The whole of binomial.ml as one bundle.                                   -/
/- ------------------------------------------------------------------------- -/

structure Binomial where
  -- @@FIELDS
  binom : thm
  BINOM_0 : thm
  BINOM_LT : thm
  BINOM_REFL : thm
  BINOM_1 : thm
  BINOM_FACT : thm
  BINOM_EQ_0 : thm
  BINOM_PENULT : thm
  BINOM_GE_TOP : thm
  BINOM_TOP_STEP : thm
  BINOM_BOTTOM_STEP : thm
  HAS_SIZE_RESTRICTED_POWERSET : thm
  CARD_RESTRICTED_POWERSET : thm
  BINOMIAL_THEOREM : thm
  REAL_BINOMIAL_THEOREM : thm
  BINOM_TOP_STEP_REAL : thm
  BINOM_BOTTOM_STEP_REAL : thm
  REAL_OF_NUM_BINOM : thm
  BINOM_BOTH_STEP_REAL : thm
  BINOM_BOTH_STEP : thm
  BINOM_BOTH_STEP_DOWN : thm
  BINOM : thm
  DIVIDES_GCD_BINOM : thm
  DIVIDES_COPRIME_BINOM : thm
  DIVIDES_PRIME_BINOM : thm
  BINOM_SYM : thm
  BINOM_MUL_SHIFT : thm
  APPELL_SEQUENCE : thm
  NUM_BINOM_CONV : term → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupBinomial [HolBase] (D : BinomialDeps) :
    ExceptT String IO Binomial := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, HAS_SIZE_CONV, INDUCT_TAC,
        MESON_TAC, NUMBER_RULE, NUM_LE_CONV, NUM_LT_CONV, NUM_REDUCE_CONV, NUM_RING,
        NUM_SUB_CONV, NUM_SUC_CONV, REAL_ARITH, REAL_FIELD, REAL_RING, SET_RULE,
        SET_TAC, define, mk_numeral, num_CONV, .. } := D
  let { ADD, ADD1, ADD_0, ADD_AC, ADD_ASSOC, ADD_CLAUSES, ADD_SUB, ADD_SUB2, ADD_SUC,
        ADD_SYM, ARITH, ARITH_SUC, CARD_CLAUSES, CONTRAPOS_THM, DISJOINT, DIVIDES_LE,
        DIV_UNIQ, EQ_ADD_RCANCEL, EQ_MULT_LCANCEL, EXP, EXTENSION, FACT, FACT_LT,
        FACT_NZ, FINITE_HAS_SIZE, FINITE_INSERT, FINITE_NUMSEG, FORALL_IN_GSPEC,
        HAS_SIZE, HAS_SIZE_0, HAS_SIZE_CLAUSES, HAS_SIZE_IMAGE_INJ, HAS_SIZE_SUC,
        HAS_SIZE_UNION, IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_IMAGE, IN_INTER, IN_NUMSEG,
        IN_SING, .. } := D.core1
  let { LEFT_IMP_EXISTS_THM, LE_0, LE_EXISTS, LE_REFL, LE_SUC, LT, LT_0, LT_MULT,
        LT_NZ, LT_REFL, LT_SUC, MULT_AC, MULT_CLAUSES, MULT_SYM, NOT_IN_EMPTY, NOT_LE,
        NOT_LT, NOT_SUC, NSUM_ADD_NUMSEG, NSUM_CLAUSES_LEFT, NSUM_CLAUSES_NUMSEG,
        NSUM_LMUL, NSUM_OFFSET, NSUM_SING_NUMSEG, ONE, PAIR_EQ, POWERSET_CLAUSES,
        PRIME_COPRIME_EQ_NONDIVISIBLE, REAL_ADD_RDISTRIB, REAL_ADD_RID,
        REAL_EQ_RDIV_EQ, REAL_LT_MUL, REAL_MUL_AC, REAL_MUL_LID, REAL_MUL_LZERO,
        REAL_MUL_RZERO, REAL_OF_NUM_ADD, REAL_OF_NUM_EQ, REAL_OF_NUM_LE,
        REAL_OF_NUM_LT, REAL_OF_NUM_MUL, REAL_OF_NUM_SUB, .. } := D.core2
  let { RIGHT_ADD_DISTRIB, SUBSET_EMPTY, SUB_0, SUB_EQ_0, SUB_REFL, SUB_SUC, SUC_INJ,
        SUC_SUB1, SUM_ADD_NUMSEG, SUM_CLAUSES_LEFT, SUM_CLAUSES_NUMSEG,
        SUM_EQ_GENERAL_INVERSES, SUM_LMUL, SUM_OFFSET, SUM_RMUL, SUM_SING_NUMSEG,
        SUM_SUM_PRODUCT, real_pow, .. } := D.core3
  -- @@SCOPE END

  let binom ← define
   r"(!n. binom(n,0) = 1) /\
     (!k. binom(0,SUC(k)) = 0) /\
     (!n k. binom(SUC(n),SUC(k)) = binom(n,SUC(k)) + binom(n,k))"

  let BINOM_0 ← prove
   r"!n. binom(0,n) = if n = 0 then 1 else 0"
   (INDUCT_TAC THEN REWRITE_TAC [binom, NOT_SUC])

  let BINOM_LT ← prove
   r"!n k. n < k ==> binom(n,k) = 0"
   (← do
    let a ← ARITH_RULE (← q r"n < k ==> n < SUC(k)")
    pure (INDUCT_TAC THEN INDUCT_TAC THEN REWRITE_TAC [binom, ARITH, LT_SUC, LT] THEN
      ASM_SIMP_TAC [a, ARITH]))

  let BINOM_REFL ← prove
   r"!n. binom(n,n) = 1"
   (INDUCT_TAC THEN ASM_SIMP_TAC [binom, BINOM_LT, LT, ARITH])

  let BINOM_1 ← prove
   r"!n. binom(n,1) = n"
   (← do
    let n ← num_CONV (← q "1")
    pure (REWRITE_TAC [n] THEN
      INDUCT_TAC THEN ASM_REWRITE_TAC [binom] THEN ARITH_TAC))

  let BINOM_FACT ← prove
   r"!n k. FACT n * FACT k * binom(n+k,k) = FACT(n + k)"
   (INDUCT_TAC THEN REWRITE_TAC [FACT, ADD_CLAUSES, MULT_CLAUSES, BINOM_REFL] THEN
    INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, FACT, MULT_CLAUSES, binom] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q "SUC k")) THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC [ADD_CLAUSES, FACT, binom] THEN CONV_TAC NUM_RING)

  let BINOM_EQ_0 ← prove
   r"!n k. binom(n,k) = 0 <=> n < k"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC, MESON_TAC [BINOM_LT]] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [NOT_LT, LE_EXISTS] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST1_TAC) THEN
    DISCH_TAC THEN MP_TAC (← SYM (← SPECL [← q "d:num", ← q "k:num"] BINOM_FACT)) THEN
    ASM_REWRITE_TAC [← GSYM LT_NZ, MULT_CLAUSES, FACT_LT])

  let BINOM_PENULT ← prove
   r"!n. binom(SUC n,n) = SUC n"
   (INDUCT_TAC THEN ASM_REWRITE_TAC [binom, ONE, BINOM_REFL] THEN
    SUBGOAL_THEN (← q "binom(n,SUC n) = 0") SUBST1_TAC THENL
     [REWRITE_TAC [BINOM_EQ_0, LT], REWRITE_TAC [ADD, ADD_0, ADD_SUC, SUC_INJ]])

  let BINOM_GE_TOP ← prove
   r"!m n. 1 <= m /\ m < n ==> n <= binom(n,m)"
   (← do
    let a ← ARITH_RULE (← q r"~(c = 0) ==> n <= b ==> n + 1 <= c + b")
    pure (INDUCT_TAC THEN INDUCT_TAC THEN REWRITE_TAC [binom] THEN
      CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN ASM_CASES_TAC (← q "m = 0") THEN
      ASM_SIMP_TAC [BINOM_1, ARITH_SUC, binom] THEN REWRITE_TAC [ADD1, LE_REFL] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q "n:num")) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      MATCH_MP_TAC a THEN
      REWRITE_TAC [BINOM_EQ_0] THEN ASM_ARITH_TAC))

  let BINOM_TOP_STEP ← prove
   r"!n k. ((n + 1) - k) * binom(n + 1,k) = (n + 1) * binom(n,k)"
   (← do
    let a ← ARITH_RULE (← q r"n < k ==> n + 1 = k \/ n + 1 < k")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "n < k:num") THENL
     [FIRST_ASSUM (DISJ_CASES_TAC o MATCH_MP a) THEN
      ASM_SIMP_TAC [BINOM_LT, SUB_REFL, MULT_CLAUSES],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [NOT_LT, LE_EXISTS]) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST1_TAC) THEN
    REWRITE_TAC [← GSYM ADD_ASSOC, ADD_SUB, ADD_SUB2] THEN
    MP_TAC (← SPECL [← q "d + 1", ← q "k:num"] BINOM_FACT) THEN
    MP_TAC (← SPECL [← q "d:num", ← q "k:num"] BINOM_FACT) THEN
    REWRITE_TAC [← GSYM ADD1, ADD_CLAUSES, FACT, ADD_AC] THEN
    MAP_EVERY (fun t => tactic_of do pure (MP_TAC (← SPEC t FACT_LT))) [← q "d:num", ← q "k:num"] THEN
    REWRITE_TAC [LT_NZ] THEN CONV_TAC NUM_RING))

  let BINOM_BOTTOM_STEP ← prove
   r"!n k. (k + 1) * binom(n,k + 1) = (n - k) * binom(n,k)"
   (← do
    let a ← ARITH_RULE (← q r"n < k + 1 ==> n = k \/ n < k")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "n < k + 1") THENL
     [FIRST_ASSUM (DISJ_CASES_TAC o MATCH_MP a) THEN
      ASM_SIMP_TAC [BINOM_LT, SUB_REFL, MULT_CLAUSES],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [NOT_LT, LE_EXISTS]) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:num") SUBST1_TAC) THEN
    REWRITE_TAC [← GSYM ADD_ASSOC, ADD_SUB, ADD_SUB2] THEN
    MP_TAC (← SPECL [← q "d + 1", ← q "k:num"] BINOM_FACT) THEN
    MP_TAC (← SPECL [← q "d:num", ← q "k + 1"] BINOM_FACT) THEN
    REWRITE_TAC [← GSYM ADD1, ADD_CLAUSES, FACT, ADD_AC] THEN
    MAP_EVERY (fun t => tactic_of do pure (MP_TAC (← SPEC t FACT_LT))) [← q "d:num", ← q "k:num"] THEN
    REWRITE_TAC [LT_NZ] THEN CONV_TAC NUM_RING))

  let HAS_SIZE_RESTRICTED_POWERSET ← prove
   r"!n m s:A->bool.
        s HAS_SIZE n ==> {t | t SUBSET s /\ t HAS_SIZE m} HAS_SIZE binom(n,m)"
   (← do
    -- `let binom_induct = prove(...) and setstep_lemma = prove(...) in ...`,
    -- a `let ... and ...`, evaluated left to right.
    let binom_induct ← prove
     r"!P. (!n. P n 0) /\
          (!k. P 0 (SUC k)) /\
          (!n k. P n (SUC k) /\ P n k ==> P (SUC n) (SUC k))
          ==> !m n. P m n"
     (GEN_TAC THEN STRIP_TAC THEN REPEAT INDUCT_TAC THEN ASM_MESON_TAC [])
    let setstep_lemma ← do
      let s1 ← SET_RULE (← q r"{y | y IN t UNION IMAGE f s /\ P y} =
        {y | y IN t /\ P y} UNION IMAGE f {x | x IN s /\ P(f x)}")
      prove
       r"~(a IN t)
         ==> {u | u SUBSET (a:A INSERT t) /\ u HAS_SIZE (SUC m)} =
             {u | u SUBSET t /\ u HAS_SIZE (SUC m)} UNION
             IMAGE (\u. a INSERT u) {u | u SUBSET t /\ u HAS_SIZE m}"
       (REWRITE_TAC [← REWRITE_RULE [EXTENSION, IN_ELIM_THM] POWERSET_CLAUSES] THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC [IN_ELIM_THM, s1] THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [HAS_SIZE, FINITE_INSERT] THEN
        ONCE_REWRITE_TAC [← TAUT (← q r"p /\ q /\ r <=> ~(p /\ q ==> ~r)")] THEN
        SIMP_TAC [CARD_CLAUSES] THEN MP_TAC SUC_INJ THEN ASM SET_TAC [])
    pure (MATCH_MP_TAC binom_induct THEN REWRITE_TAC [binom] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN CONV_TAC HAS_SIZE_CONV THEN
      EXISTS_TAC (← q r"{}:A->bool") THEN SIMP_TAC [EXTENSION, IN_SING, IN_ELIM_THM] THEN
      REWRITE_TAC [NOT_IN_EMPTY, HAS_SIZE_0] THEN SET_TAC [],
      SIMP_TAC [HAS_SIZE_0, SUBSET_EMPTY, HAS_SIZE_SUC] THEN SET_TAC [],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q "n:num", ← q "m:num"] THEN STRIP_TAC THEN
    GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [HAS_SIZE_CLAUSES] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q "a:A", ← q r"t:A->bool"] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC [setstep_lemma] THEN MATCH_MP_TAC HAS_SIZE_UNION THEN
    ASM_SIMP_TAC [] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_SIMP_TAC [] THEN
      UNDISCH_TAC (← q r"~(a:A IN t)") THEN SET_TAC [],
      ALL_TAC] THEN
    REWRITE_TAC [DISJOINT, EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
    REWRITE_TAC [IN_IMAGE, IN_ELIM_THM, HAS_SIZE_SUC] THEN
    UNDISCH_TAC (← q r"~(a:A IN t)") THEN SET_TAC []))

  let CARD_RESTRICTED_POWERSET ← prove
   r"!s k. FINITE s ==> CARD {t | t SUBSET s /\ t HAS_SIZE k} = binom(CARD s,k)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [FINITE_HAS_SIZE] THEN DISCH_THEN
     (MP_TAC o SPEC (← q "k:num") o MATCH_MP HAS_SIZE_RESTRICTED_POWERSET) THEN
    SIMP_TAC [HAS_SIZE])

  let BINOMIAL_THEOREM ← prove
   r"!n x y.
      (x + y) EXP n = nsum(0..n) (\k. binom(n,k) * x EXP k * y EXP (n - k))"
   (← do
    let a2 ← ARITH_RULE (← q r"k <= n ==> SUC n - k = SUC(n - k)")
    let r1 ← REWRITE_CONV [NSUM_OFFSET] (← q r"nsum(m+1..n+1) (\i. f i)")
    let a1 ← ARITH_RULE (← q r"a:num = e /\ b = c + d ==> a + b = c + d + e")
    let a0 ← ARITH_RULE (← q "0 <= n + 1")
    pure (INDUCT_TAC THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC [EXP] THEN
      REWRITE_TAC [NSUM_SING_NUMSEG, binom, SUB_REFL, EXP, MULT_CLAUSES] THEN
      SIMP_TAC [NSUM_CLAUSES_LEFT, ADD1, a0, NSUM_OFFSET] THEN
      ASM_REWRITE_TAC [EXP, binom, ← GSYM ADD1, ← GSYM NSUM_LMUL] THEN
      REWRITE_TAC [RIGHT_ADD_DISTRIB, NSUM_ADD_NUMSEG, MULT_CLAUSES, SUB_0] THEN
      MATCH_MP_TAC a1 THEN
      CONJ_TAC THENL [REWRITE_TAC [MULT_AC, SUB_SUC], REWRITE_TAC [← GSYM EXP]] THEN
      SIMP_TAC [ADD1, ← SYM r1] THEN
      REWRITE_TAC [NSUM_CLAUSES_NUMSEG, ← GSYM ADD1, LE_SUC, LE_0] THEN
      SIMP_TAC [NSUM_CLAUSES_LEFT, LE_0] THEN
      SIMP_TAC [BINOM_LT, LT, MULT_CLAUSES, ADD_CLAUSES, SUB_0, EXP, binom] THEN
      SIMP_TAC [ARITH, a2, EXP] THEN
      REWRITE_TAC [MULT_AC]))

  let REAL_BINOMIAL_THEOREM ← prove
   r"!n x y.
     (x + y) pow n = sum(0..n) (\k. &(binom(n,k)) * x pow k * y pow (n - k))"
   (← do
    let ra ← REAL_ARITH (← q r"a:real = e /\ b = c + d ==> a + b = c + d + e")
    let a2 ← ARITH_RULE (← q r"k <= n ==> SUC n - k = SUC(n - k)")
    let r1 ← REWRITE_CONV [SUM_OFFSET] (← q r"sum(m+1..n+1) (\i. f i)")
    let a0 ← ARITH_RULE (← q "0 <= n + 1")
    pure (INDUCT_TAC THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC [real_pow] THEN
      REWRITE_TAC [SUM_SING_NUMSEG, binom, SUB_REFL, real_pow, REAL_MUL_LID] THEN
      SIMP_TAC [SUM_CLAUSES_LEFT, ADD1, a0, SUM_OFFSET] THEN
      ASM_REWRITE_TAC [real_pow, binom, ← GSYM ADD1, ← GSYM SUM_LMUL] THEN
      REWRITE_TAC [← GSYM REAL_OF_NUM_ADD] THEN
      REWRITE_TAC [REAL_ADD_RDISTRIB, SUM_ADD_NUMSEG, REAL_MUL_LID, SUB_0] THEN
      MATCH_MP_TAC ra THEN
      CONJ_TAC THENL [SIMP_TAC [REAL_MUL_AC, SUB_SUC], SIMP_TAC [← GSYM real_pow]] THEN
      SIMP_TAC [ADD1, ← SYM r1] THEN
      REWRITE_TAC [SUM_CLAUSES_NUMSEG, ← GSYM ADD1, LE_SUC, LE_0] THEN
      SIMP_TAC [SUM_CLAUSES_LEFT, LE_0, BINOM_LT, LT, REAL_MUL_LID, SUB_0, real_pow,
                binom, REAL_MUL_LZERO, REAL_ADD_RID] THEN
      SIMP_TAC [ARITH, a2, real_pow] THEN
      REWRITE_TAC [REAL_MUL_AC]))

  let BINOM_TOP_STEP_REAL ← prove
   r"!n k. &(binom(n + 1,k)):real =
           if k = n + 1 then &1
           else (&n + &1) / (&n + &1 - &k) * &(binom(n,k))"
   (← do
    let a ← ARITH_RULE (← q r"~(k = n + 1) ==> n < k /\ n + 1 < k \/ k <= n /\ k <= n + 1")
    pure (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [BINOM_REFL] THEN
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o MATCH_MP a) THEN
      ASM_SIMP_TAC [BINOM_LT, REAL_MUL_RZERO] THEN
      MP_TAC (← SPECL [← q "n:num", ← q "k:num"] BINOM_TOP_STEP) THEN
      ASM_SIMP_TAC [← GSYM REAL_OF_NUM_EQ, ← GSYM REAL_OF_NUM_MUL, ← GSYM REAL_OF_NUM_ADD,
                    ← GSYM REAL_OF_NUM_SUB] THEN
      UNDISCH_TAC (← q "k <= n:num") THEN REWRITE_TAC [← GSYM REAL_OF_NUM_LE] THEN
      CONV_TAC REAL_FIELD))

  let BINOM_BOTTOM_STEP_REAL ← prove
   r"!n k. &(binom(n,k+1)):real = (&n - &k) / (&k + &1) * &(binom(n,k))"
   (← do
    let a ← ARITH_RULE (← q r"n < k ==> n < k + 1")
    pure (REPEAT GEN_TAC THEN DISJ_CASES_TAC (← ARITH_RULE (← q r"n:num < k \/ k <= n")) THENL
     [ASM_SIMP_TAC [BINOM_LT, a, REAL_MUL_RZERO],
      MP_TAC (← SPECL [← q "n:num", ← q "k:num"] BINOM_BOTTOM_STEP) THEN
      ASM_SIMP_TAC [← GSYM REAL_OF_NUM_EQ, ← GSYM REAL_OF_NUM_MUL,
                    ← GSYM REAL_OF_NUM_ADD, ← GSYM REAL_OF_NUM_SUB] THEN
      CONV_TAC REAL_FIELD]))

  let REAL_OF_NUM_BINOM ← prove
   r"!n k. &(binom(n,k)):real =
             if k <= n then &(FACT n) / (&(FACT(n - k)) * &(FACT k))
             else &0"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [BINOM_LT, ← GSYM NOT_LE] THEN
    SIMP_TAC [REAL_EQ_RDIV_EQ, REAL_LT_MUL, REAL_OF_NUM_LT, FACT_LT] THEN
    FIRST_ASSUM (CHOOSE_THEN SUBST1_TAC o REWRITE_RULE [LE_EXISTS]) THEN
    REWRITE_TAC [ADD_SUB2] THEN ONCE_REWRITE_TAC [ADD_SYM] THEN
    REWRITE_TAC [← GSYM BINOM_FACT] THEN REWRITE_TAC [REAL_OF_NUM_MUL, MULT_AC])

  let BINOM_BOTH_STEP_REAL ← prove
   r"!p k. &(binom(p + 1,k + 1)):real = (&p + &1) / (&k + &1) * &(binom(p,k))"
   (REWRITE_TAC [BINOM_TOP_STEP_REAL, BINOM_BOTTOM_STEP_REAL] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [EQ_ADD_RCANCEL] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [BINOM_REFL] THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC [← GSYM REAL_OF_NUM_ADD, ← GSYM REAL_OF_NUM_EQ] THEN
    CONV_TAC REAL_FIELD)

  let BINOM_BOTH_STEP ← prove
   r"!p k. (k + 1) * binom(p + 1,k + 1) = (p + 1) * binom(p,k)"
   (REWRITE_TAC [← GSYM REAL_OF_NUM_EQ, ← GSYM REAL_OF_NUM_MUL] THEN
    REWRITE_TAC [BINOM_BOTH_STEP_REAL, ← GSYM REAL_OF_NUM_ADD] THEN
    CONV_TAC REAL_FIELD)

  let BINOM_BOTH_STEP_DOWN ← prove
   r"!p k. (k = 0 ==> p = 0) ==> k * binom(p,k) = p * binom(p - 1,k - 1)"
   (REPEAT INDUCT_TAC THEN
    SIMP_TAC [BINOM_LT, LT_0, LT_REFL, ARITH] THEN
    REWRITE_TAC [SUC_SUB1, ADD1, BINOM_BOTH_STEP] THEN
    REWRITE_TAC [MULT_CLAUSES])

  let BINOM ← prove
   r"!n k. binom(n,k) =
            if k <= n then FACT(n) DIV (FACT(n - k) * FACT(k))
            else 0"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [BINOM_EQ_0, ← GSYM NOT_LE] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC (← q "0") THEN
    SIMP_TAC [LT_MULT, FACT_LT, ADD_CLAUSES] THEN
    FIRST_X_ASSUM (CHOOSE_THEN SUBST1_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    REWRITE_TAC [← GSYM BINOM_FACT, ADD_SUB] THEN REWRITE_TAC [MULT_AC])

  let DIVIDES_GCD_BINOM ← prove
   r"!n k. n divides gcd(n,k) * binom(n,k)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "k = 0") THENL
     [ASM_REWRITE_TAC [] THEN CONV_TAC NUMBER_RULE, ALL_TAC] THEN
    W (MP_TAC o PART_MATCH (rand o lhand o rand) BINOM_BOTH_STEP_DOWN o
      rand o rand o snd) THEN
    ASM_REWRITE_TAC [] THEN POP_ASSUM MP_TAC THEN CONV_TAC NUMBER_RULE)

  let DIVIDES_COPRIME_BINOM ← prove
   r"!n k. coprime(n,k) ==> n divides binom (n,k)"
   (← do
    let nr ← NUMBER_RULE (← q "coprime(n,k) <=> gcd(n,k) = 1")
    pure (MESON_TAC [DIVIDES_GCD_BINOM, MULT_CLAUSES, nr]))

  let DIVIDES_PRIME_BINOM ← prove
   r"!n p. prime p /\ 0 < n /\ n < p ==> p divides binom(p,n)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC DIVIDES_COPRIME_BINOM THEN
    ASM_CASES_TAC (← q "(p:num) divides n") THENL
     [FIRST_ASSUM (MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC,
      ASM_MESON_TAC [PRIME_COPRIME_EQ_NONDIVISIBLE]])

  let BINOM_SYM ← prove
   r"!n k. binom(n,n-k) = if k <= n then binom(n,k) else 1"
   (← do
    let a2 ← ARITH_RULE (← q r"k:num <= n ==> n - (n - k) = k")
    let a1 ← ARITH_RULE (← q r"~(k <= n) ==> n - k = 0")
    pure (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC [binom, a1] THEN
      REWRITE_TAC [← GSYM REAL_OF_NUM_EQ, REAL_OF_NUM_BINOM] THEN
      ASM_REWRITE_TAC [← ARITH_RULE (← q r"n - k:num <= n")] THEN
      ASM_SIMP_TAC [a2] THEN
      REWRITE_TAC [REAL_OF_NUM_MUL, MULT_SYM]))

  let BINOM_MUL_SHIFT ← prove
   r"!m n k. k <= m
           ==> binom(n,m) * binom(m,k) = binom(n,k) * binom(n - k,m - k)"
   (← do
    let a ← ARITH_RULE
     (← q r"k:num <= m /\ m <= n ==> n - k - (m - k) = n - m")
    pure (REPEAT STRIP_TAC THEN
      SIMP_TAC [← GSYM REAL_OF_NUM_EQ, ← GSYM REAL_OF_NUM_MUL, REAL_OF_NUM_BINOM] THEN
      ASM_CASES_TAC (← q "n:num < m") THENL
       [REPEAT (COND_CASES_TAC THEN
          ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO]) THEN
        MATCH_MP_TAC (← TAUT (← q r"F ==> p")) THEN ASM_ARITH_TAC,
        REPEAT (COND_CASES_TAC THENL
         [ALL_TAC, MATCH_MP_TAC (← TAUT (← q r"F ==> p")) THEN ASM_ARITH_TAC]) THEN
        RULE_ASSUM_TAC (REWRITE_RULE [NOT_LT]) THEN
        ASM_SIMP_TAC [a] THEN
        MAP_EVERY (MP_TAC o C SPEC FACT_NZ)
         [← q "n:num", ← q "m:num", ← q "n - m:num", ← q "n - k:num", ← q "m - k:num"] THEN
        REWRITE_TAC [← GSYM REAL_OF_NUM_EQ] THEN CONV_TAC REAL_FIELD]))

  let APPELL_SEQUENCE ← prove
   r"!c n x y. sum (0..n)
               (\k.  &(binom(n,k)) *
                     sum(0..k)
                        (\l. &(binom(k,l)) * c l * x pow (k - l)) *
                     y pow (n - k)) =
           sum (0..n) (\k. &(binom(n,k)) * c k * (x + y) pow (n - k))"
   (← do
    let rr ← REAL_RING
     (← q r"c * d:real = a * b ==> a * z * b * x * y = c * (d * z * x) * y")
    let a ← ARITH_RULE
     (← q r"j:num <= k /\ k <= n ==> (n - j) - (k - j) = n - k")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [REAL_BINOMIAL_THEOREM] THEN
      REWRITE_TAC [← GSYM SUM_LMUL, ← GSYM SUM_RMUL] THEN
      SIMP_TAC [SUM_SUM_PRODUCT, FINITE_NUMSEG] THEN
      MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
      EXISTS_TAC (← q r"(\(x,y). y,x - y):num#num->num#num") THEN
      EXISTS_TAC (← q r"(\(x,y). x + y,x):num#num->num#num") THEN
      REWRITE_TAC [FORALL_IN_GSPEC, IN_ELIM_PAIR_THM] THEN
      REWRITE_TAC [PAIR_EQ, IN_NUMSEG] THEN
      CONJ_TAC THENL [ARITH_TAC, REPEAT GEN_TAC THEN STRIP_TAC] THEN
      REPEAT (CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC]) THEN
      ASM_SIMP_TAC [a] THEN
      MATCH_MP_TAC rr THEN
      ASM_SIMP_TAC [REAL_OF_NUM_MUL, REAL_OF_NUM_EQ, BINOM_MUL_SHIFT]))

  -- Numerical computation of binom.  (binomial.ml 341-375)
  -- `let NUM_BINOM_CONV = let pth_step = ... and pth_0 = ... and pth_1 = ...
  --  and pth_swap = ... and k_tm = ... and ... and binom_tm = ... in
  --  let rec BINOM_RULE(n,k) = ... in fun tm -> ...`.  The lemmas and
  -- constants are built once; BINOM_RULE is `binomRule` (top level).
  let NUM_BINOM_CONV : term → ExceptT String IO thm ← do
    let pth_step ← prove
     r"binom(n,k) = y
       ==> k <= n
           ==> (SUC n) * y = ((n + 1) - k) * x ==> binom(SUC n,k) = x"
     (DISCH_THEN (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [ADD1, ← GSYM BINOM_TOP_STEP, EQ_MULT_LCANCEL, SUB_EQ_0] THEN
      ARITH_TAC)
    let pth_0 ← prove
     r"n < k ==> binom(n,k) = 0"
     (REWRITE_TAC [BINOM_LT])
    let pth_1 ← prove
     r"binom(n,n) = 1"
     (REWRITE_TAC [BINOM_REFL])
    let pth_swap ← prove
     r"k <= n ==> binom(n,k) = binom(n,n - k)"
     (MESON_TAC [BINOM_SYM])
    let k_tm ← q "k:num"
    let n_tm ← q "n:num"
    let x_tm ← q "x:num"
    let y_tm ← q "y:num"
    let binom_tm ← q "binom"
    let C : BinomCtx := ⟨pth_step, pth_0, pth_1, pth_swap, k_tm, n_tm, x_tm, y_tm,
      NUM_LT_CONV, NUM_LE_CONV, NUM_SUB_CONV, NUM_SUC_CONV, NUM_REDUCE_CONV, mk_numeral⟩
    pure (fun tm => do
      let (bop, nkp) ← liftExcept (dest_comb tm)
      if bop != binom_tm then throw "NUM_BINOM_CONV" else do
        let (nt, kt) ← liftExcept (HolMath.Pair.dest_pair nkp)
        binomRule C (← liftExcept (dest_numeral nt)) (← liftExcept (dest_numeral kt)))

  -- @@RETURN BEGIN
  return { binom, BINOM_0, BINOM_LT, BINOM_REFL, BINOM_1, BINOM_FACT, BINOM_EQ_0,
           BINOM_PENULT, BINOM_GE_TOP, BINOM_TOP_STEP, BINOM_BOTTOM_STEP,
           HAS_SIZE_RESTRICTED_POWERSET, CARD_RESTRICTED_POWERSET, BINOMIAL_THEOREM,
           REAL_BINOMIAL_THEOREM, BINOM_TOP_STEP_REAL, BINOM_BOTTOM_STEP_REAL,
           REAL_OF_NUM_BINOM, BINOM_BOTH_STEP_REAL, BINOM_BOTH_STEP,
           BINOM_BOTH_STEP_DOWN, BINOM, DIVIDES_GCD_BINOM, DIVIDES_COPRIME_BINOM,
           DIVIDES_PRIME_BINOM, BINOM_SYM, BINOM_MUL_SHIFT, APPELL_SEQUENCE,
           NUM_BINOM_CONV }
  -- @@RETURN END

end HolLibrary.Binomial
