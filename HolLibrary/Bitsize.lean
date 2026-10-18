/- ========================================================================= -/
/- Definition of "bitsize", how many bits are needed for a natural number.   -/
/- ========================================================================= -/
/- File: HolLibrary/Bitsize.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/bitsize.ml`, by hand, in file order,
  in the style of HolLibrary/Products.lean and HolLibrary/BitMatch.lean (see
  there and HolMath/Base.lean for the conventions).  bitsize.ml has no
  `needs`: it runs on the core library.  The whole file is one bundle (a
  `structure`) built by a `setup` function; SessionLibrary/Bitsize.lean
  builds it and exports every name under its HOL Light name.

  The file ends with `BITSIZE_CONV`, a conversion that evaluates
  `bitsize n` for a numeral `n`.  It is built from `BITSIZE_UNIQUE_EQ`
  (proved once at setup time) and installed as a rule
  `term → ExceptT String IO thm`.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE) they are bound first, in OCaml's order.
-/

import HolMath

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.Bitsize

/-- `bitfun k n` (bitsize.ml 151-153): the number of bits of `n`, counting
    up from `k`.  OCaml's `bitfun` works on `num`; here `n` is a `Nat` (from
    `dest_numeral`). -/
def bitfun (k : Nat) (n : Nat) : Nat :=
  if n == 0 then k else bitfun (k + 1) (n / 2)
termination_by n
decreasing_by
  simp only [beq_iff_eq] at *
  exact Nat.div_lt_self (by omega) (by omega)

/- ------------------------------------------------------------------------- -/
/- What bitsize.ml uses from the core library (supplied by Session).         -/
/- ------------------------------------------------------------------------- -/

/-- Theorems bitsize.ml uses from the core library. -/
structure CoreThms1 where
  (ADD_EQ_0 ADD_SUB ADD_SYM ARITH ARITH_EQ DISJ_SYM EQ_IMP_LE EXP EXP_ADD
   EXP_EQ_0 IMP_CONJ_ALT LET_TRANS LE_0 LE_ANTISYM LE_EXP LE_MULT_LCANCEL
   LE_RDIV_EQ LE_REFL LE_TRANS LT LTE_TRANS LT_ANTISYM LT_CASES LT_EXP
   LT_MULT2 LT_MULT_LCANCEL LT_POW2_REFL LT_TRANS MINIMAL_LE MINIMAL_UNIQUE
   MULT_CLAUSES MULT_SYM NOT_LE NOT_LT RDIV_LT_EQ : thm)
  deriving Inhabited

/-- What bitsize.ml uses from Session besides theorems. -/
structure BitsizeDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  SIMP_TAC : List thm → tactic
  -- numeral syntax and conversions
  mk_small_numeral : Int → Except String term
  NUM_REDUCE_CONV : ioconv
  core1 : CoreThms1

/- ------------------------------------------------------------------------- -/
/- The whole file is one bundle.  (bitsize.ml 1-174)                         -/
/- ------------------------------------------------------------------------- -/

structure Bitsize where
  -- @@FIELDS
  bitsize : thm
  BITSIZE_0 : thm
  BITSIZE_POW2 : thm
  BITSIZE_1 : thm
  BITSIZE_2 : thm
  BITSIZE_LE : thm
  BITSIZE : thm
  BITSIZE_UNIQUE : thm
  BITSIZE_UNIQUE_ALT : thm
  BITSIZE_EQ_0 : thm
  BITSIZE_MONO : thm
  BITSIZE_MAX : thm
  BITSIZE_MIN : thm
  BITSIZE_MULT_LE : thm
  BITSIZE_REV_EQ : thm
  BITSIZE_REV : thm
  BITSIZE_REV_EQ_ALT : thm
  BITSIZE_REV_ALT : thm
  LE_BITSIZE : thm
  LE_BITSIZE_ALT : thm
  BITSIZE_UNIQUE_EQ : thm
  BITSIZE_MULT : thm
  BITSIZE_MULT_ADD : thm
  BITSIZE_DIV : thm
  BITSIZE_CONV : term → ExceptT String IO thm
  deriving Inhabited

@[nospecialize]
def setupBitsize [HolBase] (D : BitsizeDeps) :
    ExceptT String IO Bitsize := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, MESON, MESON_TAC, NUM_REDUCE_CONV,
        SIMP_TAC, mk_small_numeral, new_definition, .. } := D
  let { ADD_EQ_0, ADD_SUB, ADD_SYM, ARITH, ARITH_EQ, DISJ_SYM, EQ_IMP_LE, EXP, EXP_ADD,
        EXP_EQ_0, IMP_CONJ_ALT, LET_TRANS, LE_0, LE_ANTISYM, LE_EXP, LE_MULT_LCANCEL,
        LE_RDIV_EQ, LE_REFL, LE_TRANS, LT, LTE_TRANS, LT_ANTISYM, LT_CASES, LT_EXP,
        LT_MULT2, LT_MULT_LCANCEL, LT_POW2_REFL, LT_TRANS, MINIMAL_LE, MINIMAL_UNIQUE,
        MULT_CLAUSES, MULT_SYM, NOT_LE, NOT_LT, RDIV_LT_EQ, .. } := D.core1
  -- @@SCOPE END

  let bitsize ← new_definition r"bitsize n = minimal i. n < 2 EXP i"

  let BITSIZE_0 ← prove
   r"bitsize 0 = 0"
   (REWRITE_TAC [bitsize] THEN MATCH_MP_TAC MINIMAL_UNIQUE THEN ARITH_TAC)

  let BITSIZE_POW2 ← prove
   r"!k. bitsize (2 EXP k) = k + 1"
   (GEN_TAC THEN REWRITE_TAC [bitsize, LT_EXP] THEN
    MATCH_MP_TAC MINIMAL_UNIQUE THEN ARITH_TAC)

  let BITSIZE_1 ← prove
   r"bitsize 1 = 1"
   (MP_TAC (← SPEC (← q "0") BITSIZE_POW2) THEN CONV_TAC NUM_REDUCE_CONV)

  let BITSIZE_2 ← prove
   r"bitsize 2 = 2"
   (MP_TAC (← SPEC (← q "1") BITSIZE_POW2) THEN CONV_TAC NUM_REDUCE_CONV)

  let BITSIZE_LE ← prove
   r"!n k. bitsize n <= k <=> n < 2 EXP k"
   (← do
    let m ← MESON [LT_POW2_REFL] (← q r"?i. n < 2 EXP i")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [bitsize] THEN
     SIMP_TAC [MINIMAL_LE, m] THEN
     EQ_TAC THENL [ALL_TAC, MESON_TAC [LE_REFL]] THEN
     DISCH_THEN (X_CHOOSE_THEN (← q "i:num") (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
     MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] LTE_TRANS) THEN
     ASM_REWRITE_TAC [LE_EXP, ARITH_EQ]))

  let BITSIZE ← prove
   r"!n. n < 2 EXP bitsize n"
   (REWRITE_TAC [← GSYM BITSIZE_LE, LE_REFL])

  let BITSIZE_UNIQUE ← prove
   r"!n k. bitsize n = k <=> n < 2 EXP k /\ !j. j < k ==> 2 EXP j <= n"
   (REWRITE_TAC [← GSYM NOT_LT, ← GSYM BITSIZE_LE] THEN
    MESON_TAC [LT_ANTISYM, LT_CASES, LT_TRANS])

  let BITSIZE_UNIQUE_ALT ← prove
   r"!n k. bitsize n = k <=> !j. n < 2 EXP j <=> k <= j"
   (REWRITE_TAC [BITSIZE_UNIQUE] THEN
    MESON_TAC [NOT_LE, LE_EXP, (← ARITH_RULE (← q "~(2 = 0)")), LE_TRANS, LE_ANTISYM])

  let BITSIZE_EQ_0 ← prove
   r"!n. bitsize n = 0 <=> n = 0"
   (REWRITE_TAC [BITSIZE_UNIQUE, LT] THEN ARITH_TAC)

  let BITSIZE_MONO ← prove
   r"!m n. m <= n ==> bitsize m <= bitsize n"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [BITSIZE_LE] THEN
    TRANS_TAC LET_TRANS (← q "n:num") THEN ASM_REWRITE_TAC [BITSIZE])

  let BITSIZE_MAX ← prove
   r"!m n. bitsize(MAX m n) = MAX (bitsize m) (bitsize n)"
   (← do
    -- the rules right to left, as OCaml evaluates the proof
    let a2 ← ARITH_RULE (← q "n <= m ==> MAX m n = m")
    let a1 ← ARITH_RULE (← q "m <= n ==> MAX m n = n")
    let a0 ← ARITH_RULE (← q r"m:num <= n \/ n <= m")
    pure (REPEAT GEN_TAC THEN DISJ_CASES_TAC a0 THEN
     ASM_SIMP_TAC [a1, BITSIZE_MONO, a2]))

  let BITSIZE_MIN ← prove
   r"!m n. bitsize(MIN m n) = MIN (bitsize m) (bitsize n)"
   (← do
    let a2 ← ARITH_RULE (← q "n <= m ==> MIN m n = n")
    let a1 ← ARITH_RULE (← q "m <= n ==> MIN m n = m")
    let a0 ← ARITH_RULE (← q r"m:num <= n \/ n <= m")
    pure (REPEAT GEN_TAC THEN DISJ_CASES_TAC a0 THEN
     ASM_SIMP_TAC [a1, BITSIZE_MONO, a2]))

  let BITSIZE_MULT_LE ← prove
   r"!m n. bitsize(m * n) <= bitsize m + bitsize n"
   (REPEAT GEN_TAC THEN REWRITE_TAC [BITSIZE_LE, EXP_ADD] THEN
    MATCH_MP_TAC LT_MULT2 THEN REWRITE_TAC [BITSIZE])

  let BITSIZE_REV_EQ ← prove
   r"!n. 2 EXP (bitsize n - 1) <= n <=> ~(n = 0)"
   (← do
    let a0 ← ARITH_RULE (← q r"n - 1 < n <=> ~(n = 0)")
    pure (REWRITE_TAC [← GSYM NOT_LT, ← GSYM BITSIZE_LE] THEN
     REWRITE_TAC [a0, BITSIZE_EQ_0]))

  let BITSIZE_REV ← prove
   r"!n. ~(n = 0) ==> 2 EXP (bitsize n - 1) <= n"
   (REWRITE_TAC [BITSIZE_REV_EQ])

  let BITSIZE_REV_EQ_ALT ← prove
   r"!n. 2 EXP (bitsize n) <= 2 * n <=> ~(n = 0)"
   (← do
    let a1 ← ARITH_RULE (← q r"n = SUC(n - 1) <=> ~(n = 0)")
    pure (GEN_TAC THEN ASM_CASES_TAC (← q "n = 0") THEN
     ASM_REWRITE_TAC [BITSIZE_0, ARITH] THEN
     TRANS_TAC LE_TRANS (← q "2 * 2 EXP (bitsize n - 1)") THEN
     ASM_REWRITE_TAC [LE_MULT_LCANCEL, BITSIZE_REV_EQ] THEN
     REWRITE_TAC [← GSYM (← CONJUNCT2 EXP)] THEN
     MATCH_MP_TAC EQ_IMP_LE THEN AP_TERM_TAC THEN
     ASM_REWRITE_TAC [a1, BITSIZE_EQ_0]))

  let BITSIZE_REV_ALT ← prove
   r"!n. ~(n = 0) ==> 2 EXP bitsize n <= 2 * n"
   (REWRITE_TAC [BITSIZE_REV_EQ_ALT])

  let LE_BITSIZE ← prove
   r"!n k. k <= bitsize n <=> ~(k = 0) ==> 2 EXP (k - 1) <= n"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "k = 0") THEN
    ASM_REWRITE_TAC [LE_0, ARITH] THEN
    REWRITE_TAC [← GSYM NOT_LT, ← GSYM BITSIZE_LE] THEN ASM_ARITH_TAC)

  let LE_BITSIZE_ALT ← prove
   r"!n k. k <= bitsize n <=> ~(k = 0) ==> 2 EXP k <= 2 * n"
   (← do
    let a0 ← ARITH_RULE (← q "2 * a = b ==> (a <= n <=> b <= 2 * n)")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [LE_BITSIZE] THEN
     ASM_CASES_TAC (← q "k = 0") THEN ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC a0 THEN
     REWRITE_TAC [← GSYM (← CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC))

  let BITSIZE_UNIQUE_EQ ← prove
   r"!n k. bitsize n = k <=>
          n < 2 EXP k /\ (~(k = 0) ==> 2 EXP k <= 2 * n)"
   (← do
    let a0 ← ARITH_RULE (← q r"n = k <=> k <= n /\ ~(k + 1 <= n)")
    pure (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [a0] THEN
     REWRITE_TAC [LE_BITSIZE_ALT, EXP_ADD] THEN ARITH_TAC))

  let BITSIZE_MULT ← prove
   r"(!k n. bitsize (2 EXP k * n) = if n = 0 then 0 else k + bitsize n) /\
    (!k n. bitsize (n * 2 EXP k) = if n = 0 then 0 else bitsize n + k)"
   (← do
    let a0 ← ARITH_RULE (← q "2 * a * b = a * 2 * b")
    let t ← TAUT (← q r"(p ==> q) /\ p ==> p /\ q")
    pure (MATCH_MP_TAC t THEN CONJ_TAC THENL
     [REWRITE_TAC [MULT_SYM, ADD_SYM], REPEAT GEN_TAC] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES, BITSIZE_0] THEN
     REWRITE_TAC [← GSYM LE_ANTISYM, LE_BITSIZE_ALT, BITSIZE_LE] THEN
     ONCE_REWRITE_TAC [a0] THEN
     REWRITE_TAC [EXP_ADD, LT_MULT_LCANCEL, LE_MULT_LCANCEL] THEN
     ASM_REWRITE_TAC [BITSIZE, EXP_EQ_0, ARITH_EQ, BITSIZE_REV_EQ_ALT]))

  let BITSIZE_MULT_ADD ← prove
   r"(!k m n. ~(m = 0) /\ n < 2 EXP k
             ==> bitsize (2 EXP k * m + n) = k + bitsize m) /\
    (!k m n. ~(m = 0) /\ n < 2 EXP k
             ==> bitsize (m * 2 EXP k + n) = k + bitsize m) /\
    (!k m n. ~(m = 0) /\ n < 2 EXP k
             ==> bitsize (n + 2 EXP k * m) = k + bitsize m) /\
    (!k m n. ~(m = 0) /\ n < 2 EXP k
             ==> bitsize (n + m * 2 EXP k) = k + bitsize m)"
   (← do
    let a1 ← ARITH_RULE (← q "m + 1 <= r <=> m < r")
    let t ← TAUT (← q r"(p ==> q) /\ p ==> p /\ q")
    pure (MATCH_MP_TAC t THEN CONJ_TAC THENL
     [REWRITE_TAC [MULT_SYM, ADD_SYM, DISJ_SYM], REPEAT STRIP_TAC] THEN
     REWRITE_TAC [← GSYM LE_ANTISYM] THEN CONJ_TAC THENL
      [REWRITE_TAC [BITSIZE_LE] THEN TRANS_TAC LTE_TRANS (← q "2 EXP k * (m + 1)") THEN
       REWRITE_TAC [EXP_ADD, LE_MULT_LCANCEL, EXP_EQ_0, ARITH_EQ] THEN
       REWRITE_TAC [a1, BITSIZE] THEN
       ASM_ARITH_TAC,
       TRANS_TAC LE_TRANS (← q "bitsize(2 EXP k * m)") THEN CONJ_TAC THENL
        [ASM_REWRITE_TAC [BITSIZE_MULT, LE_REFL],
         MATCH_MP_TAC BITSIZE_MONO THEN ARITH_TAC]]))

  let BITSIZE_DIV ← prove
   r"!n k. bitsize(n DIV 2 EXP k) = bitsize n - k"
   (← do
    let a3 ← ARITH_RULE (← q r"~(n:num <= k) ==> (j < n - k <=> k + j < n)")
    let a2 ← ARITH_RULE (← q r"~(n:num <= k) ==> k + n - k = n")
    let a1 ← ARITH_RULE (← q "a < b <=> a + 1 <= b")
    let a0 ← ARITH_RULE (← q "n <= k ==> n - k = 0")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [BITSIZE_UNIQUE] THEN
     SIMP_TAC [RDIV_LT_EQ, LE_RDIV_EQ, EXP_EQ_0, ARITH_EQ] THEN
     ASM_CASES_TAC (← q "bitsize n <= k") THENL
      [ASM_SIMP_TAC [a0] THEN
       REWRITE_TAC [(← CONJUNCT1 LT), MULT_CLAUSES, EXP] THEN
       TRANS_TAC LTE_TRANS (← q "2 EXP bitsize n") THEN
       ASM_REWRITE_TAC [BITSIZE, LE_EXP] THEN ASM_ARITH_TAC,
       ASM_SIMP_TAC [← GSYM EXP_ADD, BITSIZE, a2] THEN
       ASM_SIMP_TAC [a3] THEN
       REWRITE_TAC [a1, LE_BITSIZE] THEN
       REWRITE_TAC [ADD_SUB, ADD_EQ_0, ARITH_EQ]]))

  -- bitsize.ml 150-174: BITSIZE_CONV.  `bitfun` is a local recursive helper
  -- counting the bits of a numeral; the SPECL [`n`;`k`] of BITSIZE_UNIQUE_EQ
  -- is reduced to the equation by NUM_REDUCE_CONV on the RHS and EQT_ELIM.
  -- The rule's constant work (BITSIZE_UNIQUE_EQ) is done once, above.
  let BITSIZE_CONV : term → ExceptT String IO thm ← do
    pure (fun tm => do
      match tm with
      | .Comb (.Const "bitsize" _) ntm =>
        if HolMath.Nums.is_numeral ntm then do
          let nval := ((← liftExcept (dest_numeral ntm)).floor.toNat)
          let ktm ← liftExcept (mk_small_numeral (bitfun 0 nval))
          let th ← SPECL [ntm, ktm] BITSIZE_UNIQUE_EQ
          EQT_ELIM (← CONV_RULE (RAND_CONV NUM_REDUCE_CONV) th)
        else throw "BITSIZE_CONV"
      | _ => throw "BITSIZE_CONV")

  -- @@RETURN BEGIN
  return { bitsize, BITSIZE_0, BITSIZE_POW2, BITSIZE_1, BITSIZE_2, BITSIZE_LE, BITSIZE,
           BITSIZE_UNIQUE, BITSIZE_UNIQUE_ALT, BITSIZE_EQ_0, BITSIZE_MONO, BITSIZE_MAX,
           BITSIZE_MIN, BITSIZE_MULT_LE, BITSIZE_REV_EQ, BITSIZE_REV, BITSIZE_REV_EQ_ALT,
           BITSIZE_REV_ALT, LE_BITSIZE, LE_BITSIZE_ALT, BITSIZE_UNIQUE_EQ, BITSIZE_MULT,
           BITSIZE_MULT_ADD, BITSIZE_DIV, BITSIZE_CONV }
  -- @@RETURN END

end HolLibrary.Bitsize
