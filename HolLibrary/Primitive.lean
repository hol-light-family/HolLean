/- ========================================================================= -/
/- Existence of primitive roots modulo certain numbers.                      -/
/- ========================================================================= -/
/- File: HolLibrary/Primitive.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/primitive.ml`, by hand, in file
  order, in the style of HolLibrary/Pocklington.lean and HolLibrary/Card.lean
  (see there and HolMath/Base.lean for the conventions).  primitive.ml begins
  with `needs` for integer.ml, isum.ml, binomial.ml, pocklington.ml and
  multiplicative.ml; the theorems it uses from those files and the core
  library are supplied via the CoreThms structures (SessionLibrary.Primitive
  fills them), and isum.ml's INT_OF_REAL_THM and pocklington.ml's
  conversions via PrimitiveDeps.  Each section is a bundle (a `structure`)
  built by a `setup` function; SessionLibrary/Primitive.lean builds the
  bundles in order and exports every name under its HOL Light name.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, NUMBER_RULE, INTEGER_RULE, INT_ARITH,
  SET_RULE, TAUT) they are bound first, in OCaml's order.
-/

import HolLibrary.Integer
import HolLibrary.Isum
import HolLibrary.Binomial
import HolLibrary.Pocklington
import HolLibrary.Multiplicative

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.Primitive

-- @@COREFILL BEGIN
/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD1 ADD_CLAUSES ADD_EQ_0 ADD_SUB ARITH ARITH_EQ BINOMIAL_THEOREM BINOM_1
   BINOM_PENULT BINOM_REFL CARD_CLAUSES CARD_EQ_NSUM CARD_IMAGE_INJ
   CARD_NUMSEG_LT CARD_PSUBSET_IMP CARD_SUBSET_IMAGE CARD_SUBSET_LE
   CHINESE_REMAINDER_COUNT CHINESE_REMAINDER_UNIQUE CHINESE_REMAINDER_USUAL
   COND_ID CONG CONG_CHINESE_EQ CONG_COPRIME CONG_EXP CONG_IMP_EQ
   CONG_MINUS1_SQUARED CONG_MOD CONG_MOD_0 CONG_MOD_1 CONG_REFL CONG_SYM
   CONG_TO_1 CONG_TRANS CONJ_ACI CONJ_ASSOC CONJ_SYM CONTRAPOS_THM COPRIME_0
   COPRIME_1 COPRIME_2 COPRIME_EXP_DIVPROD COPRIME_GCD COPRIME_LEXP
   COPRIME_LMUL COPRIME_PRIME COPRIME_PRIME_EQ COPRIME_REFL COPRIME_REXP
   COPRIME_RMOD COPRIME_RMUL COPRIME_SYM COUNT_CONG_SOLVE DE_MORGAN_THM
   DIVIDES_0 DIVIDES_1 DIVIDES_2 DIVIDES_ADD DIVIDES_DIVIDES_DIV
   DIVIDES_DIV_SELF DIVIDES_EXP_LE DIVIDES_EXP_LE_IMP DIVIDES_GCD_LEFT
   DIVIDES_LE DIVIDES_LMUL DIVIDES_MOD DIVIDES_MUL2 DIVIDES_ONE
   DIVIDES_PRIMEPOW DIVIDES_PRIME_BINOM : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (DIVIDES_PRIME_PRIME DIVIDES_REFL DIVIDES_REXP DIVIDES_RMUL
   DIVIDES_RMUL2_EQ DIVIDES_ZERO DIVISION DIV_0 DIV_1 DIV_BY_DIV DIV_EQ_0
   DIV_MULT DIV_REFL EMPTY_GSPEC EQ_ADD_LCANCEL_0 EQ_ADD_RCANCEL_0 EQ_IMP
   EQ_IMP_LE EQ_MULT_LCANCEL EQ_TRANS ETA_AX EVEN_ADD EVEN_EXISTS EVEN_EXP
   EVEN_MULT EVEN_OR_ODD EVEN_PHI EVEN_PHI_EQ EVEN_SUB EXISTS_INT_CASES
   EXISTS_LT_MOD_THM EXISTS_REFL EXP EXP_1 EXP_ADD EXP_EQ_0 EXP_EQ_1 EXP_EXP
   EXP_MONO_LE EXP_MULT EXP_ONE EXTENSION FERMAT_LITTLE FINITE_DIVISORS
   FINITE_EMPTY FINITE_INDUCT_STRONG FINITE_INT_SEG FINITE_NUMSEG
   FINITE_NUMSEG_LT FINITE_RESTRICT FINITE_SPECIAL_DIVISORS FINITE_SUBSET
   FORALL_AND_THM FORALL_IN_IMAGE FORALL_LT_MOD_THM FORALL_PAIR_THM
   FORALL_UNWIND_THM2 FUN_EQ_THM GCD GCD_0 GCD_1 GCD_2_CASES GCD_LE GCD_ONE
   GCD_ZERO HAS_SIZE HAS_SIZE_0 HAS_SIZE_IMAGE_INJ_RESTRICT
   HAS_SIZE_NUMSEG_LT IMP_CONJ : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms3 where
  (IMP_CONJ_ALT IMP_IMP INDEX_EQ_0 INDEX_EXP INDEX_MUL INDEX_REFL
   INDUCT_COPRIME_ALT INDUCT_COPRIME_STRONG INJECTIVE_EXP_MODULO
   INT_2_DIVIDES_ADD INT_2_DIVIDES_MUL INT_2_DIVIDES_POW INT_ABS_NUM
   INT_ADD_RID INT_CONG INT_CONG_0_DIVIDES INT_CONG_MOD_0 INT_CONG_NUM_EXISTS
   INT_CONG_POW INT_CONG_SOLVE INT_CONG_SOLVE_POS INT_CONG_SYM INT_CONG_TRANS
   INT_COPRIME_LMUL INT_COPRIME_LPOW INT_DIVIDES_0 INT_DIVIDES_ADD
   INT_DIVIDES_LABS INT_DIVIDES_LE INT_DIVIDES_LMUL INT_DIVIDES_POW_LE_IMP
   INT_DIVIDES_REFL INT_EXISTS_POS INT_FORALL_ABS INT_LT_SUB_RADD
   INT_MUL_LZERO INT_MUL_RID INT_OF_NUM_ADD INT_OF_NUM_EQ INT_OF_NUM_GT
   INT_OF_NUM_LE INT_OF_NUM_LT INT_OF_NUM_MUL INT_OF_NUM_POW INT_OF_NUM_SUB
   INT_POW INT_POW_1 INT_POW_ADD INT_POW_MUL INT_POW_NEG INT_POW_POW
   INT_PRIME_DIVPROD_EQ INT_SUB_REFL IN_ELIM_PAIR_THM IN_ELIM_THM IN_IMAGE
   IN_NUMSEG ISUM_0 ISUM_CASES ISUM_CLAUSES_NUMSEG ISUM_CLAUSES_RIGHT
   ISUM_SING ISUM_SING_NUMSEG ITERATE_CLAUSES ITERATE_EQ ITERATE_SING
   ITERATE_UNION LCM_1 LCM_SYM LE : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms4 where
  (LEFT_FORALL_IMP_THM LEFT_IMP_EXISTS_THM LEFT_OR_DISTRIB LE_0 LE_1
   LE_ANTISYM LE_EXP LE_MULT2 LE_MULT_LCANCEL LE_MULT_RCANCEL LE_REFL
   LE_TRANS LT LT_IMP_NE LT_LE LT_REFL MEMBER_NOT_EMPTY MOD_EXP_MOD MOD_LT_EQ
   MONOIDAL_MUL MONO_EXISTS MULT_AC MULT_ASSOC MULT_CLAUSES MULT_EQ_0
   MULT_EQ_1 MULT_EXP MULT_SYM NEUTRAL_MUL NOT_EVEN NOT_EXISTS_THM
   NOT_FORALL_THM NOT_IMP NOT_IN_EMPTY NOT_LE NOT_LT NOT_ODD NOT_SUC
   NSUM_CLAUSES_LEFT NSUM_CLAUSES_RIGHT NSUM_CLOSED NSUM_CONST_NUMSEG NSUM_EQ
   NSUM_GROUP NSUM_LE NSUM_LMUL NSUM_LT NUM_OF_INT_OF_NUM ODD ODD_ADD
   ODD_EXISTS ODD_EXP ODD_MOD_2 ODD_MOD_EVEN ODD_MULT ODD_PRIME ORDER ORDER_1
   ORDER_CONG ORDER_DIVIDES ORDER_DIVIDES_EXPDIFF ORDER_DIVIDES_PHI
   ORDER_EQ_0 ORDER_EQ_1 ORDER_EXP ORDER_EXP_GEN ORDER_MOD ORDER_MUL_LCM
   ORDER_UNIQUE ORDER_UNIQUE_PRIME : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms5 where
  (ORDER_WORKS PHI_0 PHI_1 PHI_2 PHI_ALT PHI_DIVISORSUM PHI_EQ_0
   PHI_FINITE_LEMMA PHI_LOWERBOUND_1_STRONG PHI_LOWERBOUND_2
   PHI_MULTIPLICATIVE PHI_PRIME PHI_PRIMEPOW PHI_PRIMEPOW_ALT PRIMEPOW_FACTOR
   PRIME_0 PRIME_1 PRIME_2 PRIME_COPRIME_EQ PRIME_COPRIME_LT PRIME_DIVEXP
   PRIME_DIVEXP_EQ PRIME_DIVPROD_EQ PRIME_GE_2 PRIME_IMP_NZ PRIME_ODD
   REAL_ADD_LID REAL_MUL_AC REAL_MUL_RZERO REAL_SUB_LDISTRIB REAL_SUB_POW
   REAL_SUB_REFL RIGHT_FORALL_IMP_THM RIGHT_IMP_FORALL_THM RIGHT_SUB_DISTRIB
   SING_GSPEC SUBSET SUB_ADD SUB_REFL SUC_SUB1 SUM_CLAUSES_LEFT
   SUM_EQ_GENERAL_INVERSES SUM_LMUL SUM_RMUL SUM_SUB_NUMSEG SUM_SUM_PRODUCT
   SURJECTIVE_IFF_INJECTIVE SURJECTIVE_IFF_INJECTIVE_GEN SWAP_FORALL_THM
   UNWIND_THM2 WLOG_LT binom coprime divides int_congruent int_prime nproduct
   num_INDUCTION num_WF num_congruent num_coprime num_divides prime real_pow : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms6 where
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms7 where
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms8 where
  deriving Inhabited

-- @@COREFILL END

/-- What primitive.ml uses from Session besides theorems. -/
structure PrimitiveDeps where
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  INT_ARITH : term → ExceptT String IO thm
  ASM_INT_ARITH_TAC : tactic
  INTEGER_RULE : term → ExceptT String IO thm
  NUMBER_RULE : term → ExceptT String IO thm
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  REAL_ARITH : term → ExceptT String IO thm
  INDUCT_TAC : tactic
  -- isum.ml's rule `INT_OF_REAL_THM` (a `needs`, exported by Session Isum).
  INT_OF_REAL_THM : thm → ExceptT String IO thm
  NUM_REDUCE_CONV : ioconv        -- calc_num.ml's NUM_REDUCE_CONV
  CONG_CONV : ioconv              -- pocklington.ml's CONG_CONV
  MOD_DOWN_CONV : ioconv          -- arith.ml's MOD_DOWN_CONV
  NUM_RING : term → ExceptT String IO thm  -- HOL Light's NUM_RING
  PRIME_CONV : term → ExceptT String IO thm  -- Pocklington's PRIME_CONV
  EXPAND_CASES_CONV : ioconv          -- HOL Light's EXPAND_CASES_CONV
  COPRIME_CONV : ioconv               -- pocklington.ml's COPRIME_CONV
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  core4 : CoreThms4
  core5 : CoreThms5
  core6 : CoreThms6
  core7 : CoreThms7
  core8 : CoreThms8

/- primitive.ml's header: `Existence of primitive roots modulo certain
   numbers.`  Its needs (integer.ml, isum.ml, binomial.ml, pocklington.ml,
   multiplicative.ml) are wired by the Session; isum.ml's `INT_OF_REAL_THM`
   is supplied through PrimitiveDeps. -/

/- ------------------------------------------------------------------------- -/
/- Lemma connecting concepts in the various background theories.             -/
/- ------------------------------------------------------------------------- -/

structure Lemma where
  -- @@FIELDS
  INT_PRIME : thm
  deriving Inhabited

@[nospecialize]
def setupLemma [HolBase] (D : PrimitiveDeps) :
    ExceptT String IO Lemma := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, .. } := D
  let { ARITH, DIVIDES_0, .. } := D.core1
  let { INT_ABS_NUM, INT_DIVIDES_LABS, INT_FORALL_ABS, INT_OF_NUM_EQ, INT_OF_NUM_GT, .. } := D.core3
  let { int_prime, num_divides, prime, .. } := D.core5
  -- @@SCOPE END

  let INT_PRIME ← prove
   r"!p. int_prime(&p) <=> prime p"
   (GEN_TAC THEN REWRITE_TAC [prime, int_prime] THEN
    ONCE_REWRITE_TAC [← GSYM INT_DIVIDES_LABS] THEN
    REWRITE_TAC [← GSYM INT_FORALL_ABS, ← GSYM num_divides, INT_ABS_NUM] THEN
    REWRITE_TAC [INT_OF_NUM_GT, INT_OF_NUM_EQ] THEN ASM_CASES_TAC (← q "p = 0") THENL
     [ASM_REWRITE_TAC [ARITH, DIVIDES_0] THEN DISCH_THEN (MP_TAC o SPEC (← q "2")),
      AP_THM_TAC THEN AP_TERM_TAC] THEN
    ASM_ARITH_TAC)

  -- @@RETURN BEGIN
  return { INT_PRIME }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Explicit formula for difference of real/integer polynomials.              -/
/- ------------------------------------------------------------------------- -/

structure PolyDiff where
  -- @@FIELDS
  REAL_POLY_DIFF_EXPLICIT : thm
  INT_POLY_DIFF_EXPLICIT : thm
  deriving Inhabited

@[nospecialize]
def setupPolyDiff [HolBase] (D : PrimitiveDeps) :
    ExceptT String IO PolyDiff := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, INT_OF_REAL_THM, REAL_ARITH, .. } := D
  let { ADD_CLAUSES, .. } := D.core1
  let { FINITE_NUMSEG, FORALL_PAIR_THM, .. } := D.core2
  let { IN_ELIM_PAIR_THM, IN_NUMSEG, .. } := D.core3
  let { LE_0, .. } := D.core4
  let { REAL_ADD_LID, REAL_MUL_AC, REAL_MUL_RZERO, REAL_SUB_LDISTRIB, REAL_SUB_POW,
        REAL_SUB_REFL, SUM_CLAUSES_LEFT, SUM_EQ_GENERAL_INVERSES, SUM_LMUL, SUM_RMUL,
        SUM_SUB_NUMSEG, SUM_SUM_PRODUCT, real_pow, .. } := D.core5
  -- @@SCOPE END

  let REAL_POLY_DIFF_EXPLICIT ← prove
   r"!n a x y.
        sum(0..n) (\i. a(i) * x pow i) - sum(0..n) (\i. a(i) * y pow i) =
        (x - y) *
        sum(0..n-1) (\i. sum(i+1..n) (\j. a j * y pow (j - 1 - i)) * x pow i)"
   (REPEAT GEN_TAC THEN
    REWRITE_TAC [← GSYM SUM_SUB_NUMSEG, ← GSYM REAL_SUB_LDISTRIB] THEN
    MP_TAC (← ISPEC (← q "n:num") LE_0) THEN SIMP_TAC [SUM_CLAUSES_LEFT, ADD_CLAUSES] THEN
    DISCH_THEN (K ALL_TAC) THEN
    REWRITE_TAC [REAL_SUB_REFL, REAL_MUL_RZERO, REAL_ADD_LID, real_pow] THEN
    SIMP_TAC [REAL_SUB_POW] THEN
    ONCE_REWRITE_TAC [← REAL_ARITH (← q r"a * b * c:real = b * a * c")] THEN
    REWRITE_TAC [SUM_LMUL] THEN AP_TERM_TAC THEN
    SIMP_TAC [← GSYM SUM_LMUL, ← GSYM SUM_RMUL, SUM_SUM_PRODUCT, FINITE_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
    REPEAT (EXISTS_TAC (← q r"\(a:num,b:num). (b,a)")) THEN
    REWRITE_TAC [IN_ELIM_PAIR_THM, FORALL_PAIR_THM, REAL_MUL_AC] THEN
    REWRITE_TAC [IN_NUMSEG] THEN ARITH_TAC)

  let INT_POLY_DIFF_EXPLICIT ← INT_OF_REAL_THM REAL_POLY_DIFF_EXPLICIT

  -- @@RETURN BEGIN
  return { REAL_POLY_DIFF_EXPLICIT, INT_POLY_DIFF_EXPLICIT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Lagrange's theorem on number of roots modulo a prime.                     -/
/- ------------------------------------------------------------------------- -/

structure Lagrange where
  -- @@FIELDS
  FINITE_INTSEG_RESTRICT : thm
  INT_POLY_LAGRANGE : thm
  deriving Inhabited

@[nospecialize]
def setupLagrange [HolBase] (D : PrimitiveDeps) (BPolyDiff : PolyDiff) :
    ExceptT String IO Lagrange := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_INT_ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE, MESON, SET_RULE, .. } := D
  let { CARD_CLAUSES, .. } := D.core1
  let { EXISTS_REFL, FINITE_INT_SEG, FINITE_RESTRICT, .. } := D.core2
  let { IMP_IMP, INT_CONG, INT_CONG_0_DIVIDES, INT_CONG_SYM, INT_CONG_TRANS,
        INT_DIVIDES_0, INT_DIVIDES_LE, INT_MUL_RID, INT_POW, INT_PRIME_DIVPROD_EQ,
        INT_SUB_REFL, IN_ELIM_THM, ISUM_CLAUSES_NUMSEG, ISUM_CLAUSES_RIGHT,
        ISUM_SING_NUMSEG, LE, .. } := D.core3
  let { LEFT_FORALL_IMP_THM, LEFT_IMP_EXISTS_THM, LEFT_OR_DISTRIB, LE_0, LE_1, LE_REFL,
        MEMBER_NOT_EMPTY, .. } := D.core4
  let { RIGHT_IMP_FORALL_THM, SUB_ADD, SUB_REFL, num_WF, .. } := D.core5
  let { INT_POLY_DIFF_EXPLICIT, .. } := BPolyDiff
  -- @@SCOPE END

  let FINITE_INTSEG_RESTRICT ← prove
   r"!P a b. FINITE {x:int | a <= x /\ x <= b /\ P x}"
   (SIMP_TAC [FINITE_RESTRICT, FINITE_INT_SEG, ← SET_RULE
     (← q r"{x | P x /\ Q x /\ R x} = {x | x IN {x | P x /\ Q x} /\ R x}")])

  let INT_POLY_LAGRANGE ← prove
   r"!p l r.
    int_prime p /\ r - l < p
    ==> !n a. ~(!i. i <= n ==> (a i == &0) (mod p))
              ==> CARD {x | l <= x /\ x <= r /\
                            (isum(0..n) (\i. a(i) * x pow i) == &0) (mod p)}
                  <= n"
   (← do
    let a11 ← ARITH_RULE (← q r"n - 1 < n <=> ~(n = 0)")
    let a10 ← ARITH_RULE
     (← q r"~(n = 0) /\ x <= n - 1 ==> (if p then x else SUC x) <= n")
    let s10 ← SET_RULE (← q r"{a} UNION s = a INSERT s")
    let s8 ← SET_RULE (← q r"P c /\ (!x y. P x /\ P y ==> x = y)
                           ==> {x | P x} = {c}")
    let s7 ← SET_RULE (← q r"{x | q x \/ r x} = {x | q x} UNION {x | r x}")
    let i6 ← INTEGER_RULE
     (← q r"a - b:int = c ==> p divides b ==> (p divides a <=> p divides c)")
    let a5 ← ARITH_RULE (← q r"i <= n <=> i <= n - 1 \/ i = n")
    let a4 ← ARITH_RULE (← q r"n - 1 < n <=> ~(n = 0)")
    let a3 ← ARITH_RULE (← q r"x <= n - 1 ==> x <= n")
    let i2 ← INTEGER_RULE
     (← q r"(p:int) divides y ==> (p divides (x + y * z) <=> p divides x)")
    let m1 ← MESON []
     (← q r"!a. (~(s = a) ==> CARD s <= n) /\ CARD a <= n ==> CARD s <= n")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [INT_CONG_0_DIVIDES] THEN
    MATCH_MP_TAC num_WF THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC m1 THEN
    EXISTS_TAC (← q r"{}:int->bool") THEN REWRITE_TAC [LE_0, CARD_CLAUSES] THEN
    REWRITE_TAC [← GSYM MEMBER_NOT_EMPTY, LEFT_IMP_EXISTS_THM, IN_ELIM_THM] THEN
    X_GEN_TAC (← q "c:int") THEN STRIP_TAC THEN ASM_CASES_TAC (← q "n = 0") THENL
     [MAP_EVERY UNDISCH_TAC
       [← q r"~(!i:num. i <= n ==> (p:int) divides (a i))",
        ← q r"p divides (isum (0..n) (\i. a i * c pow i))"] THEN
      ASM_SIMP_TAC [← CONJUNCT1 LE, ISUM_CLAUSES_NUMSEG] THEN
      REWRITE_TAC [INT_POW, LEFT_FORALL_IMP_THM, EXISTS_REFL, INT_MUL_RID] THEN
      CONV_TAC TAUT,
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"p divides ((a:num->int) n)") THENL
     [ASM_SIMP_TAC [ISUM_CLAUSES_RIGHT, LE_0, LE_1] THEN
      ASM_SIMP_TAC [i2] THEN
      MATCH_MP_TAC a3 THEN
      FIRST_X_ASSUM (MP_TAC o SPEC (← q "n - 1")) THEN
      ASM_REWRITE_TAC [a4] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC [a5], ALL_TAC] THEN
    MP_TAC (← GEN (← q "x:int") (← MATCH_MP i6
       (← ISPECL [← q "n:num", ← q r"a:num->int", ← q "x:int", ← q "c:int"]
               INT_POLY_DIFF_EXPLICIT))) THEN
    ASM_SIMP_TAC [INT_PRIME_DIVPROD_EQ] THEN DISCH_THEN (K ALL_TAC) THEN
    ASM_REWRITE_TAC [LEFT_OR_DISTRIB, s7] THEN
    SUBGOAL_THEN
     (← q r"{x:int | l <= x /\ x <= r /\ p divides (x - c)} = {c}")
    SUBST1_TAC THENL
     [MATCH_MP_TAC s8 THEN
      ASM_REWRITE_TAC [INT_SUB_REFL, INT_DIVIDES_0] THEN
      MAP_EVERY X_GEN_TAC [← q "u:int", ← q "v:int"] THEN STRIP_TAC THEN
      SUBGOAL_THEN (← q r"p divides (u - v:int)") MP_TAC THENL
       [ASM_MESON_TAC [INT_CONG, INT_CONG_SYM, INT_CONG_TRANS], ALL_TAC] THEN
      DISCH_THEN (MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC,
      ALL_TAC] THEN
    REWRITE_TAC [s10] THEN
    SIMP_TAC [CARD_CLAUSES, FINITE_INTSEG_RESTRICT] THEN
    MATCH_MP_TAC a10 THEN
    ASM_REWRITE_TAC [] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [RIGHT_IMP_FORALL_THM, IMP_IMP]) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [a11] THEN
    DISCH_THEN (MP_TAC o SPEC (← q "n - 1")) THEN
    ASM_SIMP_TAC [LE_REFL, SUB_ADD, LE_1, ISUM_SING_NUMSEG, SUB_REFL] THEN
    ASM_REWRITE_TAC [INT_POW, INT_MUL_RID]))

  -- @@RETURN BEGIN
  return { FINITE_INTSEG_RESTRICT, INT_POLY_LAGRANGE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Laborious instantiation to (x^d == 1) (mod p) over natural numbers.       -/
/- ------------------------------------------------------------------------- -/

structure NumLagrange where
  -- @@FIELDS
  NUM_LAGRANGE_LEMMA : thm
  deriving Inhabited

@[nospecialize]
def setupNumLagrange [HolBase] (D : PrimitiveDeps) (BLemma : Lemma) (BLagrange : Lagrange) :
    ExceptT String IO NumLagrange := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE, INT_ARITH, MESON, .. } := D
  let { CARD_SUBSET_IMAGE, DIVIDES_ONE, .. } := D.core1
  let { FINITE_NUMSEG, FINITE_RESTRICT, .. } := D.core2
  let { INT_ADD_RID, INT_CONG_0_DIVIDES, INT_LT_SUB_RADD, INT_MUL_LZERO,
        INT_OF_NUM_ADD, INT_OF_NUM_LE, INT_OF_NUM_LT, INT_OF_NUM_POW, INT_POW,
        IN_ELIM_THM, IN_IMAGE, IN_NUMSEG, ISUM_0, ISUM_CASES, ISUM_SING, .. } := D.core3
  let { LE_REFL, NUM_OF_INT_OF_NUM, .. } := D.core4
  let { PRIME_1, SING_GSPEC, SUBSET, num_congruent, num_divides, .. } := D.core5
  let { INT_PRIME, .. } := BLemma
  let { FINITE_INTSEG_RESTRICT, INT_POLY_LAGRANGE, .. } := BLagrange
  -- @@SCOPE END

  let NUM_LAGRANGE_LEMMA ← prove
   r"!p d. prime p /\ 1 <= d
         ==> CARD {x | x IN 1..p-1 /\ (x EXP d == 1) (mod p)} <= d"
   (← do
    let i6 ← INTEGER_RULE (← q r"(x - a:int == &0) (mod p) <=>
                            (x == a) (mod p)")
    let a5 ← INT_ARITH (← q r"&1 * x + -- &1 * &1:int = x - &1")
    let a4 ← ARITH_RULE (← q r"1 <= d
                           ==> (((0 <= i /\ i <= d) /\ ~(i = d)) /\ i = 0 <=>
                                i = 0)")
    let a3 ← ARITH_RULE (← q r"(0 <= i /\ i <= d) /\ i = d <=> i = d")
    let a2 ← ARITH_RULE (← q r"x:num <= y ==> y <= d ==> x <= d")
    let m1 ← MESON []
     (← q r"(if p then x else y) * z:int = if p then x * z else y * z")
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"&p:int", ← q r"&1:int", ← q r"&(p-1):int"] INT_POLY_LAGRANGE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC [INT_PRIME, INT_LT_SUB_RADD, INT_OF_NUM_ADD, INT_OF_NUM_LT] THEN
      ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (MP_TAC o SPECL
     [← q "d:num", ← q r"\i. if i = d then &1 else if i = 0 then -- &1 else &0:int"]) THEN
    REWRITE_TAC [] THEN ANTS_TAC THENL
     [DISCH_THEN (MP_TAC o SPEC (← q "d:num")) THEN REWRITE_TAC [LE_REFL] THEN
      REWRITE_TAC [INT_CONG_0_DIVIDES, ← GSYM num_divides, DIVIDES_ONE] THEN
      ASM_MESON_TAC [PRIME_1],
      ALL_TAC] THEN
    REWRITE_TAC [m1] THEN
    SIMP_TAC [ISUM_CASES, FINITE_NUMSEG, FINITE_RESTRICT] THEN
    REWRITE_TAC [INT_POW, INT_MUL_LZERO, ISUM_0, INT_ADD_RID] THEN
    MATCH_MP_TAC a2 THEN
    REWRITE_TAC [IN_ELIM_THM, IN_NUMSEG] THEN
    ASM_SIMP_TAC [a3, a4] THEN
    REWRITE_TAC [SING_GSPEC, ISUM_SING] THEN
    REWRITE_TAC [a5] THEN
    REWRITE_TAC [i6] THEN
    MATCH_MP_TAC CARD_SUBSET_IMAGE THEN EXISTS_TAC (← q "num_of_int") THEN
    REWRITE_TAC [FINITE_INTSEG_RESTRICT, SUBSET, IN_IMAGE, IN_ELIM_THM] THEN
    X_GEN_TAC (← q "n:num") THEN DISCH_TAC THEN EXISTS_TAC (← q r"&n:int") THEN
    ASM_REWRITE_TAC [NUM_OF_INT_OF_NUM, INT_OF_NUM_LE, INT_OF_NUM_POW] THEN
    ASM_REWRITE_TAC [← GSYM num_congruent]))

  -- @@RETURN BEGIN
  return { NUM_LAGRANGE_LEMMA }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Count of elements with a given order modulo a prime.                      -/
/- ------------------------------------------------------------------------- -/

structure CountOrders where
  -- @@FIELDS
  COUNT_ORDERS_MODULO_PRIME : thm
  deriving Inhabited

@[nospecialize]
def setupCountOrders [HolBase] (D : PrimitiveDeps) (BNumLagrange : NumLagrange) :
    ExceptT String IO CountOrders := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, SET_RULE, .. } := D
  let { ADD_SUB, CARD_CLAUSES, CARD_EQ_NSUM, CARD_IMAGE_INJ, CARD_NUMSEG_LT,
        CARD_SUBSET_IMAGE, CARD_SUBSET_LE, CONG, CONG_EXP, CONG_IMP_EQ, COPRIME_SYM,
        DE_MORGAN_THM, DIVIDES_MOD, .. } := D.core1
  let { DIVIDES_ZERO, DIVISION, EQ_IMP_LE, ETA_AX, EXP_EXP, EXP_ONE, FINITE_DIVISORS,
        FINITE_NUMSEG, FINITE_NUMSEG_LT, FINITE_RESTRICT, FORALL_IN_IMAGE, IMP_CONJ, .. } := D.core2
  let { IN_ELIM_THM, IN_NUMSEG, .. } := D.core3
  let { LEFT_IMP_EXISTS_THM, LE_0, LE_1, LE_ANTISYM, LE_MULT_RCANCEL, LE_TRANS,
        MEMBER_NOT_EMPTY, MOD_EXP_MOD, MULT_CLAUSES, MULT_EQ_0, MULT_SYM, NOT_LE,
        NSUM_CONST_NUMSEG, NSUM_GROUP, NSUM_LE, NSUM_LT, ORDER, ORDER_DIVIDES_EXPDIFF,
        ORDER_DIVIDES_PHI, .. } := D.core4
  let { ORDER_WORKS, PHI_ALT, PHI_DIVISORSUM, PHI_FINITE_LEMMA, PHI_PRIME,
        PRIME_COPRIME_EQ, PRIME_COPRIME_LT, PRIME_DIVEXP, PRIME_GE_2, PRIME_IMP_NZ,
        RIGHT_FORALL_IMP_THM, SUBSET, coprime, divides, .. } := D.core5
  let { NUM_LAGRANGE_LEMMA, .. } := BNumLagrange
  -- @@SCOPE END

  let COUNT_ORDERS_MODULO_PRIME ← prove
   r"!p d. prime p /\ d divides (p - 1)
         ==> CARD {x | x IN 1..p-1 /\ order p x = d} = phi(d)"
   (← do
    let lemma ← prove
     r"!s f g:A->num.
          FINITE s /\ (!x. x IN s ==> f(x) <= g(x)) /\ nsum s f = nsum s g
          ==> !x. x IN s ==> f x = g x"
     (REWRITE_TAC [← GSYM LE_ANTISYM] THEN MESON_TAC [NSUM_LE, NSUM_LT, NOT_LE])
    let a10 ← ARITH_RULE (← q r"e <= 1 <=> e = 0 \/ e = 1")
    let a9 ← ARITH_RULE (← q r"~(d < e * d) <=> e * d <= 1 * d")
    let a8 ← ARITH_RULE (← q r"(e * m') * d':num = (e * d') * m'")
    let a7 ← ARITH_RULE (← q r"0 < d <=> ~(d = 0)")
    let a6 ← ARITH_RULE (← q r"1 <= d <=> ~(d = 0)")
    let t5 ← TAUT (← q r"a /\ c /\ (~b ==> d) ==> (a /\ b ==> ~c) ==> d")
    let s4 ← SET_RULE
     (← q r"s' SUBSET s /\ (!x. x IN t /\ f x IN s' ==> x IN t')
      ==> s = IMAGE f t ==> s' SUBSET IMAGE f t'")
    let a3 ← ARITH_RULE (← q r"1 <= x <=> ~(x = 0)")
    let a2 ← ARITH_RULE (← q r"~(p - 1 = 0) ==> (x <= p - 1 <=> x < p)")
    let s1 ← SET_RULE
     (← q r"(!x. p x ==> q x) <=> (!x. x IN {x | p x} ==> q x)")
    pure (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [s1] THEN
    MATCH_MP_TAC lemma THEN SUBGOAL_THEN (← q r"~(p - 1 = 0)") ASSUME_TAC THENL
     [FIRST_ASSUM (MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC, ALL_TAC] THEN
    ASM_SIMP_TAC [← REWRITE_RULE [ETA_AX] PHI_DIVISORSUM, FINITE_DIVISORS] THEN
    CONJ_TAC THENL
     [ALL_TAC,
      SIMP_TAC [CARD_EQ_NSUM, FINITE_RESTRICT, FINITE_NUMSEG] THEN
      W (MP_TAC o PART_MATCH (lhs o rand) NSUM_GROUP o lhs o snd) THEN
      REWRITE_TAC [NSUM_CONST_NUMSEG, FINITE_NUMSEG, ADD_SUB, MULT_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, IN_NUMSEG] THEN
      X_GEN_TAC (← q "x:num") THEN STRIP_TAC THEN ASM_SIMP_TAC [← GSYM PHI_PRIME] THEN
      MATCH_MP_TAC ORDER_DIVIDES_PHI THEN ONCE_REWRITE_TAC [COPRIME_SYM] THEN
      MATCH_MP_TAC PRIME_COPRIME_LT THEN ASM_REWRITE_TAC [] THEN
      ASM_ARITH_TAC] THEN
    X_GEN_TAC (← q "d:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_CASES_TAC (← q r"{x | x IN 1..p-1 /\ order p x = d} = {}") THEN
    ASM_REWRITE_TAC [CARD_CLAUSES, LE_0] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [← GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC [IN_ELIM_THM, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q "a:num") THEN
    REWRITE_TAC [IN_NUMSEG] THEN STRIP_TAC THEN REWRITE_TAC [PHI_ALT] THEN
    MATCH_MP_TAC CARD_SUBSET_IMAGE THEN EXISTS_TAC (← q r"\m. (a EXP m) MOD p") THEN
    REWRITE_TAC [PHI_FINITE_LEMMA] THEN
    SUBGOAL_THEN (← q r"1 <= d") ASSUME_TAC THENL
     [ASM_MESON_TAC [LE_1, DIVIDES_ZERO], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"coprime(p,a)") ASSUME_TAC THENL
     [ONCE_REWRITE_TAC [COPRIME_SYM] THEN
      MATCH_MP_TAC PRIME_COPRIME_LT THEN ASM_REWRITE_TAC [] THEN
      ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"{x | x IN 1..p-1 /\ (x EXP d == 1) (mod p)} =
    IMAGE (\m. (a EXP m) MOD p) {m | m < d}")
    MP_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_LE THEN
      SIMP_TAC [FINITE_RESTRICT, FINITE_NUMSEG] THEN CONJ_TAC THENL
       [REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM] THEN
        X_GEN_TAC (← q "m:num") THEN DISCH_TAC THEN REWRITE_TAC [IN_NUMSEG] THEN
        ASM_SIMP_TAC [a2] THEN
        ASM_SIMP_TAC [DIVISION, PRIME_IMP_NZ] THEN CONJ_TAC THENL
         [REWRITE_TAC [a3] THEN
          ASM_SIMP_TAC [← GSYM DIVIDES_MOD, PRIME_IMP_NZ] THEN
          ASM_MESON_TAC [PRIME_DIVEXP, PRIME_COPRIME_EQ],
          ASM_SIMP_TAC [CONG, PRIME_IMP_NZ, MOD_EXP_MOD] THEN
          REWRITE_TAC [EXP_EXP] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
          REWRITE_TAC [← GSYM EXP_EXP] THEN
          SUBST1_TAC (← SYM (← SPEC (← q "m:num") EXP_ONE)) THEN
          ASM_SIMP_TAC [← GSYM CONG, PRIME_IMP_NZ] THEN
          MATCH_MP_TAC CONG_EXP THEN ASM_MESON_TAC [ORDER]],
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q "d:num") THEN
        ASM_SIMP_TAC [NUM_LAGRANGE_LEMMA] THEN
        GEN_REWRITE_TAC LAND_CONV [← GSYM CARD_NUMSEG_LT] THEN
        MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC CARD_IMAGE_INJ THEN
        ASM_SIMP_TAC [← GSYM CONG, PRIME_IMP_NZ, FINITE_NUMSEG_LT, IN_ELIM_THM] THEN
        ASM_SIMP_TAC [ORDER_DIVIDES_EXPDIFF] THEN REWRITE_TAC [CONG_IMP_EQ]],
      MATCH_MP_TAC s4 THEN
      SIMP_TAC [SUBSET, IN_ELIM_THM, IN_NUMSEG] THEN
      CONJ_TAC THENL [MESON_TAC [ORDER], ALL_TAC] THEN
      X_GEN_TAC (← q "m:num") THEN ABBREV_TAC (← q r"b = (a EXP m) MOD p") THEN STRIP_TAC THEN
      REWRITE_TAC [coprime, divides] THEN X_GEN_TAC (← q "e:num") THEN
      DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN (← q "m':num") (ASSUME_TAC o SYM))
                                (X_CHOOSE_THEN (← q "d':num") (ASSUME_TAC o SYM))) THEN
      MP_TAC (← ISPECL [← q "p:num", ← q "b:num"] ORDER_WORKS) THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC (← q "d':num"))) THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC t5 THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC (← q r"1 <= d") THEN EXPAND_TAC "d" THEN
        REWRITE_TAC [a6, MULT_EQ_0] THEN
        SIMP_TAC [DE_MORGAN_THM, a7],
        EXPAND_TAC "b" THEN ASM_SIMP_TAC [CONG, PRIME_IMP_NZ, MOD_EXP_MOD] THEN
        EXPAND_TAC "m" THEN REWRITE_TAC [EXP_EXP] THEN
        ONCE_REWRITE_TAC [a8] THEN
        ASM_REWRITE_TAC [] THEN REWRITE_TAC [← GSYM EXP_EXP] THEN
        SUBST1_TAC (← SYM (← SPEC (← q "m':num") EXP_ONE)) THEN
        ASM_SIMP_TAC [← GSYM CONG, PRIME_IMP_NZ] THEN
        MATCH_MP_TAC CONG_EXP THEN ASM_MESON_TAC [ORDER],
        EXPAND_TAC "d" THEN
        REWRITE_TAC [a9] THEN
        REWRITE_TAC [LE_MULT_RCANCEL] THEN
        REWRITE_TAC [a10] THEN
        STRIP_TAC THEN UNDISCH_TAC (← q r"e * d':num = d") THEN
        ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC]]))

  -- @@RETURN BEGIN
  return { COUNT_ORDERS_MODULO_PRIME }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- In particular, primitive roots modulo a prime.                            -/
/- ------------------------------------------------------------------------- -/

structure PrimitiveRoots where
  -- @@FIELDS
  PRIMITIVE_ROOTS_MODULO_PRIME : thm
  PRIMITIVE_ROOT_MODULO_PRIME : thm
  deriving Inhabited

@[nospecialize]
def setupPrimitiveRoots [HolBase] (D : PrimitiveDeps) (BCountOrders : CountOrders) :
    ExceptT String IO PrimitiveRoots := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, SET_TAC, .. } := D
  let { CARD_CLAUSES, CONTRAPOS_THM, .. } := D.core1
  let { DIVIDES_REFL, .. } := D.core2
  let { PHI_LOWERBOUND_1_STRONG, PRIME_GE_2, .. } := D.core5
  let { COUNT_ORDERS_MODULO_PRIME, .. } := BCountOrders
  -- @@SCOPE END

  let PRIMITIVE_ROOTS_MODULO_PRIME ← prove
   r"!p. prime p ==> CARD {x | x IN 1..p-1 /\ order p x = p - 1} = phi(p - 1)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q "p:num", ← q "p - 1"] COUNT_ORDERS_MODULO_PRIME) THEN
    ASM_REWRITE_TAC [DIVIDES_REFL])

  let PRIMITIVE_ROOT_MODULO_PRIME ← prove
   r"!p. prime p ==> ?x. x IN 1..p-1 /\ order p x = p - 1"
   (← do
    let a1 ← ARITH_RULE (← q r"1 <= p ==> ~(0 = p)")
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP PRIMITIVE_ROOTS_MODULO_PRIME) THEN
    ASM_CASES_TAC (← q r"{x | x IN 1..p-1 /\ order p x = p - 1} = {}") THENL
     [ASM_REWRITE_TAC [CARD_CLAUSES], ASM SET_TAC []] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN DISCH_THEN (K ALL_TAC) THEN
    MATCH_MP_TAC a1 THEN
    MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC))

  -- @@RETURN BEGIN
  return { PRIMITIVE_ROOTS_MODULO_PRIME, PRIMITIVE_ROOT_MODULO_PRIME }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Now primitive roots modulo odd prime powers.                              -/
/- ------------------------------------------------------------------------- -/

/- ------------------------------------------------------------------------- -/
/- Now primitive roots modulo odd prime powers.                              -/
/- ------------------------------------------------------------------------- -/

structure PrimePows1 where
  -- @@FIELDS
  COPRIME_1_PLUS_POWER_STEP : thm
  COPRIME_1_PLUS_POWER : thm
  PRIMITIVE_ROOT_MODULO_PRIMEPOWS : thm
  deriving Inhabited

@[nospecialize]
def setupPrimePows1 [HolBase] (D : PrimitiveDeps) (BPrimitiveRoots : PrimitiveRoots) :
    ExceptT String IO PrimePows1 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, INTEGER_RULE,
        MESON_TAC, NUMBER_RULE, .. } := D
  let { ADD_CLAUSES, ARITH, BINOMIAL_THEOREM, BINOM_1, BINOM_PENULT, BINOM_REFL,
        CONG_TO_1, CONJ_SYM, COPRIME_EXP_DIVPROD, COPRIME_LEXP, COPRIME_SYM, DIVIDES_0,
        DIVIDES_ADD, DIVIDES_EXP_LE, DIVIDES_LMUL, DIVIDES_MUL2, DIVIDES_PRIMEPOW,
        DIVIDES_PRIME_BINOM, .. } := D.core1
  let { DIVIDES_REFL, DIVIDES_REXP, DIVIDES_RMUL, EXP, EXP_1, EXP_ADD, EXP_EQ_0,
        EXP_EXP, EXP_ONE, .. } := D.core2
  let { INT_CONG_SOLVE_POS, INT_COPRIME_LMUL, INT_COPRIME_LPOW, INT_EXISTS_POS,
        INT_OF_NUM_ADD, INT_OF_NUM_EQ, INT_OF_NUM_MUL, INT_OF_NUM_POW, INT_OF_NUM_SUB,
        IN_NUMSEG, .. } := D.core3
  let { LEFT_IMP_EXISTS_THM, LE_0, LE_1, LE_MULT_LCANCEL, LE_TRANS, MONO_EXISTS,
        MULT_AC, MULT_ASSOC, MULT_CLAUSES, MULT_EXP, MULT_SYM, NSUM_CLAUSES_LEFT,
        NSUM_CLAUSES_RIGHT, NSUM_CLOSED, NSUM_EQ, NSUM_LMUL, ORDER, ORDER_CONG,
        ORDER_DIVIDES, ORDER_DIVIDES_PHI, .. } := D.core4
  let { ORDER_WORKS, PHI_PRIMEPOW, PRIME_COPRIME_LT, RIGHT_SUB_DISTRIB, SUB_REFL,
        SUC_SUB1, binom, divides, num_coprime, .. } := D.core5
  let { PRIMITIVE_ROOT_MODULO_PRIME, .. } := BPrimitiveRoots
  -- @@SCOPE END

  let COPRIME_1_PLUS_POWER_STEP ← prove
   r"!p z k. prime p /\ coprime(z,p) /\ 3 <= p /\ 1 <= k
             ==> ?w. coprime(w,p) /\
                     (1 + z * p EXP k) EXP p = 1 + w * p EXP (k + 1)"
   (← do
    let r6 ← ARITH_RULE (← q r"3 <= p ==> 2 <= p")
    let r5 ← ARITH_RULE (← q r"k + 2 = SUC(k + 1)")
    let r4 ← ARITH_RULE (← q r"3 <= p ==> 2 <= p")
    let r3 ← ARITH_RULE (← q r"a * b * c:num = b * c * a")
    let r2 ← NUMBER_RULE (← q r"coprime(z + p * d:num,p) <=> coprime(z,p)")
    let r1 ← ARITH_RULE (← q r"1 + a * b = a * b + 1")
    pure (REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [r1] THEN
    REWRITE_TAC [BINOMIAL_THEOREM, EXP_ONE, MULT_CLAUSES] THEN
    SIMP_TAC [NSUM_CLAUSES_LEFT, LE_0, EXP, binom, MULT_CLAUSES, ADD_CLAUSES] THEN
    SUBGOAL_THEN (← q r"1 <= p") MP_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
    SIMP_TAC [NSUM_CLAUSES_LEFT, BINOM_1, EXP_1, ARITH] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"(p EXP (k + 2)) divides (nsum(2..p) (\i. binom(p,i) * (z * p EXP k) EXP i))")
    MP_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [divides, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q "d:num") THEN DISCH_THEN SUBST1_TAC THEN
      EXISTS_TAC (← q r"z + p * d:num") THEN
      ASM_REWRITE_TAC [r2] THEN
      REWRITE_TAC [EXP_ADD] THEN ARITH_TAC] THEN
    MATCH_MP_TAC NSUM_CLOSED THEN
    REWRITE_TAC [DIVIDES_0, DIVIDES_ADD, IN_NUMSEG] THEN
    X_GEN_TAC (← q "j:num") THEN STRIP_TAC THEN REWRITE_TAC [MULT_EXP] THEN
    ONCE_REWRITE_TAC [r3] THEN
    REWRITE_TAC [EXP_EXP] THEN
    MATCH_MP_TAC DIVIDES_LMUL THEN ASM_CASES_TAC (← q r"j:num = p") THENL
     [MATCH_MP_TAC DIVIDES_RMUL THEN
      ASM_SIMP_TAC [DIVIDES_EXP_LE, r4] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"k * 3") THEN CONJ_TAC THENL
       [ASM_ARITH_TAC, ASM_REWRITE_TAC [LE_MULT_LCANCEL]],
      ONCE_REWRITE_TAC [MULT_SYM] THEN
      REWRITE_TAC [EXP, r5] THEN
      MATCH_MP_TAC DIVIDES_MUL2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIVIDES_PRIME_BINOM THEN ASM_REWRITE_TAC [] THEN
        ASM_ARITH_TAC,
        ASM_SIMP_TAC [DIVIDES_EXP_LE, r6] THEN
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q r"k * 2") THEN CONJ_TAC THENL
         [ASM_ARITH_TAC, ASM_REWRITE_TAC [LE_MULT_LCANCEL]]]]))

  let COPRIME_1_PLUS_POWER ← prove
   r"!p z k. prime p /\ coprime(z,p) /\ 3 <= p
             ==> ?w. coprime(w,p) /\
                     (1 + z * p) EXP (p EXP k) = 1 + w * p EXP (k + 1)"
   (← do
    let r1 ← ARITH_RULE (← q r"1 <= k + 1")
    pure (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [ADD_CLAUSES, EXP_1, EXP] THENL [MESON_TAC [], ALL_TAC] THEN
    REWRITE_TAC [← GSYM (← ONCE_REWRITE_RULE [MULT_SYM] EXP_EXP)] THEN
    DISCH_THEN (fun th => POP_ASSUM MP_TAC THEN STRIP_ASSUME_TAC th) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "w:num") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q "p:num", ← q "w:num", ← q r"k + 1"] COPRIME_1_PLUS_POWER_STEP) THEN
    ASM_REWRITE_TAC [r1] THEN
    REWRITE_TAC [EXP_ADD, EXP_1, MULT_AC]))

  let PRIMITIVE_ROOT_MODULO_PRIMEPOWS ← prove
   r"!p. prime p /\ 3 <= p
         ==> ?g. !j. 1 <= j ==> order(p EXP j) g = phi(p EXP j)"
   (← do
    let s19 ← ARITH_RULE (← q r"3 <= p ==> 2 <= p")
    let s18 ← NUMBER_RULE (← q r"(1 + x == 1) (mod n) <=> n divides x")
    let s17 ← NUMBER_RULE
      (← q r"coprime(p:num,y + x) /\ p divides z ==> coprime(y + z + x,p)")
    let s16 ← ARITH_RULE (← q r"3 <= p ==> p - 1 - (p - 2) = 1")
    let s15 ← ARITH_RULE (← q r"3 <= p ==> 0 < p - 2")
    let s14 ← ARITH_RULE (← q r"p * b * g * pp * x:num = b * g * (p * pp) * x")
    let s13 ← ARITH_RULE (← q r"s + 1 + y * p = 1 + (y + t) * p <=> s = p * t")
    let s12 ← ARITH_RULE (← q r"n - 1 - 1 = n - 2")
    let s11 ← ARITH_RULE (← q r"3 <= p ==> 0 < p - 1")
    let s10 ← ARITH_RULE (← q r"3 <= p ==> ~(p - 1 = 0)")
    let s9 ← NUMBER_RULE
      (← q r"(a * x:num) divides (a * y) ==> ~(a = 0) ==> x divides y")
    let s8 ← NUMBER_RULE (← q r"coprime(p,g + p * x) <=> coprime(g,p)")
    let s7 ← NUMBER_RULE
      (← q r"!y. (a == 1) (mod y) /\ x divides y ==> (a == 1) (mod x)")
    let s6 ← TAUT (← q r"a /\ (b ==> c) ==> (a <=> b) ==> c")
    let s5 ← NUMBER_RULE (← q r"(g:num == g + p * x) (mod p)")
    let s4 ← ARITH_RULE (← q r"3 <= p ==> 1 <= p")
    let s3 ← INTEGER_RULE
      (← q r"(x:int == &1 - y) (mod n) ==> coprime(n,y + x)")
    let s2 ← ARITH_RULE (← q r"3 <= p ==> ~(p = 0)")
    let s1 ← INTEGER_RULE (← q r"coprime(p - &1,p)")
    pure (REPEAT STRIP_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP PRIMITIVE_ROOT_MODULO_PRIME) THEN
    REWRITE_TAC [IN_NUMSEG] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "g:num") STRIP_ASSUME_TAC) THEN
    MP_TAC (← ISPECL [← q "p:num", ← q "g:num"] ORDER) THEN
    ASM_SIMP_TAC [CONG_TO_1, EXP_EQ_0, LE_1] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "y:num") STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN (← q r"?x. coprime(p,y + (p - 1) * g EXP (p - 2) * x)") CHOOSE_TAC THENL
     [MP_TAC (← ISPECL [← q r"(&p - &1:int) * &g pow (p - 2)", ← q r"&1 - &y:int", ← q r"&p:int"]
                    INT_CONG_SOLVE_POS) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [INT_COPRIME_LMUL, INT_COPRIME_LPOW] THEN
        REWRITE_TAC [s1, ← GSYM num_coprime] THEN
        ASM_SIMP_TAC [INT_OF_NUM_EQ, s2] THEN
        DISJ1_TAC THEN MATCH_MP_TAC PRIME_COPRIME_LT THEN
        ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
        REWRITE_TAC [← GSYM INT_EXISTS_POS] THEN MATCH_MP_TAC MONO_EXISTS THEN
        GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP s3) THEN
        ASM_SIMP_TAC [INT_OF_NUM_SUB, INT_OF_NUM_POW, INT_OF_NUM_MUL,
                     INT_OF_NUM_ADD, ← GSYM num_coprime, s4] THEN
        REWRITE_TAC [MULT_ASSOC]],
      ALL_TAC] THEN
    EXISTS_TAC (← q r"g + p * x:num") THEN X_GEN_TAC (← q "j:num") THEN DISCH_TAC THEN
    STRIP_ASSUME_TAC (← ISPECL [← q r"p EXP j", ← q r"g + p * x:num"] ORDER_WORKS) THEN
    MP_TAC (← SPECL [← q "p:num", ← q r"g + p * x:num", ← q r"order (p EXP j) (g + p * x)"]
        ORDER_DIVIDES) THEN
    SUBGOAL_THEN (← q r"order p (g + p * x) = p - 1") SUBST1_TAC THENL
     [ASM_MESON_TAC [ORDER_CONG, s5],
      ALL_TAC] THEN
    MATCH_MP_TAC s6 THEN CONJ_TAC THENL
     [MATCH_MP_TAC s7 THEN
      EXISTS_TAC (← q r"p EXP j") THEN ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [DIVIDES_REFL, DIVIDES_REXP, LE_1],
      REWRITE_TAC [divides, LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC (← q "d:num") THEN
      DISCH_THEN (fun th => SUBST_ALL_TAC th THEN ASSUME_TAC th)] THEN
    MP_TAC (← ISPECL [← q r"g + p * x:num", ← q r"p EXP j"] ORDER_DIVIDES_PHI) THEN
    ASM_SIMP_TAC [PHI_PRIMEPOW, LE_1, COPRIME_LEXP] THEN ANTS_TAC THENL
     [REWRITE_TAC [s8] THEN
      MATCH_MP_TAC PRIME_COPRIME_LT THEN
      ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"p EXP j - p EXP (j - 1) = (p - 1) * p EXP (j - 1)")
    SUBST1_TAC THENL
     [UNDISCH_TAC (← q r"1 <= j") THEN SPEC_TAC (← q "j:num", ← q "j:num") THEN
      INDUCT_TAC THEN REWRITE_TAC [ARITH, SUC_SUB1] THEN
      REWRITE_TAC [EXP, RIGHT_SUB_DISTRIB] THEN ARITH_TAC,
      ALL_TAC] THEN
    DISCH_THEN (MP_TAC o MATCH_MP s9) THEN
    ASM_SIMP_TAC [DIVIDES_PRIMEPOW, s10] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "k:num")
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN (← q r"?z. (g + p * x) EXP (p - 1) = 1 + z * p /\ coprime(z,p)")
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [BINOMIAL_THEOREM] THEN
      ASM_SIMP_TAC [NSUM_CLAUSES_RIGHT, LE_0, s11] THEN
      REWRITE_TAC [BINOM_REFL, SUB_REFL, EXP, MULT_CLAUSES] THEN
      EXISTS_TAC
       (← q r"y + nsum(0..p-2) (\k. binom(p - 1,k) * g EXP k *
                              p EXP (p - 2 - k) * x EXP (p - 1 - k))") THEN
      REWRITE_TAC [s12] THEN
      SIMP_TAC [s13] THEN
      CONJ_TAC THENL
       [REWRITE_TAC [← GSYM NSUM_LMUL] THEN MATCH_MP_TAC NSUM_EQ THEN
        X_GEN_TAC (← q "i:num") THEN REWRITE_TAC [IN_NUMSEG] THEN STRIP_TAC THEN
        SIMP_TAC [s14] THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [MULT_EXP] THEN
        REWRITE_TAC [← GSYM (← CONJUNCT2 EXP)] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC,
        ALL_TAC] THEN
      ASM_SIMP_TAC [NSUM_CLAUSES_RIGHT, LE_0, s15] THEN
      REWRITE_TAC [BINOM_REFL, SUB_REFL, EXP, MULT_CLAUSES] THEN
      ASM_SIMP_TAC [EXP_1, s16] THEN
      SUBGOAL_THEN (← q r"binom(p - 1,p - 2) = p - 1") SUBST1_TAC THENL
       [SUBGOAL_THEN (← q r"p - 1 = SUC(p - 2)") SUBST1_TAC THENL
         [ASM_ARITH_TAC, REWRITE_TAC [BINOM_PENULT]],
        ALL_TAC] THEN
      MATCH_MP_TAC s17 THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC NSUM_CLOSED THEN
      REWRITE_TAC [DIVIDES_0, DIVIDES_ADD, IN_NUMSEG] THEN
      X_GEN_TAC (← q "i:num") THEN STRIP_TAC THEN
      REPLICATE_TAC 2 (MATCH_MP_TAC DIVIDES_LMUL) THEN
      MATCH_MP_TAC DIVIDES_RMUL THEN MATCH_MP_TAC DIVIDES_REXP THEN
      REWRITE_TAC [DIVIDES_REFL] THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"?w. (g + p * x) EXP ((p - 1) * p EXP k) = 1 + p EXP (k + 1) * w /\
          coprime(w,p)")
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC [← GSYM EXP_EXP] THEN
      ONCE_REWRITE_TAC [CONJ_SYM] THEN
      GEN_REWRITE_TAC (BINDER_CONV o funpow 3 RAND_CONV) [MULT_SYM] THEN
      MATCH_MP_TAC COPRIME_1_PLUS_POWER THEN ASM_REWRITE_TAC [],
      UNDISCH_TAC
       (← q r"((g + p * x) EXP ((p - 1) * p EXP k) == 1) (mod (p EXP j))") THEN
      ASM_REWRITE_TAC [s18] THEN
      ONCE_REWRITE_TAC [MULT_SYM] THEN DISCH_TAC THEN
      MP_TAC (← SPECL [← q "p:num", ← q "j:num", ← q "w:num", ← q r"p EXP (k + 1)"]
         COPRIME_EXP_DIVPROD) THEN
      ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_REWRITE_TAC [] THEN
      ASM_SIMP_TAC [DIVIDES_EXP_LE, s19] THEN
      UNDISCH_TAC (← q r"k <= j - 1") THEN ARITH_TAC]))

  -- @@RETURN BEGIN
  return { COPRIME_1_PLUS_POWER_STEP, COPRIME_1_PLUS_POWER,
           PRIMITIVE_ROOT_MODULO_PRIMEPOWS }
  -- @@RETURN END

structure PrimePows2 where
  -- @@FIELDS
  PRIMITIVE_ROOT_MODULO_PRIMEPOW : thm
  PRIME_DIVISOR_ORDER_EXISTS : thm
  INJECTIVE_EXP_MODULO_EQ : thm
  POWER_RESIDUE_MODULO_EQ_ALT : thm
  POWER_RESIDUE_MODULO_EQ : thm
  deriving Inhabited

@[nospecialize]
def setupPrimePows2 [HolBase] (D : PrimitiveDeps) (BPrimePows1 : PrimePows1) :
    ExceptT String IO PrimePows2 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, MOD_DOWN_CONV,
        NUMBER_RULE, NUM_REDUCE_CONV, SET_TAC, .. } := D
  let { ARITH_EQ, CHINESE_REMAINDER_USUAL, CONG, CONG_COPRIME, CONG_MINUS1_SQUARED,
        CONG_MOD, CONJ_ACI, CONJ_ASSOC, CONTRAPOS_THM, COPRIME_0, COPRIME_1,
        COPRIME_PRIME_EQ, COPRIME_REXP, COPRIME_RMOD, COPRIME_SYM, DE_MORGAN_THM,
        DIVIDES_DIV_SELF, DIVIDES_EXP_LE, DIVIDES_LE, DIVIDES_MOD, DIVIDES_ONE, .. } := D.core1
  let { DIVIDES_PRIME_PRIME, DIVIDES_REXP, DIVISION, DIV_BY_DIV, DIV_EQ_0, EQ_TRANS,
        EXISTS_LT_MOD_THM, EXP, EXP_EQ_0, EXP_EQ_1, EXP_ONE, FINITE_NUMSEG_LT,
        FINITE_SUBSET, FORALL_IN_IMAGE, FORALL_LT_MOD_THM, IMP_CONJ, .. } := D.core2
  let { IMP_CONJ_ALT, IMP_IMP, INDUCT_COPRIME_ALT, INJECTIVE_EXP_MODULO, IN_ELIM_THM,
        IN_NUMSEG, LCM_1, LCM_SYM, .. } := D.core3
  let { LEFT_IMP_EXISTS_THM, LE_1, LE_REFL, MOD_LT_EQ, MONO_EXISTS, MULT_CLAUSES,
        MULT_EQ_0, NOT_FORALL_THM, NOT_IMP, NOT_LT, ODD_PRIME, ORDER, ORDER_1,
        ORDER_CONG, ORDER_DIVIDES, ORDER_EQ_0, ORDER_EQ_1, ORDER_EXP, ORDER_MUL_LCM,
        ORDER_UNIQUE_PRIME, .. } := D.core4
  let { PHI_1, PHI_EQ_0, PHI_LOWERBOUND_1_STRONG, PHI_MULTIPLICATIVE, PHI_PRIMEPOW_ALT,
        PRIME_0, PRIME_1, PRIME_DIVEXP_EQ, PRIME_DIVPROD_EQ, PRIME_IMP_NZ, PRIME_ODD,
        RIGHT_FORALL_IMP_THM, RIGHT_IMP_FORALL_THM, SUBSET, SUB_ADD,
        SURJECTIVE_IFF_INJECTIVE, SWAP_FORALL_THM, .. } := D.core5
  let { PRIMITIVE_ROOT_MODULO_PRIMEPOWS, .. } := BPrimePows1
  -- @@SCOPE END

  let PRIMITIVE_ROOT_MODULO_PRIMEPOW ← prove
   r"!p k. prime p /\ 3 <= p /\ 1 <= k
           ==> ?x. x IN 1..(p EXP k - 1) /\ order (p EXP k) x = phi(p EXP k)"
   (← do
    let a5 ← ARITH_RULE (← q r"3 <= p ==> ~(p = 0)")
    let a4 ← ARITH_RULE (← q r"a < b ==> a <= b - 1")
    let a8 ← ARITH_RULE (← q r"~(p = 0) ==> 1 <= p")
    let a7 ← ARITH_RULE (← q r"1 <= p ==> ~(p = 0)")
    let a6 ← ARITH_RULE (← q r"3 <= p ==> ~(p = 1)")
    let n9 ← NUMBER_RULE
      (← q r"(x == 1) (mod p) ==> p divides x ==> p divides 1")
    let a3 ← ARITH_RULE (← q r"3 <= p ==> ~(p = 0)")
    let a2 ← ARITH_RULE (← q r"1 <= x <=> ~(x = 0)")
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPEC (← q "p:num") PRIMITIVE_ROOT_MODULO_PRIMEPOWS) THEN
    ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q "x:num") THEN DISCH_THEN (MP_TAC o SPEC (← q "k:num")) THEN
    ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    EXISTS_TAC (← q r"x MOD (p EXP k)") THEN CONJ_TAC THENL
     [REWRITE_TAC [IN_NUMSEG, a2] THEN
      CONJ_TAC THENL
       [MP_TAC (← ISPECL [← q r"p EXP k", ← q "x:num"] DIVIDES_MOD) THEN
        ASM_SIMP_TAC [EXP_EQ_0, a3] THEN
        DISCH_THEN (SUBST1_TAC o SYM) THEN DISCH_TAC THEN
        MP_TAC (← ISPECL [← q r"p EXP k", ← q "x:num"] ORDER) THEN
        DISCH_THEN (MP_TAC o MATCH_MP n9) THEN
        ASM_SIMP_TAC [EXP_EQ_1, DIVIDES_ONE, LE_1] THEN
        ASM_SIMP_TAC [a6] THEN
        MATCH_MP_TAC DIVIDES_REXP THEN ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC a7 THEN
        MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN
        MATCH_MP_TAC a8 THEN
        ASM_SIMP_TAC [EXP_EQ_0] THEN ASM_ARITH_TAC,
        MATCH_MP_TAC a4 THEN
        MP_TAC (← ISPECL [← q "x:num", ← q r"p EXP k"] DIVISION) THEN
        ASM_SIMP_TAC [EXP_EQ_0, a5]],
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"order (p EXP k) x") THEN
      CONJ_TAC THENL [ALL_TAC, ASM_REWRITE_TAC []] THEN
      MATCH_MP_TAC ORDER_CONG THEN REWRITE_TAC [CONG_MOD]]))

  let PRIME_DIVISOR_ORDER_EXISTS ← prove
   r"!n p. ~(n = 0) /\ prime p /\ p divides phi(n) ==> ?x. order n x = p"
   (← do
    let d3 ← NUMBER_RULE (← q r"(p == 2) (mod p) <=> p divides 2 EXP 1")
    let d2 ← NUMBER_RULE (← q r"(a == 1) (mod p) ==> (a + 1 == 2) (mod p)")
    let d1 ← MESON []
      (← q r"(!x y. R x y <=> R y x) /\ (!x y. P x ==> R x y)
        ==> !x y. P x \/ P y ==> R x y")
    pure (GEN_REWRITE_TAC id [SWAP_FORALL_THM] THEN X_GEN_TAC (← q "p:num") THEN
    ASM_CASES_TAC (← q r"prime p") THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC INDUCT_COPRIME_ALT THEN REWRITE_TAC [] THEN CONJ_TAC THENL
     [SIMP_TAC [ORDER_MUL_LCM, PHI_MULTIPLICATIVE, MULT_EQ_0] THEN
      ASM_SIMP_TAC [PRIME_DIVPROD_EQ, DE_MORGAN_THM, IMP_IMP, CONJ_ASSOC] THEN
      ONCE_REWRITE_TAC [IMP_CONJ_ALT] THEN MATCH_MP_TAC d1 THEN
      CONJ_TAC THENL [REWRITE_TAC [CONJ_ACI, COPRIME_SYM, LCM_SYM], ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [← q "m:num", ← q "n:num"] THEN DISCH_TAC THEN
      MAP_EVERY ASM_CASES_TAC [← q r"m = 0", ← q r"n = 0"] THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
      FIRST_X_ASSUM ((K ALL_TAC : thm → tactic) o check (is_imp o concl)) THEN
      FIRST_X_ASSUM (X_CHOOSE_TAC (← q "a:num")) THEN
      MP_TAC (← ISPECL [← q "m:num", ← q "n:num", ← q "a:num", ← q "1"]
         CHINESE_REMAINDER_USUAL) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC (← q "b:num") THEN
      DISCH_THEN (CONJUNCTS_THEN (SUBST1_TAC o MATCH_MP ORDER_CONG)) THEN
      ASM_REWRITE_TAC [ORDER_1, LCM_1],
      MAP_EVERY X_GEN_TAC [← q "q:num", ← q "k:num"]] THEN
    ASM_CASES_TAC (← q r"k = 0") THENL
     [ASM_REWRITE_TAC [PHI_1, EXP, DIVIDES_ONE] THEN ASM_MESON_TAC [PRIME_1],
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"q = 2") THENL
     [ASM_SIMP_TAC [PHI_PRIMEPOW_ALT] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC [PRIME_DIVEXP_EQ, MULT_CLAUSES, DIVIDES_PRIME_PRIME] THEN
      REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"2 EXP k - 1") THEN
      ASM_SIMP_TAC [ORDER_UNIQUE_PRIME, CONG_MINUS1_SQUARED] THEN
      DISCH_THEN (MP_TAC o MATCH_MP d2) THEN
      SIMP_TAC [SUB_ADD, LE_1, EXP_EQ_0, ARITH_EQ] THEN
      REWRITE_TAC [d3] THEN
      SIMP_TAC [DIVIDES_EXP_LE, LE_REFL] THEN ASM_ARITH_TAC,
      REPEAT STRIP_TAC] THEN
    MP_TAC (← SPECL [← q "q:num", ← q "k:num"] PRIMITIVE_ROOT_MODULO_PRIMEPOW) THEN
    ASM_SIMP_TAC [LE_1] THEN ANTS_TAC THENL
     [ASM_MESON_TAC [ODD_PRIME, PRIME_ODD], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "x:num") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q r"x EXP (phi(q EXP k) DIV p)") THEN
    W (MP_TAC o PART_MATCH (fun c => do lhand (← rand c)) ORDER_EXP o lhand o snd) THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_SIMP_TAC [DIV_BY_DIV, DIVIDES_DIV_SELF, PHI_EQ_0, DIV_EQ_0, NOT_LT,
                 PRIME_IMP_NZ]))

  let INJECTIVE_EXP_MODULO_EQ ← prove
   r"!n k. ~(n = 0)
           ==> ((!a b. coprime(n,a) /\ coprime(n,b) /\
                       (a EXP k == b EXP k) (mod n)
                       ==> (a == b) (mod n)) <=>
                coprime(k,phi n))"
   (REPEAT STRIP_TAC THEN
    EQ_TAC THENL [ALL_TAC, MESON_TAC [INJECTIVE_EXP_MODULO]] THEN
    GEN_REWRITE_TAC id [← GSYM CONTRAPOS_THM] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COPRIME_PRIME_EQ] THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM, NOT_FORALL_THM] THEN
    X_GEN_TAC (← q "p:num") THEN STRIP_TAC THEN REWRITE_TAC [NOT_IMP] THEN
    MP_TAC (← ISPECL [← q "n:num", ← q "p:num"] PRIME_DIVISOR_ORDER_EXISTS) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC (← q "x:num") THEN STRIP_TAC THEN EXISTS_TAC (← q "1") THEN
    ASM_REWRITE_TAC [COPRIME_1, EXP_ONE] THEN
    ASM_MESON_TAC [PRIME_0, PRIME_1, ORDER_EQ_0, ORDER_EQ_1, ORDER_DIVIDES])

  let POWER_RESIDUE_MODULO_EQ_ALT ← prove
   r"!n k. ~(n = 0)
           ==> ((!a. coprime(n,a)
                     ==> ?x. coprime(n,x) /\ (x EXP k == a) (mod n)) <=>
                coprime(k,phi n))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"{a:num | a < n /\ coprime(n,a)}", ← q r"\a. (a EXP k) MOD n"]
            SURJECTIVE_IFF_INJECTIVE) THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, IN_ELIM_THM] THEN
    ASM_REWRITE_TAC [← GSYM CONJ_ASSOC, FORALL_LT_MOD_THM, EXISTS_LT_MOD_THM] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{a:num | a < n}") THEN
      REWRITE_TAC [FINITE_NUMSEG_LT] THEN SET_TAC [],
      REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, RIGHT_IMP_FORALL_THM]] THEN
    REWRITE_TAC [IN_ELIM_THM, IMP_IMP, ← GSYM CONJ_ASSOC, COPRIME_RMOD] THEN
    ASM_SIMP_TAC [MOD_LT_EQ, COPRIME_REXP] THEN CONV_TAC MOD_DOWN_CONV THEN
    REWRITE_TAC [← GSYM CONG] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC INJECTIVE_EXP_MODULO_EQ THEN ASM_REWRITE_TAC [])

  let POWER_RESIDUE_MODULO_EQ ← prove
   r"!n k. ~(n = 0)
           ==> ((!a. coprime(n,a) ==> ?x. (x EXP k == a) (mod n)) <=>
                coprime(k,phi n))"
   (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (SUBST1_TAC o SYM o SPEC (← q "k:num") o MATCH_MP
     POWER_RESIDUE_MODULO_EQ_ALT) THEN
    ASM_CASES_TAC (← q r"k = 0") THENL
     [ASM_REWRITE_TAC [EXP, COPRIME_0] THEN MESON_TAC [COPRIME_1], ALL_TAC] THEN
    EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC (← q "a:num") THEN DISCH_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q "a:num")) THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q "x:num") THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP CONG_COPRIME) THEN
    ASM_REWRITE_TAC [COPRIME_REXP])

  -- @@RETURN BEGIN
  return { PRIMITIVE_ROOT_MODULO_PRIMEPOW, PRIME_DIVISOR_ORDER_EXISTS,
           INJECTIVE_EXP_MODULO_EQ, POWER_RESIDUE_MODULO_EQ_ALT, POWER_RESIDUE_MODULO_EQ }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Double prime powers and the other remaining positive cases 2 and 4.       -/
/- ------------------------------------------------------------------------- -/

structure Double where
  -- @@FIELDS
  PRIMITIVE_ROOT_MODULO_2 : thm
  PRIMITIVE_ROOT_MODULO_4 : thm
  PRIMITIVE_ROOT_DOUBLE_LEMMA : thm
  PRIMITIVE_ROOT_MODULO_DOUBLE_PRIMEPOW : thm
  deriving Inhabited

@[nospecialize]
def setupDouble [HolBase] (D : PrimitiveDeps) (BPrimePows2 : PrimePows2) :
    ExceptT String IO Double := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, CONG_CONV, NUMBER_RULE,
        NUM_REDUCE_CONV, .. } := D
  let { ARITH, CONG_CHINESE_EQ, COPRIME_2, .. } := D.core1
  let { EVEN_OR_ODD, FORALL_UNWIND_THM2, .. } := D.core2
  let { IN_NUMSEG, .. } := D.core3
  let { LE_1, LE_EXP, MULT_CLAUSES, NOT_ODD, ODD, ODD_ADD, ODD_EXP, ODD_MOD_2,
        ORDER_CONG, ORDER_UNIQUE, .. } := D.core4
  let { ORDER_WORKS, PHI_2, PHI_LOWERBOUND_1_STRONG, PHI_MULTIPLICATIVE, PHI_PRIME,
        PHI_PRIMEPOW, PRIME_2, PRIME_ODD, .. } := D.core5
  let { PRIMITIVE_ROOT_MODULO_PRIMEPOW, .. } := BPrimePows2
  -- @@SCOPE END

  let PRIMITIVE_ROOT_MODULO_2 ← prove
   r"?x. x IN 1..1 /\ order 2 x = phi(2)"
   (EXISTS_TAC (← q "1") THEN REWRITE_TAC [IN_NUMSEG, ARITH] THEN
    SIMP_TAC [PHI_PRIME, PRIME_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC ORDER_UNIQUE THEN
    REWRITE_TAC [← ARITH_RULE (← q r"~(0 < m /\ m < 1)")] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC (ONCE_DEPTH_CONV CONG_CONV) THEN
    REWRITE_TAC [])

  let PRIMITIVE_ROOT_MODULO_4 ← prove
   r"?x. x IN 1..3 /\ order 4 x = phi(4)"
   (← do
    let a2 ← ARITH_RULE (← q r"0 < m /\ m < 2 <=> m = 1")
    let a1 ← ARITH_RULE (← q r"4 = 2 EXP 2")
    pure (EXISTS_TAC (← q "3") THEN REWRITE_TAC [IN_NUMSEG, ARITH] THEN
    SUBST1_TAC a1 THEN
    SIMP_TAC [PHI_PRIMEPOW, PRIME_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC ORDER_UNIQUE THEN
    REWRITE_TAC [FORALL_UNWIND_THM2, a2] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC (ONCE_DEPTH_CONV CONG_CONV) THEN
    REWRITE_TAC []))

  let PRIMITIVE_ROOT_DOUBLE_LEMMA ← prove
   r"!n a. ODD n /\ ODD a /\ order n a = phi n
           ==> order (2 * n) a = phi(2 * n)"
   (REPEAT STRIP_TAC THEN MATCH_MP_TAC ORDER_UNIQUE THEN
    ASM_SIMP_TAC [CONG_CHINESE_EQ, COPRIME_2, PHI_MULTIPLICATIVE] THEN
    REWRITE_TAC [PHI_2, MULT_CLAUSES] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC [ODD, LE_1, PHI_LOWERBOUND_1_STRONG],
      ASM_REWRITE_TAC [← GSYM ODD_MOD_2, ODD_EXP],
      ASM_MESON_TAC [ORDER_WORKS],
      ASM_MESON_TAC [ORDER_WORKS]])

  let PRIMITIVE_ROOT_MODULO_DOUBLE_PRIMEPOW ← prove
   r"!p k. prime p /\ 3 <= p /\ 1 <= k
           ==> ?x. x IN 1..(2 * p EXP k - 1) /\
                   order (2 * p EXP k) x = phi(2 * p EXP k)"
   (← do
    let a2 ← ARITH_RULE
      (← q r"g <= x - 1 /\ p EXP 1 <= x ==> g + p <= 2 * x - 1")
    let a1 ← ARITH_RULE (← q r"3 <= p ==> ~(p = 2)")
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC (← SPEC (← q "p:num") PRIME_ODD) THEN
    ASM_SIMP_TAC [a1] THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP PRIMITIVE_ROOT_MODULO_PRIMEPOW) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "g:num") MP_TAC) THEN REWRITE_TAC [IN_NUMSEG] THEN
    STRIP_TAC THEN DISJ_CASES_TAC (← SPEC (← q "g:num") EVEN_OR_ODD) THENL
     [EXISTS_TAC (← q r"g + p EXP k") THEN CONJ_TAC THENL
       [CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
        MATCH_MP_TAC a2 THEN
        ASM_REWRITE_TAC [LE_EXP] THEN ASM_ARITH_TAC,
        ALL_TAC],
      EXISTS_TAC (← q "g:num") THEN CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC]] THEN
    MATCH_MP_TAC PRIMITIVE_ROOT_DOUBLE_LEMMA THEN
    ASM_REWRITE_TAC [ODD_ADD, ODD_EXP, NOT_ODD] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN MATCH_MP_TAC ORDER_CONG THEN
    CONV_TAC NUMBER_RULE))

  -- @@RETURN BEGIN
  return { PRIMITIVE_ROOT_MODULO_2, PRIMITIVE_ROOT_MODULO_4, PRIMITIVE_ROOT_DOUBLE_LEMMA,
           PRIMITIVE_ROOT_MODULO_DOUBLE_PRIMEPOW }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- A couple of degenerate case not usually considered.                       -/
/- ------------------------------------------------------------------------- -/

structure Degenerate where
  -- @@FIELDS
  PRIMITIVE_ROOT_MODULO_0 : thm
  PRIMITIVE_ROOT_MODULO_1 : thm
  deriving Inhabited

@[nospecialize]
def setupDegenerate [HolBase] (D : PrimitiveDeps) :
    ExceptT String IO Degenerate := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, .. } := D
  let { CONG_REFL, COPRIME_2, .. } := D.core1
  let { EXP_1, .. } := D.core2
  let { ODD, ORDER_EQ_0, ORDER_UNIQUE, .. } := D.core4
  let { PHI_0, PHI_1, .. } := D.core5
  -- @@SCOPE END

  let PRIMITIVE_ROOT_MODULO_0 ← prove
   r"(?x. order 0 x = phi(0))"
   (EXISTS_TAC (← q "2") THEN REWRITE_TAC [PHI_0, ORDER_EQ_0, COPRIME_2, ODD])

  let PRIMITIVE_ROOT_MODULO_1 ← prove
   r"?x. order 1 x = phi(1)"
   (EXISTS_TAC (← q "1") THEN REWRITE_TAC [PHI_1] THEN MATCH_MP_TAC ORDER_UNIQUE THEN
    REWRITE_TAC [← ARITH_RULE (← q r"0 < m /\ m < 1 <=> F"), EXP_1, CONG_REFL] THEN
    ARITH_TAC)

  -- @@RETURN BEGIN
  return { PRIMITIVE_ROOT_MODULO_0, PRIMITIVE_ROOT_MODULO_1 }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- The negative results.                                                     -/
/- ------------------------------------------------------------------------- -/

structure Negative where
  -- @@FIELDS
  CONG_TO_1_POW2 : thm
  NO_PRIMITIVE_ROOT_MODULO_POW2 : thm
  NO_PRIMITIVE_ROOT_MODULO_COMPOSITE : thm
  deriving Inhabited

@[nospecialize]
def setupNegative [HolBase] (D : PrimitiveDeps) :
    ExceptT String IO Negative := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, INDUCT_TAC, NUMBER_RULE, NUM_REDUCE_CONV, .. } := D
  let { ADD_CLAUSES, ADD_EQ_0, ARITH, CONG_CHINESE_EQ, CONG_EXP, CONG_TO_1, COPRIME_2,
        COPRIME_LEXP, DE_MORGAN_THM, .. } := D.core1
  let { EQ_MULT_LCANCEL, EVEN_ADD, EVEN_EXISTS, EVEN_EXP, EVEN_MULT, EVEN_OR_ODD,
        EVEN_PHI, EXP, EXP_ADD, EXP_EQ_0, EXP_EQ_1, EXP_EXP, EXP_MULT, EXP_ONE,
        FERMAT_LITTLE, .. } := D.core2
  let { LEFT_IMP_EXISTS_THM, LE_1, LE_MULT2, MULT_EQ_0, MULT_EQ_1, MULT_SYM, NOT_IMP,
        NOT_ODD, ODD_EXISTS, ORDER_EQ_0, .. } := D.core4
  let { ORDER_WORKS, PHI_LOWERBOUND_1_STRONG, PHI_LOWERBOUND_2, PHI_MULTIPLICATIVE,
        PHI_PRIMEPOW, PRIME_2, .. } := D.core5
  -- @@SCOPE END

  let CONG_TO_1_POW2 ← prove
   r"!k x. ODD x /\ 1 <= k ==> (x EXP (2 EXP k) == 1) (mod (2 EXP (k + 2)))"
   (← do
    let a3 ← ARITH_RULE
      (← q r"(1 + m * n) EXP 2 = 1 + q * 2 * n <=>
      n * m * (2 + m * n) = n * 2 * q")
    let r2 ← ONCE_REWRITE_RULE [MULT_SYM] EXP_MULT
    let a1 ← ARITH_RULE
      (← q r"SUC(2 * m) EXP 2 = 1 + q * 8 <=> m * (m + 1) = 2 * q")
    pure (INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES, EXP] THEN
    CONV_TAC NUM_REDUCE_CONV THEN GEN_TAC THEN ASM_CASES_TAC (← q r"k = 0") THENL
     [ASM_REWRITE_TAC [] THEN CONV_TAC NUM_REDUCE_CONV THEN
      SIMP_TAC [ODD_EXISTS, LEFT_IMP_EXISTS_THM] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC [CONG_TO_1] THEN DISJ2_TAC THEN
      REWRITE_TAC [← GSYM EVEN_EXISTS, a1] THEN
      REWRITE_TAC [EVEN_MULT, EVEN_ADD, ARITH] THEN CONV_TAC TAUT,
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC (← q "x:num")) THEN
      ASM_SIMP_TAC [r2, LE_1] THEN
      REWRITE_TAC [CONG_TO_1, EXP_EQ_1, ADD_EQ_0, MULT_EQ_1] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "m:num") SUBST1_TAC) THEN
      REWRITE_TAC [EQ_MULT_LCANCEL, EXP_EQ_0, ARITH, ← GSYM EVEN_EXISTS, a3] THEN
      REWRITE_TAC [EVEN_MULT, EVEN_ADD, EVEN_EXP, ARITH] THEN ARITH_TAC]))

  let NO_PRIMITIVE_ROOT_MODULO_POW2 ← prove
   r"!k. 3 <= k ==> ~(?x. order (2 EXP k) x = phi(2 EXP k))"
   (← do
    let a5 ← ARITH_RULE (← q r"x + x * 2 < x * 4 <=> ~(x = 0)")
    let a4 ← ARITH_RULE (← q r"a + b:num < c ==> a < c - b")
    let a3 ← ARITH_RULE (← q r"0 < x <=> ~(x = 0)")
    let a2 ← ARITH_RULE (← q r"3 <= k ==> ~(k = 0)")
    let a1 ← ARITH_RULE
      (← q r"a = b ==> 1 <= b /\ a = 0 ==> F")
    pure (REPEAT STRIP_TAC THEN DISJ_CASES_TAC (← SPEC (← q "x:num") EVEN_OR_ODD) THENL
     [FIRST_X_ASSUM (MP_TAC o MATCH_MP a1) THEN
      ASM_SIMP_TAC [ORDER_EQ_0, PHI_LOWERBOUND_1_STRONG, LE_1, EXP_EQ_0, ARITH,
                   COPRIME_LEXP, COPRIME_2, DE_MORGAN_THM, NOT_ODD] THEN
      ASM_ARITH_TAC,
      MP_TAC (← CONJUNCT2 (← ISPECL [← q r"2 EXP k", ← q "x:num"] ORDER_WORKS)) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o SPEC (← q r"2 EXP (k - 2)")) THEN
      ASM_SIMP_TAC [PHI_PRIMEPOW, PRIME_2, a2] THEN
      ABBREV_TAC (← q r"j = k - 2") THEN
      SUBGOAL_THEN (← q r"k - 1 = j + 1") SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      SUBGOAL_THEN (← q r"k = j + 2") SUBST1_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      SUBGOAL_THEN (← q r"1 <= j") ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      ASM_SIMP_TAC [CONG_TO_1_POW2, a3] THEN
      REWRITE_TAC [EXP_EQ_0, ARITH] THEN
      MATCH_MP_TAC a4 THEN
      REWRITE_TAC [EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC [a5] THEN
      REWRITE_TAC [EXP_EQ_0, ARITH]]))

  let NO_PRIMITIVE_ROOT_MODULO_COMPOSITE ← prove
   r"!a b. 3 <= a /\ 3 <= b /\ coprime(a,b)
           ==> ~(?x. order (a * b) x = phi(a * b))"
   (← do
    let a5 ← ARITH_RULE (← q r"3 <= p ==> 1 <= p")
    let a4 ← ARITH_RULE (← q r"((2 * a) * b) DIV 2 = b * a")
    let a3 ← ARITH_RULE (← q r"(a * 2 * b) DIV 2 = a * b")
    let a2 ← ARITH_RULE (← q r"2 * 2 <= x ==> 2 <= x")
    let a1 ← ARITH_RULE (← q r"0 < a DIV 2 /\ a DIV 2 < a <=> 2 <= a")
    pure (SIMP_TAC [PHI_MULTIPLICATIVE] THEN REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"a * b:num", ← q "x:num"] ORDER_WORKS) THEN
    ASM_SIMP_TAC [CONG_CHINESE_EQ] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"(phi a * phi b) DIV 2")) THEN
    REWRITE_TAC [a1, NOT_IMP] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC a2 THEN
      MATCH_MP_TAC LE_MULT2 THEN ASM_SIMP_TAC [PHI_LOWERBOUND_2],
      SUBGOAL_THEN (← q r"EVEN(phi b)") MP_TAC THENL
       [ASM_SIMP_TAC [EVEN_PHI], SIMP_TAC [EVEN_EXISTS, LEFT_IMP_EXISTS_THM]] THEN
      REWRITE_TAC [a3],
      SUBGOAL_THEN (← q r"EVEN(phi a)") MP_TAC THENL
       [ASM_SIMP_TAC [EVEN_PHI], SIMP_TAC [EVEN_EXISTS, LEFT_IMP_EXISTS_THM]] THEN
      REWRITE_TAC [a4]] THEN
    X_GEN_TAC (← q "m:num") THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC [← GSYM EXP_EXP] THEN SUBST1_TAC (← SYM (← SPEC (← q "m:num") EXP_ONE)) THEN
    MATCH_MP_TAC CONG_EXP THEN MATCH_MP_TAC FERMAT_LITTLE THEN
    MP_TAC (← ISPECL [← q r"a * b:num", ← q "x:num"] ORDER_EQ_0) THEN
    ASM_SIMP_TAC [MULT_EQ_0, LE_1, PHI_LOWERBOUND_1_STRONG, a5] THEN
    CONV_TAC NUMBER_RULE))

  -- @@RETURN BEGIN
  return { CONG_TO_1_POW2, NO_PRIMITIVE_ROOT_MODULO_POW2,
           NO_PRIMITIVE_ROOT_MODULO_COMPOSITE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Equivalences, one with some degenerate cases, one more conventional.      -/
/- ------------------------------------------------------------------------- -/

structure Equivalences where
  -- @@FIELDS
  PRIMITIVE_ROOT_EXISTS : thm
  PRIMITIVE_ROOT_EXISTS_NONTRIVIAL : thm
  deriving Inhabited

@[nospecialize]
def setupEquivalences [HolBase] (D : PrimitiveDeps) (BPrimePows2 : PrimePows2) (BDouble : Double) (BDegenerate : Degenerate) (BNegative : Negative) :
    ExceptT String IO Equivalences := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC,
        NUM_REDUCE_CONV, PRIME_CONV, .. } := D
  let { ARITH, COND_ID, CONG_MOD, CONTRAPOS_THM, COPRIME_2, COPRIME_LEXP, COPRIME_LMUL,
        COPRIME_REXP, COPRIME_RMUL, COPRIME_SYM, DE_MORGAN_THM, DIVIDES_MOD, .. } := D.core1
  let { DIVIDES_REFL, DIVISION, EQ_TRANS, EXP, EXP_1, EXP_EQ_0, EXP_EQ_1, EXP_MONO_LE,
        FUN_EQ_THM, .. } := D.core2
  let { IN_NUMSEG, .. } := D.core3
  let { LEFT_IMP_EXISTS_THM, LE_1, LE_EXP, LE_TRANS, MULT_AC, MULT_CLAUSES, MULT_EQ_0,
        MULT_EQ_1, MULT_SYM, NOT_EXISTS_THM, ORDER_CONG, ORDER_EQ_0, .. } := D.core4
  let { PHI_LOWERBOUND_1_STRONG, PRIMEPOW_FACTOR, PRIME_GE_2, PRIME_IMP_NZ, coprime, .. } := D.core5
  let { PRIMITIVE_ROOT_MODULO_PRIMEPOW, .. } := BPrimePows2
  let { PRIMITIVE_ROOT_MODULO_2, PRIMITIVE_ROOT_MODULO_4,
        PRIMITIVE_ROOT_MODULO_DOUBLE_PRIMEPOW, .. } := BDouble
  let { PRIMITIVE_ROOT_MODULO_0, PRIMITIVE_ROOT_MODULO_1, .. } := BDegenerate
  let { NO_PRIMITIVE_ROOT_MODULO_COMPOSITE, NO_PRIMITIVE_ROOT_MODULO_POW2, .. } := BNegative
  -- @@SCOPE END

  let PRIMITIVE_ROOT_EXISTS ← prove
   r"!n. (?x. order n x = phi n) <=>
         n = 0 \/ n = 2 \/ n = 4 \/
         ?p k. prime p /\ 3 <= p /\ (n = p EXP k \/ n = 2 * p EXP k)"
   (← do
    let a8 ← ARITH_RULE (← q r"3 <= r * 2 <=> ~(r = 0 \/ r = 1)")
    let a7 ← ARITH_RULE (← q r"~(p = 2) /\ 2 <= p ==> 3 <= p")
    let a6 ← ARITH_RULE (← q r"2 EXP 2 <= x ==> 3 <= x")
    let a5 ← ARITH_RULE (← q r"~(3 <= k) ==> 1 <= k ==> k = 1 \/ k = 2")
    let a4 ← ARITH_RULE (← q r"2 <= p ==> (~(3 <= p) <=> p = 2)")
    let t3 ← TAUT (← q r"~(a /\ b /\ c) <=> a /\ b ==> ~c")
    pure (GEN_TAC THEN
    ASM_CASES_TAC (← q "n = 0") THEN ASM_REWRITE_TAC [PRIMITIVE_ROOT_MODULO_0] THEN
    ASM_CASES_TAC (← q "n = 2") THENL
     [ASM_MESON_TAC [PRIMITIVE_ROOT_MODULO_2], ALL_TAC] THEN
    ASM_CASES_TAC (← q "n = 4") THENL
     [ASM_MESON_TAC [PRIMITIVE_ROOT_MODULO_4], ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN ASM_CASES_TAC (← q "n = 1") THENL
     [ASM_REWRITE_TAC [PRIMITIVE_ROOT_MODULO_1] THEN
      MAP_EVERY EXISTS_TAC [(← q "3"), (← q "0")] THEN
      CONV_TAC (ONCE_DEPTH_CONV PRIME_CONV) THEN CONV_TAC NUM_REDUCE_CONV,
      ALL_TAC] THEN
    EQ_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [(← q "p:num"), (← q "k:num")] THEN
      ASM_CASES_TAC (← q "k = 0") THEN ASM_REWRITE_TAC [EXP, MULT_CLAUSES] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      ASM_MESON_TAC [LE_1, PRIMITIVE_ROOT_MODULO_PRIMEPOW,
                    PRIMITIVE_ROOT_MODULO_DOUBLE_PRIMEPOW]] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [NOT_EXISTS_THM, t3] THEN
    REWRITE_TAC [DE_MORGAN_THM] THEN STRIP_TAC THEN
    MP_TAC (← ISPEC (← q "n:num") PRIMEPOW_FACTOR) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [(← q "p:num"), (← q "k:num"), (← q "m:num")] THEN
    ASM_CASES_TAC (← q "m = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN
    ASM_CASES_TAC (← q "m = 1") THENL
     [ASM_REWRITE_TAC [MULT_CLAUSES] THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [(← q "p:num"), (← q "k:num")]) THEN
      ASM_SIMP_TAC [PRIME_GE_2, a4] THEN
      DISCH_THEN SUBST_ALL_TAC THEN ASM_CASES_TAC (← q "3 <= k") THENL
       [ASM_MESON_TAC [NO_PRIMITIVE_ROOT_MODULO_POW2], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o MATCH_MP a5) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN (DISJ_CASES_THEN SUBST_ALL_TAC) THEN
      REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC NUM_REDUCE_CONV,
      ALL_TAC] THEN
    ASM_CASES_TAC (← q "m = 2") THENL
     [ASM_REWRITE_TAC [COPRIME_2] THEN
      ASM_CASES_TAC (← q "p = 2") THEN ASM_REWRITE_TAC [ARITH] THEN
      STRIP_TAC THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
      SUBGOAL_THEN (← q "3 <= p") ASSUME_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      ASM_MESON_TAC [MULT_SYM],
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q "k = 1") THENL
     [UNDISCH_THEN (← q "k = 1") SUBST_ALL_TAC,
      MP_TAC (← SPECL [(← q "p EXP k"), (← q "m:num")] NO_PRIMITIVE_ROOT_MODULO_COMPOSITE) THEN
      REWRITE_TAC [NOT_EXISTS_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [COPRIME_LEXP] THEN
      CONJ_TAC THENL [ALL_TAC, ASM_ARITH_TAC] THEN
      MATCH_MP_TAC a6 THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q "p EXP 2") THEN
      ASM_REWRITE_TAC [EXP_MONO_LE, LE_EXP] THEN
      ASM_SIMP_TAC [PRIME_GE_2, PRIME_IMP_NZ] THEN ASM_ARITH_TAC] THEN
    ASM_CASES_TAC (← q "p = 2") THENL
     [UNDISCH_THEN (← q "p = 2") SUBST_ALL_TAC,
      MP_TAC (← SPECL [(← q "p EXP 1"), (← q "m:num")] NO_PRIMITIVE_ROOT_MODULO_COMPOSITE) THEN
      REWRITE_TAC [NOT_EXISTS_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [COPRIME_LEXP] THEN REWRITE_TAC [EXP_1] THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP PRIME_GE_2) THEN ASM_ARITH_TAC] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [EXP_1]) THEN REWRITE_TAC [EXP_1] THEN
    MP_TAC (← ISPEC (← q "m:num") PRIMEPOW_FACTOR) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC, REWRITE_TAC [LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [(← q "q:num"), (← q "j:num"), (← q "r:num")] THEN
    ASM_CASES_TAC (← q "r = 0") THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN
    STRIP_TAC THEN UNDISCH_TAC (← q "coprime(2,m)") THEN
    ASM_SIMP_TAC [COPRIME_RMUL, COPRIME_REXP, LE_1] THEN
    REWRITE_TAC [COPRIME_2] THEN STRIP_TAC THEN
    SUBGOAL_THEN (← q "3 <= q") ASSUME_TAC THENL
     [MATCH_MP_TAC a7 THEN
      ASM_SIMP_TAC [PRIME_GE_2] THEN DISCH_TAC THEN
      UNDISCH_TAC (← q "ODD q") THEN ASM_REWRITE_TAC [ARITH],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [(← q "q:num"), (← q "j:num")]) THEN
    ASM_CASES_TAC (← q "r = 1") THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN STRIP_TAC THEN
    MP_TAC (← SPECL [(← q "2 * r"), (← q "q EXP j")] NO_PRIMITIVE_ROOT_MODULO_COMPOSITE) THEN
    REWRITE_TAC [COPRIME_LMUL, COPRIME_REXP] THEN ASM_REWRITE_TAC [COPRIME_2] THEN
    ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [MULT_AC, NOT_EXISTS_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [a8] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC (← q "q EXP 1") THEN
    ASM_REWRITE_TAC [LE_EXP, ARITH, COND_ID] THEN ASM_REWRITE_TAC [EXP_1]))

  let PRIMITIVE_ROOT_EXISTS_NONTRIVIAL ← prove
   r"!n. (?x. x IN 1..n-1 /\ order n x = phi n) <=>
         n = 2 \/ n = 4 \/
         ?p k. prime p /\ 3 <= p /\ 1 <= k /\ (n = p EXP k \/ n = 2 * p EXP k)"
   (← do
    let a4 ← ARITH_RULE (← q r"1 <= x <=> ~(x = 0)")
    let a3 ← ARITH_RULE (← q r"~(n = 0) /\ ~(n = 1) ==> (x <= n - 1 <=> x < n)")
    let t2 ← TAUT (← q r"~a /\ ~b ==> (a <=> b)")
    let t1 ← TAUT (← q r"~a /\ ~b ==> (a <=> b)")
    pure (GEN_TAC THEN ASM_CASES_TAC (← q "n = 0") THENL
     [ASM_REWRITE_TAC [IN_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC t1 THEN
      CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
      REWRITE_TAC [MULT_EQ_0, EXP_EQ_0] THEN ARITH_TAC,
      ALL_TAC] THEN
    ASM_CASES_TAC (← q "n = 1") THENL
     [ASM_REWRITE_TAC [IN_NUMSEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC t2 THEN
      CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
      REWRITE_TAC [MULT_EQ_1, EXP_EQ_1] THEN ARITH_TAC,
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (← q "?x. order n x = phi n") THEN CONJ_TAC THENL
     [EQ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "x:num")) THEN EXISTS_TAC (← q "x MOD n") THEN
      ASM_SIMP_TAC [IN_NUMSEG, DIVISION, a3] THEN
      CONJ_TAC THENL
       [REWRITE_TAC [a4] THEN
        ASM_SIMP_TAC [← GSYM DIVIDES_MOD] THEN DISCH_TAC THEN
        MP_TAC (← SPECL [(← q "n:num"), (← q "x:num")] ORDER_EQ_0) THEN
        ASM_SIMP_TAC [LE_1, PHI_LOWERBOUND_1_STRONG] THEN
        REWRITE_TAC [coprime] THEN DISCH_THEN (MP_TAC o SPEC (← q "n:num")) THEN
        ASM_REWRITE_TAC [DIVIDES_REFL],
        FIRST_ASSUM (SUBST1_TAC o SYM) THEN MATCH_MP_TAC ORDER_CONG THEN
        ASM_SIMP_TAC [CONG_MOD]],
      ASM_REWRITE_TAC [PRIMITIVE_ROOT_EXISTS] THEN
      ASM_CASES_TAC (← q "n = 2") THEN ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC (← q "n = 4") THEN ASM_REWRITE_TAC [] THEN
      AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q "p:num") THEN
      AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN X_GEN_TAC (← q "k:num") THEN
      CONV_TAC (BINOP_CONV (ONCE_DEPTH_CONV SYM_CONV)) THEN
      ASM_CASES_TAC (← q "k = 0") THEN ASM_SIMP_TAC [LE_1] THEN
      AP_TERM_TAC THEN ASM_ARITH_TAC]))

  -- @@RETURN BEGIN
  return { PRIMITIVE_ROOT_EXISTS, PRIMITIVE_ROOT_EXISTS_NONTRIVIAL }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- If there are any primitive roots mod n, there are exactly phi(phi n).     -/
/- ------------------------------------------------------------------------- -/

structure CountPrimitiveRoots where
  -- @@FIELDS
  COUNT_PRIMITIVE_ROOTS_ALT : thm
  COUNT_PRIMITIVE_ROOTS : thm
  deriving Inhabited

@[nospecialize]
def setupCountPrimitiveRoots [HolBase] (D : PrimitiveDeps) (BEquivalences : Equivalences) :
    ExceptT String IO CountPrimitiveRoots := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, MESON_TAC, NUMBER_RULE, NUM_RING, SET_RULE, SET_TAC, .. } := D
  let { CARD_CLAUSES, CARD_NUMSEG_LT, COND_ID, CONG, CONG_IMP_EQ, COPRIME_0,
        COPRIME_GCD, COPRIME_REXP, COPRIME_RMOD, COPRIME_SYM, .. } := D.core1
  let { DIV_1, DIV_MULT, EMPTY_GSPEC, EQ_IMP, EXTENSION, FINITE_EMPTY,
        FINITE_NUMSEG_LT, FINITE_RESTRICT, FINITE_SUBSET, FORALL_IN_IMAGE, GCD_ONE,
        HAS_SIZE, HAS_SIZE_IMAGE_INJ_RESTRICT, .. } := D.core2
  let { IN_ELIM_THM, .. } := D.core3
  let { LEFT_IMP_EXISTS_THM, LT, MOD_LT_EQ, MULT_CLAUSES, NOT_EXISTS_THM,
        ORDER_DIVIDES_EXPDIFF, ORDER_EQ_0, ORDER_EXP_GEN, ORDER_MOD, .. } := D.core4
  let { PHI_0, PHI_ALT, PHI_EQ_0, SUBSET, divides, .. } := D.core5
  let { PRIMITIVE_ROOT_EXISTS, .. } := BEquivalences
  -- @@SCOPE END

  let COUNT_PRIMITIVE_ROOTS_ALT ← prove
   r"!n. {a | a < n /\ coprime(n,a) /\ order n a = phi n} HAS_SIZE
         (if n = 0 \/ n = 2 \/ n = 4 \/
             ?p k. prime p /\ 3 <= p /\ (n = p EXP k \/ n = 2 * p EXP k)
          then phi(phi n) else 0)"
   (← do
    let n5 ← NUM_RING (← q r"d * p = p ==> d = 1 \/ p = 0")
    let n4 ← NUMBER_RULE (← q "gcd(phi n,a) divides phi n")
    let s2 ← SET_RULE (← q r"{x | P x /\ Q x} = {x | x IN {y | P y} /\ Q x}")
    let s1 ← SET_RULE (← q r"{x | P x /\ Q x /\ R x} = {x | x IN {y | P y /\ Q y} /\ R x}")
    pure (GEN_TAC THEN ASM_CASES_TAC (← q "n = 0") THENL
     [ASM_REWRITE_TAC [LT, PHI_0, COND_ID, EMPTY_GSPEC] THEN
      REWRITE_TAC [HAS_SIZE, CARD_CLAUSES, FINITE_EMPTY],
      REWRITE_TAC [← GSYM PRIMITIVE_ROOT_EXISTS]] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM (X_CHOOSE_TAC (← q "g:num")),
      RULE_ASSUM_TAC (REWRITE_RULE [NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC [EMPTY_GSPEC, HAS_SIZE, CARD_CLAUSES, FINITE_EMPTY]] THEN
    SUBGOAL_THEN (← q "coprime(n:num,g)") ASSUME_TAC THENL
     [ASM_MESON_TAC [ORDER_EQ_0, PHI_EQ_0], ALL_TAC] THEN
    ONCE_REWRITE_TAC [s1] THEN
    MATCH_MP_TAC (← ISPEC (← q r"\i. (g EXP i) MOD n") HAS_SIZE_IMAGE_INJ_RESTRICT) THEN
    EXISTS_TAC (← q "{i | i < phi n}") THEN
    REWRITE_TAC [IN_ELIM_THM, FINITE_NUMSEG_LT, CARD_NUMSEG_LT] THEN
    REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC [s2] THEN
      SIMP_TAC [FINITE_RESTRICT, FINITE_NUMSEG_LT],
      ONCE_REWRITE_TAC [COPRIME_SYM] THEN REWRITE_TAC [PHI_ALT] THEN
      AP_TERM_TAC THEN SET_TAC [],
      ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, MOD_LT_EQ] THEN
      ASM_REWRITE_TAC [COPRIME_REXP, COPRIME_RMOD],
      REWRITE_TAC [← GSYM CONG] THEN ASM_SIMP_TAC [ORDER_DIVIDES_EXPDIFF] THEN
      REWRITE_TAC [CONG_IMP_EQ],
      REWRITE_TAC [ORDER_MOD]] THEN
    SUBGOAL_THEN
     (← q r"{a | a < phi n /\ order n (g EXP a) = phi n} =
      {a | coprime(a,phi n) /\ a < phi n}")
    SUBST1_TAC THENL
     [ALL_TAC,
      REWRITE_TAC [HAS_SIZE, ← GSYM PHI_ALT] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q "{a | a < phi n}") THEN
      REWRITE_TAC [FINITE_NUMSEG_LT] THEN SET_TAC []] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC (← q "a:num") THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    ASM_CASES_TAC (← q "a < phi n") THEN ASM_REWRITE_TAC [ORDER_EXP_GEN] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC [COPRIME_0], ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [COPRIME_SYM] THEN EQ_TAC THEN
    SIMP_TAC [GCD_ONE, DIV_1] THEN
    MP_TAC n4 THEN
    REWRITE_TAC [divides, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q "e:num") THEN ABBREV_TAC (← q "d = gcd(phi n,a)") THEN
    DISCH_THEN (fun th => tactic_of do pure (SUBST1_TAC th THEN ASSUME_TAC (← SYM th))) THEN
    ASM_CASES_TAC (← q "d = 0") THENL
     [ASM_MESON_TAC [MULT_CLAUSES, PHI_EQ_0], ALL_TAC] THEN
    ASM_SIMP_TAC [DIV_MULT] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP n5) THEN
    ASM_REWRITE_TAC [PHI_EQ_0, COPRIME_GCD]))

  let COUNT_PRIMITIVE_ROOTS ← prove
   r"!n. {x | x < n /\ order n x = phi n} HAS_SIZE
         (if n = 0 \/ n = 2 \/ n = 4 \/
             ?p k. prime p /\ 3 <= p /\ (n = p EXP k \/ n = 2 * p EXP k)
          then phi(phi n) else 0)"
   (GEN_TAC THEN MP_TAC (← SPEC (← q "n:num") COUNT_PRIMITIVE_ROOTS_ALT) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    MESON_TAC [ORDER_EQ_0, PHI_EQ_0, LT])

  -- @@RETURN BEGIN
  return { COUNT_PRIMITIVE_ROOTS_ALT, COUNT_PRIMITIVE_ROOTS }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Counting roots, roots of unity and power residues.                        -/
/- ------------------------------------------------------------------------- -/

/- ------------------------------------------------------------------------- -/
/- Counting roots, roots of unity and power residues.                        -/
/- ------------------------------------------------------------------------- -/

structure CountRoots where
  -- @@FIELDS
  COUNT_ROOTS_MODULO_PRIMITIVE_GEN_ALT : thm
  COUNT_ROOTS_MODULO_PRIMITIVE_GEN : thm
  POWER_RESIDUE_MODULO_PRIMITIVE : thm
  POWER_RESIDUE_MODULO_PRIME_EQ : thm
  POWER_RESIDUE_MODULO_PRIMITIVE_ORDER_ALT : thm
  POWER_RESIDUE_MODULO_PRIMITIVE_ORDER : thm
  QUADRATIC_RESIDUE_MODULO_PRIMITIVE_ORDER : thm
  POWER_RESIDUE_MODULO_PRIMITIVE_POWER : thm
  QUADRATIC_RESIDUE_MODULO_PRIMITIVE_POWER : thm
  COUNT_POWER_RESIDUES_MODULO_PRIMITIVE : thm
  COUNT_QUADRATIC_RESIDUES_MODULO_PRIMITIVE : thm
  deriving Inhabited

@[nospecialize]
def setupCountRoots [HolBase] (D : PrimitiveDeps) (BPrimitiveRoots : PrimitiveRoots) :
    ExceptT String IO CountRoots := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, MESON, MESON_TAC, NUMBER_RULE, SET_RULE, SET_TAC, .. } := D
  let { CARD_CLAUSES, CARD_NUMSEG_LT, CONG, CONG_COPRIME, CONG_IMP_EQ, CONG_MOD_0,
        CONG_REFL, CONG_SYM, CONG_TRANS, CONJ_ASSOC, CONJ_SYM, CONTRAPOS_THM,
        COPRIME_0, COPRIME_1, COPRIME_REXP, COPRIME_RMOD, COPRIME_SYM,
        COUNT_CONG_SOLVE, DIVIDES_0, DIVIDES_1, DIVIDES_2, DIVIDES_DIVIDES_DIV,
        DIVIDES_DIV_SELF, DIVIDES_GCD_LEFT, .. } := D.core1
  let { DIVIDES_RMUL2_EQ, DIV_1, DIV_BY_DIV, DIV_EQ_0, DIV_MULT, DIV_REFL, EMPTY_GSPEC,
        EQ_IMP, EVEN_PHI, EVEN_PHI_EQ, EXP, EXP_1, EXP_EXP, EXP_ONE, EXTENSION,
        FINITE_EMPTY, FINITE_NUMSEG_LT, FINITE_RESTRICT, FINITE_SUBSET,
        FORALL_IN_IMAGE, GCD, GCD_0, GCD_2_CASES, GCD_LE, GCD_ZERO, HAS_SIZE,
        HAS_SIZE_0, HAS_SIZE_IMAGE_INJ_RESTRICT, .. } := D.core2
  let { IN_ELIM_THM, .. } := D.core3
  let { MOD_EXP_MOD, MOD_LT_EQ, MULT_CLAUSES, MULT_SYM, NOT_EXISTS_THM, NOT_IMP,
        NOT_IN_EMPTY, NOT_LE, ORDER_DIVIDES, ORDER_DIVIDES_EXPDIFF, ORDER_DIVIDES_PHI,
        ORDER_EQ_0, ORDER_EXP_GEN, .. } := D.core4
  let { PHI_ALT, PHI_EQ_0, PHI_PRIME, PRIME_COPRIME_EQ, SUBSET,
        SURJECTIVE_IFF_INJECTIVE_GEN, divides, .. } := D.core5
  let { PRIMITIVE_ROOT_MODULO_PRIME, .. } := BPrimitiveRoots
  -- @@SCOPE END

  let COUNT_ROOTS_MODULO_PRIMITIVE_GEN_ALT ← prove
   r"!n a k.
        ~(n = 0) /\ (?x. order n x = phi n)
        ==> {x | x < n /\ coprime(n,x) /\ (x EXP k == a) (mod n)} HAS_SIZE
            (if (a EXP (phi n DIV gcd(k,phi n)) == 1) (mod n)
             then gcd(k,phi n) else 0)"
   (← do
    let n7 ← NUMBER_RULE (← q r"gcd(k,n) = d /\ d * p = n ==> gcd(n,k) = d")
    let n6 ← NUMBER_RULE (← q r"gcd(k,phi(n)) divides phi(n)")
    let s5 ← SET_RULE (← q r"{x | P x /\ Q x} = {x | x IN {y | P y} /\ Q x}")
    let s4 ← SET_RULE (← q r"{x | P x /\ Q x} = {x | x IN {y | P y} /\ Q x}")
    let s3 ← SET_RULE
      (← q r"{x | P x /\ Q x /\ R x} = {x | x IN {y | P y /\ Q y} /\ R x}")
    let m2 ← MESON [CONG_COPRIME]
      (← q r"(x == a) (mod n) <=>
      (x == a) (mod n) /\ (coprime(n,x) <=> coprime(n,a))")
    let n1 ← NUMBER_RULE (← q r"(1 == a) (mod n) <=> (a == 1) (mod n)")
    pure (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_CASES_TAC (← q "k = 0") THENL
     [DISCH_THEN (K ALL_TAC) THEN
      ASM_SIMP_TAC [GCD_0, DIV_REFL, PHI_EQ_0, EXP_1, EXP] THEN
      ONCE_REWRITE_TAC [n1] THEN
      ASM_CASES_TAC (← q r"(a == 1) (mod n)") THEN
      ASM_REWRITE_TAC [EMPTY_GSPEC, HAS_SIZE, FINITE_EMPTY, CARD_CLAUSES] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"{x:num | x < n}") THEN
        REWRITE_TAC [FINITE_NUMSEG_LT] THEN SET_TAC [],
        ONCE_REWRITE_TAC [CONJ_SYM] THEN ONCE_REWRITE_TAC [COPRIME_SYM] THEN
        REWRITE_TAC [PHI_ALT]],
      DISCH_THEN (X_CHOOSE_TAC (← q "g:num"))] THEN
    ASM_CASES_TAC (← q r"coprime(n:num,a)") THENL
     [ALL_TAC,
      ONCE_REWRITE_TAC [m2] THEN
      ASM_REWRITE_TAC [COPRIME_REXP, COPRIME_1] THEN
      ASM_SIMP_TAC [DIV_EQ_0, GCD_ZERO] THEN
      ASM_REWRITE_TAC [← GSYM NOT_LE, GCD_LE, PHI_EQ_0, HAS_SIZE_0] THEN
      SET_TAC []] THEN
    SUBGOAL_THEN (← q r"coprime(n:num,g)") ASSUME_TAC THENL
     [ASM_MESON_TAC [ORDER_EQ_0, PHI_EQ_0], ALL_TAC] THEN
    ONCE_REWRITE_TAC [s3] THEN
    MATCH_MP_TAC (← ISPEC (← q r"\i. (g EXP i) MOD n") HAS_SIZE_IMAGE_INJ_RESTRICT) THEN
    EXISTS_TAC (← q "{i | i < phi n}") THEN
    REWRITE_TAC [IN_ELIM_THM, FINITE_NUMSEG_LT, CARD_NUMSEG_LT] THEN
    REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC [s4] THEN
      SIMP_TAC [FINITE_RESTRICT, FINITE_NUMSEG_LT],
      ONCE_REWRITE_TAC [COPRIME_SYM] THEN REWRITE_TAC [PHI_ALT] THEN
      AP_TERM_TAC THEN SET_TAC [],
      ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, MOD_LT_EQ] THEN
      ASM_REWRITE_TAC [COPRIME_REXP, COPRIME_RMOD],
      REWRITE_TAC [← GSYM CONG] THEN ASM_SIMP_TAC [ORDER_DIVIDES_EXPDIFF] THEN
      REWRITE_TAC [CONG_IMP_EQ],
      REWRITE_TAC [CONG, MOD_EXP_MOD] THEN REWRITE_TAC [← GSYM CONG, EXP_EXP]] THEN
    SUBGOAL_THEN (← q r"?r. r < phi n /\ (g EXP r == a) (mod n)") STRIP_ASSUME_TAC THENL
     [MP_TAC (← ISPECL [(← q "{i | i < phi n}"), (← q r"{x:num | x < n /\ coprime(n,x)}"),
               (← q r"\i. (g EXP i) MOD n")] SURJECTIVE_IFF_INJECTIVE_GEN) THEN
      REWRITE_TAC [IN_ELIM_THM, FINITE_NUMSEG_LT, CARD_NUMSEG_LT] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ONCE_REWRITE_TAC [s5] THEN
          SIMP_TAC [FINITE_RESTRICT, FINITE_NUMSEG_LT],
          ONCE_REWRITE_TAC [COPRIME_SYM] THEN REWRITE_TAC [PHI_ALT] THEN
          AP_TERM_TAC THEN SET_TAC [],
          ASM_REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, IN_ELIM_THM, MOD_LT_EQ] THEN
          ASM_REWRITE_TAC [COPRIME_REXP, COPRIME_RMOD]],
        DISCH_THEN (fun th => tactic_of do let p ← EQ_IMP_RULE th; pure (MP_TAC p.2)) THEN ANTS_TAC THENL
         [REWRITE_TAC [← GSYM CONG] THEN ASM_SIMP_TAC [ORDER_DIVIDES_EXPDIFF] THEN
          REWRITE_TAC [CONG_IMP_EQ],
          DISCH_THEN (MP_TAC o SPEC (← q "a MOD n")) THEN
          ASM_REWRITE_TAC [MOD_LT_EQ, COPRIME_RMOD, CONG]]],
      ALL_TAC] THEN
    SUBGOAL_THEN
     (← q r"!d:num. (g EXP (d * k) == a) (mod n) <=>
            (g EXP (d * k) == g EXP r) (mod n)")
     (fun th => REWRITE_TAC [th])
    THENL
     [ASM_MESON_TAC [CONG_SYM, CONG_REFL, CONG_TRANS],
      ASM_SIMP_TAC [ORDER_DIVIDES_EXPDIFF]] THEN
    SUBGOAL_THEN
     (← q r"!i:num. (a EXP i == 1) (mod n) <=> (g EXP (r * i) == 1) (mod n)")
     (fun th => REWRITE_TAC [th])
    THENL
     [X_GEN_TAC (← q "i:num") THEN REWRITE_TAC [← GSYM EXP_EXP, CONG] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [CONG]) THEN ASM_MESON_TAC [MOD_EXP_MOD],
      ALL_TAC] THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN
    REWRITE_TAC [HAS_SIZE, ← REWRITE_RULE [HAS_SIZE] COUNT_CONG_SOLVE] THEN
    ASM_REWRITE_TAC [PHI_EQ_0, ORDER_DIVIDES] THEN
    MP_TAC n6 THEN
    GEN_REWRITE_TAC LAND_CONV [divides] THEN
    ABBREV_TAC (← q "d = gcd(k,phi n)") THEN DISCH_THEN (X_CHOOSE_THEN (← q "p:num")
     (fun th => tactic_of do pure (ASSUME_TAC (← SYM th) THEN SUBST1_TAC th))) THEN
    ASM_CASES_TAC (← q "d = 0") THENL [ASM_MESON_TAC [GCD_ZERO, PHI_EQ_0], ALL_TAC] THEN
    ASM_SIMP_TAC [DIV_MULT] THEN ONCE_REWRITE_TAC [MULT_SYM] THEN
    SUBST1_TAC (← SYM (← ASSUME (← q "d * p = phi n"))) THEN
    ASM_CASES_TAC (← q "p = 0") THENL
     [ASM_MESON_TAC [MULT_CLAUSES, PHI_EQ_0], ALL_TAC] THEN
    ASM_SIMP_TAC [DIVIDES_RMUL2_EQ] THEN
    ASM_MESON_TAC [n7]))

  let COUNT_ROOTS_MODULO_PRIMITIVE_GEN ← prove
   r"!n a k.
        ~(n = 0) /\ ~(k = 0) /\ coprime(n,a) /\ (?x. order n x = phi n)
        ==> {x | x < n /\ (x EXP k == a) (mod n)} HAS_SIZE
            (if (a EXP (phi n DIV gcd(k,phi n)) == 1) (mod n)
             then gcd(k,phi n) else 0)"
   (REPEAT GEN_TAC THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    MP_TAC (← SPECL [(← q "n:num"), (← q "a:num"), (← q "k:num")]
          COUNT_ROOTS_MODULO_PRIMITIVE_GEN_ALT) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC [IN_ELIM_THM] THEN
    GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP CONG_COPRIME) THEN
    ASM_REWRITE_TAC [COPRIME_REXP])

  let POWER_RESIDUE_MODULO_PRIMITIVE ← prove
   r"!n a k.
        coprime(n,a) /\ (?x. order n x = phi n)
        ==> ((?x. (x EXP k == a) (mod n)) <=>
             (a EXP (phi n DIV gcd(k,phi n)) == 1) (mod n))"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "n = 0") THENL
     [ASM_REWRITE_TAC [COPRIME_0] THEN DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN
      REWRITE_TAC [EXP_ONE, CONG_MOD_0] THEN MESON_TAC [EXP_ONE],
      DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)] THEN
    ASM_CASES_TAC (← q "k = 0") THENL
     [ASM_SIMP_TAC [GCD_0, DIV_REFL, PHI_EQ_0, EXP_1, EXP] THEN
      REWRITE_TAC [CONG_SYM],
      ALL_TAC] THEN
    MP_TAC (← SPECL [(← q "n:num"), (← q "a:num"), (← q "k:num")]
          COUNT_ROOTS_MODULO_PRIMITIVE_GEN) THEN
    ASM_REWRITE_TAC [] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
     [GEN_REWRITE_TAC id [← GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC [NOT_EXISTS_THM] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [HAS_SIZE, EMPTY_GSPEC, CARD_CLAUSES, FINITE_EMPTY] THEN
      ASM_MESON_TAC [GCD_ZERO, PHI_EQ_0],
      REWRITE_TAC [HAS_SIZE_0, EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY] THEN
      REWRITE_TAC [← GSYM NOT_EXISTS_THM, CONTRAPOS_THM] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "x:num")) THEN EXISTS_TAC (← q "x MOD n") THEN
      ASM_REWRITE_TAC [MOD_LT_EQ] THEN REWRITE_TAC [CONG] THEN
      REWRITE_TAC [MOD_EXP_MOD] THEN ASM_REWRITE_TAC [← GSYM CONG]])

  let POWER_RESIDUE_MODULO_PRIME_EQ ← prove
   r"!p a k.
        prime p /\ ~(p divides a)
        ==> ((?x. (x EXP k == a) (mod p)) <=>
             (a EXP ((p - 1) DIV gcd(k,p - 1)) == 1) (mod p))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [(← q "p:num"), (← q "a:num"), (← q "k:num")] POWER_RESIDUE_MODULO_PRIMITIVE) THEN
    ASM_SIMP_TAC [PHI_PRIME, PRIME_COPRIME_EQ] THEN
    ASM_MESON_TAC [PRIMITIVE_ROOT_MODULO_PRIME])

  let POWER_RESIDUE_MODULO_PRIMITIVE_ORDER_ALT ← prove
   r"!n a k.
        coprime(n,a) /\ (?x. order n x = phi n)
        ==> ((?x. (x EXP k == a) (mod n)) <=>
             order n a divides phi n DIV gcd (k,phi n))"
   (SIMP_TAC [POWER_RESIDUE_MODULO_PRIMITIVE, ORDER_DIVIDES])

  let POWER_RESIDUE_MODULO_PRIMITIVE_ORDER ← prove
   r"!n a k.
        coprime(n,a) /\ (?x. order n x = phi n)
        ==> ((?x. (x EXP k == a) (mod n)) <=>
             gcd(k,phi n) divides phi n DIV order n a)"
   (ASM_SIMP_TAC [POWER_RESIDUE_MODULO_PRIMITIVE_ORDER_ALT] THEN
    SIMP_TAC [DIVIDES_DIVIDES_DIV, GCD, ORDER_DIVIDES_PHI] THEN
    REWRITE_TAC [MULT_SYM])

  let QUADRATIC_RESIDUE_MODULO_PRIMITIVE_ORDER ← prove
   r"!n a. coprime(n,a) /\ 3 <= n /\ (?x. order n x = phi n)
         ==> ((?x. (x EXP 2 == a) (mod n)) <=> EVEN(phi n DIV order n a))"
   (← do
    let n1 ← NUMBER_RULE (← q r"(a:num) divides b ==> gcd(a,b) = a")
    pure (REPEAT GEN_TAC THEN
    SIMP_TAC [POWER_RESIDUE_MODULO_PRIMITIVE_ORDER] THEN
    SIMP_TAC [← GSYM DIVIDES_2, ← REWRITE_RULE [← GSYM DIVIDES_2] EVEN_PHI,
             n1]))

  let POWER_RESIDUE_MODULO_PRIMITIVE_POWER ← prove
   r"!n g m k.
        coprime(n,g) /\ order n g = phi n
        ==> ((?x. (x EXP k == g EXP m) (mod n)) <=> gcd(k,phi n) divides m)"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q "n = 0") THENL
     [ASM_MESON_TAC [PHI_EQ_0, ORDER_EQ_0], ALL_TAC] THEN
    W (MP_TAC o PART_MATCH (lhand o rand) POWER_RESIDUE_MODULO_PRIMITIVE_ORDER o
          lhand o snd) THEN
    ANTS_TAC THENL [ASM_MESON_TAC [COPRIME_REXP], DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC [ORDER_EXP_GEN] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [GCD, DIV_1, DIVIDES_0] THEN
    ASM_SIMP_TAC [DIV_BY_DIV, PHI_EQ_0, GCD] THEN CONV_TAC NUMBER_RULE)

  let QUADRATIC_RESIDUE_MODULO_PRIMITIVE_POWER ← prove
   r"!n g m.
        coprime(n,g) /\ order n g = phi n
        ==> ((?x. (x EXP 2 == g EXP m) (mod n)) <=>
             3 <= n ==> EVEN m)"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q "n = 0") THENL
     [ASM_MESON_TAC [PHI_EQ_0, ORDER_EQ_0], ALL_TAC] THEN
    ASM_SIMP_TAC [POWER_RESIDUE_MODULO_PRIMITIVE_POWER] THEN
    ASM_REWRITE_TAC [GCD_2_CASES, EVEN_PHI_EQ] THEN
    ASM_CASES_TAC (← q "3 <= n") THEN ASM_REWRITE_TAC [DIVIDES_1, DIVIDES_2])

  let COUNT_POWER_RESIDUES_MODULO_PRIMITIVE ← prove
   r"!n k. ~(n = 0) /\ (?g. order n g = phi n)
         ==> {a | a < n /\ coprime(n,a) /\ ?x. (x EXP k == a) (mod n)}
             HAS_SIZE phi n DIV gcd(k,phi n)"
   (← do
    let s1 ← SET_RULE
      (← q r"{x | P x /\ Q x /\ R x} = {x | ~(P x /\ Q x ==> ~R x)}")
    pure (REPEAT GEN_TAC THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    ONCE_REWRITE_TAC [s1] THEN
    ASM_SIMP_TAC [POWER_RESIDUE_MODULO_PRIMITIVE] THEN
    ASM_SIMP_TAC [NOT_IMP, ← GSYM CONJ_ASSOC, HAS_SIZE,
     ← REWRITE_RULE [HAS_SIZE] COUNT_ROOTS_MODULO_PRIMITIVE_GEN_ALT] THEN
    REWRITE_TAC [EXP_ONE, CONG_REFL, ← GSYM DIVIDES_GCD_LEFT] THEN
    SIMP_TAC [DIVIDES_DIV_SELF, GCD]))

  let COUNT_QUADRATIC_RESIDUES_MODULO_PRIMITIVE ← prove
   r"!n. 3 <= n /\ (?g. order n g = phi n)
       ==> {a | a < n /\ coprime(n,a) /\ ?x. (x EXP 2 == a) (mod n)}
           HAS_SIZE phi n DIV 2"
   (GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (← SPECL [(← q "n:num"), (← q "2")] COUNT_POWER_RESIDUES_MODULO_PRIMITIVE) THEN
    ASM_SIMP_TAC [GCD_2_CASES, EVEN_PHI_EQ] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC)

  -- @@RETURN BEGIN
  return { COUNT_ROOTS_MODULO_PRIMITIVE_GEN_ALT, COUNT_ROOTS_MODULO_PRIMITIVE_GEN,
           POWER_RESIDUE_MODULO_PRIMITIVE, POWER_RESIDUE_MODULO_PRIME_EQ,
           POWER_RESIDUE_MODULO_PRIMITIVE_ORDER_ALT,
           POWER_RESIDUE_MODULO_PRIMITIVE_ORDER,
           QUADRATIC_RESIDUE_MODULO_PRIMITIVE_ORDER,
           POWER_RESIDUE_MODULO_PRIMITIVE_POWER,
           QUADRATIC_RESIDUE_MODULO_PRIMITIVE_POWER,
           COUNT_POWER_RESIDUES_MODULO_PRIMITIVE,
           COUNT_QUADRATIC_RESIDUES_MODULO_PRIMITIVE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Quadratic residues modulo odd prime powers and powers of 2.               -/
/- ------------------------------------------------------------------------- -/

structure QuadraticResidues where
  -- @@FIELDS
  INT_OF_NUM_POWER_RESIDUE : thm
  QUADRATIC_RESIDUE_MODULO_ODD_POWER : thm
  QUADRATIC_RESIDUE_MODULO_POWER_2_STABLE : thm
  QUADRATIC_RESIDUE_MODULO_POWER_2 : thm
  deriving Inhabited

@[nospecialize]
def setupQuadraticResidues [HolBase] (D : PrimitiveDeps) :
    ExceptT String IO QuadraticResidues := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, EXPAND_CASES_CONV, INTEGER_RULE, INT_ARITH,
        MESON_TAC, NUMBER_RULE, NUM_REDUCE_CONV, .. } := D
  let { ADD1, ARITH, CONG, CONG_MOD_0, CONG_MOD_1, CONG_SYM, COPRIME_2, DIVIDES_2,
        DIVIDES_EXP_LE_IMP, .. } := D.core1
  let { EXISTS_INT_CASES, EXP, EXP_ONE, FORALL_AND_THM, IMP_CONJ, .. } := D.core2
  let { INT_2_DIVIDES_ADD, INT_2_DIVIDES_MUL, INT_2_DIVIDES_POW, INT_CONG_MOD_0,
        INT_CONG_NUM_EXISTS, INT_CONG_POW, INT_CONG_SOLVE, INT_CONG_TRANS,
        INT_COPRIME_LMUL, INT_DIVIDES_ADD, INT_DIVIDES_LMUL, INT_DIVIDES_POW_LE_IMP,
        INT_DIVIDES_REFL, INT_OF_NUM_EQ, INT_OF_NUM_MUL, INT_OF_NUM_POW, INT_POW,
        INT_POW_1, INT_POW_ADD, INT_POW_MUL, INT_POW_NEG, INT_POW_POW, .. } := D.core3
  let { MOD_EXP_MOD, MONO_EXISTS, MULT_CLAUSES, NOT_EVEN, NOT_SUC, ODD_MOD_EVEN, .. } := D.core4
  let { RIGHT_FORALL_IMP_THM, int_congruent, num_INDUCTION, num_congruent, num_coprime,
        num_divides, .. } := D.core5
  -- @@SCOPE END

  let INT_OF_NUM_POWER_RESIDUE ← prove
   r"!n k a. (?x:num. (x EXP k == a) (mod n)) <=>
           (?x:int. (x pow k == &a) (mod &n))"
   (← do
    let a1 ← INT_ARITH
      (← q r"--(&m):int = &n <=> &m:int = &n /\ &n:int = &0")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "n = 0") THENL
     [ASM_REWRITE_TAC [CONG_MOD_0, INT_CONG_MOD_0] THEN
      REWRITE_TAC [EXISTS_INT_CASES, INT_POW_NEG] THEN
      ASM_CASES_TAC (← q "EVEN k") THEN
      ASM_REWRITE_TAC [INT_OF_NUM_POW, INT_OF_NUM_EQ, a1] THEN
      MESON_TAC [],
      REWRITE_TAC [num_congruent, ← GSYM INT_OF_NUM_POW]] THEN
    EQ_TAC THENL [MESON_TAC [], ALL_TAC] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q "x:int")) THEN
    MP_TAC (← ISPECL [(← q "x:int"), (← q "&n:int")] INT_CONG_NUM_EXISTS) THEN
    ASM_REWRITE_TAC [INT_OF_NUM_EQ] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q "m:num") THEN DISCH_TAC THEN
    MATCH_MP_TAC INT_CONG_TRANS THEN EXISTS_TAC (← q "(x:int) pow k") THEN
    ASM_SIMP_TAC [INT_CONG_POW]))

  let QUADRATIC_RESIDUE_MODULO_ODD_POWER ← prove
   r"!n a k.
        ODD n /\ coprime(n,a)
        ==> ((?x. (x EXP 2 == a) (mod (n EXP k))) <=>
             k = 0 \/ ?x. (x EXP 2 == a) (mod n))"
   (← do
    let i3 ← INTEGER_RULE
      (← q r"x pow 2 - a = m * z /\
      ((&2 * x) * y:int == --z) (mod n) /\
      n pow 1 divides m
      ==> ((x + y * m) pow 2 == a) (mod (n * m))")
    let i2 ← INTEGER_RULE
      (← q r"x pow 2 - a = nk * z
      ==> coprime(n,a) /\ n pow 1 divides nk ==> coprime(x,n)")
    let n1 ← NUMBER_RULE
      (← q r"p EXP 1 divides q ==> (x == a) (mod q) ==> (x == a) (mod p)")
    pure (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q "k = 0") THEN
    ASM_REWRITE_TAC [EXP, CONG_MOD_1] THEN EQ_TAC THENL
     [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q "x:num") THEN
      MATCH_MP_TAC n1 THEN
      MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ASM_ARITH_TAC,
      DISCH_TAC THEN UNDISCH_TAC (← q "~(k = 0)") THEN SPEC_TAC (← q "k:num", ← q "k:num")] THEN
    MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC [] THEN
    X_GEN_TAC (← q "k:num") THEN ASM_CASES_TAC (← q "k = 0") THEN
    ASM_REWRITE_TAC [EXP, MULT_CLAUSES, NOT_SUC] THEN
    FIRST_X_ASSUM ((K ALL_TAC : thm → tactic) o check (is_exists o concl)) THEN
    REWRITE_TAC [INT_OF_NUM_POWER_RESIDUE] THEN
    REWRITE_TAC [← GSYM INT_OF_NUM_MUL, ← GSYM INT_OF_NUM_POW] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "x:int") (MP_TAC o REWRITE_RULE [int_congruent])) THEN
    DISCH_THEN (X_CHOOSE_TAC (← q "z:int")) THEN
    MP_TAC (← ISPECL [(← q "&2 * x:int"), (← q "--z:int"), (← q "&n:int")]
          INT_CONG_SOLVE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC [INT_COPRIME_LMUL, ← GSYM num_coprime, COPRIME_2] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP i2) THEN
      ASM_REWRITE_TAC [← GSYM num_coprime] THEN
      MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN ASM_ARITH_TAC,
      DISCH_THEN (X_CHOOSE_TAC (← q "y:int")) THEN
      EXISTS_TAC (← q "(x:int) + y * &n pow k") THEN MATCH_MP_TAC i3 THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN
      ASM_ARITH_TAC]))

  let QUADRATIC_RESIDUE_MODULO_POWER_2_STABLE ← prove
   r"!a k. ODD a /\ 3 <= k
         ==> ((?x. (x EXP 2 == a) (mod (2 EXP k))) <=>
              (?x. (x EXP 2 == a) (mod 8)))"
   (← do
    let i10 ← INTEGER_RULE
      (← q r"t divides (c * x + b:int) ==> k * t divides k * b + x * c * k")
    let a9 ← ARITH_RULE (← q r"3 <= k ==> SUC(k - 1) = k")
    let i8 ← INTEGER_RULE
      (← q r"((a + b) + (d + &2 * x * c * p):int == a) (mod n) <=>
    n divides (d + b + x * c * &2 * p)")
    let r7 ← INT_ARITH
      (← q r"(x + y:int) pow 2 = x pow 2 + y pow 2 + &2 * x * y")
    let a6 ← ARITH_RULE (← q r"3 <= k ==> ~(k = 0)")
    let r5 ← INT_ARITH (← q r"a - b:int = c <=> a = b + c")
    let a4 ← ARITH_RULE (← q r"3 <= SUC k <=> SUC k = 3 \/ 3 <= k")
    let n3 ← NUMBER_RULE
      (← q r"(m:num) divides n ==> (a == b) (mod n) ==> (a == b) (mod m)")
    let t2 ← TAUT
      (← q r"p ==> (q <=> r) <=> (p ==> q ==> r) /\ (r ==> p ==> q)")
    let a1 ← ARITH_RULE (← q r"8 = 2 EXP 3")
    pure (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [FORALL_AND_THM, a1, t2] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      MATCH_MP_TAC n3 THEN
      MATCH_MP_TAC DIVIDES_EXP_LE_IMP THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC] THEN
    MATCH_MP_TAC num_INDUCTION THEN CONV_TAC NUM_REDUCE_CONV THEN
    X_GEN_TAC (← q "k:num") THEN
    REWRITE_TAC [a4] THEN
    ASM_CASES_TAC (← q "SUC k = 3") THEN ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC (← q "ODD a") THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    ASM_CASES_TAC (← q "3 <= k") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [INT_OF_NUM_POWER_RESIDUE, ← GSYM INT_OF_NUM_POW] THEN
    REWRITE_TAC [← GSYM NOT_EVEN, ← GSYM DIVIDES_2, num_divides] THEN
    DISCH_TAC THEN DISCH_THEN (X_CHOOSE_TAC (← q "x:int")) THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE id [int_congruent]) THEN
    REWRITE_TAC [r5] THEN
    DISCH_THEN (X_CHOOSE_TAC (← q "b:int")) THEN
    FIRST_ASSUM (MP_TAC o AP_TERM (← q r"\x:int. &2 divides x")) THEN
    ASM_REWRITE_TAC [INT_2_DIVIDES_POW, INT_2_DIVIDES_ADD, INT_2_DIVIDES_MUL] THEN
    ASM_SIMP_TAC [INT_DIVIDES_REFL, a6] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
    EXISTS_TAC (← q "(x:int) + b * &2 pow (k - 1)") THEN
    REWRITE_TAC [r7] THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [i8] THEN
    REWRITE_TAC [INT_POW_MUL, INT_POW_POW, ADD1] THEN
    MATCH_MP_TAC INT_DIVIDES_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC INT_DIVIDES_LMUL THEN MATCH_MP_TAC INT_DIVIDES_POW_LE_IMP THEN
      ASM_ARITH_TAC,
      REWRITE_TAC [← GSYM (← CONJUNCT2 INT_POW)]] THEN
    ASM_SIMP_TAC [a9] THEN
    REWRITE_TAC [INT_POW_ADD, INT_POW_1] THEN MATCH_MP_TAC i10 THEN
    ASM_REWRITE_TAC [INT_2_DIVIDES_ADD, INT_2_DIVIDES_MUL]))

  let QUADRATIC_RESIDUE_MODULO_POWER_2 ← prove
   r"!a k. ODD a /\ 3 <= k
         ==> ((?x. (x EXP 2 == a) (mod (2 EXP k))) <=> (a == 1) (mod 8))"
   (← do
    let a2 ← ARITH_RULE (← q r"a MOD 8 < 8")
    let a1 ← ARITH_RULE (← q r"n MOD 8 < 8")
    pure (REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [QUADRATIC_RESIDUE_MODULO_POWER_2_STABLE] THEN
    EQ_TAC THENL [ALL_TAC, MESON_TAC [EXP_ONE, CONG_SYM]] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "n:num") MP_TAC) THEN REWRITE_TAC [CONG] THEN
    ONCE_REWRITE_TAC [← GSYM MOD_EXP_MOD] THEN
    SUBGOAL_THEN (← q "ODD(a MOD 8)") MP_TAC THENL
     [ASM_SIMP_TAC [ODD_MOD_EVEN, ARITH], ALL_TAC] THEN
    MP_TAC a1 THEN SPEC_TAC (← q "n MOD 8", ← q "n:num") THEN
    MP_TAC a2 THEN SPEC_TAC (← q "a MOD 8", ← q "a:num") THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV))

  -- @@RETURN BEGIN
  return { INT_OF_NUM_POWER_RESIDUE, QUADRATIC_RESIDUE_MODULO_ODD_POWER,
           QUADRATIC_RESIDUE_MODULO_POWER_2_STABLE, QUADRATIC_RESIDUE_MODULO_POWER_2 }
  -- @@RETURN END

structure EulerCriterion where
  -- @@FIELDS
  GENERALIZED_EULER_CRITERION : thm
  GENERALIZED_EULER_CRITERION_PRIME : thm
  EULER_CRITERION : thm
  deriving Inhabited

@[nospecialize]
def setupEulerCriterion [HolBase] (D : PrimitiveDeps) (BEquivalences : Equivalences) (BCountRoots : CountRoots) :
    ExceptT String IO EulerCriterion := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, MESON_TAC, NUMBER_RULE, NUM_REDUCE_CONV, .. } := D
  let { ARITH, ARITH_EQ, CONG_MOD_0, CONG_MOD_1, COPRIME_0, DIVIDES_0, DIVIDES_2,
        DIVIDES_GCD_LEFT, .. } := D.core1
  let { DIV_0, DIV_REFL, EVEN_SUB, EXP, EXP_1, EXP_ONE, GCD_1, .. } := D.core2
  let { NOT_EVEN, ODD_MOD_2, .. } := D.core4
  let { PHI_0, PHI_PRIME, PRIME_1, PRIME_COPRIME_EQ, PRIME_DIVEXP_EQ, PRIME_GE_2,
        PRIME_ODD, .. } := D.core5
  let { PRIMITIVE_ROOT_EXISTS, .. } := BEquivalences
  let { POWER_RESIDUE_MODULO_PRIMITIVE, .. } := BCountRoots
  -- @@SCOPE END

  let GENERALIZED_EULER_CRITERION ← prove
   r"!n a k.
        (n = 0 \/ n = 1 \/ n = 2 \/ n = 4 \/
         ?p k. prime p /\ 3 <= p /\ (n = p EXP k \/ n = 2 * p EXP k)) /\
        coprime(n,a)
        ==> ((?x. (x EXP k == a) (mod n)) <=>
             (a EXP (phi n DIV gcd(k,phi n)) == 1) (mod n))"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q "n = 1") THEN ASM_REWRITE_TAC [CONG_MOD_1] THEN
    ASM_CASES_TAC (← q "n = 0") THENL
     [ASM_REWRITE_TAC [CONG_MOD_0, PHI_0, DIV_0, COPRIME_0, EXP] THEN
      MESON_TAC [EXP_ONE],
      DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
      MATCH_MP_TAC POWER_RESIDUE_MODULO_PRIMITIVE THEN
      ASM_REWRITE_TAC [PRIMITIVE_ROOT_EXISTS]])

  let GENERALIZED_EULER_CRITERION_PRIME ← prove
   r"!p a k.
        prime p
        ==> ((?x. (x EXP k == a) (mod p)) <=>
             if p divides a then ~(k = 0)
             else (a EXP ((p - 1) DIV gcd(k,p-1)) == 1) (mod p))"
   (← do
    let n2 ← NUMBER_RULE
     (← q r"p divides a ==> ((x:num == a) (mod p) <=> p divides x)")
    let n1 ← NUMBER_RULE
     (← q r"(1 == a) (mod p) ==> p divides a ==> p = 1")
    pure (REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
     [ASM_CASES_TAC (← q "k = 0") THEN ASM_REWRITE_TAC [EXP] THENL
       [DISCH_THEN (MP_TAC o MATCH_MP n1) THEN
        ASM_MESON_TAC [PRIME_1],
        EXISTS_TAC (← q "0") THEN ASM_SIMP_TAC [n2] THEN
        ASM_SIMP_TAC [PRIME_DIVEXP_EQ, DIVIDES_0]],
      MP_TAC (← SPECL [← q "p:num", ← q "a:num", ← q "k:num"] GENERALIZED_EULER_CRITERION) THEN
      ASM_SIMP_TAC [PHI_PRIME] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC [PRIME_COPRIME_EQ] THEN
      ASM_CASES_TAC (← q "p = 2") THEN ASM_REWRITE_TAC [] THEN
      REPEAT DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [← q "p:num", ← q "1"] THEN
      ASM_SIMP_TAC [EXP_1] THEN FIRST_X_ASSUM (MP_TAC o MATCH_MP PRIME_GE_2) THEN
      ASM_ARITH_TAC]))

  let EULER_CRITERION ← prove
   r"!p a. prime p
         ==> ((?x. (x EXP 2 == a) (mod p)) <=>
              p divides a \/ (a EXP ((p - 1) DIV 2) == 1) (mod p))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q "p:num", ← q "a:num", ← q "2"] GENERALIZED_EULER_CRITERION_PRIME) THEN
    ASM_CASES_TAC (← q r"(p:num) divides a") THEN ASM_REWRITE_TAC [ARITH_EQ] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_CASES_TAC (← q "p = 2") THENL
     [UNDISCH_TAC (← q r"~((p:num) divides a)") THEN
      ASM_REWRITE_TAC [DIVIDES_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
      SIMP_TAC [GCD_1, DIV_REFL, ARITH_EQ, EXP_1, ← GSYM ODD_MOD_2] THEN
      REWRITE_TAC [NOT_EVEN, EXP, ARITH],
      SUBGOAL_THEN (← q r"gcd(2,p - 1) = 2") (fun th => tactic_of do pure (REWRITE_TAC [th])) THEN
      REWRITE_TAC [← GSYM DIVIDES_GCD_LEFT, DIVIDES_2, EVEN_SUB] THEN
      DISJ2_TAC THEN REWRITE_TAC [ARITH, NOT_EVEN] THEN
      ASM_MESON_TAC [PRIME_ODD]])

  -- @@RETURN BEGIN
  return { GENERALIZED_EULER_CRITERION, GENERALIZED_EULER_CRITERION_PRIME,
           EULER_CRITERION }
  -- @@RETURN END

structure CountRootsOdd where
  -- @@FIELDS
  COUNT_ROOTS_MODULO_ODD_GEN : thm
  COUNT_ROOTS_MODULO_ODD_ALT_GEN : thm
  POWER_RESIDUE_MODULO_ODD : thm
  deriving Inhabited

@[nospecialize]
def setupCountRootsOdd [HolBase] (D : PrimitiveDeps) (BEquivalences : Equivalences) (BCountRoots : CountRoots) :
    ExceptT String IO CountRootsOdd := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, MESON, NUMBER_RULE, SET_RULE, SET_TAC, .. } := D
  let { CARD_CLAUSES, CHINESE_REMAINDER_COUNT, CONG, CONG_COPRIME, CONG_MOD_1,
        CONJ_ASSOC, CONTRAPOS_THM, COPRIME_LEXP, COPRIME_LMUL, COPRIME_PRIME,
        COPRIME_PRIME_EQ, COPRIME_REXP, DIVIDES_ONE, .. } := D.core1
  let { DIVIDES_PRIME_PRIME, DIVIDES_REFL, DIV_EQ_0, EMPTY_GSPEC, EQ_ADD_LCANCEL_0,
        EQ_ADD_RCANCEL_0, EQ_IMP, EXP_EQ_0, EXTENSION, FINITE_DIVISORS, FINITE_EMPTY,
        FINITE_INDUCT_STRONG, FINITE_SPECIAL_DIVISORS, FINITE_SUBSET,
        FORALL_UNWIND_THM2, GCD_LE, GCD_ZERO, HAS_SIZE, HAS_SIZE_0, HAS_SIZE_NUMSEG_LT, .. } := D.core2
  let { IMP_IMP, INDEX_EQ_0, INDEX_EXP, INDEX_MUL, INDEX_REFL, INDUCT_COPRIME_STRONG,
        IN_ELIM_THM, ITERATE_CLAUSES, ITERATE_EQ, ITERATE_SING, ITERATE_UNION, .. } := D.core3
  let { MOD_EXP_MOD, MOD_LT_EQ, MONOIDAL_MUL, MONO_EXISTS, MULT_CLAUSES, MULT_EQ_0,
        NEUTRAL_MUL, NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP, NOT_IN_EMPTY, NOT_LE,
        ODD, ODD_EXP, ODD_MULT, ODD_PRIME, .. } := D.core4
  let { PHI_PRIMEPOW_ALT, PRIME_0, PRIME_1, PRIME_DIVEXP_EQ, PRIME_DIVPROD_EQ,
        PRIME_GE_2, SING_GSPEC, nproduct, .. } := D.core5
  let { PRIMITIVE_ROOT_EXISTS, .. } := BEquivalences
  let { COUNT_ROOTS_MODULO_PRIMITIVE_GEN, .. } := BCountRoots
  -- @@SCOPE END

  let COUNT_ROOTS_MODULO_ODD_GEN ← prove
   r"!n a k.
        ODD n /\ coprime(n,a) /\ ~(k = 0)
        ==> {x | x < n /\ (x EXP k == a) (mod n)} HAS_SIZE
            (if !p. prime p /\ p divides n
                    ==> (a EXP ((p EXP (index p n - 1) * (p - 1)) DIV
                                gcd(k,p EXP (index p n - 1) * (p - 1))) == 1)
                        (mod (p EXP index p n))
             then nproduct {p | prime p /\ p divides n}
                           (\p. gcd(k,p EXP (index p n - 1) * (p - 1)))
             else 0)"
   (← do
    let a18 ← ARITH_RULE (← q r"2 <= p ==> ~(p <= 1)")
    let m17 ← MATCH_MP ITERATE_SING MONOIDAL_MUL
    let m16 ← MESON [PRIME_DIVEXP_EQ, DIVIDES_PRIME_PRIME]
     (← q r"~(n = 0) /\ prime p ==> (prime q /\ q divides p EXP n <=> q = p)")
    let m15 ← MATCH_MP ITERATE_EQ MONOIDAL_MUL
    let m14 ← MESON []
     (← q r"s HAS_SIZE m ==> n = m ==> s HAS_SIZE n")
    let a13 ← ARITH_RULE (← q r"1 < n ==> ~(n = 0)")
    let n12 ← NUMBER_RULE
     (← q r"coprime(a,b)
           ==> ((x == y) (mod (a * b)) <=>
                (x == y) (mod a) /\ (x == y) (mod b))")
    let m11 ← MESON [MULT_CLAUSES]
     (← q r"(if p /\ q then a * b else 0) =
      (if p then a else 0) * (if q then b else 0)")
    let m10 ← MESON []
     (← q r"(!p. prime p /\ (P p \/ Q p) ==> R p) <=>
      (!p. prime p /\ P p ==> R p) /\ (!p. prime p /\ Q p ==> R p)")
    let s9 ← SET_RULE (← q r"DISJOINT s t <=> !x. ~(x IN s /\ x IN t)")
    let a8 ← ARITH_RULE (← q r"1 < n ==> ~(n = 0)")
    let m7 ← MESON [FINITE_SUBSET]
     (← q r"FINITE {d | d divides a} /\
          {p | prime p /\ p divides a} SUBSET {d | d divides a}
          ==> FINITE {p | prime p /\ p divides a}")
    let m6 ← MATCH_MP ITERATE_UNION MONOIDAL_MUL
    let s5 ← SET_RULE
     (← q r"{x | P x /\ (Q x \/ R x)} =
      {x | P x /\ Q x} UNION {x | P x /\ R x}")
    let m4 ← MESON [PRIME_DIVPROD_EQ]
     (← q r"prime p /\ p divides a * b <=>
      prime p /\ (p divides a \/ p divides b)")
    let a3 ← ARITH_RULE (← q r"~(n = 0) /\ ~(n = 1) <=> 1 < n")
    let m2 ← MATCH_MP ITERATE_CLAUSES MONOIDAL_MUL
    let m1 ← MESON [PRIME_1, DIVIDES_ONE]
     (← q r"~(prime p /\ p divides 1)")
    pure (MAP_EVERY X_GEN_TAC [← q "n:num", ← q "z:num", ← q "k:num"] THEN
    REWRITE_TAC [nproduct] THEN ASM_CASES_TAC (← q "k = 0") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q "n = 0") THEN ASM_REWRITE_TAC [ODD] THEN
    ASM_CASES_TAC (← q "n = 1") THENL
     [ASM_REWRITE_TAC [m1] THEN
      ASM_REWRITE_TAC [EMPTY_GSPEC, m2] THEN
      REWRITE_TAC [CONG_MOD_1, NEUTRAL_MUL, HAS_SIZE_NUMSEG_LT],
      MAP_EVERY UNDISCH_TAC [← q "~(n = 1)", ← q "~(n = 0)"]] THEN
    GEN_REWRITE_TAC I [IMP_IMP] THEN
    REWRITE_TAC [a3] THEN
    SPEC_TAC (← q "n:num", ← q "n:num") THEN
    MATCH_MP_TAC INDUCT_COPRIME_STRONG THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q "a:num", ← q "b:num"] THEN REWRITE_TAC [ODD_MULT] THEN
      ASM_CASES_TAC (← q "ODD a") THEN ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC (← q "ODD b") THEN ASM_REWRITE_TAC [IMP_IMP] THEN
      REWRITE_TAC [COPRIME_LMUL] THEN
      ASM_CASES_TAC (← q r"coprime(a:num,z)") THEN ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC (← q r"coprime(b:num,z)") THEN ASM_REWRITE_TAC [] THEN
      STRIP_TAC THEN REWRITE_TAC [m4] THEN
      REWRITE_TAC [s5] THEN
      W (MP_TAC o PART_MATCH (lhand o rand) m6 o lhand o rand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THENL
         [CONJ_TAC THEN MATCH_MP_TAC m7 THEN
          ASM_SIMP_TAC [FINITE_DIVISORS, a8] THEN
          SET_TAC [],
          REWRITE_TAC [s9] THEN
          REWRITE_TAC [IN_ELIM_THM] THEN ASM_MESON_TAC [COPRIME_PRIME]],
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC [m10] THEN
      REWRITE_TAC [m11] THEN
      MATCH_MP_TAC CHINESE_REMAINDER_COUNT THEN
      EXISTS_TAC (← q r"\x. (x EXP k == z) (mod a)") THEN
      EXISTS_TAC (← q r"\x. (x EXP k == z) (mod b)") THEN
      ASM_SIMP_TAC [n12] THEN
      CONJ_TAC THENL [REWRITE_TAC [CONG, MOD_EXP_MOD], ALL_TAC] THEN
      SUBGOAL_THEN
       (← q r"(!p. prime p /\ p divides a ==> index p (a * b) = index p a) /\
      (!p. prime p /\ p divides b ==> index p (a * b) = index p b)")
      STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC [INDEX_MUL, a13] THEN
        REWRITE_TAC [EQ_ADD_LCANCEL_0, EQ_ADD_RCANCEL_0] THEN
        REWRITE_TAC [INDEX_EQ_0] THEN ASM_MESON_TAC [COPRIME_PRIME_EQ],
        ASM_SIMP_TAC []] THEN
      CONJ_TAC THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP m14) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC m15 THEN
      ASM_SIMP_TAC [IN_ELIM_THM],
      MAP_EVERY X_GEN_TAC [← q "p:num", ← q "j:num"] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [ODD_EXP, COPRIME_LEXP] THEN STRIP_TAC THEN
      ASM_SIMP_TAC [m16] THEN
      REWRITE_TAC [FORALL_UNWIND_THM2] THEN
      REWRITE_TAC [SING_GSPEC, m17] THEN
      W (MP_TAC o PART_MATCH (lhand o rand) COUNT_ROOTS_MODULO_PRIMITIVE_GEN o
          lhand o snd) THEN
      ASM_REWRITE_TAC [EXP_EQ_0] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC [PRIME_0], ALL_TAC] THEN
        ASM_REWRITE_TAC [COPRIME_LEXP] THEN
        ASM_REWRITE_TAC [PRIMITIVE_ROOT_EXISTS] THEN ASM_MESON_TAC [ODD_PRIME],
        FIRST_ASSUM (ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
        ASM_SIMP_TAC [PHI_PRIMEPOW_ALT, INDEX_EXP, INDEX_REFL] THEN
        ASM_SIMP_TAC [a18, MULT_CLAUSES]]]))

  let COUNT_ROOTS_MODULO_ODD_ALT_GEN ← prove
   r"!n a k.
        ODD n /\ ~(k = 0)
        ==> {x | x < n /\ coprime(n,x) /\ (x EXP k == a) (mod n)} HAS_SIZE
            (if !p. prime p /\ p divides n
                    ==> (a EXP ((p EXP (index p n - 1) * (p - 1)) DIV
                                gcd(k,p EXP (index p n - 1) * (p - 1))) == 1)
                        (mod (p EXP index p n))
             then nproduct {p | prime p /\ p divides n}
                           (\p. gcd(k,p EXP (index p n - 1) * (p - 1)))
             else 0)"
   (← do
    let m3 ← MESON [PRIME_1] (← q r"prime p ==> ~(p = 1)")
    let n2 ← NUMBER_RULE
     (← q r"!p. (a == 1) (mod n)
            ==> p divides a /\ p divides n ==> p divides 1")
    let m1 ← MESON [HAS_SIZE_0]
     (← q r"s = {} /\ ~p ==> s HAS_SIZE (if p then n else 0)")
    pure (REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"coprime(n:num,a)") THENL
     [MP_TAC (← SPECL [← q "n:num", ← q "a:num", ← q "k:num"]
          COUNT_ROOTS_MODULO_ODD_GEN) THEN
      ASM_REWRITE_TAC [] THEN MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
      X_GEN_TAC (← q "i:num") THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o MATCH_MP CONG_COPRIME) THEN
      ASM_REWRITE_TAC [COPRIME_REXP],
      MATCH_MP_TAC m1 THEN
      CONJ_TAC THENL
       [REWRITE_TAC [EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY] THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o MATCH_MP CONG_COPRIME) THEN
        ASM_REWRITE_TAC [COPRIME_REXP],
        FIRST_X_ASSUM (MP_TAC o
          GEN_REWRITE_RULE RAND_CONV [COPRIME_PRIME_EQ]) THEN
        REWRITE_TAC [NOT_FORALL_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
        X_GEN_TAC (← q "p:num") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
        DISCH_THEN (MP_TAC o SPEC (← q "p:num") o MATCH_MP n2) THEN
        ASM_SIMP_TAC [NOT_IMP, DIVIDES_ONE, PRIME_DIVEXP_EQ] THEN
        ASM_REWRITE_TAC [DIVIDES_REFL, INDEX_EQ_0] THEN
        ASM_SIMP_TAC [m3] THEN
        CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [ODD]] THEN
        ASM_SIMP_TAC [DIV_EQ_0, GCD_ZERO] THEN
        ASM_REWRITE_TAC [← GSYM NOT_LE, GCD_LE] THEN
        ASM_REWRITE_TAC [EXP_EQ_0, MULT_EQ_0] THEN
        FIRST_X_ASSUM (MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC]]))

  let POWER_RESIDUE_MODULO_ODD ← prove
   r"!n a k.
        ODD n /\ ~(k = 0) /\ coprime(n,a)
        ==> ((?x. (x EXP k == a) (mod n)) <=>
             !p. prime p /\ p divides n
                 ==> (a EXP ((p EXP (index p n - 1) * (p - 1)) DIV
                              gcd(k,p EXP (index p n - 1) * (p - 1))) == 1)
                     (mod (p EXP index p n)))"
   (← do
    let m1 ← MATCH_MP ITERATE_CLAUSES MONOIDAL_MUL
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q "n:num", ← q "a:num", ← q "k:num"]
          COUNT_ROOTS_MODULO_ODD_GEN) THEN
    ASM_REWRITE_TAC [nproduct] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THENL
     [GEN_REWRITE_TAC I [← GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC [NOT_EXISTS_THM] THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [HAS_SIZE, EMPTY_GSPEC, CARD_CLAUSES, FINITE_EMPTY] THEN
      CONV_TAC (RAND_CONV SYM_CONV) THEN
      SUBGOAL_THEN (← q r"FINITE {p | prime p /\ p divides n}") MP_TAC THENL
       [MATCH_MP_TAC FINITE_SPECIAL_DIVISORS THEN ASM_MESON_TAC [ODD],
        SPEC_TAC (← q r"{p | prime p /\ p divides n}", ← q r"s:num->bool")] THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      SIMP_TAC [m1, NEUTRAL_MUL] THEN
      ASM_SIMP_TAC [MULT_EQ_0, GCD_ZERO] THEN ARITH_TAC,
      REWRITE_TAC [HAS_SIZE_0, EXTENSION, IN_ELIM_THM, NOT_IN_EMPTY] THEN
      REWRITE_TAC [← GSYM NOT_EXISTS_THM, CONTRAPOS_THM] THEN
      DISCH_THEN (X_CHOOSE_TAC (← q "x:num")) THEN EXISTS_TAC (← q "x MOD n") THEN
      ASM_REWRITE_TAC [MOD_LT_EQ] THEN REWRITE_TAC [CONG] THEN
      REWRITE_TAC [MOD_EXP_MOD] THEN ASM_REWRITE_TAC [← GSYM CONG] THEN
      ASM_MESON_TAC [ODD]]))

  -- @@RETURN BEGIN
  return { COUNT_ROOTS_MODULO_ODD_GEN, COUNT_ROOTS_MODULO_ODD_ALT_GEN,
           POWER_RESIDUE_MODULO_ODD }
  -- @@RETURN END

structure CountRootsPrimitive where
  -- @@FIELDS
  COUNT_ROOTS_MODULO_PRIMITIVE_ALT : thm
  COUNT_ROOTS_MODULO_PRIMITIVE : thm
  COUNT_ROOTS_MODULO_ODD_ALT : thm
  COUNT_ROOTS_MODULO_ODD : thm
  POWER_RESIDUE_EXISTS : thm
  deriving Inhabited

@[nospecialize]
def setupCountRootsPrimitive [HolBase] (D : PrimitiveDeps) (BCountRoots : CountRoots) (BCountRootsOdd : CountRootsOdd) :
    ExceptT String IO CountRootsPrimitive := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, NUMBER_RULE, SET_RULE, SET_TAC, .. } := D
  let { ARITH, CONG_MOD_1, CONG_REFL, COPRIME_1, COPRIME_LEXP, COPRIME_SYM, .. } := D.core1
  let { EQ_IMP, EXP, EXP_ONE, EXTENSION, FINITE_NUMSEG_LT, FINITE_RESTRICT, GCD_0,
        HAS_SIZE, .. } := D.core2
  let { IN_ELIM_THM, .. } := D.core3
  let { PHI_ALT, .. } := D.core5
  let { COUNT_ROOTS_MODULO_PRIMITIVE_GEN_ALT, .. } := BCountRoots
  let { COUNT_ROOTS_MODULO_ODD_ALT_GEN, COUNT_ROOTS_MODULO_ODD_GEN, .. } := BCountRootsOdd
  -- @@SCOPE END

  let COUNT_ROOTS_MODULO_PRIMITIVE_ALT ← prove
   r"!n k. ~(n = 0) /\ (?x. order n x = phi n)
         ==> { x | x < n /\ coprime(n,x) /\ (x EXP k == 1) (mod n)}
             HAS_SIZE gcd(k,phi n)"
   (← do
    let s1 ← SET_RULE
     (← q r"{x | P x /\ Q x} = {x | x IN {y | P y} /\ Q x}")
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC (← SPECL [← q "n:num", ← q "1", ← q "k:num"]
     COUNT_ROOTS_MODULO_PRIMITIVE_GEN_ALT) THEN
    ASM_REWRITE_TAC [EXP_ONE, CONG_REFL] THEN
    ASM_CASES_TAC (← q "k = 0") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [GCD_0, EXP, CONG_REFL, HAS_SIZE] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC [s1] THEN
      SIMP_TAC [FINITE_RESTRICT, FINITE_NUMSEG_LT],
      ONCE_REWRITE_TAC [COPRIME_SYM] THEN REWRITE_TAC [PHI_ALT] THEN
      AP_TERM_TAC THEN SET_TAC []]))

  let COUNT_ROOTS_MODULO_PRIMITIVE ← prove
   r"!n k. ~(n = 0) /\ ~(k = 0) /\ (?x. order n x = phi n)
         ==> { x | x < n /\ (x EXP k == 1) (mod n)} HAS_SIZE gcd(k,phi n)"
   (← do
    let n1 ← NUMBER_RULE (← q r"(x == 1) (mod n) ==> coprime(x,n)")
    pure (REPEAT GEN_TAC THEN DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    MP_TAC (← SPECL [← q "n:num", ← q "k:num"] COUNT_ROOTS_MODULO_PRIMITIVE_ALT) THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC [EXTENSION, IN_ELIM_THM] THEN
    X_GEN_TAC (← q "x:num") THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP n1) THEN
    ASM_REWRITE_TAC [COPRIME_LEXP] THEN REWRITE_TAC [COPRIME_SYM]))

  let COUNT_ROOTS_MODULO_ODD_ALT ← prove
   r"!n k. ODD n /\ ~(k = 0)
         ==> {x | x < n /\ coprime(n,x) /\ (x EXP k == 1) (mod n)} HAS_SIZE
             nproduct {p | prime p /\ p divides n}
                      (\p. gcd(k,p EXP (index p n - 1) * (p - 1)))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q "n:num", ← q "1", ← q "k:num"]
       COUNT_ROOTS_MODULO_ODD_ALT_GEN) THEN
    ASM_REWRITE_TAC [EXP_ONE, CONG_REFL, COPRIME_1])

  let COUNT_ROOTS_MODULO_ODD ← prove
   r"!n k. ODD n /\ ~(k = 0)
         ==> {x | x < n /\ (x EXP k == 1) (mod n)} HAS_SIZE
             nproduct {p | prime p /\ p divides n}
                      (\p. gcd(k,p EXP (index p n - 1) * (p - 1)))"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q "n:num", ← q "1", ← q "k:num"] COUNT_ROOTS_MODULO_ODD_GEN) THEN
    ASM_REWRITE_TAC [EXP_ONE, CONG_REFL, COPRIME_1])

  let POWER_RESIDUE_EXISTS ← prove
   r"!n k. ~(n = 0) ==> ?a. a < n /\ coprime(n,a) /\ ?x. (x EXP k == a) (mod n)"
   (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q "n = 1") THENL
     [EXISTS_TAC (← q "0") THEN ASM_REWRITE_TAC [COPRIME_1, CONG_MOD_1, ARITH],
      EXISTS_TAC (← q "1") THEN REWRITE_TAC [COPRIME_1] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC, EXISTS_TAC (← q "1")] THEN
      REWRITE_TAC [EXP_ONE, CONG_REFL]])

  -- @@RETURN BEGIN
  return { COUNT_ROOTS_MODULO_PRIMITIVE_ALT, COUNT_ROOTS_MODULO_PRIMITIVE,
           COUNT_ROOTS_MODULO_ODD_ALT, COUNT_ROOTS_MODULO_ODD, POWER_RESIDUE_EXISTS }
  -- @@RETURN END

structure QuadraticNonresidue where
  -- @@FIELDS
  QUADRATIC_NONRESIDUE_EXISTS : thm
  deriving Inhabited

@[nospecialize]
def setupQuadraticNonresidue [HolBase] (D : PrimitiveDeps) (BEquivalences : Equivalences) (BCountRoots : CountRoots) (BQuadraticResidues : QuadraticResidues) :
    ExceptT String IO QuadraticNonresidue := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_MESON_TAC, COPRIME_CONV, EXPAND_CASES_CONV,
        MESON, MESON_TAC, NUMBER_RULE, NUM_REDUCE_CONV, SET_RULE, SET_TAC, .. } := D
  let { ARITH, ARITH_EQ, CARD_PSUBSET_IMP, CHINESE_REMAINDER_UNIQUE, CONG,
        CONG_COPRIME, CONJ_SYM, CONTRAPOS_THM, COPRIME_0, COPRIME_1, COPRIME_LEXP,
        COPRIME_LMUL, COPRIME_REFL, COPRIME_SYM, .. } := D.core1
  let { EXP_EQ_0, FORALL_AND_THM, HAS_SIZE, .. } := D.core2
  let { INDUCT_COPRIME_ALT, .. } := D.core3
  let { LT, LT_IMP_NE, LT_LE, LT_REFL, MOD_EXP_MOD, MONO_EXISTS, MULT_SYM,
        NOT_EXISTS_THM, ODD_PRIME, .. } := D.core4
  let { PHI_ALT, PHI_EQ_0, PRIME_0, PRIME_2, PRIME_ODD, UNWIND_THM2, WLOG_LT, .. } := D.core5
  let { PRIMITIVE_ROOT_EXISTS, .. } := BEquivalences
  let { COUNT_QUADRATIC_RESIDUES_MODULO_PRIMITIVE, .. } := BCountRoots
  let { QUADRATIC_RESIDUE_MODULO_POWER_2, .. } := BQuadraticResidues
  -- @@SCOPE END

  let QUADRATIC_NONRESIDUE_EXISTS ← prove
   r"!n. (?a. a < n /\ coprime(n,a) /\ ~(?x. (x EXP 2 == a) (mod n))) <=>
       3 <= n"
   (← do
    let a9 ← ARITH_RULE (← q r"n DIV 2 < n <=> ~(n = 0)")
    let s8 ← SET_RULE
     (← q r"{x | P x /\ Q x /\ R x} PSUBSET {x | P x /\ Q x}
      ==> ?a. P a /\ Q a /\ ~R a")
    let m6 ← MESON [COPRIME_REFL]
     (← q r"~(a = 1) /\ coprime(n,a) /\ P a n
        ==> ~(a = n) /\ coprime(n,a) /\ P a n")
    let a7 ← ARITH_RULE (← q r"n MOD 4 < 4")
    let n5 ← NUMBER_RULE (← q r"(u == 1) (mod a) ==> coprime(a,u)")
    let t4 ← TAUT (← q r"~(p /\ q) <=> p ==> ~q")
    let a3 ← ARITH_RULE (← q r"a < 1 <=> a = 0")
    let a2 ← ARITH_RULE (← q r"~(3 <= n) <=> n = 0 \/ n = 1 \/ n = 2")
    let t1 ← TAUT (← q r"(p <=> q) <=> (~q ==> ~p) /\ (q ==> p)")
    pure (REWRITE_TAC [FORALL_AND_THM, t1] THEN
    CONJ_TAC THENL
     [REWRITE_TAC [a2] THEN
      GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [LT] THENL
       [REWRITE_TAC [a3, UNWIND_THM2] THEN
        REWRITE_TAC [COPRIME_1, CONG] THEN EXISTS_TAC (← q "0") THEN
        CONV_TAC NUM_REDUCE_CONV,
        REWRITE_TAC [NOT_EXISTS_THM, t4] THEN
        CONV_TAC EXPAND_CASES_CONV THEN
        REWRITE_TAC [COPRIME_0, COPRIME_1, CONG, ARITH_EQ] THEN
        EXISTS_TAC (← q "1") THEN
        CONV_TAC NUM_REDUCE_CONV],
      ALL_TAC] THEN
    MATCH_MP_TAC INDUCT_COPRIME_ALT THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL
     [MATCH_MP_TAC WLOG_LT THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC [COPRIME_REFL] THEN MESON_TAC [LT_REFL],
        REWRITE_TAC [MULT_SYM, COPRIME_SYM] THEN MESON_TAC [],
        MAP_EVERY X_GEN_TAC [← q "a:num", ← q "b:num"]] THEN
      DISCH_TAC THEN
      REPLICATE_TAC 3 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (MP_TAC o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "t:num") STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
      MP_TAC (← SPECL [← q "a:num", ← q "b:num", ← q "1", ← q "t:num"] CHINESE_REMAINDER_UNIQUE) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [ASM_ARITH_TAC, DISCH_THEN (MP_TAC o EXISTENCE)] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC (← q "u:num") THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [COPRIME_LMUL] THEN
      ASM_SIMP_TAC [n5] THEN
      CONJ_TAC THENL [ASM_MESON_TAC [CONG_COPRIME], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
      REWRITE_TAC [← GSYM NOT_EXISTS_THM, CONTRAPOS_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      UNDISCH_TAC (← q r"(u:num == t) (mod b)") THEN CONV_TAC NUMBER_RULE,
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q "p:num", ← q "k:num"] THEN ASM_CASES_TAC (← q "p = 2") THENL
     [ASM_REWRITE_TAC [PRIME_2] THEN
      ASM_CASES_TAC (← q "k = 0") THEN ASM_REWRITE_TAC [ARITH] THEN
      ASM_CASES_TAC (← q "k = 1") THEN ASM_REWRITE_TAC [ARITH] THEN
      ASM_CASES_TAC (← q "k = 2") THEN ASM_REWRITE_TAC [ARITH] THENL
       [EXISTS_TAC (← q "3") THEN CONV_TAC (ONCE_DEPTH_CONV COPRIME_CONV) THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC [CONG, NOT_EXISTS_THM] THEN
        X_GEN_TAC (← q "n:num") THEN ONCE_REWRITE_TAC [← GSYM MOD_EXP_MOD] THEN
        MP_TAC a7 THEN SPEC_TAC (← q "n MOD 4", ← q "n:num") THEN
        CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV,
        DISCH_TAC THEN EXISTS_TAC (← q "3") THEN ASM_REWRITE_TAC [LT_LE] THEN
        MATCH_MP_TAC m6 THEN
        REWRITE_TAC [COPRIME_LEXP] THEN
        CONV_TAC (ONCE_DEPTH_CONV COPRIME_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
        MP_TAC (← ISPECL [← q "3", ← q "k:num"] QUADRATIC_RESIDUE_MODULO_POWER_2) THEN
        REWRITE_TAC [CONG] THEN CONV_TAC NUM_REDUCE_CONV THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC],
      REPEAT DISCH_TAC THEN MATCH_MP_TAC s8 THEN
      MATCH_MP_TAC CARD_PSUBSET_IMP THEN
      CONJ_TAC THENL [SET_TAC [], MATCH_MP_TAC LT_IMP_NE] THEN
      MP_TAC (← SPEC (← q "p EXP k") COUNT_QUADRATIC_RESIDUES_MODULO_PRIMITIVE) THEN
      ASM_REWRITE_TAC [PRIMITIVE_ROOT_EXISTS, HAS_SIZE] THEN
      ANTS_TAC THENL [ASM_MESON_TAC [ODD_PRIME, PRIME_ODD], ALL_TAC] THEN
      DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN
      ONCE_REWRITE_TAC [COPRIME_SYM] THEN ONCE_REWRITE_TAC [CONJ_SYM] THEN
      REWRITE_TAC [← GSYM PHI_ALT] THEN
      REWRITE_TAC [a9] THEN
      REWRITE_TAC [PHI_EQ_0, EXP_EQ_0, ARITH_EQ] THEN ASM_MESON_TAC [PRIME_0]]))

  -- @@RETURN BEGIN
  return { QUADRATIC_NONRESIDUE_EXISTS }
  -- @@RETURN END

end HolLibrary.Primitive
