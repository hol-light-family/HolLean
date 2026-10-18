/- ========================================================================= -/
/- Basic divisibility notions over the integers.                             -/
/-                                                                           -/
/- This is similar to stuff in Library/prime.ml etc. for natural numbers.    -/
/- ========================================================================= -/
/- File: HolLibrary/Integer.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/integer.ml`, by hand, in file order,
  in the style of HolLibrary/Pocklington.lean and HolLibrary/Card.lean (see
  there and HolMath/Base.lean for the conventions).  integer.ml has no
  `needs`: it runs on the core library, and begins with `prioritize_int()`.
  Each section of integer.ml is a bundle (a `structure`) built by a `setup`
  function; SessionLibrary/Integer.lean builds the bundles in order and
  exports every name under its HOL Light name.  The theorems integer.ml uses
  from the core library are supplied via the CoreThms structures.

  integer.ml 220 binds `INT_GCD_MULTIPLE` to a (term, tactic) pair (the
  `prove` is missing in HOL Light); it is translated as that pair and is not
  exported.  integer.ml proves `INT_GCD_ABS` twice (216 and 279); the second
  binding is the one exported, as in OCaml.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, INT_ARITH, INTEGER_RULE, TAUT) they are
  bound first, in OCaml's order.
-/

import HolMath

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.Integer

-- @@COREFILL BEGIN
/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CONJ_ASSOC CONTRAPOS_THM DE_MORGAN_THM DISJ_ACI EQ_ADD_RCANCEL_0
   EXISTS_OR_THM FACT FACT_NZ FINITE_IMAGE_INJ INFINITE INT_ABS INT_ABS_ABS
   INT_ABS_MUL INT_ABS_MUL_1 INT_ABS_NEG INT_ABS_NUM INT_ABS_POS INT_ABS_POW
   INT_ABS_ZERO INT_CONG_DIV2 INT_CONG_RREM INT_DIVIDES_ABS INT_DIVIDES_LABS
   INT_DIVIDES_LCM_GCD INT_DIVIDES_RABS INT_DIV_1 INT_DIV_MUL INT_ENTIRE
   INT_EQ_MUL_LCANCEL INT_EXISTS_POS INT_GT INT_IMAGE INT_LCM_DIVIDES
   INT_LCM_POS INT_LE_LMUL INT_LE_MUL INT_LT_LE INT_LT_MUL INT_MUL_AC
   INT_MUL_LCM_GCD INT_MUL_LID INT_MUL_LNEG INT_MUL_LZERO INT_MUL_RID
   INT_MUL_RNEG INT_MUL_RZERO INT_MUL_SYM INT_NEG_EQ_0 INT_NEG_NEG INT_NOT_LE
   INT_OF_NUM_ADD INT_OF_NUM_EQ INT_OF_NUM_LT INT_OF_NUM_MUL INT_OF_NUM_SUC
   INT_POS INT_POW INT_POW_ADD INT_POW_EQ_0 INT_POW_MONO_LT INT_POW_MUL
   INT_POW_NEG INT_POW_ONE INT_POW_ZERO INT_SUB_0 IN_ELIM_THM
   LEFT_EXISTS_AND_THM LEFT_IMP_EXISTS_THM LE_EXISTS MONO_AND : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (MONO_EXISTS MONO_FORALL NOT_EXISTS_THM NOT_FORALL_THM NOT_IMP NOT_LE
   NOT_ODD NOT_SUC OR_EXISTS_THM RIGHT_EXISTS_AND_THM RIGHT_OR_DISTRIB
   SWAP_FORALL_THM UNWIND_THM2 WF_INT_MEASURE int_congruent int_divides
   int_gcd int_lcm num_FINITE : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms3 where
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms4 where
  deriving Inhabited

-- @@COREFILL END

/-- What integer.ml uses from Session besides theorems. -/
structure IntegerDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  prioritize_int : IO Unit
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  INT_ARITH : term → ExceptT String IO thm
  INT_ARITH_TAC : tactic
  ASM_INT_ARITH_TAC : tactic
  INTEGER_RULE : term → ExceptT String IO thm
  INTEGER_TAC : tactic
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  INDUCT_TAC : tactic
  -- INT_RING: Session's int-ring decision procedure (as in Words/Frag/RingTheory)
  INT_RING : term → ExceptT String IO thm
  -- INT_REDUCE_CONV: Session's integer literal reduction conv (as in Words/Frag)
  INT_REDUCE_CONV : ioconv
  METIS_TAC : List thm → tactic
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  core4 : CoreThms4

/- ------------------------------------------------------------------------- -/
/- Basic properties of divisibility.  (integer.ml 9-145)                     -/
/- ------------------------------------------------------------------------- -/

structure Divides where
  -- @@FIELDS
  INT_DIVIDES_REFL : thm
  INT_DIVIDES_TRANS : thm
  INT_DIVIDES_ADD : thm
  INT_DIVIDES_SUB : thm
  INT_DIVIDES_0 : thm
  INT_DIVIDES_ZERO : thm
  INT_DIVIDES_LNEG : thm
  INT_DIVIDES_RNEG : thm
  INT_DIVIDES_RMUL : thm
  INT_DIVIDES_LMUL : thm
  INT_DIVIDES_1 : thm
  INT_DIVIDES_ADD_REVR : thm
  INT_DIVIDES_ADD_REVL : thm
  INT_DIVIDES_MUL_L : thm
  INT_DIVIDES_MUL_R : thm
  INT_DIVIDES_LMUL2 : thm
  INT_DIVIDES_RMUL2 : thm
  INT_DIVIDES_CMUL2 : thm
  INT_DIVIDES_LMUL2_EQ : thm
  INT_DIVIDES_RMUL2_EQ : thm
  INT_DIVIDES_MUL2 : thm
  INT_DIVIDES_POW : thm
  INT_DIVIDES_POW2 : thm
  INT_DIVIDES_RPOW : thm
  INT_DIVIDES_RPOW_SUC : thm
  INT_DIVIDES_POW_LE_IMP : thm
  INT_DIVIDES_ANTISYM_DIVISORS : thm
  INT_DIVIDES_ANTISYM_MULTIPLES : thm
  INT_DIVIDES_ONE_POS : thm
  INT_DIVIDES_ONE_ABS : thm
  INT_DIVIDES_ONE : thm
  INT_DIVIDES_ANTISYM_ASSOCIATED : thm
  INT_DIVIDES_ANTISYM : thm
  INT_DIVIDES_ANTISYM_ABS : thm
  INT_DIVIDES_ANTISYM_POS : thm
  deriving Inhabited

@[nospecialize]
def setupDivides [HolBase] (D : IntegerDeps) :
    ExceptT String IO Divides := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INDUCT_TAC, INTEGER_RULE, INTEGER_TAC, INT_ARITH_TAC, MESON_TAC,
        prioritize_int, .. } := D
  let { EXISTS_OR_THM, INT_ABS, INT_ABS_MUL_1, INT_ABS_NUM, INT_ABS_POS,
        INT_DIVIDES_LABS, INT_MUL_LZERO, INT_POW, INT_POW_ADD, INT_POW_MUL,
        LEFT_IMP_EXISTS_THM, LE_EXISTS, .. } := D.core1
  let { NOT_SUC, RIGHT_OR_DISTRIB, UNWIND_THM2, int_divides, .. } := D.core2
  -- @@SCOPE END

  prioritize_int

  let INT_DIVIDES_REFL ← INTEGER_RULE (← q
   r"!d. d divides d")

  let INT_DIVIDES_TRANS ← INTEGER_RULE (← q
   r"!x y z. x divides y /\ y divides z ==> x divides z")

  let INT_DIVIDES_ADD ← INTEGER_RULE (← q
   r"!d a b. d divides a /\ d divides b ==> d divides (a + b)")

  let INT_DIVIDES_SUB ← INTEGER_RULE (← q
   r"!d a b. d divides a /\ d divides b ==> d divides (a - b)")

  let INT_DIVIDES_0 ← INTEGER_RULE (← q
   r"!d. d divides &0")

  let INT_DIVIDES_ZERO ← INTEGER_RULE (← q
   r"!x. &0 divides x <=> x = &0")

  let INT_DIVIDES_LNEG ← INTEGER_RULE (← q
   r"!d x. (--d) divides x <=> d divides x")

  let INT_DIVIDES_RNEG ← INTEGER_RULE (← q
   r"!d x. d divides (--x) <=> d divides x")

  let INT_DIVIDES_RMUL ← INTEGER_RULE (← q
   r"!d x y. d divides x ==> d divides (x * y)")

  let INT_DIVIDES_LMUL ← INTEGER_RULE (← q
   r"!d x y. d divides y ==> d divides (x * y)")

  let INT_DIVIDES_1 ← INTEGER_RULE (← q
   r"!x. &1 divides x")

  let INT_DIVIDES_ADD_REVR ← INTEGER_RULE (← q
   r"!d a b. d divides a /\ d divides (a + b) ==> d divides b")

  let INT_DIVIDES_ADD_REVL ← INTEGER_RULE (← q
   r"!d a b. d divides b /\ d divides (a + b) ==> d divides a")

  let INT_DIVIDES_MUL_L ← INTEGER_RULE (← q
   r"!a b c. a divides b ==> (c * a) divides (c * b)")

  let INT_DIVIDES_MUL_R ← INTEGER_RULE (← q
   r"!a b c. a divides b ==> (a * c) divides (b * c)")

  let INT_DIVIDES_LMUL2 ← INTEGER_RULE (← q
   r"!d a x. (x * d) divides a ==> d divides a")

  let INT_DIVIDES_RMUL2 ← INTEGER_RULE (← q
   r"!d a x. (d * x) divides a ==> d divides a")

  let INT_DIVIDES_CMUL2 ← INTEGER_RULE (← q
   r"!a b c. (c * a) divides (c * b) /\ ~(c = &0) ==> a divides b")

  let INT_DIVIDES_LMUL2_EQ ← INTEGER_RULE (← q
   r"!a b c. ~(c = &0) ==> ((c * a) divides (c * b) <=> a divides b)")

  let INT_DIVIDES_RMUL2_EQ ← INTEGER_RULE (← q
   r"!a b c. ~(c = &0) ==> ((a * c) divides (b * c) <=> a divides b)")

  let INT_DIVIDES_MUL2 ← INTEGER_RULE (← q
   r"!a b c d. a divides b /\ c divides d ==> (a * c) divides (b * d)")

  let INT_DIVIDES_POW ← prove
   r"!x y n. x divides y ==> (x pow n) divides (y pow n)"
   (REWRITE_TAC [int_divides] THEN MESON_TAC [INT_POW_MUL])

  let INT_DIVIDES_POW2 ← prove
   r"!n x y. ~(n = 0) /\ (x pow n) divides y ==> x divides y"
   (INDUCT_TAC THEN REWRITE_TAC [NOT_SUC, INT_POW] THEN INTEGER_TAC)

  let INT_DIVIDES_RPOW ← prove
   r"!x y n. x divides y /\ ~(n = 0) ==> x divides (y pow n)"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    SIMP_TAC [INT_DIVIDES_RMUL, INT_POW])

  let INT_DIVIDES_RPOW_SUC ← prove
   r"!x y n. x divides y ==> x divides (y pow (SUC n))"
   (SIMP_TAC [INT_DIVIDES_RPOW, NOT_SUC])

  let INT_DIVIDES_POW_LE_IMP ← prove
   r"!(p:int) m n. m <= n ==> p pow m divides p pow n"
   (SIMP_TAC [LE_EXISTS, INT_POW_ADD, LEFT_IMP_EXISTS_THM] THEN
    CONV_TAC INTEGER_RULE)

  let INT_DIVIDES_ANTISYM_DIVISORS ← prove
   r"!a b:int. a divides b /\ b divides a <=> !d. d divides a <=> d divides b"
   (MESON_TAC [INT_DIVIDES_REFL, INT_DIVIDES_TRANS])

  let INT_DIVIDES_ANTISYM_MULTIPLES ← prove
   r"!a b. a divides b /\ b divides a <=> !d. a divides d <=> b divides d"
   (MESON_TAC [INT_DIVIDES_REFL, INT_DIVIDES_TRANS])

  /- --------------------------------------------------------------------- -/
  /- Now carefully distinguish signs.                                      -/
  /- --------------------------------------------------------------------- -/

  let INT_DIVIDES_ONE_POS ← prove
   r"!x. &0 <= x ==> (x divides &1 <=> x = &1)"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [int_divides], INTEGER_TAC] THEN
    DISCH_THEN (CHOOSE_THEN (MP_TAC o AP_TERM (← q "abs") o SYM)) THEN
    SIMP_TAC [INT_ABS_NUM, INT_ABS_MUL_1] THEN ASM_SIMP_TAC [INT_ABS])

  let INT_DIVIDES_ONE_ABS ← prove
   r"!d. d divides &1 <=> abs(d) = &1"
   (MESON_TAC [INT_DIVIDES_LABS, INT_DIVIDES_ONE_POS, INT_ABS_POS])

  let INT_DIVIDES_ONE ← prove
   r"!d. d divides &1 <=> d = &1 \/ d = -- &1"
   (REWRITE_TAC [INT_DIVIDES_ONE_ABS] THEN INT_ARITH_TAC)

  let INT_DIVIDES_ANTISYM_ASSOCIATED ← prove
   r"!x y. x divides y /\ y divides x <=> ?u. u divides &1 /\ x = y * u"
   (← do
    let i1 ← INTEGER_RULE (← q r"y = x * d /\ x = y * e /\ ~(y = &0) ==> d divides &1")
    pure (REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC, INTEGER_TAC] THEN
    ASM_CASES_TAC (← q r"x = &0") THEN ASM_SIMP_TAC [INT_DIVIDES_ZERO, INT_MUL_LZERO] THEN
    ASM_MESON_TAC [int_divides, INT_DIVIDES_REFL, i1]))

  let INT_DIVIDES_ANTISYM ← prove
   r"!x y. x divides y /\ y divides x <=> x = y \/ x = --y"
   (REWRITE_TAC [INT_DIVIDES_ANTISYM_ASSOCIATED, INT_DIVIDES_ONE] THEN
    REWRITE_TAC [RIGHT_OR_DISTRIB, EXISTS_OR_THM, UNWIND_THM2] THEN
    INT_ARITH_TAC)

  let INT_DIVIDES_ANTISYM_ABS ← prove
   r"!x y. x divides y /\ y divides x <=> abs(x) = abs(y)"
   (REWRITE_TAC [INT_DIVIDES_ANTISYM] THEN INT_ARITH_TAC)

  let INT_DIVIDES_ANTISYM_POS ← prove
   r"!x y. &0 <= x /\ &0 <= y ==> (x divides y /\ y divides x <=> x = y)"
   (REWRITE_TAC [INT_DIVIDES_ANTISYM_ABS] THEN INT_ARITH_TAC)

  -- @@RETURN BEGIN
  return { INT_DIVIDES_REFL, INT_DIVIDES_TRANS, INT_DIVIDES_ADD, INT_DIVIDES_SUB,
           INT_DIVIDES_0, INT_DIVIDES_ZERO, INT_DIVIDES_LNEG, INT_DIVIDES_RNEG,
           INT_DIVIDES_RMUL, INT_DIVIDES_LMUL, INT_DIVIDES_1, INT_DIVIDES_ADD_REVR,
           INT_DIVIDES_ADD_REVL, INT_DIVIDES_MUL_L, INT_DIVIDES_MUL_R, INT_DIVIDES_LMUL2,
           INT_DIVIDES_RMUL2, INT_DIVIDES_CMUL2, INT_DIVIDES_LMUL2_EQ,
           INT_DIVIDES_RMUL2_EQ, INT_DIVIDES_MUL2, INT_DIVIDES_POW, INT_DIVIDES_POW2,
           INT_DIVIDES_RPOW, INT_DIVIDES_RPOW_SUC, INT_DIVIDES_POW_LE_IMP,
           INT_DIVIDES_ANTISYM_DIVISORS, INT_DIVIDES_ANTISYM_MULTIPLES,
           INT_DIVIDES_ONE_POS, INT_DIVIDES_ONE_ABS, INT_DIVIDES_ONE,
           INT_DIVIDES_ANTISYM_ASSOCIATED, INT_DIVIDES_ANTISYM, INT_DIVIDES_ANTISYM_ABS,
           INT_DIVIDES_ANTISYM_POS }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Lemmas about GCDs.  (integer.ml 146-321)                                  -/
/- ------------------------------------------------------------------------- -/

structure Gcd where
  -- @@FIELDS
  INT_GCD_POS : thm
  INT_ABS_GCD : thm
  INT_GCD_DIVIDES : thm
  INT_COPRIME_GCD : thm
  INT_GCD_BEZOUT : thm
  INT_DIVIDES_GCD : thm
  INT_GCD : thm
  INT_GCD_UNIQUE : thm
  INT_GCD_UNIQUE_ABS : thm
  INT_GCD_REFL : thm
  INT_GCD_SYM : thm
  INT_GCD_ASSOC : thm
  INT_GCD_1 : thm
  INT_GCD_0 : thm
  INT_GCD_EQ_0 : thm
  INT_GCD_ABS : thm
  INT_GCD_ADD : thm
  INT_GCD_SUB : thm
  INT_DIVIDES_GCD_LEFT : thm
  INT_DIVIDES_GCD_RIGHT : thm
  INT_GCD_EQ : thm
  INT_GCD_LNEG : thm
  INT_GCD_RNEG : thm
  INT_GCD_NEG : thm
  INT_GCD_LABS : thm
  INT_GCD_RABS : thm
  INT_GCD_LMUL : thm
  INT_GCD_RMUL : thm
  INT_GCD_COPRIME_LMUL : thm
  INT_GCD_COPRIME_RMUL : thm
  INT_GCD_COPRIME_DIVIDES_LMUL : thm
  INT_GCD_COPRIME_DIVIDES_RMUL : thm
  INT_GCD_COPRIME_EXISTS : thm
  deriving Inhabited

@[nospecialize]
def setupGcd [HolBase] (D : IntegerDeps) (BDivides : Divides) :
    ExceptT String IO Gcd := do
  -- @@SCOPE BEGIN
  let { INTEGER_RULE, INTEGER_TAC, INT_REDUCE_CONV, MESON_TAC, .. } := D
  let { INT_ABS, INT_ABS_MUL, INT_ABS_POS, INT_DIVIDES_ABS, INT_MUL_SYM, INT_POS, .. } := D.core1
  let { int_gcd, .. } := D.core2
  let { INT_DIVIDES_1, INT_DIVIDES_ANTISYM_ABS, INT_DIVIDES_ANTISYM_POS,
        INT_DIVIDES_ONE_POS, INT_DIVIDES_REFL, INT_DIVIDES_TRANS, .. } := BDivides
  -- @@SCOPE END

  let INT_GCD_POS ← prove
   r"!a b. &0 <= gcd(a,b)"
   (REWRITE_TAC [int_gcd])

  let INT_ABS_GCD ← prove
   r"!a b. abs(gcd(a,b)) = gcd(a,b)"
   (REWRITE_TAC [INT_ABS, INT_GCD_POS])

  let INT_GCD_DIVIDES ← prove
   r"!a b. gcd(a,b) divides a /\ gcd(a,b) divides b"
   (INTEGER_TAC)

  let INT_COPRIME_GCD ← prove
   r"!a b. coprime(a,b) <=> gcd(a,b) = &1"
   (SIMP_TAC [← GSYM INT_DIVIDES_ONE_POS, INT_GCD_POS] THEN INTEGER_TAC)

  let INT_GCD_BEZOUT ← prove
   r"!a b. ?x y. gcd(a,b) = a * x + b * y"
   (INTEGER_TAC)

  let INT_DIVIDES_GCD ← prove
   r"!a b d. d divides gcd(a,b) <=> d divides a /\ d divides b"
   (INTEGER_TAC)

  let INT_GCD ← INTEGER_RULE (← q
   r"!a b. (gcd(a,b) divides a /\ gcd(a,b) divides b) /\
          (!e. e divides a /\ e divides b ==> e divides gcd(a,b))")

  let INT_GCD_UNIQUE ← prove
   r"!a b d. gcd(a,b) = d <=> &0 <= d /\ d divides a /\ d divides b /\
                              !e. e divides a /\ e divides b ==> e divides d"
   (REPEAT GEN_TAC THEN EQ_TAC THENL
     [MESON_TAC [INT_GCD, INT_GCD_POS], ALL_TAC] THEN
    ASM_SIMP_TAC [INT_GCD_POS, ← GSYM INT_DIVIDES_ANTISYM_POS, INT_DIVIDES_GCD] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN INTEGER_TAC)

  let INT_GCD_UNIQUE_ABS ← prove
   r"!a b d. gcd(a,b) = abs(d) <=>
             d divides a /\ d divides b /\
             !e. e divides a /\ e divides b ==> e divides d"
   (REWRITE_TAC [INT_GCD_UNIQUE, INT_ABS_POS, INT_DIVIDES_ABS])

  let INT_GCD_REFL ← prove
   r"!a. gcd(a,a) = abs(a)"
   (REWRITE_TAC [INT_GCD_UNIQUE_ABS] THEN INTEGER_TAC)

  let INT_GCD_SYM ← prove
   r"!a b. gcd(a,b) = gcd(b,a)"
   (SIMP_TAC [INT_GCD_POS, ← GSYM INT_DIVIDES_ANTISYM_POS] THEN INTEGER_TAC)

  let INT_GCD_ASSOC ← prove
   r"!a b c. gcd(a,gcd(b,c)) = gcd(gcd(a,b),c)"
   (SIMP_TAC [INT_GCD_POS, ← GSYM INT_DIVIDES_ANTISYM_POS] THEN INTEGER_TAC)

  let INT_GCD_1 ← prove
   r"!a. gcd(a,&1) = &1 /\ gcd(&1,a) = &1"
   (SIMP_TAC [INT_GCD_UNIQUE, INT_POS, INT_DIVIDES_1])

  let INT_GCD_0 ← prove
   r"!a. gcd(a,&0) = abs(a) /\ gcd(&0,a) = abs(a)"
   (SIMP_TAC [INT_GCD_UNIQUE_ABS] THEN INTEGER_TAC)

  let INT_GCD_EQ_0 ← prove
   r"!a b. gcd(a,b) = &0 <=> a = &0 /\ b = &0"
   (INTEGER_TAC)

  let INT_GCD_ABS ← prove
   r"!a b. gcd(abs(a),b) = gcd(a,b) /\ gcd(a,abs(b)) = gcd(a,b)"
   (REWRITE_TAC [INT_GCD_UNIQUE, INT_DIVIDES_ABS, INT_GCD_POS, INT_GCD])
  -- integer.ml binds INT_GCD_ABS twice (lines 216 and 279); the second
  -- shadows this one.  Discard to match OCaml's dead first binding.
  let _ := INT_GCD_ABS

  -- NB: integer.ml omits `prove` here, so INT_GCD_MULTIPLE is a (term,tactic)
  -- pair, not a theorem; it is never used.  Translated faithfully as a pair.
  let loc_mult_tm ← q
   r"!a b. gcd(a,a * b) = abs(a) /\ gcd(b,a * b) = abs(b)"
  let INT_GCD_MULTIPLE :=
   (loc_mult_tm,
    (REWRITE_TAC [INT_GCD_UNIQUE_ABS] THEN INTEGER_TAC))
  let _ := INT_GCD_MULTIPLE

  let INT_GCD_ADD ← prove
   r"(!a b. gcd(a + b,b) = gcd(a,b)) /\
     (!a b. gcd(b + a,b) = gcd(a,b)) /\
     (!a b. gcd(a,a + b) = gcd(a,b)) /\
     (!a b. gcd(a,b + a) = gcd(a,b))"
   (SIMP_TAC [INT_GCD_UNIQUE, INT_GCD_POS] THEN INTEGER_TAC)

  let INT_GCD_SUB ← prove
   r"(!a b. gcd(a - b,b) = gcd(a,b)) /\
     (!a b. gcd(b - a,b) = gcd(a,b)) /\
     (!a b. gcd(a,a - b) = gcd(a,b)) /\
     (!a b. gcd(a,b - a) = gcd(a,b))"
   (SIMP_TAC [INT_GCD_UNIQUE, INT_GCD_POS] THEN INTEGER_TAC)

  let INT_DIVIDES_GCD_LEFT ← prove
   r"!m n:int. m divides n <=> gcd(m,n) = abs m"
   (SIMP_TAC [INT_GCD_UNIQUE, INT_ABS_POS, INT_DIVIDES_ABS, INT_DIVIDES_REFL] THEN
    MESON_TAC [INT_DIVIDES_REFL, INT_DIVIDES_TRANS])

  let INT_DIVIDES_GCD_RIGHT ← prove
   r"!m n:int. n divides m <=> gcd(m,n) = abs n"
   (SIMP_TAC [INT_GCD_UNIQUE, INT_ABS_POS, INT_DIVIDES_ABS, INT_DIVIDES_REFL] THEN
    MESON_TAC [INT_DIVIDES_REFL, INT_DIVIDES_TRANS])

  let INT_GCD_EQ ← prove
   r"!x y u v:int.
          (!d. d divides x /\ d divides y <=> d divides u /\ d divides v)
          ==> gcd(x,y) = gcd(u,v)"
   (REPEAT STRIP_TAC THEN
    SIMP_TAC [← GSYM INT_DIVIDES_ANTISYM_POS, INT_GCD_POS] THEN
    ASM_REWRITE_TAC [INT_DIVIDES_GCD, INT_GCD_DIVIDES] THEN
    FIRST_X_ASSUM (fun th => tactic_of do pure (REWRITE_TAC [← GSYM th])) THEN
    REWRITE_TAC [INT_GCD_DIVIDES])

  let INT_GCD_LNEG ← prove
   r"!a b:int. gcd(--a,b) = gcd(a,b)"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC INT_GCD_EQ THEN INTEGER_TAC)

  let INT_GCD_RNEG ← prove
   r"!a b:int. gcd(a,--b) = gcd(a,b)"
   (REPEAT GEN_TAC THEN MATCH_MP_TAC INT_GCD_EQ THEN INTEGER_TAC)

  let INT_GCD_NEG ← prove
   r"(!a b. gcd(--a,b) = gcd(a,b)) /\
     (!a b. gcd(a,--b) = gcd(a,b))"
   (REWRITE_TAC [INT_GCD_LNEG, INT_GCD_RNEG])

  let INT_GCD_LABS ← prove
   r"!a b. gcd(abs a,b) = gcd(a,b)"
   (REWRITE_TAC [INT_ABS] THEN MESON_TAC [INT_GCD_LNEG])

  let INT_GCD_RABS ← prove
   r"!a b. gcd(a,abs b) = gcd(a,b)"
   (REWRITE_TAC [INT_ABS] THEN MESON_TAC [INT_GCD_RNEG])

  let INT_GCD_ABS ← prove
   r"(!a b. gcd(abs a,b) = gcd(a,b)) /\
     (!a b. gcd(a,abs b) = gcd(a,b))"
   (REWRITE_TAC [INT_GCD_LABS, INT_GCD_RABS])

  let INT_GCD_LMUL ← prove
   r"!a b c:int. gcd(c * a,c * b) = abs c * gcd(a,b)"
   (ONCE_REWRITE_TAC [← GSYM INT_ABS_GCD] THEN REWRITE_TAC [← GSYM INT_ABS_MUL] THEN
    REWRITE_TAC [← GSYM INT_DIVIDES_ANTISYM_ABS] THEN CONV_TAC INTEGER_RULE)

  let INT_GCD_RMUL ← prove
   r"!a b c:int. gcd(a * c,b * c) = gcd(a,b) * abs c"
   (ONCE_REWRITE_TAC [INT_MUL_SYM] THEN REWRITE_TAC [INT_GCD_LMUL])

  let INT_GCD_COPRIME_LMUL ← prove
   r"!a b c:int. coprime(a,b) ==> gcd(a * b,c) = gcd(a,c) * gcd(b,c)"
   (ONCE_REWRITE_TAC [← GSYM INT_ABS_GCD] THEN REWRITE_TAC [← GSYM INT_ABS_MUL] THEN
    REWRITE_TAC [← GSYM INT_DIVIDES_ANTISYM_ABS] THEN CONV_TAC INTEGER_RULE)

  let INT_GCD_COPRIME_RMUL ← prove
   r"!a b c:int. coprime(b,c) ==> gcd(a, b * c) = gcd(a,b) * gcd(a,c)"
   (ONCE_REWRITE_TAC [INT_GCD_SYM] THEN REWRITE_TAC [INT_GCD_COPRIME_LMUL])

  let INT_GCD_COPRIME_DIVIDES_LMUL ← prove
   r"!a b c:int. coprime(a,b) /\ a divides c
                  ==> gcd(a * b,c) = abs a * gcd(b,c)"
   (ONCE_REWRITE_TAC [← GSYM INT_ABS_GCD] THEN REWRITE_TAC [← GSYM INT_ABS_MUL] THEN
    REWRITE_TAC [← GSYM INT_DIVIDES_ANTISYM_ABS] THEN CONV_TAC INTEGER_RULE)

  let INT_GCD_COPRIME_DIVIDES_RMUL ← prove
   r"!a b c:int. coprime(b,c) /\ b divides a
                 ==> gcd(a,b * c) = abs b * gcd(a,c)"
   (ONCE_REWRITE_TAC [INT_GCD_SYM] THEN
    REWRITE_TAC [INT_GCD_COPRIME_DIVIDES_LMUL])

  let INT_GCD_COPRIME_EXISTS ← prove
   r"!a b. ?a' b'. a = a' * gcd(a,b) /\ b = b' * gcd(a,b) /\ coprime(a',b')"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"gcd(a,b):int = &0") THENL
     [ALL_TAC, POP_ASSUM MP_TAC THEN CONV_TAC INTEGER_RULE] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [INT_GCD_EQ_0]) THEN
    REPEAT (EXISTS_TAC (← q r"&1:int")) THEN ASM_REWRITE_TAC [INT_GCD_0] THEN
    CONV_TAC INT_REDUCE_CONV THEN CONV_TAC INTEGER_RULE)

  -- @@RETURN BEGIN
  return { INT_GCD_POS, INT_ABS_GCD, INT_GCD_DIVIDES, INT_COPRIME_GCD, INT_GCD_BEZOUT,
           INT_DIVIDES_GCD, INT_GCD, INT_GCD_UNIQUE, INT_GCD_UNIQUE_ABS, INT_GCD_REFL,
           INT_GCD_SYM, INT_GCD_ASSOC, INT_GCD_1, INT_GCD_0, INT_GCD_EQ_0, INT_GCD_ABS,
           INT_GCD_ADD, INT_GCD_SUB, INT_DIVIDES_GCD_LEFT, INT_DIVIDES_GCD_RIGHT,
           INT_GCD_EQ, INT_GCD_LNEG, INT_GCD_RNEG, INT_GCD_NEG, INT_GCD_LABS,
           INT_GCD_RABS, INT_GCD_LMUL, INT_GCD_RMUL, INT_GCD_COPRIME_LMUL,
           INT_GCD_COPRIME_RMUL, INT_GCD_COPRIME_DIVIDES_LMUL,
           INT_GCD_COPRIME_DIVIDES_RMUL, INT_GCD_COPRIME_EXISTS }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Lemmas about lcms.  (integer.ml 322-436)                                  -/
/- ------------------------------------------------------------------------- -/

structure Lcm where
  -- @@FIELDS
  INT_ABS_LCM : thm
  INT_LCM_EQ_0 : thm
  INT_DIVIDES_LCM : thm
  INT_LCM_0 : thm
  INT_LCM_1 : thm
  INT_LCM_UNIQUE_ABS : thm
  INT_LCM_UNIQUE : thm
  INT_LCM_EQ : thm
  INT_LCM_REFL : thm
  INT_LCM_SYM : thm
  INT_LCM_ASSOC : thm
  INT_LCM_LNEG : thm
  INT_LCM_RNEG : thm
  INT_LCM_NEG : thm
  INT_LCM_LABS : thm
  INT_LCM_RABS : thm
  INT_LCM_ABS : thm
  INT_LCM_LMUL : thm
  INT_LCM_RMUL : thm
  deriving Inhabited

@[nospecialize]
def setupLcm [HolBase] (D : IntegerDeps) (BDivides : Divides) (BGcd : Gcd) :
    ExceptT String IO Lcm := do
  -- @@SCOPE BEGIN
  let { INTEGER_RULE, INTEGER_TAC, INT_ARITH, INT_ARITH_TAC, INT_RING, MESON_TAC, .. } := D
  let { CONJ_ASSOC, INT_ABS, INT_ABS_MUL, INT_ABS_NEG, INT_ABS_NUM, INT_ABS_ZERO,
        INT_DIVIDES_LCM_GCD, INT_DIV_1, INT_DIV_MUL, INT_ENTIRE, INT_LCM_DIVIDES,
        INT_LCM_POS, INT_MUL_AC, INT_MUL_LCM_GCD, INT_MUL_LID, INT_MUL_LNEG,
        INT_MUL_LZERO, INT_MUL_RID, INT_MUL_RNEG, INT_MUL_RZERO, INT_MUL_SYM,
        INT_NEG_EQ_0, .. } := D.core1
  let { int_lcm, .. } := D.core2
  let { INT_DIVIDES_ANTISYM_ABS, INT_DIVIDES_ANTISYM_MULTIPLES, INT_DIVIDES_REFL,
        INT_DIVIDES_TRANS, .. } := BDivides
  let { INT_GCD_1, INT_GCD_EQ_0, INT_GCD_LMUL, INT_GCD_LNEG, INT_GCD_REFL,
        INT_GCD_RNEG, INT_GCD_SYM, .. } := BGcd
  -- @@SCOPE END

  let INT_ABS_LCM ← prove
   r"!a b. abs(lcm(a,b)) = lcm(a,b)"
   (REWRITE_TAC [INT_ABS, INT_LCM_POS])

  let INT_LCM_EQ_0 ← prove
   r"!m n. lcm(m,n) = &0 <=> m = &0 \/ n = &0"
   (← do
    let i1 ← INTEGER_RULE (← q r"n:int = &0 <=> &0 divides n")
    pure (REWRITE_TAC [i1] THEN
    REWRITE_TAC [INT_DIVIDES_LCM_GCD] THEN INTEGER_TAC))

  let INT_DIVIDES_LCM ← prove
   r"!m n r. r divides m \/ r divides n ==> r divides lcm(m,n)"
   (REWRITE_TAC [INT_DIVIDES_LCM_GCD] THEN INTEGER_TAC)

  let INT_LCM_0 ← prove
   r"(!n. lcm(&0,n) = &0) /\ (!n. lcm(n,&0) = &0)"
   (REWRITE_TAC [INT_LCM_EQ_0])

  let INT_LCM_1 ← prove
   r"(!n. lcm(&1,n) = abs n) /\ (!n. lcm(n,&1) = abs n)"
   (SIMP_TAC [int_lcm, INT_MUL_LID, INT_MUL_RID, INT_GCD_1] THEN
    GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [INT_DIV_1, INT_ABS_NUM])

  let INT_LCM_UNIQUE_ABS ← prove
   r"!a b m.
          lcm(a,b) = abs m <=>
          a divides m /\
          b divides m /\
          (!n. a divides n /\ b divides n  ==> m divides n)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM INT_ABS_LCM] THEN
    REWRITE_TAC [← GSYM INT_DIVIDES_ANTISYM_ABS, INT_DIVIDES_ANTISYM_MULTIPLES] THEN
    REWRITE_TAC [INT_LCM_DIVIDES] THEN
    MESON_TAC [INT_DIVIDES_REFL, INT_DIVIDES_TRANS])

  let INT_LCM_UNIQUE ← prove
   r"!a b m.
          lcm(a,b) = m <=>
          &0 <= m /\
          a divides m /\
          b divides m /\
          (!n. a divides n /\ b divides n ==> m divides n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [← GSYM INT_LCM_UNIQUE_ABS] THEN
    MP_TAC (← SPECL [← q r"a:int", ← q r"b:int"] INT_LCM_POS) THEN INT_ARITH_TAC)

  let INT_LCM_EQ ← prove
   r"!x y u v.
          (!m. x divides m /\ y divides m <=> u divides m /\ v divides m)
          ==> lcm(x,y) = lcm(u,v)"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [← GSYM INT_ABS_LCM] THEN
    REWRITE_TAC [← GSYM INT_DIVIDES_ANTISYM_ABS, INT_DIVIDES_ANTISYM_MULTIPLES] THEN
    ASM_REWRITE_TAC [INT_LCM_DIVIDES])

  let INT_LCM_REFL ← prove
   r"!n. lcm(n,n) = abs n"
   (REWRITE_TAC [int_lcm, INT_GCD_REFL, INT_ENTIRE] THEN
    GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [INT_ABS_NUM, INT_ABS_MUL] THEN
    ASM_SIMP_TAC [INT_DIV_MUL, INT_ABS_ZERO])

  let INT_LCM_SYM ← prove
   r"!m n. lcm(m,n) = lcm(n,m)"
   (REWRITE_TAC [int_lcm, INT_GCD_SYM, INT_MUL_SYM])

  let INT_LCM_ASSOC ← prove
   r"!m n p. lcm(m,lcm(n,p)) = lcm(lcm(m,n),p)"
   (REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM INT_ABS_LCM] THEN
    REWRITE_TAC [← GSYM INT_DIVIDES_ANTISYM_ABS, INT_DIVIDES_ANTISYM_MULTIPLES] THEN
    REWRITE_TAC [INT_LCM_DIVIDES] THEN REWRITE_TAC [CONJ_ASSOC])

  let INT_LCM_LNEG ← prove
   r"!a b:int. lcm(--a,b) = lcm(a,b)"
   (SIMP_TAC [int_lcm, INT_MUL_LNEG, INT_ABS_NEG, INT_GCD_LNEG, INT_NEG_EQ_0])

  let INT_LCM_RNEG ← prove
   r"!a b:int. lcm(a,--b) = lcm(a,b)"
   (SIMP_TAC [int_lcm, INT_MUL_RNEG, INT_ABS_NEG, INT_GCD_RNEG, INT_NEG_EQ_0])

  let INT_LCM_NEG ← prove
   r"(!a b. lcm(--a,b) = lcm(a,b)) /\
     (!a b. lcm(a,--b) = lcm(a,b))"
   (REWRITE_TAC [INT_LCM_LNEG, INT_LCM_RNEG])

  let INT_LCM_LABS ← prove
   r"!a b. lcm(abs a,b) = lcm(a,b)"
   (REWRITE_TAC [INT_ABS] THEN MESON_TAC [INT_LCM_LNEG])

  let INT_LCM_RABS ← prove
   r"!a b. lcm(a,abs b) = lcm(a,b)"
   (REWRITE_TAC [INT_ABS] THEN MESON_TAC [INT_LCM_RNEG])

  let INT_LCM_ABS ← prove
   r"(!a b. lcm(abs a,b) = lcm(a,b)) /\
     (!a b. lcm(a,abs b) = lcm(a,b))"
   (REWRITE_TAC [INT_LCM_LABS, INT_LCM_RABS])

  let INT_LCM_LMUL ← prove
   r"!a b c:int. lcm(c * a,c * b) = abs c * lcm(a,b)"
   (← do
    let a2 ← INT_ARITH (← q r"(x * a) * x * b:int = x * x * a * b")
    let r1 ← INT_RING (← q r"!x:int. ~(x = &0) /\ a * x = b * x ==> a = b")
    pure (REPEAT GEN_TAC THEN
    MAP_EVERY ASM_CASES_TAC [← q r"a:int = &0", ← q r"b:int = &0", ← q r"c:int = &0"] THEN
    ASM_REWRITE_TAC [INT_MUL_LZERO, INT_MUL_RZERO, INT_ABS_NUM, INT_LCM_0] THEN
    MATCH_MP_TAC r1 THEN
    EXISTS_TAC (← q r"gcd(c * a:int,c * b)") THEN
    ASM_REWRITE_TAC [INT_GCD_EQ_0, INT_ENTIRE, INT_MUL_LCM_GCD] THEN
    REWRITE_TAC [INT_GCD_LMUL, INT_MUL_LCM_GCD, a2] THEN
    REWRITE_TAC [INT_ABS_MUL, INT_MUL_AC]))

  let INT_LCM_RMUL ← prove
   r"!a b c:int. lcm(a * c,b * c) = lcm(a,b) * abs c"
   (ONCE_REWRITE_TAC [INT_MUL_SYM] THEN REWRITE_TAC [INT_LCM_LMUL])

  -- @@RETURN BEGIN
  return { INT_ABS_LCM, INT_LCM_EQ_0, INT_DIVIDES_LCM, INT_LCM_0, INT_LCM_1,
           INT_LCM_UNIQUE_ABS, INT_LCM_UNIQUE, INT_LCM_EQ, INT_LCM_REFL, INT_LCM_SYM,
           INT_LCM_ASSOC, INT_LCM_LNEG, INT_LCM_RNEG, INT_LCM_NEG, INT_LCM_LABS,
           INT_LCM_RABS, INT_LCM_ABS, INT_LCM_LMUL, INT_LCM_RMUL }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- More lemmas about coprimality.  (integer.ml 437-598)                      -/
/- ------------------------------------------------------------------------- -/

structure Coprime where
  -- @@FIELDS
  INT_COPRIME : thm
  INT_COPRIME_ALT : thm
  INT_COPRIME_SYM : thm
  INT_COPRIME_DIVPROD : thm
  INT_COPRIME_1 : thm
  INT_GCD_COPRIME : thm
  INT_COPRIME_0 : thm
  INT_COPRIME_MUL : thm
  INT_COPRIME_LMUL2 : thm
  INT_COPRIME_RMUL2 : thm
  INT_COPRIME_LMUL : thm
  INT_COPRIME_RMUL : thm
  INT_COPRIME_REFL : thm
  INT_COPRIME_PLUS1 : thm
  INT_COPRIME_MINUS1 : thm
  INT_COPRIME_RPOW : thm
  INT_COPRIME_LPOW : thm
  INT_COPRIME_POW2 : thm
  INT_COPRIME_POW : thm
  INT_COPRIME_POW_IMP : thm
  INT_GCD_POW : thm
  INT_LCM_POW : thm
  INT_DIVISION_DECOMP : thm
  INT_DIVIDES_MUL : thm
  INT_CHINESE_REMAINDER : thm
  INT_CHINESE_REMAINDER_USUAL : thm
  INT_COPRIME_DIVISORS : thm
  INT_COPRIME_LNEG : thm
  INT_COPRIME_RNEG : thm
  INT_COPRIME_NEG : thm
  INT_COPRIME_LABS : thm
  INT_COPRIME_RABS : thm
  INT_COPRIME_ABS : thm
  deriving Inhabited

@[nospecialize]
def setupCoprime [HolBase] (D : IntegerDeps) (BDivides : Divides) (BGcd : Gcd) (BLcm : Lcm) :
    ExceptT String IO Coprime := do
  -- @@SCOPE BEGIN
  let { INDUCT_TAC, INTEGER_TAC, INT_RING, MESON_TAC, .. } := D
  let { DISJ_ACI, INT_ABS, INT_ABS_NUM, INT_ABS_POW, INT_MUL_LCM_GCD, INT_MUL_LZERO,
        INT_POS, INT_POW, INT_POW_EQ_0, INT_POW_MUL, INT_POW_ONE, INT_POW_ZERO,
        LEFT_IMP_EXISTS_THM, .. } := D.core1
  let { NOT_SUC, .. } := D.core2
  let { INT_DIVIDES_1, INT_DIVIDES_REFL, INT_DIVIDES_TRANS, .. } := BDivides
  let { INT_COPRIME_GCD, INT_GCD_0, INT_GCD_COPRIME_EXISTS, INT_GCD_EQ_0, INT_GCD_RMUL,
        INT_GCD_UNIQUE, .. } := BGcd
  let { INT_LCM_0, INT_LCM_1, .. } := BLcm
  -- @@SCOPE END

  let INT_COPRIME ← prove
   r"!a b. coprime(a,b) <=> !d. d divides a /\ d divides b ==> d divides &1"
   (REWRITE_TAC [INT_COPRIME_GCD, INT_GCD_UNIQUE, INT_POS, INT_DIVIDES_1])

  let INT_COPRIME_ALT ← prove
   r"!a b. coprime(a,b) <=> !d. d divides a /\ d divides b <=> d divides &1"
   (MESON_TAC [INT_DIVIDES_1, INT_DIVIDES_TRANS, INT_COPRIME])

  let INT_COPRIME_SYM ← prove
   r"!a b. coprime(a,b) <=> coprime(b,a)"
   (INTEGER_TAC)

  let INT_COPRIME_DIVPROD ← prove
   r"!d a b. d divides (a * b) /\ coprime(d,a) ==> d divides b"
   (INTEGER_TAC)

  let INT_COPRIME_1 ← prove
   r"!a. coprime(a,&1) /\ coprime(&1,a)"
   (INTEGER_TAC)

  let INT_GCD_COPRIME ← prove
   r"!a b a' b'. ~(gcd(a,b) = &0) /\ a = a' * gcd(a,b) /\ b = b' * gcd(a,b)
                 ==> coprime(a',b')"
   (INTEGER_TAC)

  let INT_COPRIME_0 ← prove
   r"(!a. coprime(a,&0) <=> a divides &1) /\
     (!a. coprime(&0,a) <=> a divides &1)"
   (INTEGER_TAC)

  let INT_COPRIME_MUL ← prove
   r"!d a b. coprime(d,a) /\ coprime(d,b) ==> coprime(d,a * b)"
   (INTEGER_TAC)

  let INT_COPRIME_LMUL2 ← prove
   r"!d a b. coprime(d,a * b) ==> coprime(d,b)"
   (INTEGER_TAC)

  let INT_COPRIME_RMUL2 ← prove
   r"!d a b.  coprime(d,a * b) ==> coprime(d,a)"
   (INTEGER_TAC)

  let INT_COPRIME_LMUL ← prove
   r"!d a b. coprime(a * b,d) <=> coprime(a,d) /\ coprime(b,d)"
   (INTEGER_TAC)

  let INT_COPRIME_RMUL ← prove
   r"!d a b. coprime(d,a * b) <=> coprime(d,a) /\ coprime(d,b)"
   (INTEGER_TAC)

  let INT_COPRIME_REFL ← prove
   r"!n. coprime(n,n) <=> n divides &1"
   (INTEGER_TAC)

  let INT_COPRIME_PLUS1 ← prove
   r"!n. coprime(n + &1,n) /\ coprime(n,n + &1)"
   (INTEGER_TAC)

  let INT_COPRIME_MINUS1 ← prove
   r"!n. coprime(n - &1,n) /\ coprime(n,n - &1)"
   (INTEGER_TAC)

  let INT_COPRIME_RPOW ← prove
   r"!m n k. coprime(m,n pow k) <=> coprime(m,n) \/ k = 0"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_SIMP_TAC [INT_POW, INT_COPRIME_1, INT_COPRIME_RMUL, NOT_SUC] THEN
    CONV_TAC TAUT)

  let INT_COPRIME_LPOW ← prove
   r"!m n k. coprime(m pow k,n) <=> coprime(m,n) \/ k = 0"
   (ONCE_REWRITE_TAC [INT_COPRIME_SYM] THEN REWRITE_TAC [INT_COPRIME_RPOW])

  let INT_COPRIME_POW2 ← prove
   r"!m n k. coprime(m pow k,n pow k) <=> coprime(m,n) \/ k = 0"
   (REWRITE_TAC [INT_COPRIME_RPOW, INT_COPRIME_LPOW, DISJ_ACI])

  let INT_COPRIME_POW ← prove
   r"!n a d. coprime(d,a) ==> coprime(d,a pow n)"
   (SIMP_TAC [INT_COPRIME_RPOW])

  let INT_COPRIME_POW_IMP ← prove
   r"!n a b. coprime(a,b) ==> coprime(a pow n,b pow n)"
   (MESON_TAC [INT_COPRIME_POW, INT_COPRIME_SYM])

  let INT_GCD_POW ← prove
   r"!(a:int) b n. gcd(a pow n,b pow n) = gcd(a,b) pow n"
   (← do
    let e1 := (← EQ_IMP_RULE (← SPEC_ALL INT_COPRIME_GCD)).1
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"a:int", ← q r"b:int"] INT_GCD_COPRIME_EXISTS) THEN
    REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"a':int", ← q r"b':int"] THEN
    STRIP_TAC THEN ONCE_ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [INT_POW_MUL, INT_GCD_RMUL, INT_ABS_POW] THEN
    ASM_SIMP_TAC [e1, INT_COPRIME_POW2, INT_POW_ONE]))

  let INT_LCM_POW ← prove
   r"!(a:int) b n. lcm(a pow n,b pow n) = lcm(a,b) pow n"
   (← do
    let r1 ← INT_RING (← q r"!x:int. ~(x = &0) /\ a * x = b * x ==> a = b")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_REWRITE_TAC [INT_POW, INT_LCM_1, INT_POW_ONE, INT_ABS_NUM] THEN
    MAP_EVERY ASM_CASES_TAC [← q r"a:int = &0", ← q r"b:int = &0"] THEN
    ASM_REWRITE_TAC [INT_POW_ZERO, INT_LCM_0] THEN
    MATCH_MP_TAC r1 THEN
    EXISTS_TAC (← q r"gcd((a:int) pow n,b pow n)") THEN
    ASM_REWRITE_TAC [INT_GCD_EQ_0, INT_POW_EQ_0, INT_MUL_LCM_GCD] THEN
    REWRITE_TAC [INT_GCD_POW, ← GSYM INT_POW_MUL] THEN
    REWRITE_TAC [INT_MUL_LCM_GCD, INT_ABS_POW]))

  let INT_DIVISION_DECOMP ← prove
   r"!a b c. a divides (b * c)
             ==> ?b' c'. (a = b' * c') /\ b' divides b /\ c' divides c"
   (REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"gcd(a,b)") THEN
    ASM_CASES_TAC (← q r"gcd(a,b) = &0") THEN REPEAT (POP_ASSUM MP_TAC) THENL
     [SIMP_TAC [INT_GCD_EQ_0, INT_GCD_0, INT_ABS_NUM], INTEGER_TAC] THEN
    REWRITE_TAC [INT_MUL_LZERO] THEN MESON_TAC [INT_DIVIDES_REFL])

  let INT_DIVIDES_MUL ← prove
   r"!m n r. m divides r /\ n divides r /\ coprime(m,n) ==> (m * n) divides r"
   (INTEGER_TAC)

  let INT_CHINESE_REMAINDER ← prove
   r"!a b u v. coprime(a,b) /\ ~(a = &0) /\ ~(b = &0)
               ==> ?x q1 q2. (x = u + q1 * a) /\ (x = v + q2 * b)"
   (INTEGER_TAC)

  let INT_CHINESE_REMAINDER_USUAL ← prove
   r"!a b u v. coprime(a,b) ==> ?x. (x == u) (mod a) /\ (x == v) (mod b)"
   (INTEGER_TAC)

  let INT_COPRIME_DIVISORS ← prove
   r"!a b d e. d divides a /\ e divides b /\ coprime(a,b) ==> coprime(d,e)"
   (INTEGER_TAC)

  let INT_COPRIME_LNEG ← prove
   r"!a b. coprime(--a,b) <=> coprime(a,b)"
   (INTEGER_TAC)

  let INT_COPRIME_RNEG ← prove
   r"!a b. coprime(a,--b) <=> coprime(a,b)"
   (INTEGER_TAC)

  let INT_COPRIME_NEG ← prove
   r"(!a b. coprime(--a,b) <=> coprime(a,b)) /\
     (!a b. coprime(a,--b) <=> coprime(a,b))"
   (INTEGER_TAC)

  let INT_COPRIME_LABS ← prove
   r"!a b. coprime(abs a,b) <=> coprime(a,b)"
   (REWRITE_TAC [INT_ABS] THEN MESON_TAC [INT_COPRIME_LNEG])

  let INT_COPRIME_RABS ← prove
   r"!a b. coprime(a,abs b) <=> coprime(a,b)"
   (REWRITE_TAC [INT_ABS] THEN MESON_TAC [INT_COPRIME_RNEG])

  let INT_COPRIME_ABS ← prove
   r"(!a b. coprime(abs a,b) <=> coprime(a,b)) /\
     (!a b. coprime(a,abs b) <=> coprime(a,b))"
   (REWRITE_TAC [INT_COPRIME_LABS, INT_COPRIME_RABS])

  -- @@RETURN BEGIN
  return { INT_COPRIME, INT_COPRIME_ALT, INT_COPRIME_SYM, INT_COPRIME_DIVPROD,
           INT_COPRIME_1, INT_GCD_COPRIME, INT_COPRIME_0, INT_COPRIME_MUL,
           INT_COPRIME_LMUL2, INT_COPRIME_RMUL2, INT_COPRIME_LMUL, INT_COPRIME_RMUL,
           INT_COPRIME_REFL, INT_COPRIME_PLUS1, INT_COPRIME_MINUS1, INT_COPRIME_RPOW,
           INT_COPRIME_LPOW, INT_COPRIME_POW2, INT_COPRIME_POW, INT_COPRIME_POW_IMP,
           INT_GCD_POW, INT_LCM_POW, INT_DIVISION_DECOMP, INT_DIVIDES_MUL,
           INT_CHINESE_REMAINDER, INT_CHINESE_REMAINDER_USUAL, INT_COPRIME_DIVISORS,
           INT_COPRIME_LNEG, INT_COPRIME_RNEG, INT_COPRIME_NEG, INT_COPRIME_LABS,
           INT_COPRIME_RABS, INT_COPRIME_ABS }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- More lemmas about congruences.  (integer.ml 600-841)                      -/
/- ------------------------------------------------------------------------- -/

structure Cong where
  -- @@FIELDS
  INT_CONG_MOD_0 : thm
  INT_CONG_MOD_1 : thm
  INT_CONG : thm
  INT_CONG_MOD_ABS : thm
  INT_CONG_MUL_LCANCEL : thm
  INT_CONG_MUL_RCANCEL : thm
  INT_CONG_MULT_LCANCEL_ALL : thm
  INT_CONG_LMUL : thm
  INT_CONG_RMUL : thm
  INT_CONG_REFL : thm
  INT_EQ_IMP_CONG : thm
  INT_CONG_SYM : thm
  INT_CONG_TRANS : thm
  INT_CONG_ADD : thm
  INT_CONG_SUB : thm
  INT_CONG_MUL : thm
  INT_CONG_POW : thm
  INT_CONG_MUL_1 : thm
  INT_CONG_POW_1 : thm
  INT_CONG_MUL_LCANCEL_EQ : thm
  INT_CONG_MUL_RCANCEL_EQ : thm
  INT_CONG_ADD_LCANCEL_EQ : thm
  INT_CONG_ADD_RCANCEL_EQ : thm
  INT_CONG_ADD_RCANCEL : thm
  INT_CONG_ADD_LCANCEL : thm
  INT_CONG_ADD_LCANCEL_EQ_0 : thm
  INT_CONG_ADD_RCANCEL_EQ_0 : thm
  INT_CONG_INT_DIVIDES_MODULUS : thm
  INT_CONG_0_DIVIDES : thm
  INT_CONG_1_DIVIDES : thm
  INT_CONG_DIVIDES : thm
  INT_CONG_COPRIME : thm
  INT_COPRIME_RREM : thm
  INT_COPRIME_LREM : thm
  INT_CONG_GCD_RIGHT : thm
  INT_CONG_GCD_LEFT : thm
  INT_CONG_TO_1 : thm
  INT_CONG_SOLVE : thm
  INT_CONG_SOLVE_EQ : thm
  INT_CONG_SOLVE_UNIQUE : thm
  INT_CONG_CHINESE : thm
  INT_CHINESE_REMAINDER_COPRIME : thm
  INT_CHINESE_REMAINDER_COPRIME_UNIQUE : thm
  SOLVABLE_GCD : thm
  INT_LINEAR_CONG_POS : thm
  INT_CONG_SOLVE_POS : thm
  INT_CONG_IMP_EQ : thm
  INT_CONG_DIV : thm
  INT_CONG_DIV_COPRIME : thm
  deriving Inhabited

@[nospecialize]
def setupCong [HolBase] (D : IntegerDeps) (BDivides : Divides) (BGcd : Gcd) (BCoprime : Coprime) :
    ExceptT String IO Cong := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_INT_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, INTEGER_RULE,
        INTEGER_TAC, INT_ARITH, INT_ARITH_TAC, MESON_TAC, METIS_TAC, .. } := D
  let { CONTRAPOS_THM, DE_MORGAN_THM, INT_ABS_MUL, INT_CONG_DIV2, INT_CONG_RREM,
        INT_DIVIDES_LABS, INT_DIVIDES_RABS, INT_DIV_MUL, INT_ENTIRE, INT_LE_LMUL,
        INT_LE_MUL, INT_LT_LE, INT_MUL_LID, INT_POW, INT_POW_ONE, INT_SUB_0, .. } := D.core1
  let { int_congruent, .. } := D.core2
  let { INT_DIVIDES_ONE, .. } := BDivides
  let { INT_GCD_POS, INT_GCD_UNIQUE, .. } := BGcd
  let { INT_COPRIME_0, INT_COPRIME_SYM, .. } := BCoprime
  -- @@SCOPE END

  let INT_CONG_MOD_0 ← prove
   r"!x y. (x == y) (mod &0) <=> (x = y)"
   (INTEGER_TAC)

  let INT_CONG_MOD_1 ← prove
   r"!x y. (x == y) (mod &1)"
   (INTEGER_TAC)

  let INT_CONG ← prove
   r"!x y n. (x == y) (mod n) <=> n divides (x - y)"
   (INTEGER_TAC)

  let INT_CONG_MOD_ABS ← prove
   r"!a b n:int. (a == b) (mod (abs n)) <=> (a == b) (mod n)"
   (REWRITE_TAC [INT_CONG, INT_DIVIDES_LABS])

  let INT_CONG_MUL_LCANCEL ← prove
   r"!a n x y. coprime(a,n) /\ (a * x == a * y) (mod n) ==> (x == y) (mod n)"
   (INTEGER_TAC)

  let INT_CONG_MUL_RCANCEL ← prove
   r"!a n x y. coprime(a,n) /\ (x * a == y * a) (mod n) ==> (x == y) (mod n)"
   (INTEGER_TAC)

  let INT_CONG_MULT_LCANCEL_ALL ← INTEGER_RULE (← q
   r"!a x y n:int.
        (a * x == a * y) (mod (a * n)) <=> a = &0 \/ (x == y) (mod n)")

  let INT_CONG_LMUL ← INTEGER_RULE (← q
   r"!a x y n:int. (x == y) (mod n) ==> (a * x == a * y) (mod n)")

  let INT_CONG_RMUL ← INTEGER_RULE (← q
   r"!x y a n:int. (x == y) (mod n) ==> (x * a == y * a) (mod n)")

  let INT_CONG_REFL ← prove
   r"!x n. (x == x) (mod n)"
   (INTEGER_TAC)

  let INT_EQ_IMP_CONG ← prove
   r"!a b n. a = b ==> (a == b) (mod n)"
   (INTEGER_TAC)

  let INT_CONG_SYM ← prove
   r"!x y n. (x == y) (mod n) <=> (y == x) (mod n)"
   (INTEGER_TAC)

  let INT_CONG_TRANS ← prove
   r"!x y z n. (x == y) (mod n) /\ (y == z) (mod n) ==> (x == z) (mod n)"
   (INTEGER_TAC)

  let INT_CONG_ADD ← prove
   r"!x x' y y'.
       (x == x') (mod n) /\ (y == y') (mod n) ==> (x + y == x' + y') (mod n)"
   (INTEGER_TAC)

  let INT_CONG_SUB ← prove
   r"!x x' y y'.
       (x == x') (mod n) /\ (y == y') (mod n) ==> (x - y == x' - y') (mod n)"
   (INTEGER_TAC)

  let INT_CONG_MUL ← prove
   r"!x x' y y'.
       (x == x') (mod n) /\ (y == y') (mod n) ==> (x * y == x' * y') (mod n)"
   (INTEGER_TAC)

  let INT_CONG_POW ← prove
   r"!n k x y. (x == y) (mod n) ==> (x pow k == y pow k) (mod n)"
   (GEN_TAC THEN INDUCT_TAC THEN
    ASM_SIMP_TAC [INT_CONG_MUL, INT_POW, INT_CONG_REFL])

  let INT_CONG_MUL_1 ← prove
   r"!n x y:int.
          (x == &1) (mod n) /\ (y == &1) (mod n)
          ==> (x * y == &1) (mod n)"
   (MESON_TAC [INT_CONG_MUL, INT_MUL_LID])

  let INT_CONG_POW_1 ← prove
   r"!a k n:int. (a == &1) (mod n) ==> (a pow k == &1) (mod n)"
   (MESON_TAC [INT_CONG_POW, INT_POW_ONE])

  let INT_CONG_MUL_LCANCEL_EQ ← prove
   r"!a n x y. coprime(a,n) ==> ((a * x == a * y) (mod n) <=> (x == y) (mod n))"
   (INTEGER_TAC)

  let INT_CONG_MUL_RCANCEL_EQ ← prove
   r"!a n x y. coprime(a,n) ==> ((x * a == y * a) (mod n) <=> (x == y) (mod n))"
   (INTEGER_TAC)

  let INT_CONG_ADD_LCANCEL_EQ ← prove
   r"!a n x y. (a + x == a + y) (mod n) <=> (x == y) (mod n)"
   (INTEGER_TAC)

  let INT_CONG_ADD_RCANCEL_EQ ← prove
   r"!a n x y. (x + a == y + a) (mod n) <=> (x == y) (mod n)"
   (INTEGER_TAC)

  let INT_CONG_ADD_RCANCEL ← prove
   r"!a n x y. (x + a == y + a) (mod n) ==> (x == y) (mod n)"
   (INTEGER_TAC)

  let INT_CONG_ADD_LCANCEL ← prove
   r"!a n x y. (a + x == a + y) (mod n) ==> (x == y) (mod n)"
   (INTEGER_TAC)

  let INT_CONG_ADD_LCANCEL_EQ_0 ← prove
   r"!a n x y. (a + x == a) (mod n) <=> (x == &0) (mod n)"
   (INTEGER_TAC)

  let INT_CONG_ADD_RCANCEL_EQ_0 ← prove
   r"!a n x y. (x + a == a) (mod n) <=> (x == &0) (mod n)"
   (INTEGER_TAC)

  let INT_CONG_INT_DIVIDES_MODULUS ← prove
   r"!x y m n. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)"
   (INTEGER_TAC)

  let INT_CONG_0_DIVIDES ← prove
   r"!n x. (x == &0) (mod n) <=> n divides x"
   (INTEGER_TAC)

  let INT_CONG_1_DIVIDES ← prove
   r"!n x. (x == &1) (mod n) ==> n divides (x - &1)"
   (INTEGER_TAC)

  let INT_CONG_DIVIDES ← prove
   r"!x y n. (x == y) (mod n) ==> (n divides x <=> n divides y)"
   (INTEGER_TAC)

  let INT_CONG_COPRIME ← prove
   r"!x y n. (x == y) (mod n) ==> (coprime(n,x) <=> coprime(n,y))"
   (INTEGER_TAC)

  let INT_COPRIME_RREM ← prove
   r"!m n. coprime(m,n rem m) <=> coprime(m,n)"
   (MESON_TAC [INT_CONG_COPRIME, INT_CONG_RREM, INT_CONG_REFL])

  let INT_COPRIME_LREM ← prove
   r"!a b. coprime(a rem n,n) <=> coprime(a,n)"
   (MESON_TAC [INT_COPRIME_RREM, INT_COPRIME_SYM])

  let INT_CONG_GCD_RIGHT ← prove
   r"!x y n. (x == y) (mod n) ==> gcd(n,x) = gcd(n,y)"
   (REWRITE_TAC [INT_GCD_UNIQUE, INT_GCD_POS] THEN INTEGER_TAC)

  let INT_CONG_GCD_LEFT ← prove
   r"!x y n. (x == y) (mod n) ==> gcd(x,n) = gcd(y,n)"
   (REWRITE_TAC [INT_GCD_UNIQUE, INT_GCD_POS] THEN INTEGER_TAC)

  let INT_CONG_TO_1 ← prove
   r"!a n. (a == &1) (mod n) <=> ?m. a = &1 + m * n"
   (INTEGER_TAC)

  let INT_CONG_SOLVE ← prove
   r"!a b n. coprime(a,n) ==> ?x. (a * x == b) (mod n)"
   (INTEGER_TAC)

  let INT_CONG_SOLVE_EQ ← prove
   r"!n a b:int. (?x. (a * x == b) (mod n)) <=> gcd(a,n) divides b"
   (INTEGER_TAC)

  let INT_CONG_SOLVE_UNIQUE ← prove
   r"!a b n. coprime(a,n)
             ==> !x y. (a * x == b) (mod n) /\ (a * y == b) (mod n)
                       ==> (x == y) (mod n)"
   (INTEGER_TAC)

  let INT_CONG_CHINESE ← prove
   r"coprime(a,b) /\ (x == y) (mod a) /\ (x == y) (mod b)
     ==> (x == y) (mod (a * b))"
   (INTEGER_TAC)

  let INT_CHINESE_REMAINDER_COPRIME ← prove
   r"!a b m n.
          coprime(a,b) /\ ~(a = &0) /\ ~(b = &0) /\ coprime(m,a) /\ coprime(n,b)
          ==> ?x. coprime(x,a * b) /\
                  (x == m) (mod a) /\ (x == n) (mod b)"
   (INTEGER_TAC)

  let INT_CHINESE_REMAINDER_COPRIME_UNIQUE ← prove
   r"!a b m n x y.
          coprime(a,b) /\
          (x == m) (mod a) /\ (x == n) (mod b) /\
          (y == m) (mod a) /\ (y == n) (mod b)
          ==> (x == y) (mod (a * b))"
   (INTEGER_TAC)

  let SOLVABLE_GCD ← prove
   r"!a b n. gcd(a,n) divides b ==> ?x. (a * x == b) (mod n)"
   (INTEGER_TAC)

  let INT_LINEAR_CONG_POS ← prove
   r"!n a x:int. ~(n = &0) ==> ?y. &0 <= y /\ (a * x == a * y) (mod n)"
   (← do
    let i2 ← INTEGER_RULE (← q
      r"n divides y ==> (a * x:int == a * (x + y)) (mod n)")
    let i1 ← INT_ARITH (← q r"abs(x:int) * &1 <= y ==> &0 <= x + y")
    pure (REPEAT STRIP_TAC THEN EXISTS_TAC (← q r"x + abs(x * n):int") THEN CONJ_TAC THENL
     [MATCH_MP_TAC i1 THEN
      REWRITE_TAC [INT_ABS_MUL] THEN MATCH_MP_TAC INT_LE_LMUL THEN
      ASM_INT_ARITH_TAC,
      MATCH_MP_TAC i2 THEN
      REWRITE_TAC [INT_DIVIDES_RABS] THEN INTEGER_TAC]))

  let INT_CONG_SOLVE_POS ← prove
   r"!a b n:int.
          coprime(a,n) /\ ~(n = &0 /\ abs a = &1)
          ==> ?x. &0 <= x /\ (a * x == b) (mod n)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n:int = &0") THEN
    ASM_REWRITE_TAC [INT_COPRIME_0, INT_DIVIDES_ONE] THENL
     [INT_ARITH_TAC,
      ASM_MESON_TAC [INT_LINEAR_CONG_POS, INT_CONG_SOLVE, INT_CONG_TRANS,
                    INT_CONG_SYM]])

  let INT_CONG_IMP_EQ ← prove
   r"!x y n:int. abs(x - y) < n /\ (x == y) (mod n) ==> x = y"
   (← do
    let a2 ← INT_ARITH
     (← q r"abs n * (q:int) < abs n * &1 <=> ~(&0 <= abs n * (q - &1))")
    let a1 ← ARITH_RULE (← q
      r"abs(n * q) < n ==> abs(n * q) < abs n * &1")
    pure (REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ONCE_REWRITE_TAC [int_congruent, ← GSYM INT_SUB_0] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "q:int") SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP a1) THEN
    REWRITE_TAC [INT_ABS_MUL, INT_ENTIRE] THEN
    REWRITE_TAC [a2] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN REWRITE_TAC [DE_MORGAN_THM] THEN
    STRIP_TAC THEN MATCH_MP_TAC INT_LE_MUL THEN ASM_INT_ARITH_TAC))

  let INT_CONG_DIV ← prove
   r"!m n a b.
          ~(m = &0) /\ (a == m * b) (mod (m * n)) ==> (a div m == b) (mod n)"
   (METIS_TAC [INT_CONG_DIV2, INT_DIV_MUL, INT_LT_LE])

  let INT_CONG_DIV_COPRIME ← prove
   r"!m n a b:int.
          coprime(m,n) /\ m divides a /\ (a == m * b) (mod n)
          ==> (a div m == b) (mod n)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"m:int = &0") THEN
    ASM_SIMP_TAC [INT_COPRIME_0, INT_CONG_MOD_1] THENL
     [INTEGER_TAC, STRIP_TAC] THEN
    ASM_REWRITE_TAC [] THEN MATCH_MP_TAC INT_CONG_DIV THEN
    REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC INTEGER_RULE)

  -- @@RETURN BEGIN
  return { INT_CONG_MOD_0, INT_CONG_MOD_1, INT_CONG, INT_CONG_MOD_ABS,
           INT_CONG_MUL_LCANCEL, INT_CONG_MUL_RCANCEL, INT_CONG_MULT_LCANCEL_ALL,
           INT_CONG_LMUL, INT_CONG_RMUL, INT_CONG_REFL, INT_EQ_IMP_CONG, INT_CONG_SYM,
           INT_CONG_TRANS, INT_CONG_ADD, INT_CONG_SUB, INT_CONG_MUL, INT_CONG_POW,
           INT_CONG_MUL_1, INT_CONG_POW_1, INT_CONG_MUL_LCANCEL_EQ,
           INT_CONG_MUL_RCANCEL_EQ, INT_CONG_ADD_LCANCEL_EQ, INT_CONG_ADD_RCANCEL_EQ,
           INT_CONG_ADD_RCANCEL, INT_CONG_ADD_LCANCEL, INT_CONG_ADD_LCANCEL_EQ_0,
           INT_CONG_ADD_RCANCEL_EQ_0, INT_CONG_INT_DIVIDES_MODULUS, INT_CONG_0_DIVIDES,
           INT_CONG_1_DIVIDES, INT_CONG_DIVIDES, INT_CONG_COPRIME, INT_COPRIME_RREM,
           INT_COPRIME_LREM, INT_CONG_GCD_RIGHT, INT_CONG_GCD_LEFT, INT_CONG_TO_1,
           INT_CONG_SOLVE, INT_CONG_SOLVE_EQ, INT_CONG_SOLVE_UNIQUE, INT_CONG_CHINESE,
           INT_CHINESE_REMAINDER_COPRIME, INT_CHINESE_REMAINDER_COPRIME_UNIQUE,
           SOLVABLE_GCD, INT_LINEAR_CONG_POS, INT_CONG_SOLVE_POS, INT_CONG_IMP_EQ,
           INT_CONG_DIV, INT_CONG_DIV_COPRIME }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- A stronger form of the CRT.  (integer.ml 843-857)                         -/
/- Other miscellaneous lemmas.  (integer.ml 859-889)                         -/
/- ------------------------------------------------------------------------- -/

structure Crt where
  -- @@FIELDS
  INT_CRT_STRONG : thm
  INT_CRT_STRONG_IFF : thm
  EVEN_SQUARE_MOD4 : thm
  ODD_SQUARE_MOD4 : thm
  INT_DIVIDES_LE : thm
  INT_DIVIDES_POW_LE : thm
  deriving Inhabited

@[nospecialize]
def setupCrt [HolBase] (D : IntegerDeps) :
    ExceptT String IO Crt := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_INT_ARITH_TAC, ASM_MESON_TAC, INTEGER_TAC, INT_ARITH, .. } := D
  let { CONTRAPOS_THM, INT_ABS_MUL, INT_ABS_POW, INT_ENTIRE, INT_LE_MUL, INT_NOT_LE,
        INT_POW_ADD, INT_POW_EQ_0, INT_POW_MONO_LT, LEFT_IMP_EXISTS_THM, LE_EXISTS, .. } := D.core1
  let { NOT_LE, int_divides, .. } := D.core2
  -- @@SCOPE END

  let INT_CRT_STRONG ← prove
   r"!a1 a2 n1 n2:int.
          (a1 == a2) (mod (gcd(n1,n2)))
          ==> ?x. (x == a1) (mod n1) /\ (x == a2) (mod n2)"
   (INTEGER_TAC)

  let INT_CRT_STRONG_IFF ← prove
   r"!a1 a2 n1 n2:int.
          (?x. (x == a1) (mod n1) /\ (x == a2) (mod n2)) <=>
          (a1 == a2) (mod (gcd(n1,n2)))"
   (INTEGER_TAC)

  /- --------------------------------------------------------------------- -/
  /- Other miscellaneous lemmas.                                           -/
  /- --------------------------------------------------------------------- -/

  let EVEN_SQUARE_MOD4 ← prove
   r"((&2 * n) pow 2 == &0) (mod &4)"
   (INTEGER_TAC)

  let ODD_SQUARE_MOD4 ← prove
   r"((&2 * n + &1) pow 2 == &1) (mod &4)"
   (INTEGER_TAC)

  let INT_DIVIDES_LE ← prove
   r"!x y. x divides y ==> abs(x) <= abs(y) \/ y = &0"
   (REWRITE_TAC [int_divides, LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [← q "x:int", ← q "y:int", ← q "z:int"] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [INT_ABS_MUL, INT_ENTIRE] THEN
    REWRITE_TAC [← INT_ARITH (← q r"x <= x * z <=> &0 <= x * (z - &1)")] THEN
    ASM_CASES_TAC (← q r"x = &0") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"z = &0") THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC INT_LE_MUL THEN ASM_INT_ARITH_TAC)

  let INT_DIVIDES_POW_LE ← prove
   r"!p m n. &2 <= abs p ==> ((p pow m) divides (p pow n) <=> m <= n)"
   (← do
    let a2 ← ARITH_RULE (← q r"&2 <= x ==> &1 < x")
    let a1 ← INT_ARITH (← q r"&2 <= abs p ==> ~(p = &0)")
    pure (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [DISCH_THEN (MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN
      ASM_SIMP_TAC [INT_POW_EQ_0, a1] THEN
      ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC [INT_NOT_LE, NOT_LE, INT_ABS_POW] THEN
      ASM_MESON_TAC [INT_POW_MONO_LT, a2],
      SIMP_TAC [LE_EXISTS, LEFT_IMP_EXISTS_THM, INT_POW_ADD] THEN INTEGER_TAC]))

  -- @@RETURN BEGIN
  return { INT_CRT_STRONG, INT_CRT_STRONG_IFF, EVEN_SQUARE_MOD4, ODD_SQUARE_MOD4,
           INT_DIVIDES_LE, INT_DIVIDES_POW_LE }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Integer primality / irreducibility.  (integer.ml 891-978)                 -/
/- ------------------------------------------------------------------------- -/

structure IntPrime where
  -- @@FIELDS
  int_prime : thm
  INT_PRIME_NEG : thm
  INT_PRIME_ABS : thm
  INT_PRIME_GE_2 : thm
  INT_PRIME_0 : thm
  INT_PRIME_1 : thm
  INT_PRIME_2 : thm
  INT_PRIME_FACTOR : thm
  INT_PRIME_FACTOR_LT : thm
  INT_PRIME_FACTOR_INDUCT : thm
  deriving Inhabited

@[nospecialize]
def setupIntPrime [HolBase] (D : IntegerDeps) (BDivides : Divides) (BCrt : Crt) :
    ExceptT String IO IntPrime := do
  -- @@SCOPE BEGIN
  let { ASM_INT_ARITH_TAC, ASM_MESON_TAC, INTEGER_TAC, INT_ARITH, INT_ARITH_TAC,
        INT_REDUCE_CONV, new_definition, .. } := D
  let { DE_MORGAN_THM, INT_ABS, INT_ABS_MUL, INT_ABS_NEG, INT_ABS_POS, INT_ENTIRE,
        INT_LT_MUL, INT_MUL_RZERO, .. } := D.core1
  let { MONO_EXISTS, NOT_FORALL_THM, NOT_IMP, WF_INT_MEASURE, int_divides, .. } := D.core2
  let { INT_DIVIDES_0, INT_DIVIDES_RNEG, INT_DIVIDES_ZERO, .. } := BDivides
  let { INT_DIVIDES_LE, .. } := BCrt
  -- @@SCOPE END

  let int_prime ← new_definition
   r"int_prime p <=> abs(p) > &1 /\
                    !x. x divides p ==> abs(x) = &1 \/ abs(x) = abs(p)"

  let INT_PRIME_NEG ← prove
   r"!p. int_prime(--p) <=> int_prime p"
   (REWRITE_TAC [int_prime, INT_DIVIDES_RNEG, INT_ABS_NEG])

  let INT_PRIME_ABS ← prove
   r"!p. int_prime(abs p) <=> int_prime p"
   (GEN_TAC THEN REWRITE_TAC [INT_ABS] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [INT_PRIME_NEG])

  let INT_PRIME_GE_2 ← prove
   r"!p. int_prime p ==> &2 <= abs(p)"
   (REWRITE_TAC [int_prime] THEN INT_ARITH_TAC)

  let INT_PRIME_0 ← prove
   r"~(int_prime(&0))"
   (REWRITE_TAC [int_prime] THEN INT_ARITH_TAC)

  let INT_PRIME_1 ← prove
   r"~(int_prime(&1))"
   (REWRITE_TAC [int_prime] THEN INT_ARITH_TAC)

  let INT_PRIME_2 ← prove
   r"int_prime(&2)"
   (REWRITE_TAC [int_prime] THEN CONV_TAC INT_REDUCE_CONV THEN
    X_GEN_TAC (← q "x:int") THEN
    ASM_CASES_TAC (← q r"x = &0") THEN ASM_REWRITE_TAC [INT_DIVIDES_ZERO] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    DISCH_THEN (MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC)

  let INT_PRIME_FACTOR ← prove
   r"!x. ~(abs x = &1) ==> ?p. int_prime p /\ p divides x"
   (← do
    let a1 ← INT_ARITH (← q r"~(x = &0) /\ ~(abs x = &1) ==> abs x > &1")
    pure (MATCH_MP_TAC WF_INT_MEASURE THEN EXISTS_TAC (← q "abs") THEN
    REWRITE_TAC [INT_ABS_POS] THEN X_GEN_TAC (← q "x:int") THEN
    REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q "int_prime x") THENL
     [EXISTS_TAC (← q "x:int") THEN ASM_REWRITE_TAC [] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN INTEGER_TAC,
      ALL_TAC] THEN
    ASM_CASES_TAC (← q r"x = &0") THEN ASM_REWRITE_TAC [] THENL
     [EXISTS_TAC (← q "&2") THEN ASM_REWRITE_TAC [INT_PRIME_2, INT_DIVIDES_0],
      ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [int_prime]) THEN
    ASM_SIMP_TAC [a1] THEN
    REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, DE_MORGAN_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "y:int") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q "y:int")) THEN ASM_REWRITE_TAC [] THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC,
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN SIMP_TAC [] THEN
      UNDISCH_TAC (← q "y divides x") THEN INTEGER_TAC]))

  let INT_PRIME_FACTOR_LT ← prove
   r"!n m p. int_prime(p) /\ ~(n = &0) /\ n = p * m ==> abs m < abs n"
   (← do
    let a1 ← INT_ARITH (← q r"&0 < m * (p - &1) ==> m < p * m")
    pure (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [INT_ABS_MUL] THEN
    MATCH_MP_TAC a1 THEN
    MATCH_MP_TAC INT_LT_MUL THEN
    UNDISCH_TAC (← q r"~(n = &0)") THEN ASM_CASES_TAC (← q r"m = &0") THEN
    ASM_REWRITE_TAC [INT_MUL_RZERO] THEN DISCH_THEN (K ALL_TAC) THEN
    CONJ_TAC THENL [ASM_INT_ARITH_TAC, ALL_TAC] THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP INT_PRIME_GE_2) THEN INT_ARITH_TAC))

  let INT_PRIME_FACTOR_INDUCT ← prove
   r"!P. P(&0) /\ P(&1) /\ P(-- &1) /\
         (!p n. int_prime p /\ ~(n = &0) /\ P n ==> P(p * n))
         ==> !n. P n"
   (← do
    let a1 ← INT_ARITH (← q r"abs x = &a <=> x = &a \/ x = -- &a")
    pure (GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC WF_INT_MEASURE THEN EXISTS_TAC (← q "abs") THEN
    REWRITE_TAC [INT_ABS_POS] THEN X_GEN_TAC (← q "n:int") THEN DISCH_TAC THEN
    ASM_CASES_TAC (← q r"n = &0") THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"abs n = &1") THENL
     [ASM_MESON_TAC [a1],
      ALL_TAC] THEN
    FIRST_ASSUM (X_CHOOSE_THEN (← q "p:int")
      STRIP_ASSUME_TAC o MATCH_MP INT_PRIME_FACTOR) THEN
    FIRST_X_ASSUM (X_CHOOSE_THEN (← q "d:int") SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [int_divides]) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [← q "p:int", ← q "d:int"]) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [INT_ENTIRE, DE_MORGAN_THM]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC [INT_PRIME_FACTOR_LT, INT_ENTIRE]))

  -- @@RETURN BEGIN
  return { int_prime, INT_PRIME_NEG, INT_PRIME_ABS, INT_PRIME_GE_2, INT_PRIME_0,
           INT_PRIME_1, INT_PRIME_2, INT_PRIME_FACTOR, INT_PRIME_FACTOR_LT,
           INT_PRIME_FACTOR_INDUCT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Infinitude.  (integer.ml 980-1266)                                        -/
/- ------------------------------------------------------------------------- -/

structure IntPrime2 where
  -- @@FIELDS
  INT_DIVIDES_FACT : thm
  INT_EUCLID_BOUND : thm
  INT_EUCLID : thm
  INT_PRIMES_INFINITE : thm
  INT_COPRIME_PRIME : thm
  INT_COPRIME_PRIME_EQ : thm
  INT_PRIME_COPRIME : thm
  INT_PRIME_COPRIME_EQ : thm
  INT_COPRIME_PRIMEPOW : thm
  INT_COPRIME_BEZOUT : thm
  INT_COPRIME_BEZOUT_ALT : thm
  INT_BEZOUT_PRIME : thm
  INT_PRIME_DIVPROD : thm
  INT_PRIME_DIVPROD_EQ : thm
  INT_PRIME_DIVPOW : thm
  INT_PRIME_DIVPOW_N : thm
  INT_COPRIME_SOS : thm
  INT_PRIME_IMP_NZ : thm
  INT_DISTINCT_PRIME_COPRIME : thm
  INT_PRIME_COPRIME_LT : thm
  INT_DIVIDES_PRIME_PRIME : thm
  INT_COPRIME_POW_DIVPROD : thm
  INT_PRIME_COPRIME_CASES : thm
  INT_PRIME_DIVPROD_POW : thm
  INT_DIVIDES_POW2_REV : thm
  INT_DIVIDES_POW2_EQ : thm
  INT_POW_MUL_EXISTS : thm
  INT_COPRIME_POW_ABS : thm
  INT_COPRIME_POW_ODD : thm
  INT_DIVIDES_PRIME_POW_LE : thm
  INT_EQ_PRIME_POW_ABS : thm
  INT_EQ_PRIME_POW_POS : thm
  INT_DIVIDES_FACT_PRIME : thm
  deriving Inhabited

@[nospecialize]
def setupIntPrime2 [HolBase] (D : IntegerDeps) (BDivides : Divides) (BGcd : Gcd) (BCoprime : Coprime) (BCrt : Crt) (BIntPrime : IntPrime) :
    ExceptT String IO IntPrime2 := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, ASM_INT_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, INTEGER_RULE,
        INTEGER_TAC, INT_ARITH, INT_ARITH_TAC, INT_RING, MESON_TAC, .. } := D
  let { CONTRAPOS_THM, EQ_ADD_RCANCEL_0, FACT, FACT_NZ, FINITE_IMAGE_INJ, INFINITE,
        INT_ABS, INT_ABS_ABS, INT_ABS_MUL, INT_ABS_MUL_1, INT_ABS_NEG, INT_ABS_NUM,
        INT_ABS_POW, INT_DIVIDES_LABS, INT_DIVIDES_RABS, INT_ENTIRE,
        INT_EQ_MUL_LCANCEL, INT_EXISTS_POS, INT_GT, INT_IMAGE, INT_MUL_LID,
        INT_MUL_SYM, INT_NEG_NEG, INT_NOT_LE, INT_OF_NUM_ADD, INT_OF_NUM_EQ,
        INT_OF_NUM_LT, INT_OF_NUM_MUL, INT_OF_NUM_SUC, INT_POW, INT_POW_EQ_0,
        INT_POW_MUL, INT_POW_NEG, INT_POW_ONE, INT_POW_ZERO, IN_ELIM_THM,
        LEFT_EXISTS_AND_THM, LEFT_IMP_EXISTS_THM, MONO_AND, .. } := D.core1
  let { MONO_EXISTS, MONO_FORALL, NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP, NOT_LE,
        NOT_ODD, OR_EXISTS_THM, RIGHT_EXISTS_AND_THM, SWAP_FORALL_THM, int_divides,
        num_FINITE, .. } := D.core2
  let { INT_DIVIDES_1, INT_DIVIDES_ANTISYM_ABS, INT_DIVIDES_LMUL, INT_DIVIDES_ONE,
        INT_DIVIDES_ONE_ABS, INT_DIVIDES_POW, INT_DIVIDES_POW2, INT_DIVIDES_REFL,
        INT_DIVIDES_RMUL, INT_DIVIDES_RMUL2_EQ, INT_DIVIDES_TRANS, .. } := BDivides
  let { INT_GCD_COPRIME_EXISTS, INT_GCD_EQ_0, .. } := BGcd
  let { INT_COPRIME, INT_COPRIME_0, INT_COPRIME_DIVPROD, INT_COPRIME_LMUL,
        INT_COPRIME_LPOW, INT_COPRIME_POW, INT_COPRIME_POW2, INT_COPRIME_RMUL,
        INT_COPRIME_RPOW, INT_COPRIME_SYM, .. } := BCoprime
  let { INT_DIVIDES_LE, INT_DIVIDES_POW_LE, .. } := BCrt
  let { INT_PRIME_0, INT_PRIME_1, INT_PRIME_ABS, INT_PRIME_FACTOR,
        INT_PRIME_FACTOR_INDUCT, INT_PRIME_GE_2, INT_PRIME_NEG, int_prime, .. } := BIntPrime
  -- @@SCOPE END

  let INT_DIVIDES_FACT ← prove
   r"!n x. &1 <= abs(x) /\ abs(x) <= &n ==> x divides &(FACT n)"
   (← do
    let a2 ← INT_ARITH (← q r"x < &m + &1 <=> x <= &m")
    let a1 ← INT_ARITH (← q r"x <= &n <=> x = &n \/ x < &n")
    pure (INDUCT_TAC THENL [INT_ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [FACT, a1] THEN
    REWRITE_TAC [← GSYM INT_OF_NUM_SUC, a2] THEN
    REWRITE_TAC [INT_OF_NUM_SUC, ← GSYM INT_OF_NUM_MUL] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC [INT_DIVIDES_LMUL] THEN
    MATCH_MP_TAC INT_DIVIDES_RMUL THEN
    ASM_MESON_TAC [INT_DIVIDES_LABS, INT_DIVIDES_REFL]))

  let INT_EUCLID_BOUND ← prove
   r"!n. ?p. int_prime(p) /\ &n < p /\ p <= &(FACT n) + &1"
   (← do
    let a1 ← INT_ARITH (← q r"&2 <= p ==> &1 <= p")
    pure (GEN_TAC THEN MP_TAC (← SPEC (← q r"&(FACT n) + &1") INT_PRIME_FACTOR) THEN
    REWRITE_TAC [INT_OF_NUM_ADD, INT_ABS_NUM, INT_OF_NUM_EQ] THEN
    REWRITE_TAC [EQ_ADD_RCANCEL_0, FACT_NZ, ← GSYM INT_OF_NUM_ADD] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "p:int") STRIP_ASSUME_TAC) THEN
    EXISTS_TAC (← q "abs p") THEN ASM_REWRITE_TAC [INT_PRIME_ABS] THEN CONJ_TAC THENL
     [ALL_TAC,
      FIRST_ASSUM (MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN
      REWRITE_TAC [← GSYM INT_OF_NUM_ADD, ← GSYM INT_OF_NUM_SUC] THEN
      INT_ARITH_TAC] THEN
    REWRITE_TAC [← GSYM INT_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC (← SPECL [← q "n:num", ← q "p:int"] INT_DIVIDES_FACT) THEN
    ASM_SIMP_TAC [INT_PRIME_GE_2, a1] THEN
    DISCH_TAC THEN SUBGOAL_THEN (← q r"p divides &1") MP_TAC THENL
     [REPEAT (POP_ASSUM MP_TAC) THEN INTEGER_TAC,
      REWRITE_TAC [INT_DIVIDES_ONE] THEN
      ASM_MESON_TAC [INT_PRIME_NEG, INT_PRIME_1]]))

  let INT_EUCLID ← prove
   r"!n. ?p. int_prime(p) /\ p > n"
   (MP_TAC INT_IMAGE THEN MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC (← q "n:int") THEN REWRITE_TAC [INT_GT] THEN
    ASM_REWRITE_TAC [OR_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
    MP_TAC INT_EUCLID_BOUND THEN MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC (← q "m:num") THEN DISCH_THEN (fun th => DISCH_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC [] THEN
    FIRST_X_ASSUM (DISJ_CASES_THEN SUBST1_TAC) THEN INT_ARITH_TAC)

  let INT_PRIMES_INFINITE ← prove
   r"INFINITE {p | int_prime p}"
   (SUBGOAL_THEN (← q r"INFINITE {n | int_prime(&n)}") MP_TAC THEN
    REWRITE_TAC [INFINITE, CONTRAPOS_THM] THENL
     [REWRITE_TAC [num_FINITE, IN_ELIM_THM] THEN
      REWRITE_TAC [NOT_EXISTS_THM, NOT_FORALL_THM, NOT_IMP, NOT_LE] THEN
      REWRITE_TAC [← GSYM INT_OF_NUM_LT, INT_EXISTS_POS] THEN
      MP_TAC INT_EUCLID_BOUND THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      SIMP_TAC [] THEN INT_ARITH_TAC,
      MP_TAC (← ISPECL [← q "&", ← q r"{p | int_prime p}"] FINITE_IMAGE_INJ) THEN
      REWRITE_TAC [INT_OF_NUM_EQ, IN_ELIM_THM]])

  let INT_COPRIME_PRIME ← prove
   r"!p a b. coprime(a,b) ==> ~(int_prime(p) /\ p divides a /\ p divides b)"
   (REWRITE_TAC [INT_COPRIME] THEN
    MESON_TAC [INT_DIVIDES_ONE, INT_PRIME_NEG, INT_PRIME_1])

  let INT_COPRIME_PRIME_EQ ← prove
   r"!a b. coprime(a,b) <=> !p. ~(int_prime(p) /\ p divides a /\ p divides b)"
   (REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC [INT_COPRIME_PRIME], ALL_TAC] THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [INT_COPRIME, INT_DIVIDES_ONE_ABS] THEN
    ONCE_REWRITE_TAC [NOT_FORALL_THM] THEN REWRITE_TAC [NOT_IMP] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:int") STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM (X_CHOOSE_TAC (← q "p:int") o MATCH_MP INT_PRIME_FACTOR) THEN
    EXISTS_TAC (← q "p:int") THEN ASM_MESON_TAC [INT_DIVIDES_TRANS])

  let INT_PRIME_COPRIME ← prove
   r"!x p. int_prime(p) ==> p divides x \/ coprime(p,x)"
   (← do
    let t1 ← TAUT (← q r"(~b ==> a) ==> a \/ b")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [INT_COPRIME] THEN
    MATCH_MP_TAC t1 THEN
    REWRITE_TAC [NOT_FORALL_THM, NOT_IMP, INT_DIVIDES_ONE_ABS] THEN
    DISCH_THEN (X_CHOOSE_THEN (← q "d:int") STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [int_prime]) THEN
    DISCH_THEN (MP_TAC o SPEC (← q "d:int") o CONJUNCT2) THEN ASM_REWRITE_TAC [] THEN
    ASM_MESON_TAC [INT_DIVIDES_TRANS, INT_DIVIDES_LABS, INT_DIVIDES_RABS]))

  let INT_PRIME_COPRIME_EQ ← prove
   r"!p n. int_prime p ==> (coprime(p,n) <=> ~(p divides n))"
   (← do
    let t1 ← TAUT (← q r"(b \/ a) /\ ~(a /\ b) ==> (a <=> ~b)")
    pure (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC t1 THEN
    ASM_SIMP_TAC [INT_PRIME_COPRIME, INT_COPRIME, INT_DIVIDES_ONE_ABS] THEN
    ASM_MESON_TAC [INT_DIVIDES_REFL, INT_PRIME_1, INT_PRIME_ABS]))

  let INT_COPRIME_PRIMEPOW ← prove
   r"!p k m. int_prime p /\ ~(k = 0)
             ==> (coprime(m,p pow k) <=> ~(p divides m))"
   (SIMP_TAC [INT_COPRIME_RPOW] THEN ONCE_REWRITE_TAC [INT_COPRIME_SYM] THEN
    SIMP_TAC [INT_PRIME_COPRIME_EQ])

  let INT_COPRIME_BEZOUT ← prove
   r"!a b. coprime(a,b) <=> ?x y. a * x + b * y = &1"
   (INTEGER_TAC)

  let INT_COPRIME_BEZOUT_ALT ← prove
   r"!a b. coprime(a,b) ==> ?x y. a * x = b * y + &1"
   (INTEGER_TAC)

  let INT_BEZOUT_PRIME ← prove
   r"!a p. int_prime p /\ ~(p divides a) ==> ?x y. a * x = p * y + &1"
   (MESON_TAC [INT_COPRIME_BEZOUT_ALT, INT_COPRIME_SYM, INT_PRIME_COPRIME_EQ])

  let INT_PRIME_DIVPROD ← prove
   r"!p a b. int_prime(p) /\ p divides (a * b) ==> p divides a \/ p divides b"
   (← do
    let t1 ← TAUT (← q r"a /\ b ==> c \/ d <=> a ==> (~c /\ ~d ==> ~b)")
    pure (ONCE_REWRITE_TAC [t1] THEN
    SIMP_TAC [← GSYM INT_PRIME_COPRIME_EQ] THEN INTEGER_TAC))

  let INT_PRIME_DIVPROD_EQ ← prove
   r"!p a b. int_prime(p)
             ==> (p divides (a * b) <=> p divides a \/ p divides b)"
   (MESON_TAC [INT_PRIME_DIVPROD, INT_DIVIDES_LMUL, INT_DIVIDES_RMUL])

  let INT_PRIME_DIVPOW ← prove
   r"!n p x. int_prime(p) /\ p divides (x pow n) ==> p divides x"
   (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
    ASM_SIMP_TAC [← GSYM INT_PRIME_COPRIME_EQ, INT_COPRIME_POW])

  let INT_PRIME_DIVPOW_N ← prove
   r"!n p x. int_prime p /\ p divides (x pow n) ==> (p pow n) divides (x pow n)"
   (MESON_TAC [INT_PRIME_DIVPOW, INT_DIVIDES_POW])

  let INT_COPRIME_SOS ← prove
   r"!x y. coprime(x,y) ==> coprime(x * y,x pow 2 + y pow 2)"
   (INTEGER_TAC)

  let INT_PRIME_IMP_NZ ← prove
   r"!p. int_prime p ==> ~(p = &0)"
   (GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP INT_PRIME_GE_2) THEN
    INT_ARITH_TAC)

  let INT_DISTINCT_PRIME_COPRIME ← prove
   r"!p q. int_prime p /\ int_prime q /\ ~(abs p = abs q) ==> coprime(p,q)"
   (REWRITE_TAC [← GSYM INT_DIVIDES_ANTISYM_ABS] THEN
    MESON_TAC [INT_COPRIME_SYM, INT_PRIME_COPRIME_EQ])

  let INT_PRIME_COPRIME_LT ← prove
   r"!x p. int_prime p /\ &0 < abs x /\ abs x < abs p ==> coprime(x,p)"
   (ONCE_REWRITE_TAC [INT_COPRIME_SYM] THEN SIMP_TAC [INT_PRIME_COPRIME_EQ] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    DISCH_THEN (MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC)

  let INT_DIVIDES_PRIME_PRIME ← prove
   r"!p q. int_prime p /\ int_prime q  ==> (p divides q <=> abs p = abs q)"
   (REPEAT STRIP_TAC THEN EQ_TAC THENL
     [ONCE_REWRITE_TAC [← GSYM CONTRAPOS_THM] THEN
      ASM_SIMP_TAC [← GSYM INT_PRIME_COPRIME_EQ, INT_DISTINCT_PRIME_COPRIME],
      SIMP_TAC [← GSYM INT_DIVIDES_ANTISYM_ABS]])

  let INT_COPRIME_POW_DIVPROD ← prove
   r"!d a b. (d pow n) divides (a * b) /\ coprime(d,a) ==> (d pow n) divides b"
   (MESON_TAC [INT_COPRIME_DIVPROD, INT_COPRIME_POW, INT_COPRIME_SYM])

  let INT_PRIME_COPRIME_CASES ← prove
   r"!p a b. int_prime p /\ coprime(a,b) ==> coprime(p,a) \/ coprime(p,b)"
   (MESON_TAC [INT_COPRIME_PRIME, INT_PRIME_COPRIME_EQ])

  let INT_PRIME_DIVPROD_POW ← prove
   r"!n p a b. int_prime(p) /\ coprime(a,b) /\ (p pow n) divides (a * b)
               ==> (p pow n) divides a \/ (p pow n) divides b"
   (MESON_TAC [INT_COPRIME_POW_DIVPROD, INT_PRIME_COPRIME_CASES, INT_MUL_SYM])

  let INT_DIVIDES_POW2_REV ← prove
   r"!n a b. (a pow n) divides (b pow n) /\ ~(n = 0) ==> a divides b"
   (← do
    let i1 ← INTEGER_RULE (← q
      r"a divides b ==> coprime(a,b) ==> a divides &1")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"gcd(a,b) = &0") THENL
     [ASM_MESON_TAC [INT_GCD_EQ_0, INT_DIVIDES_REFL], ALL_TAC] THEN
    MP_TAC (← SPECL [← q "a:int", ← q "b:int"] INT_GCD_COPRIME_EXISTS) THEN
    STRIP_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    ONCE_ASM_REWRITE_TAC [] THEN REWRITE_TAC [INT_POW_MUL] THEN
    ASM_SIMP_TAC [INT_POW_EQ_0, INT_DIVIDES_RMUL2_EQ] THEN
    DISCH_THEN (MP_TAC o MATCH_MP i1) THEN
    ASM_SIMP_TAC [INT_COPRIME_POW2] THEN
    ASM_MESON_TAC [INT_DIVIDES_POW2, INT_DIVIDES_TRANS, INT_DIVIDES_1]))

  let INT_DIVIDES_POW2_EQ ← prove
   r"!n a b. ~(n = 0) ==> ((a pow n) divides (b pow n) <=> a divides b)"
   (MESON_TAC [INT_DIVIDES_POW2_REV, INT_DIVIDES_POW])

  let INT_POW_MUL_EXISTS ← prove
   r"!m n p k. ~(m = &0) /\ m pow k * n = p pow k ==> ?q. n = q pow k"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"k = 0") THEN
    ASM_SIMP_TAC [INT_POW, INT_MUL_LID] THEN STRIP_TAC THEN
    MP_TAC (← SPECL [← q "k:num", ← q "m:int", ← q "p:int"] INT_DIVIDES_POW2_REV) THEN
    ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
     [ASM_MESON_TAC [int_divides, INT_MUL_SYM], ALL_TAC] THEN
    REWRITE_TAC [int_divides] THEN DISCH_THEN (CHOOSE_THEN SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o SYM) THEN
    ASM_SIMP_TAC [INT_POW_MUL, INT_EQ_MUL_LCANCEL, INT_POW_EQ_0] THEN
    MESON_TAC [])

  let INT_COPRIME_POW_ABS ← prove
   r"!n a b c. coprime(a,b) /\ a * b = c pow n
               ==> ?r s. abs a = r pow n /\ abs b = s pow n"
   (← do
    let r1 ← INT_RING (← q r"!p. ~(p = &0) /\ a * p = b * p ==> a = b")
    pure (GEN_TAC THEN GEN_REWRITE_TAC BINDER_CONV [SWAP_FORALL_THM] THEN
    GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN ASM_CASES_TAC (← q r"n = 0") THENL
     [ASM_REWRITE_TAC [INT_POW] THEN MESON_TAC [INT_ABS_MUL_1, INT_ABS_NUM],
      ALL_TAC] THEN
    MATCH_MP_TAC INT_PRIME_FACTOR_INDUCT THEN REPEAT CONJ_TAC THENL
     [REPEAT GEN_TAC THEN ASM_REWRITE_TAC [INT_POW_ZERO, INT_ENTIRE] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC DISJ_CASES_TAC) THEN
      ASM_SIMP_TAC [INT_COPRIME_0, INT_DIVIDES_ONE_ABS, INT_ABS_NUM] THEN
      ASM_MESON_TAC [INT_POW_ONE, INT_POW_ZERO],
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o AP_TERM (← q "abs:int->int")) THEN
      SIMP_TAC [INT_POW_ONE, INT_ABS_NUM, INT_ABS_MUL_1] THEN
      MESON_TAC [INT_POW_ONE],
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o AP_TERM (← q "abs:int->int")) THEN
      SIMP_TAC [INT_POW_ONE, INT_ABS_POW, INT_ABS_NEG, INT_ABS_NUM,
               INT_ABS_MUL_1] THEN MESON_TAC [INT_POW_ONE],
      REWRITE_TAC [INT_POW_MUL] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"p pow n divides a \/ p pow n divides b") MP_TAC THENL
       [ASM_MESON_TAC [INT_PRIME_DIVPROD_POW, int_divides], ALL_TAC] THEN
      REWRITE_TAC [int_divides] THEN
      DISCH_THEN (DISJ_CASES_THEN (X_CHOOSE_THEN (← q "d:int") SUBST_ALL_TAC)) THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [INT_COPRIME_SYM]) THEN
      ASM_SIMP_TAC [INT_COPRIME_RMUL, INT_COPRIME_LMUL,
                   INT_COPRIME_LPOW, INT_COPRIME_RPOW] THEN
      STRIP_TAC THENL
       [FIRST_X_ASSUM (MP_TAC o SPECL [← q "b:int", ← q "d:int"]),
        FIRST_X_ASSUM (MP_TAC o SPECL [← q "d:int", ← q "a:int"])] THEN
      ASM_REWRITE_TAC [] THEN
      (ANTS_TAC THENL
        [MATCH_MP_TAC r1 THEN
         EXISTS_TAC (← q "p pow n") THEN
         ASM_SIMP_TAC [INT_POW_EQ_0, INT_PRIME_IMP_NZ] THEN
         FIRST_X_ASSUM (MP_TAC o SYM) THEN CONV_TAC INT_RING,
         STRIP_TAC THEN
         ASM_REWRITE_TAC [INT_ABS_POW, ← GSYM INT_POW_MUL, INT_ABS_MUL] THEN
         MESON_TAC []])]))

  let INT_COPRIME_POW_ODD ← prove
   r"!n a b c. ODD n /\ coprime(a,b) /\ a * b = c pow n
               ==> ?r s. a = r pow n /\ b = s pow n"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q "n:num", ← q "a:int", ← q "b:int", ← q "c:int"] INT_COPRIME_POW_ABS) THEN
    ASM_REWRITE_TAC [INT_ABS] THEN
    REWRITE_TAC [RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM] THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC [INT_ABS] THEN
    ASM_MESON_TAC [INT_POW_NEG, INT_NEG_NEG, NOT_ODD])

  let INT_DIVIDES_PRIME_POW_LE ← prove
   r"!p q m n. int_prime p /\ int_prime q
               ==> ((p pow m) divides (q pow n) <=>
                    m = 0 \/ abs p = abs q /\ m <= n)"
   (← do
    let t1 ← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")
    pure (REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"m = 0") THEN
    ASM_REWRITE_TAC [INT_POW, INT_DIVIDES_1] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM INT_DIVIDES_LABS] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM INT_DIVIDES_RABS] THEN
    REWRITE_TAC [INT_ABS_POW] THEN EQ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC t1,
      ALL_TAC] THEN
    ASM_MESON_TAC [INT_DIVIDES_POW_LE, INT_PRIME_GE_2, INT_PRIME_DIVPOW,
        INT_ABS_ABS, INT_PRIME_ABS, INT_DIVIDES_POW2, INT_DIVIDES_PRIME_PRIME]))

  let INT_EQ_PRIME_POW_ABS ← prove
   r"!p q m n. int_prime p /\ int_prime q
               ==> (abs p pow m = abs q pow n <=>
                    m = 0 /\ n = 0 \/ abs p = abs q /\ m = n)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [← GSYM INT_ABS_POW] THEN
    GEN_REWRITE_TAC LAND_CONV [← GSYM INT_DIVIDES_ANTISYM_ABS] THEN
    ASM_SIMP_TAC [INT_DIVIDES_PRIME_POW_LE, INT_PRIME_ABS] THEN
    ASM_CASES_TAC (← q r"abs p = abs q") THEN ASM_REWRITE_TAC [] THEN ARITH_TAC)

  let INT_EQ_PRIME_POW_POS ← prove
   r"!p q m n. int_prime p /\ int_prime q /\ &0 <= p /\ &0 <= q
               ==> (p pow m = q pow n <=>
                    m = 0 /\ n = 0 \/ p = q /\ m = n)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← SPECL [← q "p:int", ← q "q:int", ← q "m:num", ← q "n:num"] INT_EQ_PRIME_POW_ABS) THEN
    ASM_SIMP_TAC [INT_ABS])

  let INT_DIVIDES_FACT_PRIME ← prove
   r"!p. int_prime p ==> !n. p divides &(FACT n) <=> abs p <= &n"
   (← do
    let a6 ← INT_ARITH (← q r"abs(&n + &1) = &n + &1")
    let a5 ← INT_ARITH (← q r"~(&n + &1 = &0)")
    let a4 ← INT_ARITH (← q r"p <= n + &1 ==> p <= n \/ p = n + &1")
    let a3 ← INT_ARITH (← q r"x <= n ==> x <= n + &1")
    let a2 ← INT_ARITH (← q r"abs x <= &0 <=> x = &0")
    pure (GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC [FACT] THENL
     [REWRITE_TAC [a2] THEN
      ASM_MESON_TAC [INT_DIVIDES_ONE, INT_PRIME_NEG, INT_PRIME_0, INT_PRIME_1],
      ASM_SIMP_TAC [INT_PRIME_DIVPROD_EQ, ← GSYM INT_OF_NUM_MUL] THEN
      REWRITE_TAC [← GSYM INT_OF_NUM_SUC] THEN
      ASM_MESON_TAC [INT_DIVIDES_LE, a3,
                    INT_DIVIDES_REFL, INT_DIVIDES_LABS,
                    a4, a5, a6]]))

  -- @@RETURN BEGIN
  return { INT_DIVIDES_FACT, INT_EUCLID_BOUND, INT_EUCLID, INT_PRIMES_INFINITE,
           INT_COPRIME_PRIME, INT_COPRIME_PRIME_EQ, INT_PRIME_COPRIME,
           INT_PRIME_COPRIME_EQ, INT_COPRIME_PRIMEPOW, INT_COPRIME_BEZOUT,
           INT_COPRIME_BEZOUT_ALT, INT_BEZOUT_PRIME, INT_PRIME_DIVPROD,
           INT_PRIME_DIVPROD_EQ, INT_PRIME_DIVPOW, INT_PRIME_DIVPOW_N, INT_COPRIME_SOS,
           INT_PRIME_IMP_NZ, INT_DISTINCT_PRIME_COPRIME, INT_PRIME_COPRIME_LT,
           INT_DIVIDES_PRIME_PRIME, INT_COPRIME_POW_DIVPROD, INT_PRIME_COPRIME_CASES,
           INT_PRIME_DIVPROD_POW, INT_DIVIDES_POW2_REV, INT_DIVIDES_POW2_EQ,
           INT_POW_MUL_EXISTS, INT_COPRIME_POW_ABS, INT_COPRIME_POW_ODD,
           INT_DIVIDES_PRIME_POW_LE, INT_EQ_PRIME_POW_ABS, INT_EQ_PRIME_POW_POS,
           INT_DIVIDES_FACT_PRIME }
  -- @@RETURN END

end HolLibrary.Integer
