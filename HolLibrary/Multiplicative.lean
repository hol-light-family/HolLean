/- ========================================================================= -/
/- Multiplicative functions into N or R (could add Z, C etc.)                -/
/- ========================================================================= -/
/- File: HolLibrary/Multiplicative.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/multiplicative.ml`, by hand, in file
  order, in the style of HolLibrary/Pocklington.lean and HolLibrary/Card.lean
  (see there and HolMath/Base.lean for the conventions).  multiplicative.ml
  begins with `needs "Library/products.ml"`, `needs "Library/prime.ml"` and
  `needs "Library/pocklington.ml"`; the theorems it uses from those files
  and the core library are supplied via the CoreThms structures
  (SessionLibrary.Multiplicative fills them).  Each section is a bundle (a
  `structure`) built by a `setup` function; SessionLibrary/Multiplicative.lean
  builds the bundles in order and exports every name under its HOL Light
  name.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, NUMBER_RULE, REAL_ARITH, SET_RULE, TAUT)
  they are bound first, in OCaml's order.
-/

import HolLibrary.Pocklington

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolLibrary.Multiplicative

-- @@COREFILL BEGIN
/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ARITH_EQ CARD_CLAUSES CARD_SING CARD_UNION_EQ COND_SWAP COPRIME_0
   COPRIME_DIVISORS COPRIME_DIVPROD COPRIME_PRIME COPRIME_PRIME_EQ
   COPRIME_SYM DE_MORGAN_THM DISJOINT DIVIDES_ANTISYM DIVIDES_DIVIDES_DIV
   DIVIDES_DIV_MULT DIVIDES_LE DIVIDES_MUL2 DIVIDES_ONE DIVIDES_PRIMEPOW
   DIVIDES_PRIME_PRIME DIVIDES_REFL DIVIDES_RMUL DIVIDES_ZERO DIVISION_DECOMP
   DIV_1 DIV_EQ_0 DIV_MULT DIV_REFL EMPTY_GSPEC EQ_ADD_LCANCEL_0
   EQ_ADD_RCANCEL_0 EQ_PRIMEPOW EQ_TRANS ETA_AX EXISTS_PAIR_THM
   EXISTS_UNIQUE_DEF EXP EXP_1 EXP_ONE EXTENSION FINITE_DIVISORS
   FINITE_NUMSEG_LE FINITE_RULES FINITE_SPECIAL_DIVISORS FORALL_PAIR_THM
   GCD_1 GCD_SYM IMP_IMP INDEX_EQ_0 INDEX_EXP INDEX_MUL INDEX_REFL
   INDUCT_COPRIME_STRONG IN_ELIM_PAIR_THM IN_ELIM_THM IN_INSERT IN_INTER
   IN_SING LE LE_0 LE_1 LE_EXP MONO_FORALL MULT_AC MULT_CLAUSES MULT_EQ_0
   MULT_EQ_1 MULT_EXP MULT_SYM : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (NOT_IN_EMPTY NOT_LT NOT_SUC NPRODUCT_CLAUSES NPRODUCT_EQ NPRODUCT_SING
   NPRODUCT_UNION NSUM_CLAUSES NSUM_CONST NSUM_EQ_GENERAL NSUM_IMAGE
   NSUM_LMUL NSUM_NSUM_PRODUCT NSUM_SING PAIR_EQ PHI_0 PHI_1
   PHI_MULTIPLICATIVE PHI_PRIMEPOW PHI_PRIMEPOW_ALT PRIME_0 PRIME_1
   PRIME_DIVEXP_EQ PRIME_DIVPROD_EQ PRIME_IMP_NZ PRIME_IMP_SQUAREFREE
   REAL_ABS_NEG REAL_ABS_NUM REAL_ABS_POW REAL_ADD_RID REAL_ADD_RINV
   REAL_MUL_LID REAL_MUL_LZERO REAL_MUL_RID REAL_MUL_RZERO REAL_MUL_SYM
   REAL_POW_ADD REAL_POW_ONE RIGHT_FORALL_IMP_THM SING_GSPEC SQUAREFREE_0
   SQUAREFREE_1 SQUAREFREE_EXP SQUAREFREE_MUL SQUAREFREE_PRIME SUBSET
   SUC_SUB1 SUM_CLAUSES SUM_EQ_GENERAL SUM_EQ_GENERAL_INVERSES SUM_LMUL
   SUM_SING SUM_SUM_PRODUCT SUM_SUPERSET divides num_WF o_DEF real_pow : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms3 where
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms4 where
  deriving Inhabited

-- @@COREFILL END

/-- What multiplicative.ml uses from Session besides theorems. -/
structure MultiplicativeDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  prioritize_real : IO Unit
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  NUMBER_RULE : term → ExceptT String IO thm
  NUMBER_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  REAL_ARITH_TAC : tactic
  INDUCT_TAC : tactic
  -- conversions (HOL Light GEN_BETA_CONV, REAL_RAT_REDUCE_CONV)
  GEN_BETA_CONV : ioconv
  REAL_RAT_REDUCE_CONV : ioconv
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  core4 : CoreThms4

/- ------------------------------------------------------------------------- -/
/- Definition of multiplicativity of functions into N.  (multiplicative.ml   -/
/- 9-149)                                                                     -/
/- ------------------------------------------------------------------------- -/

structure Basics where
  -- @@FIELDS
  multiplicative : thm
  MULTIPLICATIVE_1 : thm
  MULTIPLICATIVE : thm
  MULTIPLICATIVE_IGNOREZERO : thm
  MULTIPLICATIVE_EXPAND : thm
  MULTIPLICATIVE_CONVOLUTION : thm
  MULTIPLICATIVE_CONST : thm
  MULTIPLICATIVE_DELTA : thm
  MULTIPLICATIVE_DIVISORSUM : thm
  deriving Inhabited

@[nospecialize]
def setupBasics [HolBase] (D : MultiplicativeDeps) :
    ExceptT String IO Basics := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, GEN_BETA_CONV, MESON, NUMBER_RULE,
        SET_RULE, new_definition, .. } := D
  let { ARITH_EQ, COPRIME_0, COPRIME_DIVISORS, COPRIME_DIVPROD, COPRIME_PRIME_EQ,
        COPRIME_SYM, DE_MORGAN_THM, DISJOINT, DIVIDES_ANTISYM, DIVIDES_MUL2,
        DIVIDES_ONE, DIVIDES_PRIME_PRIME, DIVIDES_REFL, DIVIDES_RMUL, DIVISION_DECOMP,
        DIV_1, DIV_MULT, EMPTY_GSPEC, EQ_ADD_LCANCEL_0, EQ_ADD_RCANCEL_0, ETA_AX,
        EXISTS_PAIR_THM, EXISTS_UNIQUE_DEF, EXTENSION, FINITE_DIVISORS,
        FINITE_SPECIAL_DIVISORS, FORALL_PAIR_THM, IMP_IMP, INDEX_EQ_0, INDEX_EXP,
        INDEX_MUL, INDEX_REFL, INDUCT_COPRIME_STRONG, IN_ELIM_PAIR_THM, IN_ELIM_THM,
        IN_INTER, MONO_FORALL, MULT_AC, MULT_CLAUSES, MULT_EQ_0, MULT_EQ_1, MULT_SYM, .. } := D.core1
  let { NOT_IN_EMPTY, NPRODUCT_CLAUSES, NPRODUCT_EQ, NPRODUCT_SING, NPRODUCT_UNION,
        NSUM_EQ_GENERAL, NSUM_LMUL, NSUM_NSUM_PRODUCT, NSUM_SING, PAIR_EQ, PRIME_0,
        PRIME_1, PRIME_DIVEXP_EQ, PRIME_DIVPROD_EQ, SING_GSPEC, divides, .. } := D.core2
  -- @@SCOPE END

  let multiplicative ← new_definition
   r"multiplicative f <=>
       f(1) = 1 /\ !m n. coprime(m,n) ==> f(m * n) = f(m) * f(n)"

  let MULTIPLICATIVE_1 ← prove
   r"!f. multiplicative f ==> f(1) = 1"
   (SIMP_TAC [multiplicative])

  /- --------------------------------------------------------------------- -/
  /- We can really ignore the value at zero.                               -/
  /- --------------------------------------------------------------------- -/

  let MULTIPLICATIVE ← prove
   r"multiplicative f <=>
          f(1) = 1 /\
          !m n. ~(m = 0) /\ ~(n = 0) /\ coprime(m,n) ==> f(m * n) = f(m) * f(n)"
   (REWRITE_TAC [multiplicative] THEN EQ_TAC THEN
    STRIP_TAC THEN ASM_SIMP_TAC [] THEN
    MAP_EVERY X_GEN_TAC [← q "m:num", ← q "n:num"] THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_SIMP_TAC [MULT_CLAUSES] THEN
    ONCE_REWRITE_TAC [COPRIME_SYM] THEN
    ASM_CASES_TAC (← q r"m = 0") THEN ASM_SIMP_TAC [MULT_CLAUSES] THEN
    ASM_MESON_TAC [COPRIME_SYM, COPRIME_0, DIVIDES_ONE, MULT_CLAUSES])

  let MULTIPLICATIVE_IGNOREZERO ← prove
   r"!f g. (!n. ~(n = 0) ==> g(n) = f(n)) /\ multiplicative f
           ==> multiplicative g"
   (REPEAT GEN_TAC THEN SIMP_TAC [MULTIPLICATIVE, ARITH_EQ] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [MULT_EQ_0])

  /- --------------------------------------------------------------------- -/
  /- Expanding a multiplicative function in terms of values on prime powers. -/
  /- --------------------------------------------------------------------- -/

  let MULTIPLICATIVE_EXPAND ← prove
   r"!f n.
         multiplicative f /\ ~(n = 0)
         ==> f n = nproduct {p | prime p /\ p divides n}
                            (\p. f(p EXP index p n))"
   (← do
    let a7 ← ARITH_RULE (← q r"p <= 1 <=> p = 0 \/ p = 1")
    let m8 ← MESON [PRIME_DIVEXP_EQ, DIVIDES_PRIME_PRIME]
      (← q r"prime p ==> (prime q /\ q divides p EXP k <=> q = p /\ ~(k = 0))")
    let a6 ← ARITH_RULE (← q r"1 < p ==> ~(p = 0)")
    let a3 ← ARITH_RULE (← q r"1 < p ==> ~(p = 0)")
    let s5 ← SET_RULE (← q r"{x | P x \/ Q x} = {x | P x} UNION {x | Q x}")
    let m4 ← MESON [PRIME_DIVPROD_EQ]
      (← q r"prime p /\ p divides a * b <=>
             prime p /\ p divides a \/ prime p /\ p divides b")
    let a2 ← ARITH_RULE (← q r"~(n = 0) /\ ~(n = 1) <=> 1 < n")
    let m1 ← MESON [PRIME_1, DIVIDES_ONE]
      (← q r"~(prime p /\ p divides 1)")
    pure (REWRITE_TAC [multiplicative] THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (← q r"n = 1") THENL
     [ASM_REWRITE_TAC [m1] THEN
      ASM_REWRITE_TAC [EMPTY_GSPEC, NPRODUCT_CLAUSES],
      MAP_EVERY UNDISCH_TAC [← q r"~(n = 1)", ← q r"~(n = 0)"] THEN
      REWRITE_TAC [IMP_IMP, a2]] THEN
    SPEC_TAC (← q "n:num", ← q "n:num") THEN
    MATCH_MP_TAC INDUCT_COPRIME_STRONG THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [← q "a:num", ← q "b:num"] THEN ASM_SIMP_TAC [] THEN
      REPLICATE_TAC 3 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC) THEN
      REWRITE_TAC [m4] THEN
      REWRITE_TAC [s5] THEN
      W (MP_TAC o PART_MATCH (fun c => do lhand (← rand c)) NPRODUCT_UNION o rand o snd) THEN
      ASM_SIMP_TAC [FINITE_SPECIAL_DIVISORS, a6] THEN
      ANTS_TAC THENL
       [REWRITE_TAC [DISJOINT, EXTENSION, IN_ELIM_THM,
                    IN_INTER, NOT_IN_EMPTY] THEN
        ASM_MESON_TAC [COPRIME_PRIME_EQ],
        DISCH_THEN SUBST1_TAC] THEN
      BINOP_TAC THEN MATCH_MP_TAC NPRODUCT_EQ THEN
      X_GEN_TAC (← q "p:num") THEN REWRITE_TAC [IN_ELIM_THM] THEN STRIP_TAC THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      ASM_SIMP_TAC [INDEX_MUL, a3] THEN
      REWRITE_TAC [EQ_ADD_LCANCEL_0, EQ_ADD_RCANCEL_0] THEN
      REWRITE_TAC [INDEX_EQ_0] THEN ASM_MESON_TAC [COPRIME_PRIME_EQ],
      SIMP_TAC [m8] THEN
      REWRITE_TAC [SING_GSPEC, NPRODUCT_SING] THEN
      SIMP_TAC [INDEX_EXP, INDEX_REFL] THEN
      REWRITE_TAC [a7] THEN
      ASM_MESON_TAC [PRIME_0, PRIME_1, MULT_CLAUSES]]))

  /- --------------------------------------------------------------------- -/
  /- A key "building block" theorem.                                       -/
  /- --------------------------------------------------------------------- -/

  let MULTIPLICATIVE_CONVOLUTION ← prove
   r"!f g. multiplicative f /\ multiplicative g
           ==> multiplicative (\n. nsum {d | d divides n}
                                        (\d. f(d) * g(n DIV d)))"
   (← do
    let n1 ← NUMBER_RULE
      (← q r"coprime(a * b:num,c * d) ==> coprime(c,a) /\ coprime(d,b)")
    let ac2 ← AC MULT_AC
      (← q r"(e * e') * d * d':num = (d * e) * (d' * e')")
    pure (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [multiplicative] THEN
    REWRITE_TAC [MULTIPLICATIVE, ← GSYM NSUM_LMUL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [DIVIDES_ONE, DIV_1, SING_GSPEC, NSUM_SING, MULT_CLAUSES] THEN
    MAP_EVERY X_GEN_TAC [← q "m:num", ← q "n:num"] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
    ASM_SIMP_TAC [← GSYM NSUM_LMUL, NSUM_NSUM_PRODUCT, FINITE_DIVISORS] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_EQ_GENERAL THEN
    EXISTS_TAC (← q r"\(a:num,b). a * b") THEN REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN
    REWRITE_TAC [FORALL_PAIR_THM, EXISTS_PAIR_THM, IN_ELIM_PAIR_THM] THEN
    CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC [IN_ELIM_THM] THEN
    REWRITE_TAC [PAIR_EQ] THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_THEN (ASSUME_TAC o MATCH_MP DIVISION_DECOMP) THEN
      CONJ_TAC THENL [ASM_MESON_TAC [MULT_SYM], ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [← q "a1:num", ← q "b1:num", ← q "a2:num", ← q "b2:num"] THEN
      STRIP_TAC THEN FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
      REWRITE_TAC [← GSYM DIVIDES_ANTISYM] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC COPRIME_DIVPROD THENL
       (List.map EXISTS_TAC [← q "b2:num", ← q "b1:num", ← q "a2:num", ← q "a1:num"]) THEN
      ASM_MESON_TAC [COPRIME_DIVISORS, DIVIDES_REFL,
                    DIVIDES_RMUL, COPRIME_SYM, MULT_SYM],
      MAP_EVERY X_GEN_TAC [← q "d:num", ← q "e:num"] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM_MESON_TAC [DIVIDES_MUL2, MULT_SYM], ALL_TAC] THEN
      MP_TAC (← REWRITE_RULE [divides] (← ASSUME (← q r"(d:num) divides n"))) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d':num") SUBST_ALL_TAC) THEN
      MP_TAC (← REWRITE_RULE [divides] (← ASSUME (← q r"(e:num) divides m"))) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "e':num") SUBST_ALL_TAC) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [MULT_EQ_0, DE_MORGAN_THM]) THEN
      ONCE_REWRITE_TAC [ac2] THEN
      ASM_SIMP_TAC [DIV_MULT, MULT_EQ_0] THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP n1) THEN
      ASM_SIMP_TAC [] THEN ARITH_TAC]))

  let MULTIPLICATIVE_CONST ← prove
   r"!c. multiplicative(\n. c) <=> c = 1"
   (GEN_TAC THEN REWRITE_TAC [multiplicative] THEN
    ASM_CASES_TAC (← q r"c = 1") THEN ASM_REWRITE_TAC [MULT_CLAUSES])

  let MULTIPLICATIVE_DELTA ← prove
   r"multiplicative(\n. if n = 1 then 1 else 0)"
   (REWRITE_TAC [MULTIPLICATIVE, MULT_EQ_1] THEN ARITH_TAC)

  let MULTIPLICATIVE_DIVISORSUM ← prove
   r"!f. multiplicative f ==> multiplicative (\n. nsum {d | d divides n} f)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:num->num", ← q r"\n:num. 1"] MULTIPLICATIVE_CONVOLUTION) THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, MULTIPLICATIVE_CONST, ETA_AX])

  -- @@RETURN BEGIN
  return { multiplicative, MULTIPLICATIVE_1, MULTIPLICATIVE, MULTIPLICATIVE_IGNOREZERO,
           MULTIPLICATIVE_EXPAND, MULTIPLICATIVE_CONVOLUTION, MULTIPLICATIVE_CONST,
           MULTIPLICATIVE_DELTA, MULTIPLICATIVE_DIVISORSUM }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Some particular multiplicative functions.  (multiplicative.ml 150-236)    -/
/- ------------------------------------------------------------------------- -/

structure Particular where
  -- @@FIELDS
  MULTIPLICATIVE_ID : thm
  MULTIPLICATIVE_POWERSUM : thm
  sigma : thm
  tau : thm
  MULTIPLICATIVE_SIGMA : thm
  MULTIPLICATIVE_TAU : thm
  MULTIPLICATIVE_PHI : thm
  MULTIPLICATIVE_GCD : thm
  PHI_EXPAND : thm
  MULTIPLICATIVE_UNIQUE : thm
  PHI_DIVISORSUM : thm
  deriving Inhabited

@[nospecialize]
def setupParticular [HolBase] (D : MultiplicativeDeps) (BBasics : Basics) :
    ExceptT String IO Particular := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, MESON_TAC, NUMBER_TAC,
        SET_RULE, new_definition, .. } := D
  let { DIVIDES_ANTISYM, DIVIDES_PRIMEPOW, EQ_PRIMEPOW, ETA_AX, EXP, EXP_1, EXP_ONE,
        FINITE_DIVISORS, FINITE_NUMSEG_LE, GCD_1, GCD_SYM, IMP_IMP, INDEX_EQ_0,
        INDUCT_COPRIME_STRONG, IN_ELIM_THM, LE, LE_EXP, MULT_CLAUSES, MULT_EXP, .. } := D.core1
  let { NOT_SUC, NPRODUCT_EQ, NSUM_CLAUSES, NSUM_CONST, NSUM_IMAGE, NSUM_SING, PHI_0,
        PHI_1, PHI_MULTIPLICATIVE, PHI_PRIMEPOW, PHI_PRIMEPOW_ALT, PRIME_1,
        PRIME_IMP_NZ, RIGHT_FORALL_IMP_THM, SUC_SUB1, num_WF, o_DEF, .. } := D.core2
  let { MULTIPLICATIVE, MULTIPLICATIVE_DIVISORSUM, MULTIPLICATIVE_EXPAND,
        MULTIPLICATIVE_IGNOREZERO, multiplicative, .. } := BBasics
  -- @@SCOPE END

  let MULTIPLICATIVE_ID ← prove
   r"multiplicative(\n. n)"
   (REWRITE_TAC [multiplicative])

  let MULTIPLICATIVE_POWERSUM ← prove
   r"!k. multiplicative(\n. nsum {d | d divides n} (\d. d EXP k))"
   (GEN_TAC THEN MATCH_MP_TAC MULTIPLICATIVE_DIVISORSUM THEN
    REWRITE_TAC [MULTIPLICATIVE, EXP_ONE, MULT_EXP])

  let sigma ← new_definition
   r"sigma(n) = if n = 0 then 0 else nsum {d | d divides n} (\i. i)"

  let tau ← new_definition
   r"tau(n) = if n = 0 then 0 else CARD {d | d divides n}"

  let MULTIPLICATIVE_SIGMA ← prove
   r"multiplicative(sigma)"
   (MP_TAC (← SPEC (← q "1") MULTIPLICATIVE_POWERSUM) THEN
    MATCH_MP_TAC (← REWRITE_RULE [← GSYM IMP_IMP] MULTIPLICATIVE_IGNOREZERO) THEN
    SIMP_TAC [sigma, EXP_1])

  let MULTIPLICATIVE_TAU ← prove
   r"multiplicative(tau)"
   (MP_TAC (← SPEC (← q "0") MULTIPLICATIVE_POWERSUM) THEN
    MATCH_MP_TAC (← REWRITE_RULE [← GSYM IMP_IMP] MULTIPLICATIVE_IGNOREZERO) THEN
    SIMP_TAC [tau, EXP, NSUM_CONST, MULT_CLAUSES, FINITE_DIVISORS])

  let MULTIPLICATIVE_PHI ← prove
   r"multiplicative(phi)"
   (REWRITE_TAC [multiplicative, PHI_MULTIPLICATIVE, PHI_1])

  let MULTIPLICATIVE_GCD ← prove
   r"!n. multiplicative(\m. gcd(n,m))"
   (REWRITE_TAC [multiplicative, ← ONCE_REWRITE_RULE [GCD_SYM] GCD_1] THEN
    ONCE_REWRITE_TAC [← GSYM DIVIDES_ANTISYM] THEN NUMBER_TAC)

  let PHI_EXPAND ← prove
   r"!n. phi n = if n = 0 then 0
                 else nproduct {p | prime p /\ p divides n}
                               (\p. p EXP (index p n - 1) * (p - 1))"
   (GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [PHI_0] THEN
    MP_TAC (← SPECL [← q r"phi", ← q "n:num"] MULTIPLICATIVE_EXPAND) THEN
    ASM_REWRITE_TAC [MULTIPLICATIVE_PHI] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC NPRODUCT_EQ THEN SIMP_TAC [IN_ELIM_THM, PHI_PRIMEPOW_ALT] THEN
    ASM_SIMP_TAC [INDEX_EQ_0] THEN MESON_TAC [PRIME_1])

  /- --------------------------------------------------------------------- -/
  /- Uniqueness of multiplicative functions if equal on prime powers.      -/
  /- --------------------------------------------------------------------- -/

  let MULTIPLICATIVE_UNIQUE ← prove
   r"!f g. multiplicative f /\ multiplicative g /\
           (!p k. prime p ==> f(p EXP k) = g(p EXP k))
           ==> !n. ~(n = 0) ==> f n = g n"
   (← do
    let a1 ← ARITH_RULE (← q r"~(n = 0) ==> n = 1 \/ 1 < n")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC num_WF THEN
    X_GEN_TAC (← q "n:num") THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (DISJ_CASES_THEN2 ASSUME_TAC MP_TAC o MATCH_MP a1)
    THENL [ASM_MESON_TAC [multiplicative], ALL_TAC] THEN
    SPEC_TAC (← q "n:num", ← q "n:num") THEN MATCH_MP_TAC INDUCT_COPRIME_STRONG THEN
    ASM_MESON_TAC [multiplicative]))

  /- --------------------------------------------------------------------- -/
  /- Derive the divisor-sum identity for phi from this.                    -/
  /- --------------------------------------------------------------------- -/

  let PHI_DIVISORSUM ← prove
   r"!n. ~(n = 0) ==> nsum {d | d divides n} (\d. phi(d)) = n"
   (← do
    let a5 ← ARITH_RULE (← q r"a:num <= b ==> b - a + a = b")
    let a4 ← ARITH_RULE (← q r"~(SUC k <= k)")
    let s3 ← SET_RULE (← q r"{i:num | i = a \/ i <= b} = a INSERT {i | i <= b}")
    let s2 ← SET_RULE (← q r"{x | x = 0} = {0}")
    let s1 ← SET_RULE
      (← q r"{d | ?i. i <= k /\ d = p EXP i} = IMAGE (\i. p EXP i) {i | i <= k}")
    pure (MATCH_MP_TAC MULTIPLICATIVE_UNIQUE THEN REWRITE_TAC [MULTIPLICATIVE_ID] THEN
    SIMP_TAC [MULTIPLICATIVE_DIVISORSUM, ETA_AX, MULTIPLICATIVE_PHI] THEN
    SIMP_TAC [DIVIDES_PRIMEPOW, s1] THEN
    SIMP_TAC [NSUM_IMAGE, EQ_PRIMEPOW, o_DEF, PHI_PRIMEPOW] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    INDUCT_TAC THEN REWRITE_TAC [LE, NOT_SUC] THEN
    REWRITE_TAC [← CONJUNCT1 EXP, s2, NSUM_SING] THEN
    REWRITE_TAC [s3] THEN
    ASM_SIMP_TAC [NSUM_CLAUSES, FINITE_NUMSEG_LE, NOT_SUC] THEN
    REWRITE_TAC [IN_ELIM_THM, SUC_SUB1, a4] THEN
    MATCH_MP_TAC a5 THEN
    ASM_SIMP_TAC [LE_EXP, PRIME_IMP_NZ] THEN ARITH_TAC))

  -- @@RETURN BEGIN
  return { MULTIPLICATIVE_ID, MULTIPLICATIVE_POWERSUM, sigma, tau, MULTIPLICATIVE_SIGMA,
           MULTIPLICATIVE_TAU, MULTIPLICATIVE_PHI, MULTIPLICATIVE_GCD, PHI_EXPAND,
           MULTIPLICATIVE_UNIQUE, PHI_DIVISORSUM }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Now the real analog.  (multiplicative.ml 237-322)                         -/
/- ------------------------------------------------------------------------- -/

structure Real where
  -- @@FIELDS
  real_multiplicative : thm
  REAL_MULTIPLICATIVE : thm
  REAL_MULTIPLICATIVE_CONST : thm
  REAL_MULTIPLICATIVE_DELTA : thm
  REAL_MULTIPLICATIVE_IGNOREZERO : thm
  REAL_MULTIPLICATIVE_CONVOLUTION : thm
  REAL_MULTIPLICATIVE_DIVISORSUM : thm
  deriving Inhabited

@[nospecialize]
def setupReal [HolBase] (D : MultiplicativeDeps) :
    ExceptT String IO Real := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, NUMBER_RULE, REAL_ARITH_TAC, new_definition, .. } := D
  let { ARITH_EQ, COPRIME_0, COPRIME_DIVISORS, COPRIME_DIVPROD, COPRIME_SYM,
        DE_MORGAN_THM, DIVIDES_ANTISYM, DIVIDES_MUL2, DIVIDES_ONE, DIVIDES_REFL,
        DIVIDES_RMUL, DIVISION_DECOMP, DIV_1, DIV_MULT, ETA_AX, EXISTS_PAIR_THM,
        EXISTS_UNIQUE_DEF, FINITE_DIVISORS, FORALL_PAIR_THM, IN_ELIM_PAIR_THM,
        IN_ELIM_THM, MONO_FORALL, MULT_AC, MULT_CLAUSES, MULT_EQ_0, MULT_EQ_1,
        MULT_SYM, .. } := D.core1
  let { PAIR_EQ, REAL_MUL_LID, REAL_MUL_RID, REAL_MUL_SYM, SING_GSPEC, SUM_EQ_GENERAL,
        SUM_LMUL, SUM_SING, SUM_SUM_PRODUCT, divides, .. } := D.core2
  -- @@SCOPE END

  let real_multiplicative ← new_definition
   r"real_multiplicative (f:num->real) <=>
       f(1) = &1 /\ !m n. coprime(m,n) ==> f(m * n) = f(m) * f(n)"

  let REAL_MULTIPLICATIVE ← prove
   r"real_multiplicative f <=>
          f(1) = &1 /\
          !m n. ~(m = 0) /\ ~(n = 0) /\ coprime(m,n) ==> f(m * n) = f(m) * f(n)"
   (REWRITE_TAC [real_multiplicative] THEN EQ_TAC THEN
    STRIP_TAC THEN ASM_SIMP_TAC [] THEN
    MAP_EVERY X_GEN_TAC [← q "m:num", ← q "n:num"] THEN
    ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_SIMP_TAC [COPRIME_0, MULT_CLAUSES, REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC [COPRIME_SYM] THEN
    ASM_CASES_TAC (← q r"m = 0") THEN
    ASM_SIMP_TAC [COPRIME_0, MULT_CLAUSES, REAL_MUL_RID] THEN
    ASM_MESON_TAC [COPRIME_SYM, COPRIME_0, DIVIDES_ONE, MULT_CLAUSES])

  let REAL_MULTIPLICATIVE_CONST ← prove
   r"!c. real_multiplicative(\n. c) <=> c = &1"
   (GEN_TAC THEN REWRITE_TAC [real_multiplicative] THEN
    ASM_CASES_TAC (← q r"c:real = &1") THEN ASM_REWRITE_TAC [REAL_MUL_LID])

  let REAL_MULTIPLICATIVE_DELTA ← prove
   r"real_multiplicative(\n. if n = 1 then &1 else &0)"
   (REWRITE_TAC [REAL_MULTIPLICATIVE, MULT_EQ_1] THEN REAL_ARITH_TAC)

  let REAL_MULTIPLICATIVE_IGNOREZERO ← prove
   r"!f g. (!n. ~(n = 0) ==> g(n) = f(n)) /\ real_multiplicative f
           ==> real_multiplicative g"
   (REPEAT GEN_TAC THEN SIMP_TAC [REAL_MULTIPLICATIVE, ARITH_EQ] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN (fun th => STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC [] THEN ASM_MESON_TAC [MULT_EQ_0])

  let REAL_MULTIPLICATIVE_CONVOLUTION ← prove
   r"!f g. real_multiplicative f /\ real_multiplicative g
           ==> real_multiplicative (\n. sum {d | d divides n}
                                            (\d. f(d) * g(n DIV d)))"
   (← do
    let n1 ← NUMBER_RULE
      (← q r"coprime(a * b:num,c * d) ==> coprime(c,a) /\ coprime(d,b)")
    let ac2 ← AC MULT_AC
      (← q r"(e * e') * d * d':num = (d * e) * (d' * e')")
    pure (REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [real_multiplicative] THEN
    REWRITE_TAC [REAL_MULTIPLICATIVE, ← GSYM SUM_LMUL] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC [DIVIDES_ONE, DIV_1, SING_GSPEC, SUM_SING, REAL_MUL_LID] THEN
    MAP_EVERY X_GEN_TAC [← q "m:num", ← q "n:num"] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
    ASM_SIMP_TAC [← GSYM SUM_LMUL, SUM_SUM_PRODUCT, FINITE_DIVISORS] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_EQ_GENERAL THEN
    EXISTS_TAC (← q r"\(a:num,b). a * b") THEN REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN
    REWRITE_TAC [FORALL_PAIR_THM, EXISTS_PAIR_THM, IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC [IN_ELIM_THM, PAIR_EQ] THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_THEN (ASSUME_TAC o MATCH_MP DIVISION_DECOMP) THEN
      CONJ_TAC THENL [ASM_MESON_TAC [MULT_SYM], ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [← q "a1:num", ← q "b1:num", ← q "a2:num", ← q "b2:num"] THEN
      STRIP_TAC THEN FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
      REWRITE_TAC [← GSYM DIVIDES_ANTISYM] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC COPRIME_DIVPROD THENL
       (List.map EXISTS_TAC [← q "b2:num", ← q "b1:num", ← q "a2:num", ← q "a1:num"]) THEN
      ASM_MESON_TAC [COPRIME_DIVISORS, DIVIDES_REFL,
                    DIVIDES_RMUL, COPRIME_SYM, MULT_SYM],
      MAP_EVERY X_GEN_TAC [← q "d:num", ← q "e:num"] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM_MESON_TAC [DIVIDES_MUL2, MULT_SYM], ALL_TAC] THEN
      MP_TAC (← REWRITE_RULE [divides] (← ASSUME (← q r"(d:num) divides n"))) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "d':num") SUBST_ALL_TAC) THEN
      MP_TAC (← REWRITE_RULE [divides] (← ASSUME (← q r"(e:num) divides m"))) THEN
      DISCH_THEN (X_CHOOSE_THEN (← q "e':num") SUBST_ALL_TAC) THEN
      RULE_ASSUM_TAC (REWRITE_RULE [MULT_EQ_0, DE_MORGAN_THM]) THEN
      ONCE_REWRITE_TAC [ac2] THEN
      ASM_SIMP_TAC [DIV_MULT, MULT_EQ_0] THEN
      FIRST_ASSUM (ASSUME_TAC o MATCH_MP n1) THEN
      ASM_SIMP_TAC [] THEN REAL_ARITH_TAC]))

  let REAL_MULTIPLICATIVE_DIVISORSUM ← prove
   r"!f. real_multiplicative f
         ==> real_multiplicative (\n. sum {d | d divides n} f)"
   (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:num->real", ← q r"(\n. &1):num->real"]
       REAL_MULTIPLICATIVE_CONVOLUTION) THEN
    ASM_REWRITE_TAC [REAL_MUL_RID, REAL_MULTIPLICATIVE_CONST, ETA_AX])

  -- @@RETURN BEGIN
  return { real_multiplicative, REAL_MULTIPLICATIVE, REAL_MULTIPLICATIVE_CONST,
           REAL_MULTIPLICATIVE_DELTA, REAL_MULTIPLICATIVE_IGNOREZERO,
           REAL_MULTIPLICATIVE_CONVOLUTION, REAL_MULTIPLICATIVE_DIVISORSUM }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- The Mobius function (into the reals).  (multiplicative.ml 323-448)         -/
/- ------------------------------------------------------------------------- -/

structure Mobius where
  -- @@FIELDS
  mobius : thm
  MOBIUS_ALT : thm
  MOBIUS_0 : thm
  MOBIUS_1 : thm
  REAL_ABS_MOBIUS : thm
  MOBIUS_MULT : thm
  REAL_MULTIPLICATIVE_MOBIUS : thm
  MOBIUS_PRIME : thm
  MOBIUS_PRIMEPOW : thm
  DIVISORSUM_MOBIUS : thm
  MOBIUS_INVERSION : thm
  deriving Inhabited

@[nospecialize]
def setupMobius [HolBase] (D : MultiplicativeDeps) (BReal : Real) :
    ExceptT String IO Mobius := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_MESON_TAC, MESON, NUMBER_RULE, REAL_RAT_REDUCE_CONV, SET_RULE,
        SET_TAC, new_definition, prioritize_real, .. } := D
  let { CARD_CLAUSES, CARD_SING, CARD_UNION_EQ, COND_SWAP, COPRIME_PRIME,
        DE_MORGAN_THM, DIVIDES_DIVIDES_DIV, DIVIDES_DIV_MULT, DIVIDES_LE, DIVIDES_ONE,
        DIVIDES_PRIMEPOW, DIVIDES_PRIME_PRIME, DIVIDES_REFL, DIVIDES_ZERO, DIV_EQ_0,
        DIV_REFL, EQ_TRANS, ETA_AX, EXP, EXP_1, FINITE_DIVISORS, FINITE_RULES,
        FINITE_SPECIAL_DIVISORS, FORALL_PAIR_THM, INDUCT_COPRIME_STRONG,
        IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_INSERT, IN_SING, LE_0, LE_1, MULT_CLAUSES,
        MULT_EQ_0, MULT_SYM, .. } := D.core1
  let { NOT_IN_EMPTY, NOT_LT, PRIME_1, PRIME_DIVPROD_EQ, PRIME_IMP_SQUAREFREE,
        REAL_ABS_NEG, REAL_ABS_NUM, REAL_ABS_POW, REAL_ADD_RID, REAL_ADD_RINV,
        REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RZERO, REAL_MUL_SYM, REAL_POW_ADD,
        REAL_POW_ONE, SQUAREFREE_0, SQUAREFREE_1, SQUAREFREE_EXP, SQUAREFREE_MUL,
        SQUAREFREE_PRIME, SUBSET, SUM_CLAUSES, SUM_EQ_GENERAL_INVERSES, SUM_LMUL,
        SUM_SING, SUM_SUM_PRODUCT, SUM_SUPERSET, real_pow, .. } := D.core2
  let { REAL_MULTIPLICATIVE_DIVISORSUM, real_multiplicative, .. } := BReal
  -- @@SCOPE END

  prioritize_real

  let mobius ← new_definition
   r"mobius(n) = if squarefree n then --(&1) pow CARD {p | prime p /\ p divides n}
                else &0:real"

  let MOBIUS_ALT ← prove
   r"!n. mobius(n) = if ?p. prime p /\ (p EXP 2) divides n then &0
                     else --(&1) pow CARD {p | prime p /\ p divides n}"
   (← do
    let m1 ← MESON [] (← q r"~(?x. P x /\ Q x) <=> !x. P x ==> ~Q x")
    pure (ONCE_REWRITE_TAC [← GSYM COND_SWAP] THEN
    REWRITE_TAC [m1] THEN
    REWRITE_TAC [← GSYM SQUAREFREE_PRIME, ← GSYM mobius]))

  let MOBIUS_0 ← prove
   r"mobius 0 = &0"
   (REWRITE_TAC [mobius, SQUAREFREE_0])

  let MOBIUS_1 ← prove
   r"mobius 1 = &1"
   (REWRITE_TAC [mobius, SQUAREFREE_1, DIVIDES_ONE] THEN
    SUBGOAL_THEN (← q r"{p | prime p /\ p = 1} = {}")
     (fun th => SIMP_TAC [th, CARD_CLAUSES, real_pow]) THEN SET_TAC [PRIME_1])

  let REAL_ABS_MOBIUS ← prove
   r"!n. abs(mobius n) <= &1"
   (GEN_TAC THEN REWRITE_TAC [mobius] THEN COND_CASES_TAC THEN
    REWRITE_TAC [REAL_ABS_POW, REAL_ABS_NEG, REAL_POW_ONE, REAL_ABS_NUM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV)

  let MOBIUS_MULT ← prove
   r"!a b. coprime(a,b) ==> mobius(a * b) = mobius a * mobius b"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [mobius, SQUAREFREE_MUL] THEN
    MAP_EVERY ASM_CASES_TAC [← q r"squarefree a", ← q r"squarefree b"] THEN
    ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_MUL_RZERO] THEN
    REWRITE_TAC [← GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN
    ASM_CASES_TAC (← q r"a = 0") THENL [ASM_MESON_TAC [SQUAREFREE_0], ALL_TAC] THEN
    ASM_CASES_TAC (← q r"b = 0") THENL [ASM_MESON_TAC [SQUAREFREE_0], ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
    ASM_SIMP_TAC [FINITE_SPECIAL_DIVISORS, MULT_EQ_0] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o MATCH_MP COPRIME_PRIME) THEN SET_TAC [],
      MP_TAC PRIME_DIVPROD_EQ THEN ASM SET_TAC []])

  let REAL_MULTIPLICATIVE_MOBIUS ← prove
   r"real_multiplicative mobius"
   (SIMP_TAC [real_multiplicative, MOBIUS_1, MOBIUS_MULT])

  let MOBIUS_PRIME ← prove
   r"!p. prime p ==> mobius(p) = -- &1"
   (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [mobius, PRIME_IMP_SQUAREFREE] THEN
    SUBGOAL_THEN (← q r"{q | prime q /\ q divides p} = {p}") SUBST1_TAC THENL
     [ASM SET_TAC [DIVIDES_PRIME_PRIME], ALL_TAC] THEN
    REWRITE_TAC [CARD_SING] THEN CONV_TAC REAL_RAT_REDUCE_CONV)

  let MOBIUS_PRIMEPOW ← prove
   r"!p k. prime p ==> mobius(p EXP k) = if k = 0 then &1
                                         else if k = 1 then -- &1
                                         else &0"
   (REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [MOBIUS_1, EXP] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [MOBIUS_PRIME, EXP_1] THEN
    ASM_REWRITE_TAC [mobius, SQUAREFREE_EXP] THEN ASM_MESON_TAC [PRIME_1])

  let DIVISORSUM_MOBIUS ← prove
   r"!n. 1 <= n
         ==> sum {d | d divides n} (\d. mobius d) = if n = 1 then &1 else &0"
   (← do
    let a4 ← ARITH_RULE (← q r"1 < n ==> ~(n = 1)")
    let s3 ← SET_RULE (← q r"{x | x = a} = {a}")
    let t2 ← TAUT (← q r"(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)")
    let a1 ← ARITH_RULE (← q r"1 <= n <=> n = 1 \/ 1 < n")
    pure (REWRITE_TAC [a1] THEN
    REWRITE_TAC [t2] THEN
    SIMP_TAC [DIVIDES_ONE, s3, SUM_SING, MOBIUS_1] THEN
    SIMP_TAC [a4] THEN
    MATCH_MP_TAC INDUCT_COPRIME_STRONG THEN CONJ_TAC THENL
     [MP_TAC (← MATCH_MP REAL_MULTIPLICATIVE_DIVISORSUM
                      REAL_MULTIPLICATIVE_MOBIUS) THEN
      SIMP_TAC [real_multiplicative, ETA_AX, REAL_MUL_LZERO],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q "p:num", ← q "k:num"] THEN STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (← q r"sum {1,p} (\d. mobius d)") THEN
    CONJ_TAC THENL
     [ALL_TAC,
      ASM_SIMP_TAC [SUM_CLAUSES, FINITE_RULES, NOT_IN_EMPTY, IN_SING,
                   MOBIUS_PRIME, MOBIUS_1, REAL_ADD_RID, REAL_ADD_RINV] THEN
      ASM_MESON_TAC [PRIME_1]] THEN
    MATCH_MP_TAC SUM_SUPERSET THEN ASM_SIMP_TAC [DIVIDES_PRIMEPOW] THEN
    REWRITE_TAC [SUBSET, IN_ELIM_THM, IN_INSERT, NOT_IN_EMPTY, DE_MORGAN_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THENL
     [ASM_MESON_TAC [EXP, LE_0],
      ASM_MESON_TAC [EXP_1, LE_1],
      ASM_SIMP_TAC [MOBIUS_PRIMEPOW] THEN ASM_MESON_TAC [EXP, EXP_1]]))

  let MOBIUS_INVERSION ← prove
   r"!f g. (!n. 1 <= n ==> g(n) = sum {d | d divides n} f)
           ==> !n. 1 <= n
                   ==> f(n) = sum {d | d divides n} (\d. mobius(d) * g(n DIV d))"
   (← do
    let n2 ← NUMBER_RULE (← q r"(a * b:num) divides c ==> b divides c")
    pure (REPEAT STRIP_TAC THEN
    SUBGOAL_THEN (← q r"!d. d divides n ==> ~(n DIV d = 0)") ASSUME_TAC THENL
     [GEN_TAC THEN ASM_CASES_TAC (← q r"d = 0") THEN
      ASM_SIMP_TAC [DIVIDES_ZERO, LE_1] THEN
      DISCH_THEN (MP_TAC o MATCH_MP DIVIDES_LE) THEN
      ASM_SIMP_TAC [LE_1, NOT_LT, DIV_EQ_0],
      ALL_TAC] THEN
    ASM_SIMP_TAC [LE_1] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     (← q r"sum {d | d divides n} (\d. f(d) * (if n DIV d = 1 then &1 else &0))") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC (← q r"sum {n} (\d. f(d) * (if n DIV d = 1 then &1 else &0))") THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC [SUM_SING, DIV_REFL, LE_1, REAL_MUL_RID], ALL_TAC] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
      SIMP_TAC [SUBSET, IN_SING, IN_ELIM_THM, DIVIDES_REFL] THEN
      X_GEN_TAC (← q "d:num") THEN REWRITE_TAC [DIVIDES_DIV_MULT] THEN
      DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES, REAL_MUL_RZERO],
      ASM_SIMP_TAC [← GSYM DIVISORSUM_MOBIUS, LE_1] THEN
      REWRITE_TAC [← GSYM SUM_LMUL] THEN
      ASM_SIMP_TAC [SUM_SUM_PRODUCT, FINITE_DIVISORS, LE_1, IN_ELIM_THM] THEN
      MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
      REPEAT (EXISTS_TAC (← q r"\(m:num,n:num). (n,m)")) THEN
      REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
      CONJ_TAC THEN REPEAT GEN_TAC THEN
      DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      REWRITE_TAC [REAL_MUL_SYM] THEN
      ASM_MESON_TAC [DIVIDES_DIVIDES_DIV, MULT_SYM, n2]]))

  -- @@RETURN BEGIN
  return { mobius, MOBIUS_ALT, MOBIUS_0, MOBIUS_1, REAL_ABS_MOBIUS, MOBIUS_MULT,
           REAL_MULTIPLICATIVE_MOBIUS, MOBIUS_PRIME, MOBIUS_PRIMEPOW, DIVISORSUM_MOBIUS,
           MOBIUS_INVERSION }
  -- @@RETURN END

end HolLibrary.Multiplicative
