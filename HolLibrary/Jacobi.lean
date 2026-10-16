/- ========================================================================= -/
/- Jacobi symbols for N and Z, taking in Legendre symbols as a special case. -/
/- ========================================================================= -/
/- File: HolLibrary/Jacobi.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Library/jacobi.ml`, by hand, in file order,
  in the style of HolLibrary/Primitive.lean and HolLibrary/Pocklington.lean
  (see there and HolMath/Base.lean for the conventions).  jacobi.ml begins
  with `needs "Library/primitive.ml"`; the theorems it uses from primitive.ml,
  the files primitive.ml needs, and the core library are supplied via the
  CoreThms structures (SessionLibrary.Jacobi fills them).  Each section is a
  bundle (a `structure`) built by a `setup` function; SessionLibrary/Jacobi.lean
  builds the bundles in order and exports every name under its HOL Light
  name.

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, NUMBER_RULE, INTEGER_RULE, INT_ARITH,
  INT_RING, TAUT) they are bound first, in OCaml's order.
-/

import HolLibrary.Primitive

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

set_option maxRecDepth 8000

namespace HolLibrary.Jacobi

-- @@COREFILL BEGIN
/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD1 ADD_CLAUSES ADD_SUB ALL ARITH ARITH_EQ BIJECTIONS_CARD_EQ CARD_CROSS
   CARD_IMAGE_INJ_EQ CARD_NUMSEG CARD_NUMSEG_1 CARD_UNION
   COMPLETE_FACTOR_INDUCT COND_SWAP CONG CONG_ADD CONG_DIVIDES CONG_IMP_EQ
   CONG_LMOD CONG_MOD_0 CONG_MOD_2 CONG_MOD_2_ALT CONG_MULT CONG_MULT_LCANCEL
   CONG_REFL CONG_SQUARE_1_PRIME_POWER CONG_SUB CONG_SYM CONG_TRANS
   CONJ_ASSOC COPRIME_0 COPRIME_1 COPRIME_2 COPRIME_LMUL COPRIME_PRIME_EQ
   COPRIME_RMUL COPRIME_SYM DISJOINT DIVIDES_0 DIVIDES_2 DIVIDES_ADD
   DIVIDES_DIVIDES_DIV DIVIDES_DIV_MULT DIVIDES_LE DIVIDES_LMUL
   DIVIDES_LMUL2_EQ DIVIDES_MOD DIVIDES_MUL2 DIVIDES_MUL_L DIVIDES_ONE
   DIVIDES_PRIME_PRIME DIVIDES_REFL DIVIDES_RMUL DIVISION DIV_ADD DIV_MULT
   DIV_MULT_ADD EQ_IMP EQ_TRANS EULER_CRITERION EVEN_ADD EVEN_EXISTS EVEN_EXP
   EVEN_MULT EVEN_OR_ODD EVEN_SUB EXISTS_IN_GSPEC EXISTS_PAIR_THM
   EXISTS_UNIQUE_THM EXP : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms2 where
  (EXP_1 EXP_2 EXP_EXP EXP_ONE EXP_ZERO EXTENSION FERMAT_LITTLE_PRIME
   FINITE_CROSS_EQ FINITE_INDUCT_STRONG FINITE_NUMSEG FINITE_RESTRICT
   FINITE_SPECIAL_DIVISORS FINITE_SUBSET FINITE_UNION FORALL_IN_GSPEC
   FORALL_PAIR_THM FUN_EQ_THM IMP_CONJ IMP_CONJ_ALT IMP_IMP INDEX_1
   INDEX_EQ_0 INDEX_MUL INDEX_REFL INDEX_ZERO INFINITE INT_ABS_ABS
   INT_ABS_MUL INT_ABS_NEG INT_ABS_NUM INT_ABS_POS INT_ABS_POW INT_ABS_ZERO
   INT_CONG_IMP_EQ INT_CONG_LREM INT_CONG_MOD_0 INT_CONG_MOD_ABS INT_CONG_POW
   INT_CONG_REFL INT_CONG_RREM INT_CONG_TRANS INT_COPRIME_1 INT_COPRIME_LREM
   INT_COPRIME_RABS INT_DIVIDES_RABS INT_DIVIDES_REFL INT_DIVISION INT_ENTIRE
   INT_FORALL_ABS INT_FORALL_POS INT_LE_MUL INT_LE_MUL2 INT_LE_REFL
   INT_MUL_LID INT_MUL_LNEG INT_MUL_LZERO INT_MUL_REM INT_MUL_RNEG
   INT_MUL_RZERO INT_NEG_EQ_0 INT_NEG_MINUS1 INT_OF_NUM_ADD INT_OF_NUM_EQ
   INT_OF_NUM_LE INT_OF_NUM_MUL INT_OF_NUM_OF_INT INT_OF_NUM_POW
   INT_OF_NUM_REM INT_OF_NUM_SUB INT_POW : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms3 where
  (INT_POW_1 INT_POW_1_LE INT_POW_ADD INT_POW_EQ_0 INT_POW_MUL INT_POW_NEG
   INT_POW_ONE INT_POW_POW INT_POW_ZERO INT_REM_2_CASES INT_REM_EQ
   INT_REM_EQ_SELF INT_REM_RABS INT_REM_REM INT_REM_REM_MUL INT_REM_RNEG
   INT_REM_ZERO IN_CROSS IN_ELIM_PAIR_THM IN_ELIM_THM IN_INTER IN_NUMSEG
   IN_UNION IPRODUCT_ABS IPRODUCT_CLAUSES IPRODUCT_CLOSED IPRODUCT_CONST
   IPRODUCT_EQ IPRODUCT_EQ_0 IPRODUCT_EQ_1 IPRODUCT_INJECTION IPRODUCT_LE_1
   IPRODUCT_MUL IPRODUCT_ONE IPRODUCT_RELATED IPRODUCT_RESTRICT_SET
   IPRODUCT_SING IPRODUCT_SUPERSET LEFT_ADD_DISTRIB LEFT_IMP_EXISTS_THM
   LEFT_SUB_DISTRIB LE_1 LE_MULT_LCANCEL LE_MULT_RCANCEL LTE_TRANS
   LT_ADD_LCANCEL LT_IMP_LE LT_MULT_LCANCEL MOD_2_CASES MOD_ADD_MOD MOD_LT
   MOD_LT_EQ MOD_MULT MOD_MULT_ADD MOD_ZERO MONO_FORALL MULT_ASSOC
   MULT_CLAUSES MULT_EQ_0 MULT_EQ_1 MULT_SYM NOT_EVEN NOT_FORALL_THM NOT_IMP
   NOT_IN_EMPTY NOT_LE NOT_ODD NPRODUCT_CLAUSES NUM_OF_INT_MUL
   NUM_OF_INT_OF_NUM : thm)
  deriving Inhabited

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms4 where
  (ODD ODD_EXISTS ODD_MULT ODD_PRIME OR_EXISTS_THM PAIRWISE PAIR_EQ
   PRIMES_INFINITE PRIME_0 PRIME_1 PRIME_2 PRIME_COPRIME_EQ PRIME_COPRIME_LT
   PRIME_DIVEXP_EQ PRIME_DIVPROD_EQ PRIME_FACTOR_INDUCT PRIME_GE_2
   PRIME_IMP_NZ PRIME_ODD RIGHT_FORALL_IMP_THM SING_GSPEC SUBSET SUB_EQ_0
   SUC_SUB1 coprime num_congruent num_coprime num_divides numseg o_DEF o_THM : thm)
  deriving Inhabited

-- @@COREFILL END

/-- What jacobi.ml uses from Session besides theorems. -/
structure JacobiDeps where
  -- definitions and parser state
  new_definition : String → ExceptT String IO thm
  -- decision procedures and tactics
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  INT_ARITH : term → ExceptT String IO thm
  INT_ARITH_TAC : tactic
  ASM_INT_ARITH_TAC : tactic
  INTEGER_RULE : term → ExceptT String IO thm
  NUMBER_RULE : term → ExceptT String IO thm
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  INDUCT_TAC : tactic
  -- (add fields here as needed, with a comment naming the HOL Light value)
  TAUT : term → ExceptT String IO thm           -- bool.ml's TAUT
  INT_REDUCE_CONV : ioconv                       -- int.ml's INT_REDUCE_CONV
  NUM_REDUCE_CONV : ioconv                       -- calc_num.ml's NUM_REDUCE_CONV
  INT_RING : term → ExceptT String IO thm         -- HOL Light's INT_RING
  EXPAND_CASES_CONV : ioconv                       -- HOL Light's EXPAND_CASES_CONV
  core1 : CoreThms1
  core2 : CoreThms2
  core3 : CoreThms3
  core4 : CoreThms4

/- jacobi.ml's header: `Jacobi symbols for N and Z, taking in Legendre
   symbols as a special case.`  Its `needs "Library/primitive.ml"` is wired
   by the Session. -/

/- ------------------------------------------------------------------------- -/
/- Some fairly generic lemmas, but it's not quite clear where to put them.   -/
/- ------------------------------------------------------------------------- -/

structure Generic where
  -- @@FIELDS
  COPRIME_IPRODUCT : thm
  CONG_IPRODUCT : thm
  deriving Inhabited

@[nospecialize]
def setupGeneric [HolBase] (D : JacobiDeps) :
    ExceptT String IO Generic := do
  -- @@SCOPE BEGIN
  let { INTEGER_RULE, .. } := D
  let { IMP_CONJ, INT_COPRIME_1, .. } := D.core2
  let { IPRODUCT_CLOSED, IPRODUCT_RELATED, .. } := D.core3
  -- @@SCOPE END

  let COPRIME_IPRODUCT ← prove
   r"!s (a:A->int) n.
        (!i. i IN s ==> coprime(n,a i)) ==> coprime(n,iproduct s a)"
   (REPEAT GEN_TAC THEN
    MP_TAC (← ISPECL [← q r"\i:int. coprime(n,i)", ← q r"a:A->int", ← q r"s:A->bool"]
          IPRODUCT_CLOSED) THEN
    REWRITE_TAC [INT_COPRIME_1, IMP_CONJ] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONV_TAC INTEGER_RULE)

  let CONG_IPRODUCT ← prove
   r"!s (a:A->int) (b:A->int) n.
        FINITE s /\
        (!i. i IN s ==> (a i == b i) (mod n))
        ==> (iproduct s a == iproduct s b) (mod n)"
   (REPEAT STRIP_TAC THEN MP_TAC (← ISPECL
     [← q r"\i j:int. (i == j) (mod n)", ← q r"a:A->int", ← q r"b:A->int", ← q r"s:A->bool"]
     IPRODUCT_RELATED) THEN
    ASM_REWRITE_TAC [] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONV_TAC INTEGER_RULE)

  -- @@RETURN BEGIN
  return { COPRIME_IPRODUCT, CONG_IPRODUCT }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- The definition over N (with the range still being Z).                     -/
/- ------------------------------------------------------------------------- -/

structure JacobiDef where
  -- @@FIELDS
  jacobi : thm
  JACOBI_BOUND : thm
  JACOBI_CASES : thm
  JACOBI_PRIME : thm
  JACOBI : thm
  JACOBI_ALT : thm
  JACOBI_EQ_0 : thm
  JACOBI_ZERO : thm
  JACOBI_1 : thm
  JACOBI_0 : thm
  JACOBI_2_CASES : thm
  JACOBI_2 : thm
  deriving Inhabited

@[nospecialize]
def setupJacobiDef [HolBase] (D : JacobiDeps) :
    ExceptT String IO JacobiDef := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, INT_ARITH_TAC, INT_REDUCE_CONV, MESON, MESON_TAC,
        NUM_REDUCE_CONV, SET_RULE, TAUT, new_definition, .. } := D
  let { ARITH_EQ, COND_SWAP, CONG_MOD_2, CONG_REFL, CONJ_ASSOC, COPRIME_0,
        COPRIME_PRIME_EQ, DIVIDES_0, DIVIDES_2, DIVIDES_ONE, DIVIDES_PRIME_PRIME,
        EVEN_EXP, EXISTS_IN_GSPEC, .. } := D.core1
  let { FINITE_SPECIAL_DIVISORS, FINITE_SUBSET, FORALL_IN_GSPEC, FUN_EQ_THM, IMP_CONJ,
        INDEX_1, INDEX_EQ_0, INDEX_REFL, INDEX_ZERO, INFINITE, INT_ABS_POS,
        INT_ABS_POW, INT_POW, .. } := D.core2
  let { INT_POW_1, INT_POW_1_LE, INT_POW_EQ_0, INT_POW_ONE, IN_ELIM_THM, IPRODUCT_ABS,
        IPRODUCT_EQ, IPRODUCT_EQ_0, IPRODUCT_EQ_1, IPRODUCT_LE_1, IPRODUCT_ONE,
        IPRODUCT_SING, IPRODUCT_SUPERSET, MOD_2_CASES, MONO_FORALL, NOT_EVEN,
        NOT_FORALL_THM, NOT_ODD, .. } := D.core3
  let { ODD, PRIMES_INFINITE, PRIME_1, PRIME_2, PRIME_GE_2, PRIME_IMP_NZ, SING_GSPEC,
        SUBSET, .. } := D.core4
  -- @@SCOPE END

  let jacobi ← new_definition
   r"(jacobi:num#num->int)(a,n) =
        if n = 0 then if a = 1 then &1 else &0
        else iproduct {p | prime p /\ p divides n}
                      (\p. (if p divides a then &0
                            else if ?x. (x EXP 2 == a) (mod p) then &1
                            else --(&1)) pow index p n)"

  let JACOBI_BOUND ← prove
   r"!a n. abs(jacobi(a,n)) <= &1"
   (REPEAT GEN_TAC THEN REWRITE_TAC [jacobi] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
           CONV_TAC INT_REDUCE_CONV) THEN
    ASM_SIMP_TAC [← GSYM IPRODUCT_ABS, FINITE_SPECIAL_DIVISORS] THEN
    MATCH_MP_TAC IPRODUCT_LE_1 THEN
    ASM_SIMP_TAC [FINITE_SPECIAL_DIVISORS, FORALL_IN_GSPEC, INT_ABS_POS] THEN
    X_GEN_TAC (← q "p:num") THEN STRIP_TAC THEN REWRITE_TAC [INT_ABS_POW] THEN
    MATCH_MP_TAC INT_POW_1_LE THEN INT_ARITH_TAC)

  let JACOBI_CASES ← prove
   r"!a n. jacobi(a,n) = -- &1 \/ jacobi(a,n) = &0 \/ jacobi(a,n) = &1"
   (MP_TAC JACOBI_BOUND THEN REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    INT_ARITH_TAC)

  let JACOBI_PRIME ← prove
   r"!a p. prime p
         ==> jacobi(a,p) =
             if p divides a then &0
             else if ?x. (x EXP 2 == a) (mod p) then &1
             else --(&1)"
   (← do
    let m2 ← MESON [] (← q r"~(prime q ==> ~(q = p)) <=> prime p /\ q = p")
    let s1 ← SET_RULE (← q r"{x | P x /\ Q x} = {x | ~(P x ==> ~Q x)}")
    pure (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [jacobi, PRIME_IMP_NZ] THEN
    ONCE_REWRITE_TAC [s1] THEN
    ASM_SIMP_TAC [DIVIDES_PRIME_PRIME] THEN
    REWRITE_TAC [m2] THEN
    ASM_REWRITE_TAC [SING_GSPEC, IPRODUCT_SING, INDEX_REFL] THEN
    ASM_CASES_TAC (← q "p <= 1") THEN ASM_REWRITE_TAC [INT_POW_1] THEN
    FIRST_X_ASSUM (MP_TAC o MATCH_MP PRIME_GE_2) THEN ASM_ARITH_TAC))

  let JACOBI ← prove
   r"!a n. jacobi(a,n) =
         if n = 0 then if a = 1 then &1 else &0
         else iproduct {p | prime p /\ p divides n}
                       (\p. jacobi(a,p) pow index p n)"
   (REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [jacobi] THEN
    ASM_CASES_TAC (← q "n = 0") THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC IPRODUCT_EQ THEN REWRITE_TAC [FORALL_IN_GSPEC] THEN
    SIMP_TAC [JACOBI_PRIME])

  let JACOBI_ALT ← prove
   r"!s a n.
        FINITE s /\
        {p | prime p /\ p divides n} SUBSET s /\
        s SUBSET {p | prime p}
        ==> jacobi(a,n) = iproduct s (\p. jacobi(a,p) pow index p n)"
   (← do
    let t1 ← TAUT (← q r"~p ==> p ==> q")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "n = 0") THENL
     [REWRITE_TAC [CONJ_ASSOC] THEN
      DISCH_THEN (MP_TAC o CONJUNCT1) THEN
      DISCH_THEN (MP_TAC o MATCH_MP FINITE_SUBSET) THEN
      MATCH_MP_TAC t1 THEN
      ASM_REWRITE_TAC [← GSYM INFINITE, PRIMES_INFINITE, DIVIDES_0],
      STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [JACOBI] THEN
      ASM_REWRITE_TAC [] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC IPRODUCT_SUPERSET THEN ASM_REWRITE_TAC [] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [SUBSET, IN_ELIM_THM]) THEN
      ASM_SIMP_TAC [IN_ELIM_THM, IMP_CONJ, INDEX_ZERO, INT_POW]]))

  let JACOBI_EQ_0 ← prove
   r"!a n. jacobi(a,n) = &0 <=> ~coprime(a,n)"
   (← do
    let m1 ← MESON [PRIME_1] (← q r"prime p ==> ~(p = 1)")
    pure (REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [JACOBI] THEN
    ASM_CASES_TAC (← q "n = 0") THENL
     [ASM_REWRITE_TAC [COPRIME_0] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      CONV_TAC INT_REDUCE_CONV,
      ASM_SIMP_TAC [IPRODUCT_EQ_0, FINITE_SPECIAL_DIVISORS] THEN
      REWRITE_TAC [EXISTS_IN_GSPEC, INT_POW_EQ_0] THEN
      REWRITE_TAC [COPRIME_PRIME_EQ, NOT_FORALL_THM] THEN
      AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      X_GEN_TAC (← q "p:num") THEN ASM_CASES_TAC (← q "prime p") THEN ASM_REWRITE_TAC [] THEN
      ASM_CASES_TAC (← q r"(p:num) divides n") THEN ASM_REWRITE_TAC [INDEX_EQ_0] THEN
      ASM_SIMP_TAC [m1] THEN
      ASM_SIMP_TAC [JACOBI_PRIME] THEN
      REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
      CONV_TAC INT_REDUCE_CONV]))

  let JACOBI_ZERO ← prove
   r"!a b. ~coprime(a,n) ==> jacobi(a,n) = &0"
   (REWRITE_TAC [JACOBI_EQ_0])

  let JACOBI_1 ← prove
   r"(!n. jacobi(1,n) = &1) /\
   (!a. jacobi(a,1) = &1)"
   (← do
    let m1 ← MESON [PRIME_1] (← q r"prime p ==> ~(p = 1)")
    pure (REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [JACOBI] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC [INDEX_1, INT_POW, IPRODUCT_ONE] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC IPRODUCT_EQ_1 THEN REWRITE_TAC [FORALL_IN_GSPEC] THEN
    X_GEN_TAC (← q "p:num") THEN STRIP_TAC THEN
    ASM_SIMP_TAC [JACOBI_PRIME, DIVIDES_ONE] THEN
    ASM_SIMP_TAC [m1] THEN
    SUBGOAL_THEN (← q r"?x. (x EXP 2 == 1) (mod p)")
     (fun th => REWRITE_TAC [th, INT_POW_ONE]) THEN
    EXISTS_TAC (← q "1") THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC [CONG_REFL]))

  let JACOBI_0 ← prove
   r"(!n. jacobi(0,n) = if n = 1 then &1 else &0) /\
   (!a. jacobi(a,0) = if a = 1 then &1 else &0)"
   (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [JACOBI_1] THEN
    ASM_REWRITE_TAC [JACOBI_EQ_0, COPRIME_0])

  let JACOBI_2_CASES ← prove
   r"!a. jacobi(a,2) = if ODD a then &1 else &0"
   (GEN_TAC THEN SIMP_TAC [JACOBI_PRIME, PRIME_2, DIVIDES_2, ← GSYM NOT_EVEN] THEN
    ASM_CASES_TAC (← q "EVEN a") THEN ASM_REWRITE_TAC [CONG_MOD_2] THEN
    REWRITE_TAC [EVEN_EXP, ARITH_EQ] THEN REWRITE_TAC [NOT_EVEN] THEN
    MESON_TAC [ODD])

  let JACOBI_2 ← prove
   r"!a. jacobi(a,2) = &(a MOD 2)"
   (GEN_TAC THEN REWRITE_TAC [JACOBI_2_CASES, MOD_2_CASES] THEN
    REWRITE_TAC [← GSYM NOT_ODD, COND_SWAP] THEN MESON_TAC [])

  -- @@RETURN BEGIN
  return { jacobi, JACOBI_BOUND, JACOBI_CASES, JACOBI_PRIME, JACOBI, JACOBI_ALT,
           JACOBI_EQ_0, JACOBI_ZERO, JACOBI_1, JACOBI_0, JACOBI_2_CASES, JACOBI_2 }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Euler's criterion and multiplicativity properties.                        -/
/- ------------------------------------------------------------------------- -/

structure JacobiEuler where
  -- @@FIELDS
  JACOBI_EULER : thm
  JACOBI_EULER_ALT : thm
  JACOBI_RMUL : thm
  JACOBI_LMUL : thm
  JACOBI_REXP : thm
  JACOBI_LEXP : thm
  JACOBI_EXP_2 : thm
  JACOBI_EXP_2_ALT : thm
  JACOBI_NPRODUCT_RIGHT : thm
  JACOBI_NPRODUCT_LEFT : thm
  JACOBI_CONG : thm
  JACOBI_MOD_GEN : thm
  JACOBI_MOD : thm
  JACOBI_SQUARED : thm
  deriving Inhabited

@[nospecialize]
def setupJacobiEuler [HolBase] (D : JacobiDeps) (BJacobiDef : JacobiDef) :
    ExceptT String IO JacobiEuler := do
  -- @@SCOPE BEGIN
  let { ASM_ARITH_TAC, ASM_MESON_TAC, INDUCT_TAC, INTEGER_RULE, INT_ARITH,
        INT_REDUCE_CONV, NUMBER_RULE, NUM_REDUCE_CONV, .. } := D
  let { ARITH, COND_SWAP, CONG_LMOD, CONG_MOD_0, CONG_MOD_2_ALT, CONG_REFL,
        CONG_SQUARE_1_PRIME_POWER, CONG_SYM, CONG_TRANS, CONJ_ASSOC, COPRIME_SYM,
        DIVIDES_2, DIVIDES_DIV_MULT, DIVIDES_LMUL, DIVIDES_REFL, DIVIDES_RMUL,
        EULER_CRITERION, EVEN_SUB, EXP, .. } := D.core1
  let { EXP_1, EXP_2, EXP_EXP, EXP_ONE, EXP_ZERO, FERMAT_LITTLE_PRIME,
        FINITE_INDUCT_STRONG, FINITE_SPECIAL_DIVISORS, FORALL_IN_GSPEC, IMP_IMP,
        INDEX_MUL, INT_ABS_MUL, INT_ABS_POS, INT_CONG_IMP_EQ, INT_LE_MUL2, INT_MUL_LID,
        INT_MUL_LZERO, INT_MUL_RZERO, INT_OF_NUM_EQ, INT_OF_NUM_LE, INT_OF_NUM_MUL,
        INT_OF_NUM_POW, INT_OF_NUM_SUB, INT_POW, .. } := D.core2
  let { INT_POW_1, INT_POW_ADD, INT_POW_MUL, INT_POW_ONE, INT_POW_ZERO, IN_ELIM_THM,
        IPRODUCT_CLAUSES, IPRODUCT_EQ, IPRODUCT_MUL, LE_1, MOD_2_CASES, MULT_CLAUSES,
        MULT_EQ_0, MULT_EQ_1, NOT_EVEN, NPRODUCT_CLAUSES, .. } := D.core3
  let { ODD_MULT, ODD_PRIME, PRIME_COPRIME_EQ, PRIME_DIVEXP_EQ, PRIME_GE_2,
        PRIME_IMP_NZ, PRIME_ODD, SUBSET, num_congruent, num_divides, .. } := D.core4
  let { JACOBI, JACOBI_0, JACOBI_1, JACOBI_2, JACOBI_2_CASES, JACOBI_ALT, JACOBI_BOUND,
        JACOBI_CASES, JACOBI_EQ_0, JACOBI_PRIME, jacobi, .. } := BJacobiDef
  -- @@SCOPE END

  let JACOBI_EULER ← prove
   r"!a p. prime p /\ ~(p = 2)
         ==> (jacobi(a,p) == &a pow ((p - 1) DIV 2)) (mod &p)"
   (← do
    let i1 ← INTEGER_RULE (← q r"(&0:int == a) (mod p) <=> p divides a")
    pure (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [EULER_CRITERION, JACOBI_PRIME] THEN
    COND_CASES_TAC THENL
     [REWRITE_TAC [i1] THEN
      ASM_SIMP_TAC [INT_OF_NUM_POW, ← GSYM num_divides, PRIME_DIVEXP_EQ] THEN
      FIRST_ASSUM (MP_TAC o MATCH_MP PRIME_GE_2) THEN ASM_ARITH_TAC,
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"((a EXP ((p - 1) DIV 2)) EXP 2 == 1) (mod p)") MP_TAC THENL
     [MP_TAC (← SPECL [← q "a:num", ← q "p:num"] FERMAT_LITTLE_PRIME) THEN
      ASM_SIMP_TAC [← ONCE_REWRITE_RULE [COPRIME_SYM] PRIME_COPRIME_EQ] THEN
      REWRITE_TAC [EXP_EXP] THEN
      SUBGOAL_THEN (← q r"(p - 1) DIV 2 * 2 = p - 1") (fun th => REWRITE_TAC [th]) THEN
      REWRITE_TAC [← GSYM DIVIDES_DIV_MULT, DIVIDES_2, EVEN_SUB, ARITH] THEN
      ASM_MESON_TAC [PRIME_ODD, NOT_EVEN],
      ALL_TAC] THEN
    MP_TAC (← SPECL [← q "p:num", ← q "1", ← q r"a EXP ((p - 1) DIV 2)"]
      CONG_SQUARE_1_PRIME_POWER) THEN
    ASM_REWRITE_TAC [EXP_1] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_CASES_TAC (← q r"(a EXP ((p - 1) DIV 2) == 1) (mod p)") THEN
    ASM_REWRITE_TAC [] THENL
     [REWRITE_TAC [← GSYM num_congruent, INT_OF_NUM_POW] THEN
      ASM_MESON_TAC [CONG_SYM],
      REWRITE_TAC [num_congruent, ← GSYM INT_OF_NUM_POW] THEN
      ASM_SIMP_TAC [← GSYM INT_OF_NUM_SUB, LE_1, PRIME_IMP_NZ] THEN
      CONV_TAC INTEGER_RULE]))

  let JACOBI_EULER_ALT ← prove
   r"!a p. prime p
         ==> (jacobi(a,p) == &a pow (if p = 2 then 1 else (p - 1) DIV 2))
             (mod &p)"
   (REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC [JACOBI_EULER] THEN
    DISCH_THEN (K ALL_TAC) THEN ASM_REWRITE_TAC [INT_POW_1, JACOBI_2_CASES] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [← GSYM num_congruent, CONG_MOD_2_ALT] THEN
    CONV_TAC NUM_REDUCE_CONV)

  let JACOBI_RMUL ← prove
   r"!a m n. jacobi(a,m * n) = jacobi(a,m) * jacobi(a,n)"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q "a = 1") THEN ASM_REWRITE_TAC [JACOBI_1, INT_MUL_LID] THEN
    ASM_CASES_TAC (← q "m = 0") THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, JACOBI_0, INT_MUL_LZERO] THEN
    ASM_CASES_TAC (← q "n = 0") THEN
    ASM_REWRITE_TAC [MULT_CLAUSES, JACOBI_0, INT_MUL_RZERO] THEN
    MP_TAC (← SPECL [← q r"{p | prime p /\ p divides m * n}", ← q "a:num"] JACOBI_ALT) THEN
    DISCH_THEN (fun th => tactic_of do
      pure (MP_TAC (← SPEC (← q "m:num") th) THEN MP_TAC (← SPEC (← q "n:num") th))) THEN
    ASM_SIMP_TAC [FINITE_SPECIAL_DIVISORS, MULT_EQ_0] THEN
    SIMP_TAC [SUBSET, IN_ELIM_THM, DIVIDES_LMUL, DIVIDES_RMUL] THEN
    REPEAT (DISCH_THEN SUBST1_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [JACOBI] THEN
    ASM_REWRITE_TAC [MULT_EQ_0] THEN
    ASM_SIMP_TAC [← GSYM IPRODUCT_MUL, FINITE_SPECIAL_DIVISORS, MULT_EQ_0] THEN
    MATCH_MP_TAC IPRODUCT_EQ THEN
    REWRITE_TAC [FORALL_IN_GSPEC, ← GSYM INT_POW_ADD] THEN
    ASM_SIMP_TAC [INDEX_MUL])

  let JACOBI_LMUL ← prove
   r"!a b n. jacobi(a * b,n) = jacobi(a,n) * jacobi(b,n)"
   (← do
    let i1 ← INTEGER_RULE
     (← q r"(a' * b':int == c') (mod p)
        ==> (a == a') (mod p) /\ (b == b') (mod p) /\ (c == c') (mod p)
            ==> (c == a * b) (mod p)")
    let a2 ← INT_ARITH
     (← q r"abs(x:int) <= &1 /\ abs(y) <= &1 /\ &3 <= p ==> abs(x - y) < p")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "n = 0") THENL
     [ASM_REWRITE_TAC [JACOBI_0, MULT_EQ_1] THEN
      MAP_EVERY ASM_CASES_TAC [← q "a = 1", ← q "b = 1"] THEN
      ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV,
      ONCE_REWRITE_TAC [JACOBI] THEN ASM_REWRITE_TAC []] THEN
    ASM_SIMP_TAC [← GSYM IPRODUCT_MUL, FINITE_SPECIAL_DIVISORS] THEN
    MATCH_MP_TAC IPRODUCT_EQ THEN
    REWRITE_TAC [FORALL_IN_GSPEC, ← GSYM INT_POW_MUL] THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    X_GEN_TAC (← q "p:num") THEN DISCH_THEN (ASSUME_TAC o CONJUNCT1) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_CASES_TAC (← q "p = 2") THENL
     [ASM_REWRITE_TAC [JACOBI_2_CASES, ODD_MULT] THEN
      MAP_EVERY ASM_CASES_TAC [← q "ODD a", ← q "ODD b"] THEN
      ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV,
      MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC (← q r"&p:int") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC a2 THEN
        REWRITE_TAC [INT_OF_NUM_LE, JACOBI_BOUND] THEN
        CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [ODD_PRIME, PRIME_ODD]] THEN
        GEN_REWRITE_TAC RAND_CONV [← GSYM INT_MUL_LID] THEN
        REWRITE_TAC [INT_ABS_MUL] THEN MATCH_MP_TAC INT_LE_MUL2 THEN
        REWRITE_TAC [JACOBI_BOUND, INT_ABS_POS],
        MP_TAC (← SPECL [← q r"a * b:num", ← q "p:num"] JACOBI_EULER) THEN
        MP_TAC (← SPECL [← q "b:num", ← q "p:num"] JACOBI_EULER) THEN
        MP_TAC (← SPECL [← q "a:num", ← q "p:num"] JACOBI_EULER) THEN
        ASM_REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC] THEN MATCH_MP_TAC i1 THEN
        REWRITE_TAC [← GSYM INT_POW_MUL, ← GSYM INT_OF_NUM_MUL] THEN
        CONV_TAC INTEGER_RULE]]))

  let JACOBI_REXP ← prove
   r"!a n k. jacobi(a,n EXP k) = jacobi(a,n) pow k"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [EXP, JACOBI_RMUL, JACOBI_1, INT_POW])

  let JACOBI_LEXP ← prove
   r"!a n k. jacobi(a EXP k,n) = jacobi(a,n) pow k"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [EXP, JACOBI_LMUL, JACOBI_1, INT_POW] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [INT_MUL_RZERO])

  let JACOBI_EXP_2 ← prove
   r"!a k. jacobi(a,2 EXP k) = if k = 0 then &1 else &(a MOD 2)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [JACOBI_REXP, JACOBI_2] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [INT_POW] THEN
    REWRITE_TAC [INT_OF_NUM_POW, INT_OF_NUM_EQ] THEN
    REWRITE_TAC [MOD_2_CASES] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [EXP_ZERO, EXP_ONE])

  let JACOBI_EXP_2_ALT ← prove
   r"!a k. jacobi(a,2 EXP k) = if k = 0 \/ ODD a then &1 else &0"
   (REPEAT GEN_TAC THEN REWRITE_TAC [JACOBI_REXP, JACOBI_2_CASES] THEN
    ASM_CASES_TAC (← q "ODD a") THEN ASM_REWRITE_TAC [INT_POW_ONE, INT_POW_ZERO])

  let JACOBI_NPRODUCT_RIGHT ← prove
   r"!a (n:A->num) k.
        FINITE k
        ==> jacobi(a,nproduct k n) = iproduct k (\i. jacobi(a,n i))"
   (GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [NPRODUCT_CLAUSES, JACOBI_RMUL, JACOBI_1, IPRODUCT_CLAUSES])

  let JACOBI_NPRODUCT_LEFT ← prove
   r"!(a:A->num) n k.
        FINITE k
        ==> jacobi(nproduct k a,n) = iproduct k (\i. jacobi(a i,n))"
   (GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC [NPRODUCT_CLAUSES, JACOBI_LMUL, JACOBI_1, IPRODUCT_CLAUSES])

  let JACOBI_CONG ← prove
   r"!a b n. (a == b) (mod n) ==> jacobi(a,n) = jacobi(b,n)"
   (← do
    let n2 ← NUMBER_RULE
     (← q r"p divides n /\ (a:num == b) (mod n) ==> (a == b) (mod p)")
    let n1 ← NUMBER_RULE (← q r"p divides a <=> (0 == a) (mod p)")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q "n = 0") THEN ASM_SIMP_TAC [CONG_MOD_0] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC [jacobi] THEN MATCH_MP_TAC IPRODUCT_EQ THEN
    REWRITE_TAC [FORALL_IN_GSPEC] THEN X_GEN_TAC (← q "p:num") THEN STRIP_TAC THEN
    REWRITE_TAC [n1] THEN
    MP_TAC n2 THEN
    ASM_MESON_TAC [CONG_TRANS, CONG_SYM]))

  let JACOBI_MOD_GEN ← prove
   r"!a m n. n divides m ==> jacobi(a MOD m,n) = jacobi(a,n)"
   (← do
    let n1 ← NUMBER_RULE
      (← q r"(n:num) divides m ==> (x == y) (mod m) ==> (x == y) (mod n)")
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC JACOBI_CONG THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP n1) THEN
    REWRITE_TAC [CONG_LMOD, CONG_REFL]))

  let JACOBI_MOD ← prove
   r"!a n. jacobi(a MOD n,n) = jacobi(a,n)"
   (SIMP_TAC [JACOBI_MOD_GEN, DIVIDES_REFL])

  let JACOBI_SQUARED ← prove
   r"(!a n. jacobi(a EXP 2,n) = if coprime(a,n) then &1 else &0) /\
   (!a n. jacobi(a,n EXP 2) = if coprime(a,n) then &1 else &0)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [EXP_2, JACOBI_LMUL, JACOBI_RMUL] THEN
    ONCE_REWRITE_TAC [← GSYM COND_SWAP] THEN REWRITE_TAC [← GSYM JACOBI_EQ_0] THEN
    MP_TAC (← SPECL [← q "a:num", ← q "n:num"] JACOBI_CASES) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV)

  -- @@RETURN BEGIN
  return { JACOBI_EULER, JACOBI_EULER_ALT, JACOBI_RMUL, JACOBI_LMUL, JACOBI_REXP,
           JACOBI_LEXP, JACOBI_EXP_2, JACOBI_EXP_2_ALT, JACOBI_NPRODUCT_RIGHT,
           JACOBI_NPRODUCT_LEFT, JACOBI_CONG, JACOBI_MOD_GEN, JACOBI_MOD, JACOBI_SQUARED }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- The minus-one case and Gauss's lemma.                                     -/
/- ------------------------------------------------------------------------- -/

structure Gauss where
  -- @@FIELDS
  JACOBI_MINUS1 : thm
  JACOBI_MINUS1_CASES : thm
  JACOBI_GAUSS_LEMMA : thm
  deriving Inhabited

@[nospecialize]
def setupGauss [HolBase] (D : JacobiDeps) (BGeneric : Generic) (BJacobiDef : JacobiDef) (BJacobiEuler : JacobiEuler) :
    ExceptT String IO Gauss := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INTEGER_RULE, INT_ARITH,
        INT_REDUCE_CONV, NUMBER_RULE, NUM_REDUCE_CONV, .. } := D
  let { ADD1, ADD_CLAUSES, ARITH, ARITH_EQ, CARD_NUMSEG_1, COND_SWAP, CONG,
        CONG_DIVIDES, CONG_IMP_EQ, CONG_MULT_LCANCEL, CONG_SUB, COPRIME_SYM, DIVIDES_2,
        DIVIDES_LE, DIVIDES_MOD, DIVIDES_REFL, DIVISION, EVEN_ADD, EVEN_MULT, .. } := D.core1
  let { FINITE_NUMSEG, FINITE_RESTRICT, IMP_CONJ_ALT, INT_ABS_NEG, INT_ABS_NUM,
        INT_ABS_POW, INT_CONG_IMP_EQ, INT_CONG_POW, INT_CONG_REFL, INT_CONG_RREM,
        INT_CONG_TRANS, INT_LE_REFL, INT_MUL_LID, INT_MUL_LNEG, INT_MUL_RNEG,
        INT_OF_NUM_EQ, INT_OF_NUM_LE, INT_OF_NUM_MUL, INT_OF_NUM_REM, INT_OF_NUM_SUB, .. } := D.core2
  let { INT_POW_ADD, INT_POW_NEG, INT_POW_ONE, INT_POW_POW, IN_NUMSEG, IPRODUCT_CONST,
        IPRODUCT_INJECTION, IPRODUCT_MUL, IPRODUCT_RESTRICT_SET, LEFT_ADD_DISTRIB,
        LEFT_IMP_EXISTS_THM, LE_1, LT_IMP_LE, MOD_ADD_MOD, MOD_LT_EQ, MULT_ASSOC,
        MULT_CLAUSES, MULT_EQ_0, MULT_SYM, NOT_LE, .. } := D.core3
  let { ODD_EXISTS, ODD_MULT, ODD_PRIME, PRIME_0, PRIME_1, PRIME_COPRIME_LT,
        PRIME_DIVPROD_EQ, PRIME_FACTOR_INDUCT, PRIME_IMP_NZ, PRIME_ODD, SUB_EQ_0,
        SUC_SUB1, coprime, num_coprime, o_DEF, o_THM, .. } := D.core4
  let { CONG_IPRODUCT, COPRIME_IPRODUCT, .. } := BGeneric
  let { JACOBI_0, JACOBI_BOUND, JACOBI_EQ_0, .. } := BJacobiDef
  let { JACOBI_CONG, JACOBI_EULER, JACOBI_EULER_ALT, JACOBI_RMUL, .. } := BJacobiEuler
  -- @@SCOPE END

  let JACOBI_MINUS1 ← prove
   r"!n. ODD n ==> jacobi(n - 1,n) = --(&1) pow ((n - 1) DIV 2)"
   (← do
    let a0 ← ARITH_RULE (← q r"(2 * n) DIV 2 = n")
    let a1 ← INT_ARITH
     (← q r"abs(x:int) <= &1 /\ abs(y) <= &1 /\ &3 <= p ==> abs(x - y) < p")
    let a2 ← ARITH_RULE (← q r"1 <= n <=> ~(n = 0)")
    pure (MATCH_MP_TAC PRIME_FACTOR_INDUCT THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [JACOBI_0] THEN
    CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY X_GEN_TAC [← q "p:num", ← q "n:num"] THEN
    ASM_CASES_TAC (← q "ODD n") THEN ASM_REWRITE_TAC [ODD_MULT] THEN
    ASM_CASES_TAC (← q "p = 2") THEN ASM_REWRITE_TAC [ARITH] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [JACOBI_RMUL] THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
    SUBGOAL_THEN (← q r"jacobi(p * n - 1,n) = jacobi (n - 1,n)") SUBST1_TAC THENL
     [MATCH_MP_TAC JACOBI_CONG THEN MATCH_MP_TAC CONG_SUB THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [CONV_TAC NUMBER_RULE, ALL_TAC]) THEN
      ASM_REWRITE_TAC [a2, MULT_EQ_0],
      ASM_REWRITE_TAC []] THEN
    SUBGOAL_THEN (← q r"jacobi (p * n - 1,p) = --(&1) pow ((p - 1) DIV 2)")
    SUBST1_TAC THENL
     [MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC (← q r"&p:int") THEN CONJ_TAC THENL
       [MATCH_MP_TAC a1 THEN
        REWRITE_TAC [INT_OF_NUM_LE, JACOBI_BOUND] THEN
        CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [ODD_PRIME, PRIME_ODD]] THEN
        REWRITE_TAC [INT_ABS_POW, INT_ABS_NEG, INT_POW_ONE, INT_ABS_NUM] THEN
        REWRITE_TAC [INT_LE_REFL],
        MP_TAC (← SPECL [← q r"p * n - 1", ← q "p:num"] JACOBI_EULER_ALT) THEN
        ASM_REWRITE_TAC [] THEN
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] INT_CONG_TRANS) THEN
        MATCH_MP_TAC INT_CONG_POW THEN
        ASM_SIMP_TAC [← GSYM INT_OF_NUM_SUB, LE_1, MULT_EQ_0] THEN
        REWRITE_TAC [← GSYM INT_OF_NUM_MUL] THEN CONV_TAC INTEGER_RULE],
      REWRITE_TAC [← GSYM INT_POW_ADD] THEN
      REWRITE_TAC [INT_POW_NEG, INT_POW_ONE] THEN
      AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REPEAT (FIRST_X_ASSUM
       (CHOOSE_THEN SUBST_ALL_TAC o REWRITE_RULE [ODD_EXISTS])) THEN
      REWRITE_TAC [SUC_SUB1, ADD_CLAUSES, MULT_CLAUSES] THEN
      REWRITE_TAC [← GSYM LEFT_ADD_DISTRIB, ← GSYM MULT_ASSOC] THEN
      REWRITE_TAC [a0] THEN
      REWRITE_TAC [EVEN_ADD, EVEN_MULT, ARITH]]))

  let JACOBI_MINUS1_CASES ← prove
   r"!n. ODD n
       ==> jacobi(n - 1,n) =
           if (n == 1) (mod 4) then &1 else -- &1"
   (← do
    let n1 ← NUMBER_RULE
     (← q r"~(t = 0) ==> ((t * n + 1 == 1) (mod (t * t)) <=> t divides n)")
    let a1 ← ARITH_RULE (← q r"4 = 2 * 2")
    pure (SIMP_TAC [JACOBI_MINUS1] THEN
    SIMP_TAC [ODD_EXISTS, ADD1, LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [← ARITH_RULE (← q r"((2 * n + 1) - 1) DIV 2 = n")] THEN
    SIMP_TAC [ARITH_EQ, a1, n1] THEN
    REWRITE_TAC [INT_POW_NEG, INT_POW_ONE, DIVIDES_2]))

  let JACOBI_GAUSS_LEMMA ← prove
   r"!a p. prime p /\ ~(p = 2)
         ==> jacobi(a,p) =
             if coprime(a,p)
             then --(&1) pow CARD {x | x IN 1 .. (p - 1) DIV 2 /\
                                       (p - 1) DIV 2 < (a * x) MOD p}
             else &0"
   (← do
    let i7 ← INTEGER_RULE (← q r"(--x:int == p - a) (mod p) <=> (x == a) (mod p)")
    let a8 ← ARITH_RULE (← q r"1 <= i ==> ~(i + j = 0)")
    let a1 ← ARITH_RULE
     (← q r"(if a then x else p - x) = (if b then y else p - y) ==> x < p /\ y < p
        ==> x:num = y \/ x + y = p")
    let a3 ← ARITH_RULE (← q r"i <= r ==> i < 2 * r + 1")
    let a4 ← ARITH_RULE (← q r"~(2 * r + 1 <= i /\ i <= r)")
    let a5 ← ARITH_RULE (← q r"~(1 <= 0)")
    let a6 ← ARITH_RULE (← q r"1 <= x <=> ~(x = 0)")
    let i6 ← INTEGER_RULE
     (← q r"!c:int. x pow 2 = &1 /\ coprime(p,c) /\ (a * x * c == c) (mod p)
            ==> (a == x) (mod p)")
    let a2 ← INT_ARITH
     (← q r"abs(x:int) <= &1 /\ abs(y) <= &1 /\ &3 <= p ==> abs(x - y) < p")
    pure (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [JACOBI_EQ_0] THEN
    SUBGOAL_THEN (← q r"ODD(p)") MP_TAC THENL
     [ASM_MESON_TAC [PRIME_ODD, ODD_PRIME],
      REWRITE_TAC [ODD_EXISTS, LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC (← q "r:num") THEN REWRITE_TAC [ADD1] THEN
    DISCH_THEN (ASSUME_TAC o SYM) THEN
    MATCH_MP_TAC INT_CONG_IMP_EQ THEN EXISTS_TAC (← q r"&p:int") THEN CONJ_TAC THENL
     [MATCH_MP_TAC a2 THEN
      REWRITE_TAC [INT_OF_NUM_LE, JACOBI_BOUND] THEN
      CONJ_TAC THENL [ALL_TAC, ASM_MESON_TAC [ODD_PRIME, PRIME_ODD]] THEN
      SIMP_TAC [INT_ABS_POW, INT_ABS_NEG, INT_POW_ONE, INT_ABS_NUM, INT_LE_REFL],
      ALL_TAC] THEN
    MP_TAC (← SPECL [← q "a:num", ← q "p:num"] JACOBI_EULER) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] INT_CONG_TRANS) THEN
    SUBGOAL_THEN (← q r"(p - 1) DIV 2 = r") SUBST1_TAC THENL
     [EXPAND_TAC "p" THEN ARITH_TAC, ALL_TAC] THEN
    MATCH_MP_TAC i6 THEN
    EXISTS_TAC (← q r"iproduct (1..r) (\i. &i)") THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC [← ONCE_REWRITE_RULE [MULT_SYM] INT_POW_POW] THEN
      REWRITE_TAC [← GSYM INT_POW_POW] THEN CONV_TAC INT_REDUCE_CONV THEN
      REWRITE_TAC [INT_POW_ONE],
      MATCH_MP_TAC COPRIME_IPRODUCT THEN
      REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG, ← GSYM num_coprime] THEN
      X_GEN_TAC (← q "i:num") THEN STRIP_TAC THEN ONCE_REWRITE_TAC [COPRIME_SYM] THEN
      MATCH_MP_TAC PRIME_COPRIME_LT THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC,
      GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o LAND_CONV o RAND_CONV)
        [← GSYM CARD_NUMSEG_1] THEN
      SIMP_TAC [← GSYM IPRODUCT_CONST, FINITE_RESTRICT, FINITE_NUMSEG] THEN
      REWRITE_TAC [IPRODUCT_RESTRICT_SET]] THEN
    MP_TAC (← ISPECL
     [← q r"(\i. &i):num->int",
      ← q r"(\x. if x <= r then x else p - x) o (\x. (a * x) MOD p)",
      ← q r"1..r"] IPRODUCT_INJECTION) THEN
    REWRITE_TAC [o_THM, FINITE_NUMSEG] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC [IN_NUMSEG] THEN REPEAT STRIP_TAC THENL
         [ALL_TAC, EXPAND_TAC "p" THEN ARITH_TAC] THEN
        REWRITE_TAC [a6] THEN COND_CASES_TAC THENL
         [ALL_TAC, ASM_MESON_TAC [DIVISION, NOT_LE, SUB_EQ_0, PRIME_0]] THEN
        ASM_SIMP_TAC [← GSYM DIVIDES_MOD, PRIME_IMP_NZ] THEN
        ASM_SIMP_TAC [PRIME_DIVPROD_EQ] THEN STRIP_TAC THENL
         [ASM_MESON_TAC [coprime, DIVIDES_REFL, PRIME_1],
          ASM_MESON_TAC [DIVIDES_LE, a5, a4]],
        MAP_EVERY X_GEN_TAC [← q "i:num", ← q "j:num"] THEN REWRITE_TAC [IN_NUMSEG] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN
        EXISTS_TAC (← q "p:num") THEN REPEAT (CONJ_TAC THENL
         [ASM_MESON_TAC [a3], ALL_TAC]) THEN
        MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC (← q "a:num") THEN
        FIRST_X_ASSUM (MP_TAC o MATCH_MP a1) THEN
        ASM_SIMP_TAC [MOD_LT_EQ, PRIME_IMP_NZ] THEN
        DISCH_THEN (DISJ_CASES_THEN MP_TAC) THENL
         [ASM_MESON_TAC [CONG], ALL_TAC] THEN
        DISCH_THEN (MP_TAC o flip AP_THM (← q "p:num") o AP_TERM (← q r"(MOD)")) THEN
        ASM_SIMP_TAC [MOD_ADD_MOD] THEN ASM_SIMP_TAC [← GSYM CONG] THEN
        DISCH_THEN (MP_TAC o MATCH_MP CONG_DIVIDES) THEN
        ASM_SIMP_TAC [← GSYM LEFT_ADD_DISTRIB, PRIME_DIVPROD_EQ, DIVIDES_REFL] THEN
        STRIP_TAC THENL
         [ASM_MESON_TAC [coprime, DIVIDES_REFL, PRIME_1], ALL_TAC] THEN
        FIRST_ASSUM (MP_TAC o MATCH_MP DIVIDES_LE) THEN
        ASM_SIMP_TAC [a8] THEN
        MAP_EVERY UNDISCH_TAC [← q r"i:num <= r", ← q r"j:num <= r", ← q r"2 * r + 1 = p"] THEN
        ARITH_TAC],
      DISCH_THEN (fun th => tactic_of do pure (GEN_REWRITE_TAC (LAND_CONV) [← GSYM th]))] THEN
    SIMP_TAC [← GSYM IPRODUCT_MUL, FINITE_NUMSEG, o_DEF] THEN
    MATCH_MP_TAC CONG_IPRODUCT THEN REWRITE_TAC [FINITE_NUMSEG, IN_NUMSEG] THEN
    X_GEN_TAC (← q "i:num") THEN STRIP_TAC THEN
    REWRITE_TAC [COND_SWAP, ← GSYM NOT_LE] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_SIMP_TAC [← GSYM INT_OF_NUM_SUB, MOD_LT_EQ, PRIME_IMP_NZ, INT_OF_NUM_EQ,
                 LT_IMP_LE, INT_MUL_LID, INT_MUL_LNEG, INT_MUL_RNEG] THEN
    REWRITE_TAC [i7, ← GSYM INT_OF_NUM_REM, ← GSYM INT_OF_NUM_MUL] THEN
    REWRITE_TAC [INT_CONG_RREM, INT_CONG_REFL]))

  -- @@RETURN BEGIN
  return { JACOBI_MINUS1, JACOBI_MINUS1_CASES, JACOBI_GAUSS_LEMMA }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- The Jacobi symbol of 2.                                                   -/
/- ------------------------------------------------------------------------- -/

structure JacobiOf2 where
  -- @@FIELDS
  JACOBI_OF_2 : thm
  deriving Inhabited

@[nospecialize]
def setupJacobiOf2 [HolBase] (D : JacobiDeps) (BJacobiDef : JacobiDef) (BJacobiEuler : JacobiEuler) (BGauss : Gauss) :
    ExceptT String IO JacobiOf2 := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, INT_ARITH_TAC, INT_REDUCE_CONV, MESON, NUMBER_RULE,
        NUM_REDUCE_CONV, TAUT, .. } := D
  let { ADD1, ADD_SUB, ARITH, ARITH_EQ, CARD_NUMSEG, COPRIME_2, DIVIDES_2, DIVIDES_ADD,
        DIVIDES_DIVIDES_DIV, DIVIDES_MUL_L, DIV_ADD, DIV_MULT, DIV_MULT_ADD, EVEN_ADD,
        EVEN_EXISTS, EVEN_EXP, EVEN_MULT, EVEN_OR_ODD, .. } := D.core1
  let { EXP_2, INT_OF_NUM_ADD, INT_OF_NUM_EQ, INT_OF_NUM_MUL, INT_OF_NUM_SUB, .. } := D.core2
  let { INT_POW_ADD, INT_POW_NEG, INT_POW_ONE, IN_NUMSEG, LEFT_IMP_EXISTS_THM, LE_1,
        MOD_LT, MOD_MULT, MOD_MULT_ADD, MULT_EQ_0, NOT_EVEN, NOT_IMP, .. } := D.core3
  let { ODD, ODD_EXISTS, ODD_MULT, OR_EXISTS_THM, PRIME_FACTOR_INDUCT, PRIME_IMP_NZ,
        numseg, .. } := D.core4
  let { JACOBI_1, JACOBI_EQ_0, .. } := BJacobiDef
  let { JACOBI_RMUL, .. } := BJacobiEuler
  let { JACOBI_GAUSS_LEMMA, .. } := BGauss
  -- @@SCOPE END

  let JACOBI_OF_2 ← prove
   r"!n. jacobi(2,n) = if EVEN n then &0 else --(&1) pow ((n EXP 2 - 1) DIV 8)"
   (← do
    let lemma0 ← prove
     r"!n. ODD n ==> 8 divides (n EXP 2 - 1)"
     (← do
      let a2 ← ARITH_RULE (← q r"8 = 4 * 2")
      let a1 ← ARITH_RULE (← q r"(2 * n + 1) EXP 2 - 1 = 4 * (n EXP 2 + n)")
      pure (GEN_TAC THEN REWRITE_TAC [ODD_EXISTS, ADD1, LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC (← q "m:num") THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [a1] THEN
      REWRITE_TAC [a2] THEN MATCH_MP_TAC DIVIDES_MUL_L THEN
      REWRITE_TAC [DIVIDES_2, EVEN_ADD, EVEN_EXP, ARITH_EQ]))
    let lemma1 ← prove
     r"!m n. ODD m /\ ODD n
           ==> (EVEN(((m * n) EXP 2 - 1) DIV 8) <=>
                EVEN((m EXP 2 - 1) DIV 8 + (n EXP 2 - 1) DIV 8))"
     (← do
      let n1 ← NUMBER_RULE
       (← q r"e divides d /\ d divides a /\ d divides b
        ==> d * e divides a * b")
      let n0 ← NUMBER_RULE
       (← q r"(d:num) divides a ==> (d divides (a + b) <=> d divides b)")
      let m2 ← MESON [ODD] (← q r"ODD n ==> ~(n = 0)")
      pure (REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC [← GSYM DIV_ADD, lemma0, ← GSYM DIVIDES_2] THEN
      ASM_SIMP_TAC [DIVIDES_DIVIDES_DIV, lemma0, ODD_MULT, DIVIDES_ADD] THEN
      SUBGOAL_THEN
       (← q r"(m * n) EXP 2 - 1 =
      (m EXP 2 - 1) * (n EXP 2 - 1) + (m EXP 2 - 1) + (n EXP 2 - 1)")
      SUBST1_TAC THENL
       [ASM_SIMP_TAC [← GSYM INT_OF_NUM_EQ, ← GSYM INT_OF_NUM_ADD,
                     ← GSYM INT_OF_NUM_MUL, ← GSYM INT_OF_NUM_SUB, LE_1,
                     MULT_EQ_0, EXP_2, m2] THEN
        INT_ARITH_TAC,
        MATCH_MP_TAC n0 THEN
        MATCH_MP_TAC n1 THEN
        ASM_SIMP_TAC [lemma0] THEN REWRITE_TAC [DIVIDES_2, ARITH]]))
    let a9 ← ARITH_RULE (← q r"((2 * q + 1) EXP 2 + 2 * q + 1) DIV 2 =
    2 * q EXP 2 + 3 * q + 1")
    let a8 ← ARITH_RULE (← q r"((2 * q) EXP 2) DIV 2 = 2 * q * q")
    let a7 ← ARITH_RULE
     (← q r"((2 * n + 1) EXP 2 - 1) DIV 8 = (n EXP 2 + n) DIV 2")
    let a6 ← ARITH_RULE (← q r"(n + 1) - (n DIV 2 + 1) = n DIV 2 + n MOD 2")
    let a5 ← ARITH_RULE
     (← q r"(1 <= x /\ x <= b) /\ c < 2 * x <=> c DIV 2 + 1 <= x /\ x <= b")
    let a4 ← ARITH_RULE
     (← q r"1 <= x /\ x <= (p - 1) DIV 2 ==> 2 * x < p")
    let t3 ← TAUT (← q r"(p /\ q) /\ r <=> ~(p /\ q ==> ~r)")
    pure (GEN_TAC THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC [JACOBI_EQ_0, COPRIME_2, ← GSYM NOT_EVEN],
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [NOT_EVEN])] THEN
    SPEC_TAC (← q "n:num", ← q "n:num") THEN  MATCH_MP_TAC PRIME_FACTOR_INDUCT THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [JACOBI_1] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    MAP_EVERY X_GEN_TAC [← q "p:num", ← q "n:num"] THEN
    ASM_CASES_TAC (← q "ODD n") THEN ASM_REWRITE_TAC [ODD_MULT] THEN
    ASM_CASES_TAC (← q "p = 2") THEN ASM_REWRITE_TAC [ARITH] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [JACOBI_RMUL] THEN
    ASM_SIMP_TAC [JACOBI_GAUSS_LEMMA, COPRIME_2, IN_NUMSEG] THEN
    ONCE_REWRITE_TAC [t3] THEN
    ASM_SIMP_TAC [PRIME_IMP_NZ, MOD_LT, a4] THEN
    REWRITE_TAC [NOT_IMP, a5] THEN
    REWRITE_TAC [← GSYM numseg, CARD_NUMSEG] THEN
    REWRITE_TAC [← GSYM INT_POW_ADD] THEN REWRITE_TAC [INT_POW_NEG, INT_POW_ONE] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC [EVEN_ADD, lemma1] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [a6] THEN
    UNDISCH_TAC (← q "ODD p") THEN
    REWRITE_TAC [ODD_EXISTS, ADD1, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q "t:num") THEN DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC [ADD_SUB, DIV_MULT, ARITH_EQ] THEN
    REWRITE_TAC [a7] THEN
    MP_TAC (← SPEC (← q "t:num") (← REWRITE_RULE [EVEN_EXISTS, ODD_EXISTS] EVEN_OR_ODD)) THEN
    REWRITE_TAC [ADD1, OR_EXISTS_THM, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q "q:num") THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    SIMP_TAC [MOD_MULT_ADD, DIV_MULT_ADD, ARITH_EQ, DIV_MULT, MOD_MULT] THEN
    REWRITE_TAC [a8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [EVEN_ADD, EVEN_MULT, ARITH] THEN
    REWRITE_TAC [a9] THEN
    REWRITE_TAC [EVEN_ADD, EVEN_MULT, EVEN_EXP, ARITH]))

  -- @@RETURN BEGIN
  return { JACOBI_OF_2 }
  -- @@RETURN END

structure Of2Cases where
  -- @@FIELDS
  JACOBI_OF_2_CASES : thm
  deriving Inhabited

@[nospecialize]
def setupOf2Cases [HolBase] (D : JacobiDeps) (BJacobiOf2 : JacobiOf2) :
    ExceptT String IO Of2Cases := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, EXPAND_CASES_CONV, NUMBER_RULE, NUM_REDUCE_CONV, .. } := D
  let { ADD1, CONG, CONG_ADD, CONG_LMOD, CONG_MULT, CONG_REFL, DIVIDES_2,
        DIVIDES_LMUL2_EQ, DIVIDES_MOD, EQ_IMP, EVEN_EXISTS, EVEN_OR_ODD, .. } := D.core1
  let { INT_POW_NEG, INT_POW_ONE, LEFT_IMP_EXISTS_THM, NOT_EVEN, .. } := D.core3
  let { ODD_EXISTS, .. } := D.core4
  let { JACOBI_OF_2, .. } := BJacobiOf2
  -- @@SCOPE END

  let JACOBI_OF_2_CASES ← prove
   r"!n. jacobi(2,n) =
       if EVEN n then &0
       else if (n == 1) (mod 8) \/ (n == 7) (mod 8) then &1 else --(&1)"
   (← do
    let a6 ← ARITH_RULE (← q r"p MOD 8 < 8")
    let a5 ← ARITH_RULE (← q r"((2 * p + 1) * ((2 * p + 1) + 1)) DIV 2 =
                            (p + 1) * (2 * p + 1)")
    let a4 ← ARITH_RULE (← q r"((2 * p) * (2 * p + 1)) DIV 2 = p * (2 * p + 1)")
    let n3 ← NUMBER_RULE (← q r"(n + 1 == 7) (mod p) <=> (n == 6) (mod p)")
    let n2 ← NUMBER_RULE (← q r"(n + 1 == 1) (mod p) <=> (n == 0) (mod p)")
    let a1 ← ARITH_RULE (← q r"((2 * m + 1) EXP 2 - 1) DIV 8 = (m * (m + 1)) DIV 2")
    pure (GEN_TAC THEN REWRITE_TAC [JACOBI_OF_2] THEN
    COND_CASES_TAC THEN REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [NOT_EVEN]) THEN
    SIMP_TAC [ODD_EXISTS, ADD1, LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC [a1] THEN
    X_GEN_TAC (← q "m:num") THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [n2] THEN
    REWRITE_TAC [n3] THEN
    REWRITE_TAC [INT_POW_NEG, INT_POW_ONE] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC (← SPEC (← q "m:num")
     (← REWRITE_RULE [EVEN_EXISTS, ODD_EXISTS, ADD1] EVEN_OR_ODD)) THEN
    DISCH_THEN (DISJ_CASES_THEN (X_CHOOSE_THEN (← q "p:num") SUBST1_TAC)) THENL
     [REWRITE_TAC [a4],
      REWRITE_TAC [a5]] THEN
    MP_TAC (← GEN (← q "n:num") (← SPECL [← q "2", ← q "n:num", ← q "4"] DIVIDES_LMUL2_EQ)) THEN
    REWRITE_TAC [← GSYM DIVIDES_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← GSYM th])) THEN
    REWRITE_TAC [DIVIDES_MOD, CONG] THEN CONV_TAC NUM_REDUCE_CONV THEN
    (W (fun (_asl, w) => tactic_of do
        let w8 ← ExceptT.mk ((← ExceptT.mk (subst [(← q "p MOD 8", ← q "p:num")])) w)
        pure (SUBGOAL_THEN w8 MP_TAC)) THENL
     [ALL_TAC,
      MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL [ALL_TAC, BINOP_TAC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [← GSYM CONG] THEN
      REPEAT (MATCH_MP_TAC CONG_ADD ORELSE MATCH_MP_TAC CONG_MULT THEN
             REPEAT CONJ_TAC THEN REWRITE_TAC [CONG_REFL, CONG_LMOD])]) THEN
    MP_TAC a6 THEN SPEC_TAC (← q "p MOD 8", ← q "k:num") THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV))

  -- @@RETURN BEGIN
  return { JACOBI_OF_2_CASES }
  -- @@RETURN END

structure Reciprocity where
  -- @@FIELDS
  JACOBI_RECIPROCITY_ALT : thm
  JACOBI_RECIPROCITY : thm
  deriving Inhabited

@[nospecialize]
def setupReciprocity [HolBase] (D : JacobiDeps) (BJacobiDef : JacobiDef) (BJacobiEuler : JacobiEuler) (BGauss : Gauss) :
    ExceptT String IO Reciprocity := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, ASM_MESON_TAC, INT_ARITH,
        INT_REDUCE_CONV, INT_RING, MESON_TAC, NUMBER_RULE, NUM_REDUCE_CONV, SET_RULE,
        SET_TAC, TAUT, .. } := D
  let { ADD1, ADD_CLAUSES, ALL, ARITH, BIJECTIONS_CARD_EQ, CARD_CROSS,
        CARD_IMAGE_INJ_EQ, CARD_NUMSEG_1, CARD_UNION, COMPLETE_FACTOR_INDUCT,
        CONJ_ASSOC, COPRIME_1, COPRIME_LMUL, COPRIME_RMUL, COPRIME_SYM, DISJOINT,
        DIVIDES_2, DIVIDES_ADD, DIVIDES_DIVIDES_DIV, DIVIDES_LE, DIVIDES_MUL2,
        DIVIDES_REFL, DIVISION, DIV_ADD, EQ_TRANS, EVEN_ADD, EVEN_MULT, EVEN_SUB,
        EXISTS_IN_GSPEC, EXISTS_PAIR_THM, EXISTS_UNIQUE_THM, .. } := D.core1
  let { EXTENSION, FINITE_CROSS_EQ, FINITE_NUMSEG, FINITE_SUBSET, FINITE_UNION,
        FORALL_IN_GSPEC, FORALL_PAIR_THM, IMP_CONJ, IMP_CONJ_ALT, INT_ENTIRE, .. } := D.core2
  let { INT_POW_ADD, INT_POW_MUL, INT_POW_NEG, INT_POW_ONE, INT_POW_POW, IN_CROSS,
        IN_ELIM_PAIR_THM, IN_INTER, IN_NUMSEG, IN_UNION, LEFT_IMP_EXISTS_THM,
        LEFT_SUB_DISTRIB, LE_MULT_LCANCEL, LE_MULT_RCANCEL, LTE_TRANS, LT_ADD_LCANCEL,
        LT_MULT_LCANCEL, MULT_CLAUSES, MULT_SYM, NOT_EVEN, NOT_IN_EMPTY, NOT_ODD, .. } := D.core3
  let { ODD, ODD_EXISTS, ODD_MULT, PAIRWISE, PAIR_EQ, PRIME_1, PRIME_DIVPROD_EQ,
        PRIME_IMP_NZ, RIGHT_FORALL_IMP_THM, SUBSET, SUC_SUB1, coprime, .. } := D.core4
  let { JACOBI_1, JACOBI_CASES, JACOBI_EQ_0, .. } := BJacobiDef
  let { JACOBI_LMUL, JACOBI_RMUL, .. } := BJacobiEuler
  let { JACOBI_GAUSS_LEMMA, .. } := BGauss
  -- @@SCOPE END

  let JACOBI_RECIPROCITY_ALT ← prove
   r"!m n. ODD m /\ ODD n
         ==> jacobi(m,n) * jacobi(n,m) =
             if coprime(m,n) then --(&1) pow ((m - 1) DIV 2 * (n - 1) DIV 2)
             else &0"
   (← do
    let lemma0 ← prove
     r"!n. ODD n ==> 2 divides (n - 1)"
     (SIMP_TAC [DIVIDES_2, EVEN_SUB, ← GSYM NOT_EVEN, ARITH])
    let lemma1 ← prove
     r"!m n. ODD m /\ ODD n
           ==> (EVEN((m * n - 1) DIV 2) <=>
                EVEN((m - 1) DIV 2 + (n - 1) DIV 2))"
     (← do
      let n1 ← NUMBER_RULE
       (← q r"d divides a * b /\ a * b + a + b = c
        ==> (d divides c <=> d divides (a + b))")
      pure (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [← GSYM DIV_ADD, DIVIDES_2, lemma0] THEN
      ASM_SIMP_TAC [DIVIDES_DIVIDES_DIV, ← GSYM DIVIDES_2,
                   ODD_MULT, DIVIDES_ADD, lemma0] THEN
      MATCH_MP_TAC n1 THEN
      ASM_SIMP_TAC [DIVIDES_MUL2, lemma0] THEN
      REPEAT (FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS])) THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [SUC_SUB1, MULT_CLAUSES, ADD_CLAUSES] THEN ARITH_TAC))
    let flemma ← prove
     r"!r s p. FINITE {x,y | x IN 1..r /\ y IN 1..s /\ p x y}"
     (REPEAT GEN_TAC THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC (← q r"(1..r) CROSS (1..s)") THEN
      REWRITE_TAC [FINITE_CROSS_EQ, FINITE_NUMSEG] THEN
      SIMP_TAC [SUBSET, FORALL_IN_GSPEC, IN_CROSS])
    let glemma ← prove
     r"!p q r s. prime p /\ prime q /\ coprime(p,q) /\
               2 * r + 1 = p /\ 2 * s + 1 = q
               ==> jacobi(q,p) =
                   -- &1 pow CARD {x,y | x IN 1..r /\ y IN 1..s /\
                                         q * x < p * y /\ p * y <= q * x + r}"
     (← do
      let a6 ← ARITH_RULE (← q r"~(x <= y) /\ ~(y + 2 <= x) ==> x = y + 1")
      let a5 ← ARITH_RULE
       (← q r"!p d. 2 * r + 1 = p /\ p * (d + 1) <= (d * p + m) + r
                  ==> r < m")
      let t4 ← TAUT (← q r"a /\ (a ==> b) ==> a /\ b")
      let a3 ← ARITH_RULE (← q r"x < y ==> x + 1 <= y")
      let a2 ← ARITH_RULE (← q r"(2 * r + 1) * d + r < (2 * s + 1) * r
                      ==> (2 * r) * d < (2 * r) * s")
      let a1 ← ARITH_RULE (← q r"1 <= n + 1")
      pure (ONCE_REWRITE_TAC [COPRIME_SYM] THEN REPEAT STRIP_TAC THEN
      MP_TAC (← SPECL [← q "q:num", ← q "p:num"] JACOBI_GAUSS_LEMMA) THEN
      ASM_REWRITE_TAC [] THEN ANTS_TAC THENL
       [EXPAND_TAC "p" THEN DISCH_THEN (MP_TAC o AP_TERM (← q "EVEN")) THEN
        REWRITE_TAC [EVEN_ADD, EVEN_MULT, ARITH],
        DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC] THEN
      SUBGOAL_THEN (← q r"(p - 1) DIV 2 = r") SUBST1_TAC THENL
       [EXPAND_TAC "p" THEN ARITH_TAC, ALL_TAC] THEN
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
       (← q r"CARD {x,y | x IN 1..r /\ y IN 1..s /\
                  y = (q * x) DIV p + 1 /\ r < (q * x) MOD p}") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN EXISTS_TAC (← q r"\(x:num,y:num). x") THEN
        REWRITE_TAC [FORALL_IN_GSPEC, EXISTS_UNIQUE_THM, IN_NUMSEG, flemma,
                    IMP_CONJ, RIGHT_FORALL_IMP_THM, EXISTS_IN_GSPEC] THEN
        CONJ_TAC THENL [SET_TAC [], ALL_TAC] THEN
        X_GEN_TAC (← q "x:num") THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
        SIMP_TAC [PAIR_EQ] THEN EXISTS_TAC (← q "x:num") THEN
        EXISTS_TAC (← q r"(q * x) DIV p + 1") THEN
        ASM_REWRITE_TAC [a1] THEN
        SUBGOAL_THEN (← q r"p * (q * x) DIV p + r < q * r") MP_TAC THENL
         [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC (← q r"q * x:num") THEN
          ASM_REWRITE_TAC [LE_MULT_LCANCEL] THEN
          GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
          ASM_MESON_TAC [PRIME_IMP_NZ, LT_ADD_LCANCEL, DIVISION],
          MAP_EVERY EXPAND_TAC ["p", "q"] THEN DISCH_THEN (MP_TAC o MATCH_MP a2) THEN
          SIMP_TAC [LT_MULT_LCANCEL, a3]],
        AP_TERM_TAC THEN
        REWRITE_TAC [EXTENSION, IN_ELIM_PAIR_THM, FORALL_PAIR_THM] THEN
        MAP_EVERY X_GEN_TAC [← q "x:num", ← q "y:num"] THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN EQ_TAC THEN DISCH_TAC THENL
         [MP_TAC (← MATCH_MP PRIME_IMP_NZ (← ASSUME (← q r"prime p"))) THEN
          DISCH_THEN (MP_TAC o SPEC (← q r"q * x:num") o MATCH_MP DIVISION) THEN
          FIRST_ASSUM (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
          UNDISCH_TAC (← q r"2 * r + 1 = p") THEN ARITH_TAC,
          MATCH_MP_TAC t4 THEN CONJ_TAC THENL
           [ALL_TAC,
            DISCH_THEN SUBST_ALL_TAC THEN
            MATCH_MP_TAC a5 THEN
            MAP_EVERY EXISTS_TAC [← q "p:num", ← q r"(q * x) DIV p"] THEN
            ASM_MESON_TAC [DIVISION, PRIME_IMP_NZ]] THEN
          MATCH_MP_TAC a6 THEN
          REPEAT STRIP_TAC THENL
           [SUBGOAL_THEN (← q r"y * p <= ((q * x) DIV p) * p") MP_TAC THENL
             [ASM_SIMP_TAC [LE_MULT_RCANCEL, PRIME_IMP_NZ], ALL_TAC],
            SUBGOAL_THEN (← q r"((q * x) DIV p + 2) * p <= y * p") MP_TAC THENL
             [ASM_SIMP_TAC [LE_MULT_RCANCEL, PRIME_IMP_NZ], ALL_TAC]] THEN
          MP_TAC (← MATCH_MP PRIME_IMP_NZ (← ASSUME (← q r"prime p"))) THEN
          DISCH_THEN (MP_TAC o SPEC (← q r"q * x:num") o MATCH_MP DIVISION) THEN
          ASM_ARITH_TAC]]))
    let hlemma ← prove
     r"!p q r s. prime p /\ prime q /\ coprime(p,q) /\
               2 * r + 1 = p /\ 2 * s + 1 = q
               ==> jacobi(p,q) =
                   -- &1 pow CARD {x,y | x IN 1..r /\ y IN 1..s /\
                                         p * y < q * x /\ q * x <= p * y + s}"
     (REPEAT STRIP_TAC THEN
      MP_TAC (← SPECL [← q "q:num", ← q "p:num", ← q "s:num", ← q "r:num"] glemma) THEN
      ONCE_REWRITE_TAC [COPRIME_SYM] THEN ASM_REWRITE_TAC [] THEN
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN
      EXISTS_TAC (← q r"\(x:num,y:num). (y,x)") THEN REWRITE_TAC [flemma] THEN
      REWRITE_TAC [EXISTS_UNIQUE_THM, FORALL_PAIR_THM, EXISTS_PAIR_THM] THEN
      SIMP_TAC [IN_ELIM_PAIR_THM, PAIR_EQ] THEN MESON_TAC [])
    let rlemma ← prove
     r"!a b c d r s.
          a UNION b UNION c UNION d = (1..r) CROSS (1..s) /\
          PAIRWISE DISJOINT [a;b;c;d] /\ CARD b = CARD c
          ==> ((EVEN(CARD a) <=> EVEN(CARD d)) <=> ~(ODD r /\ ODD s))"
     (← do
      let s1 ← SET_RULE
       (← q r"a INTER (b UNION c) = {} <=> a INTER b = {} /\ a INTER c = {}")
      pure (REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (← q r"CARD(a:num#num->bool) + CARD(b:num#num->bool) +
                  CARD(c:num#num->bool) + CARD(d:num#num->bool) = r * s")
       (fun th => tactic_of do pure (MP_TAC (← AP_TERM (← q "EVEN") th) THEN
                  ASM_REWRITE_TAC [EVEN_ADD, ← GSYM NOT_EVEN, EVEN_MULT] THEN
                  CONV_TAC TAUT)) THEN
      SUBGOAL_THEN
       (← q r"FINITE(a:num#num->bool) /\ FINITE(b:num#num->bool) /\
      FINITE(c:num#num->bool) /\ FINITE(d:num#num->bool)")
      STRIP_ASSUME_TAC THENL
       [ASM_REWRITE_TAC [← GSYM FINITE_UNION] THEN
        REWRITE_TAC [FINITE_CROSS_EQ, FINITE_NUMSEG],
        ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o AP_TERM (← q r"CARD:(num#num->bool)->num")) THEN
      SIMP_TAC [CARD_CROSS, CARD_NUMSEG_1, FINITE_NUMSEG] THEN
      DISCH_THEN (SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [PAIRWISE]) THEN
      REWRITE_TAC [PAIRWISE, DISJOINT, ALL] THEN
      ASM_SIMP_TAC [CARD_UNION, FINITE_UNION, s1]))
    let a1 ← ARITH_RULE (← q r"a + x:num < y + a <=> x < y")
    let a2 ← ARITH_RULE (← q r"x <= r ==> x <= r + 1")
    let a3 ← ARITH_RULE
     (← q r"x:num <= y /\ v + y + z < x + u ==> (y - x) + z < u - v")
    let a4 ← ARITH_RULE
     (← q r"1 <= x /\ x <= y ==> 1 <= (y + 1) - x /\ (y + 1) - x <= y")
    let a5 ← ARITH_RULE (← q r"x <= y ==> (y + 1) - ((y + 1) - x) = x")
    let i6 ← INT_ARITH (← q r"(a * b) * (c * d):int = (a * c) * (b * d)")
    let i7 ← INT_ARITH (← q r"(a * b) * (c * d):int = (a * c) * (b * d)")
    pure (REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [INT_ENTIRE, JACOBI_EQ_0] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [← GSYM IMP_CONJ_ALT, ← GSYM CONJ_ASSOC] THEN
    MAP_EVERY (fun t => SPEC_TAC (t, t)) [← q "n:num", ← q "m:num"] THEN
    MATCH_MP_TAC COMPLETE_FACTOR_INDUCT THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC [COPRIME_1, JACOBI_1, MULT_CLAUSES, ODD] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV,
      X_GEN_TAC (← q "p:num") THEN DISCH_TAC,
      MAP_EVERY X_GEN_TAC [← q "m:num", ← q "n:num"] THEN
      REWRITE_TAC [COPRIME_LMUL, COPRIME_RMUL, ODD_MULT,
                  JACOBI_LMUL, JACOBI_RMUL] THEN
      ONCE_REWRITE_TAC [i7] THEN
      SIMP_TAC [] THEN DISCH_THEN (K ALL_TAC) THEN
      X_GEN_TAC (← q "q:num") THEN STRIP_TAC THEN REWRITE_TAC [← GSYM INT_POW_POW] THEN
      REWRITE_TAC [← GSYM INT_POW_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [← GSYM INT_POW_ADD] THEN
      REWRITE_TAC [INT_POW_NEG, INT_POW_ONE] THEN
      AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC [lemma1]] THEN
    MATCH_MP_TAC COMPLETE_FACTOR_INDUCT THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC [COPRIME_1, JACOBI_1, MULT_CLAUSES, ODD] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV,
      X_GEN_TAC (← q "q:num") THEN DISCH_TAC THEN STRIP_TAC,
      MAP_EVERY X_GEN_TAC [← q "m:num", ← q "n:num"] THEN
      REWRITE_TAC [COPRIME_LMUL, COPRIME_RMUL, ODD_MULT,
                  JACOBI_LMUL, JACOBI_RMUL] THEN
      ONCE_REWRITE_TAC [i6] THEN
      SIMP_TAC [] THEN DISCH_THEN (K ALL_TAC) THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC [MULT_SYM] THEN REWRITE_TAC [← GSYM INT_POW_POW] THEN
      REWRITE_TAC [← GSYM INT_POW_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC [← GSYM INT_POW_ADD] THEN
      REWRITE_TAC [INT_POW_NEG, INT_POW_ONE] THEN
      AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC [lemma1]] THEN
    MAP_EVERY UNDISCH_TAC [← q r"ODD q", ← q r"ODD p"] THEN
    REWRITE_TAC [ODD_EXISTS, ADD1, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q "r:num") THEN DISCH_THEN (ASSUME_TAC o SYM) THEN
    X_GEN_TAC (← q "s:num") THEN DISCH_THEN (ASSUME_TAC o SYM) THEN
    MP_TAC (← SPECL [← q "p:num", ← q "q:num", ← q "r:num", ← q "s:num"] glemma) THEN
    MP_TAC (← SPECL [← q "p:num", ← q "q:num", ← q "r:num", ← q "s:num"] hlemma) THEN
    ASM_REWRITE_TAC [] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN
    SUBGOAL_THEN (← q r"(p - 1) DIV 2 = r /\ (q - 1) DIV 2 = s")
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [MAP_EVERY EXPAND_TAC ["p", "q"] THEN ARITH_TAC, ALL_TAC] THEN
    REWRITE_TAC [← GSYM INT_POW_ADD] THEN
    REWRITE_TAC [INT_POW_NEG, INT_POW_ONE] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [← GSYM NOT_ODD] THEN
    REWRITE_TAC [EVEN_ADD, ODD_MULT] THEN
    MATCH_MP_TAC rlemma THEN
    EXISTS_TAC (← q r"{x,y | x IN 1..r /\ y IN 1..s /\ q * x + r < p * y}") THEN
    EXISTS_TAC (← q r"{x,y | x IN 1..r /\ y IN 1..s /\ p * y + s < q * x}") THEN
    REPEAT CONJ_TAC THEN
    REWRITE_TAC [PAIRWISE, DISJOINT, EXTENSION, NOT_IN_EMPTY, FORALL_PAIR_THM,
                ALL, IN_UNION, IN_CROSS, IN_ELIM_PAIR_THM, IN_INTER]
    THENL
     [MAP_EVERY X_GEN_TAC [← q "x:num", ← q "y:num"] THEN
      MAP_EVERY ASM_CASES_TAC [← q r"x IN 1..r", ← q r"y IN 1..s"] THEN ASM_SIMP_TAC [] THEN
      SUBGOAL_THEN (← q r"~(q * x:num = p * y)")
       (fun th => tactic_of do pure (MP_TAC th THEN ARITH_TAC)) THEN
      DISCH_THEN (MP_TAC o AP_TERM (← q r"(divides) (p:num)")) THEN
      ASM_SIMP_TAC [PRIME_DIVPROD_EQ, DIVIDES_REFL] THEN STRIP_TAC THENL
       [ASM_MESON_TAC [DIVIDES_REFL, PRIME_1, coprime], ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o MATCH_MP DIVIDES_LE) THEN
      UNDISCH_TAC (← q r"x IN 1..r") THEN REWRITE_TAC [IN_NUMSEG] THEN
      EXPAND_TAC "p" THEN ARITH_TAC,
      ARITH_TAC,
      MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
      REPEAT (EXISTS_TAC (← q r"\(x,y). (r + 1) - x,(s + 1) - y")) THEN
      REWRITE_TAC [flemma] THEN
      REWRITE_TAC [FORALL_PAIR_THM, IN_ELIM_PAIR_THM, IN_NUMSEG, PAIR_EQ] THEN
      CONJ_TAC THEN MAP_EVERY X_GEN_TAC [← q "x:num", ← q "y:num"] THEN
      SIMP_TAC [a5] THEN
      SIMP_TAC [a4] THEN
      REWRITE_TAC [LEFT_SUB_DISTRIB] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC a3 THEN
      ASM_SIMP_TAC [LE_MULT_LCANCEL, a2] THEN
      REWRITE_TAC [a1] THEN
      REPEAT (FIRST_X_ASSUM (SUBST_ALL_TAC o SYM)) THEN
      ASM_ARITH_TAC]))

  let JACOBI_RECIPROCITY ← prove
   r"!m n. ODD m /\ ODD n
         ==> jacobi(n,m) =
             if coprime(m,n)
             then --(&1) pow ((m - 1) DIV 2 * (n - 1) DIV 2) * jacobi(m,n)
             else &0"
   (← do
    let r2 ← INT_RING
     (← q r"(x:int = -- &1 \/ x = &0 \/ x = &1) /\ ~(x = &0) ==> x pow 2 = &1")
    let r1 ← INT_RING
     (← q r"!x y:int.
        x pow 2 = &1 /\ y pow 2 = &1 /\ x * y = z
        ==> y = z * x")
    pure (REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
     [ALL_TAC, ASM_MESON_TAC [JACOBI_EQ_0, COPRIME_SYM]] THEN
    MATCH_MP_TAC r1 THEN
    ASM_SIMP_TAC [JACOBI_RECIPROCITY_ALT] THEN CONJ_TAC THEN
    MATCH_MP_TAC r2 THEN
    REWRITE_TAC [JACOBI_CASES] THEN ASM_REWRITE_TAC [JACOBI_EQ_0] THEN
    ASM_MESON_TAC [ODD, COPRIME_SYM]))

  -- @@RETURN BEGIN
  return { JACOBI_RECIPROCITY_ALT, JACOBI_RECIPROCITY }
  -- @@RETURN END

structure Jacobi2 where
  -- @@FIELDS
  JACOBI_EQ_1 : thm
  JACOBI_NE_MINUS1 : thm
  deriving Inhabited

@[nospecialize]
def setupJacobi2 [HolBase] (D : JacobiDeps) (BJacobiDef : JacobiDef) :
    ExceptT String IO Jacobi2 := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, INT_REDUCE_CONV, MESON, NUMBER_RULE, .. } := D
  let { COPRIME_0, COPRIME_PRIME_EQ, .. } := D.core1
  let { FORALL_IN_GSPEC, .. } := D.core2
  let { INT_POW_ONE, IPRODUCT_EQ_1, .. } := D.core3
  let { JACOBI_1, JACOBI_ZERO, jacobi, .. } := BJacobiDef
  -- @@SCOPE END

  let JACOBI_EQ_1 ← prove
   r"!n a. coprime(a,n) /\ (?x. (x EXP 2 == a) (mod n))
         ==> jacobi(a,n) = &1"
   (← do
    let n1 ← NUMBER_RULE
     (← q r"(a == b) (mod m) /\ n divides m ==> (a == b) (mod n)")
    let m2 ← MESON [INT_POW_ONE] (← q r"x:int = &1 ==> x pow n = &1")
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n = 0") THEN
    ASM_SIMP_TAC [COPRIME_0, JACOBI_1] THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    ASM_REWRITE_TAC [jacobi] THEN MATCH_MP_TAC IPRODUCT_EQ_1 THEN
    REWRITE_TAC [FORALL_IN_GSPEC] THEN X_GEN_TAC (← q "p:num") THEN STRIP_TAC THEN
    MATCH_MP_TAC m2 THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC [COPRIME_PRIME_EQ], ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC [] THEN ASM_MESON_TAC [n1]))

  let JACOBI_NE_MINUS1 ← prove
   r"!n a. (?x. (x EXP 2 == a) (mod n)) ==> ~(jacobi(a,n) = -- &1)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"coprime(a:num,n)") THEN
    ASM_SIMP_TAC [JACOBI_ZERO, JACOBI_EQ_1] THEN CONV_TAC INT_REDUCE_CONV)

  -- @@RETURN BEGIN
  return { JACOBI_EQ_1, JACOBI_NE_MINUS1 }
  -- @@RETURN END

/- ------------------------------------------------------------------------- -/
/- Integer version. The totalization at zero is a bit blunter; it's hard to  -/
/- keep all the nice properties in the light of -1 * -1 = 1; we prioritize   -/
/- simple complete multiplicativity over the relation with coprimality.      -/
/- ------------------------------------------------------------------------- -/

structure IntJacobi1 where
  -- @@FIELDS
  int_jacobi : thm
  INT_JACOBI_RNEG : thm
  INT_JACOBI_RABS : thm
  INT_JACOBI_NUMS : thm
  INT_JACOBI_BOUND : thm
  INT_JACOBI_CASES : thm
  INT_JACOBI_CONG : thm
  INT_JACOBI_REM_GEN : thm
  INT_JACOBI_REM : thm
  INT_JACOBI_1 : thm
  INT_JACOBI_0 : thm
  deriving Inhabited

@[nospecialize]
def setupIntJacobi1 [HolBase] (D : JacobiDeps) (BJacobiDef : JacobiDef) (BJacobiEuler : JacobiEuler) :
    ExceptT String IO IntJacobi1 := do
  -- @@SCOPE BEGIN
  let { ASM_INT_ARITH_TAC, INT_REDUCE_CONV, NUMBER_RULE, new_definition, .. } := D
  let { INT_ABS_ABS, INT_ABS_NEG, INT_ABS_NUM, INT_ABS_POS, INT_ABS_ZERO,
        INT_CONG_LREM, INT_CONG_MOD_0, INT_CONG_REFL, INT_DIVIDES_REFL, INT_NEG_EQ_0,
        INT_OF_NUM_EQ, INT_OF_NUM_OF_INT, INT_OF_NUM_REM, .. } := D.core2
  let { INT_REM_EQ, INT_REM_EQ_SELF, INT_REM_RABS, INT_REM_RNEG, INT_REM_ZERO,
        MOD_ZERO, NUM_OF_INT_OF_NUM, .. } := D.core3
  let { JACOBI_0, JACOBI_1, JACOBI_BOUND, JACOBI_CASES, .. } := BJacobiDef
  let { JACOBI_MOD, .. } := BJacobiEuler
  -- @@SCOPE END

  let int_jacobi ← new_definition
   r"int_jacobi(a,n) =
        if n = &0 then &0
        else jacobi(num_of_int(a rem n),num_of_int(abs n))"

  let INT_JACOBI_RNEG ← prove
   r"!a n. int_jacobi(a,--n) = int_jacobi(a,n)"
   (REWRITE_TAC [int_jacobi, INT_ABS_NEG, INT_NEG_EQ_0, INT_REM_RNEG])

  let INT_JACOBI_RABS ← prove
   r"!a n. int_jacobi(a,abs n) = int_jacobi(a,n)"
   (REWRITE_TAC [int_jacobi, INT_ABS_ABS, INT_REM_RABS, INT_ABS_ZERO])

  let INT_JACOBI_NUMS ← prove
   r"!a n. int_jacobi(&a,&n) = if n = 0 /\ a = 1 then &0 else jacobi(a,n)"
   (REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC [← q r"n = 0", ← q r"a = 1"] THEN
    ASM_REWRITE_TAC [int_jacobi, JACOBI_0, JACOBI_1, INT_OF_NUM_EQ] THEN
    REWRITE_TAC [int_jacobi, INT_ABS_NUM, INT_OF_NUM_REM, NUM_OF_INT_OF_NUM] THEN
    ASM_REWRITE_TAC [INT_OF_NUM_EQ, JACOBI_0, MOD_ZERO, JACOBI_MOD, JACOBI_1])

  let INT_JACOBI_BOUND ← prove
   r"!a n. abs(int_jacobi(a,n)) <= &1"
   (REPEAT GEN_TAC THEN REWRITE_TAC [int_jacobi] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [JACOBI_BOUND]) THEN
    CONV_TAC INT_REDUCE_CONV)

  let INT_JACOBI_CASES ← prove
   r"!a n. int_jacobi(a,n) = -- &1 \/
         int_jacobi(a,n) = &0 \/
         int_jacobi(a,n) = &1"
   (REPEAT GEN_TAC THEN REWRITE_TAC [int_jacobi] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [JACOBI_CASES]) THEN
    CONV_TAC INT_REDUCE_CONV)

  let INT_JACOBI_CONG ← prove
   r"!a b n. (a == b) (mod n) ==> int_jacobi(a,n) = int_jacobi(b,n)"
   (REPEAT GEN_TAC THEN REWRITE_TAC [int_jacobi] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC [INT_CONG_MOD_0] THEN
    SIMP_TAC [← GSYM INT_REM_EQ])

  let INT_JACOBI_REM_GEN ← prove
   r"!a m n. n divides m ==> int_jacobi(a rem m,n) = int_jacobi(a,n)"
   (← do
    let n1 ← NUMBER_RULE
     (← q r"(n:int) divides m ==> (x == y) (mod m) ==> (x == y) (mod n)")
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_JACOBI_CONG THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o MATCH_MP n1) THEN
    REWRITE_TAC [INT_CONG_LREM, INT_CONG_REFL]))

  let INT_JACOBI_REM ← prove
   r"!a n. int_jacobi(a rem n,n) = int_jacobi(a,n)"
   (SIMP_TAC [INT_JACOBI_REM_GEN, INT_DIVIDES_REFL])

  let INT_JACOBI_1 ← prove
   r"(!n. int_jacobi(&1,n) = if n = &0 then &0 else &1) /\
   (!a. int_jacobi(a,&1) = &1)"
   (REWRITE_TAC [int_jacobi] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC [NUM_OF_INT_OF_NUM, JACOBI_1] THEN
    X_GEN_TAC (← q "n:int") THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC (← q r"abs(n:int) = &1") THEN
    ASM_REWRITE_TAC [NUM_OF_INT_OF_NUM, JACOBI_1] THEN
    SUBGOAL_THEN (← q r"&1 rem n = &1") SUBST1_TAC THENL
     [REWRITE_TAC [INT_REM_EQ_SELF] THEN ASM_INT_ARITH_TAC,
      REWRITE_TAC [NUM_OF_INT_OF_NUM, JACOBI_1] THEN
      SIMP_TAC [← GSYM INT_OF_NUM_EQ, INT_OF_NUM_OF_INT, INT_ABS_POS] THEN
      ASM_REWRITE_TAC [INT_ABS_ZERO]])

  let INT_JACOBI_0 ← prove
   r"(!n. int_jacobi(&0,n) = if abs n = &1 then &1 else &0) /\
   (!a. int_jacobi(a,&0) = &0)"
   (REPEAT STRIP_TAC THEN REWRITE_TAC [int_jacobi] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [INT_REM_ZERO] THEN
    REWRITE_TAC [NUM_OF_INT_OF_NUM, JACOBI_0] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    SIMP_TAC [← GSYM INT_OF_NUM_EQ, INT_OF_NUM_OF_INT, INT_ABS_POS])

  -- @@RETURN BEGIN
  return { int_jacobi, INT_JACOBI_RNEG, INT_JACOBI_RABS, INT_JACOBI_NUMS,
           INT_JACOBI_BOUND, INT_JACOBI_CASES, INT_JACOBI_CONG, INT_JACOBI_REM_GEN,
           INT_JACOBI_REM, INT_JACOBI_1, INT_JACOBI_0 }
  -- @@RETURN END

structure IntJacobi2 where
  -- @@FIELDS
  INT_JACOBI_RMUL : thm
  INT_JACOBI_LMUL : thm
  INT_JACOBI_RPOW : thm
  INT_JACOBI_LPOW : thm
  INT_JACOBI_2 : thm
  INT_JACOBI_POW_2 : thm
  INT_JACOBI_EQ_0 : thm
  INT_JACOBI_MINUS1 : thm
  INT_JACOBI_OF_2 : thm
  INT_JACOBI_LNEG : thm
  INT_JACOBI_SQUARED : thm
  deriving Inhabited

@[nospecialize]
def setupIntJacobi2 [HolBase] (D : JacobiDeps) (BJacobiDef : JacobiDef) (BJacobiEuler : JacobiEuler) (BGauss : Gauss) (BOf2Cases : Of2Cases) (BIntJacobi1 : IntJacobi1) :
    ExceptT String IO IntJacobi2 := do
  -- @@SCOPE BEGIN
  let { ASM_INT_ARITH_TAC, INDUCT_TAC, INTEGER_RULE, INT_ARITH_TAC, INT_RING,
        NUM_REDUCE_CONV, .. } := D
  let { DIVIDES_2, EQ_TRANS, .. } := D.core1
  let { IMP_CONJ, INT_ABS_MUL, INT_ABS_POS, INT_ABS_ZERO, INT_CONG_MOD_ABS,
        INT_COPRIME_LREM, INT_COPRIME_RABS, INT_DIVIDES_RABS, INT_DIVISION, INT_ENTIRE,
        INT_FORALL_ABS, INT_FORALL_POS, INT_LE_MUL, INT_MUL_LZERO, INT_MUL_REM,
        INT_MUL_RZERO, INT_NEG_MINUS1, INT_OF_NUM_EQ, INT_OF_NUM_MUL,
        INT_OF_NUM_OF_INT, INT_OF_NUM_SUB, INT_POW, .. } := D.core2
  let { INT_POW_EQ_0, INT_POW_ONE, INT_POW_ZERO, INT_REM_2_CASES, INT_REM_EQ,
        INT_REM_REM, INT_REM_REM_MUL, LE_1, NOT_EVEN, NUM_OF_INT_MUL, .. } := D.core3
  let { ODD, num_congruent, num_coprime, num_divides, .. } := D.core4
  let { JACOBI_2_CASES, JACOBI_EQ_0, .. } := BJacobiDef
  let { JACOBI_CONG, JACOBI_LMUL, JACOBI_RMUL, .. } := BJacobiEuler
  let { JACOBI_MINUS1_CASES, .. } := BGauss
  let { JACOBI_OF_2_CASES, .. } := BOf2Cases
  let { INT_JACOBI_0, INT_JACOBI_1, INT_JACOBI_CASES, INT_JACOBI_CONG, INT_JACOBI_NUMS,
        INT_JACOBI_RABS, INT_JACOBI_REM, int_jacobi, .. } := BIntJacobi1
  -- @@SCOPE END

  let INT_JACOBI_RMUL ← prove
   r"!a m n. int_jacobi(a,m * n) = int_jacobi(a,m) * int_jacobi(a,n)"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"m:int = &0") THEN
    ASM_REWRITE_TAC [INT_JACOBI_0, INT_MUL_LZERO] THEN
    ASM_CASES_TAC (← q r"n:int = &0") THEN
    ASM_REWRITE_TAC [INT_JACOBI_0, INT_MUL_RZERO] THEN
    ASM_REWRITE_TAC [int_jacobi, INT_ENTIRE, INT_ABS_MUL] THEN
    SIMP_TAC [NUM_OF_INT_MUL, INT_ABS_POS, JACOBI_RMUL] THEN
    BINOP_TAC THEN MATCH_MP_TAC JACOBI_CONG THEN REWRITE_TAC [num_congruent] THEN
    ASM_SIMP_TAC [INT_OF_NUM_OF_INT, INT_ABS_POS, INT_DIVISION, INT_ENTIRE] THEN
    REWRITE_TAC [INT_CONG_MOD_ABS] THEN REWRITE_TAC [← GSYM INT_REM_EQ] THEN
    REWRITE_TAC [INT_REM_REM_MUL, INT_REM_REM])

  let INT_JACOBI_LMUL ← prove
   r"!a b n. int_jacobi(a * b,n) = int_jacobi(a,n) * int_jacobi(b,n)"
   (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"n:int = &0") THEN
    ASM_REWRITE_TAC [INT_JACOBI_0, INT_MUL_LZERO] THEN
    ASM_REWRITE_TAC [int_jacobi, ← GSYM JACOBI_LMUL] THEN
    MATCH_MP_TAC JACOBI_CONG THEN REWRITE_TAC [num_congruent] THEN
    ASM_SIMP_TAC [INT_OF_NUM_OF_INT, INT_LE_MUL, INT_DIVISION, INT_ABS_POS,
                 ← GSYM INT_OF_NUM_MUL, INT_CONG_MOD_ABS] THEN
    REWRITE_TAC [← GSYM INT_REM_EQ, INT_REM_REM, INT_MUL_REM])

  let INT_JACOBI_RPOW ← prove
   r"!a n k. int_jacobi(a,n pow k) = int_jacobi(a,n) pow k"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [INT_JACOBI_RMUL, INT_JACOBI_1, INT_POW])

  let INT_JACOBI_LPOW ← prove
   r"!a n k. int_jacobi(a pow k,n) =
           if n = &0 then &0 else int_jacobi(a,n) pow k"
   (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [INT_JACOBI_LMUL, INT_JACOBI_1, INT_POW] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [INT_MUL_RZERO])

  let INT_JACOBI_2 ← prove
   r"!a. int_jacobi(a,&2) = a rem &2"
   (GEN_TAC THEN ONCE_REWRITE_TAC [← GSYM INT_JACOBI_REM] THEN
    MP_TAC (← SPEC (← q "a:int") INT_REM_2_CASES) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [INT_JACOBI_NUMS, JACOBI_2_CASES] THEN
    CONV_TAC NUM_REDUCE_CONV)

  let INT_JACOBI_POW_2 ← prove
   r"!a k. int_jacobi(a,&2 pow k) = if k = 0 then &1 else a rem &2"
   (REPEAT GEN_TAC THEN REWRITE_TAC [INT_JACOBI_RPOW, INT_JACOBI_2] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [INT_POW] THEN
    MP_TAC (← SPEC (← q "a:int") INT_REM_2_CASES) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [INT_POW_ZERO, INT_POW_ONE])

  let INT_JACOBI_EQ_0 ← prove
   r"!a n. int_jacobi(a,n) = &0 <=> coprime(a,n) ==> n = &0"
   (REPEAT GEN_TAC THEN
    ASM_CASES_TAC (← q r"n:int = &0") THEN ASM_REWRITE_TAC [INT_JACOBI_0] THEN
    ONCE_REWRITE_TAC [← GSYM INT_JACOBI_RABS, ← GSYM INT_COPRIME_RABS] THEN
    ONCE_REWRITE_TAC [← GSYM INT_COPRIME_LREM, ← GSYM INT_JACOBI_REM] THEN
    SUBGOAL_THEN (← q r"&0 <= a rem abs n") MP_TAC THENL
     [ASM_SIMP_TAC [INT_DIVISION, INT_ABS_ZERO],
      SPEC_TAC (← q r"a rem abs n", ← q "x:int")] THEN
    SUBGOAL_THEN (← q r"&0 <= abs(n:int) /\ ~(abs n = &0)") MP_TAC THENL
     [ASM_INT_ARITH_TAC, REWRITE_TAC [IMP_CONJ]] THEN
    SPEC_TAC (← q r"abs n:int", ← q "y:int") THEN
    REWRITE_TAC [← GSYM INT_FORALL_POS] THEN
    SIMP_TAC [INT_OF_NUM_EQ, INT_JACOBI_NUMS, ← GSYM num_coprime] THEN
    SIMP_TAC [JACOBI_EQ_0])

  let INT_JACOBI_MINUS1 ← prove
   r"!n. ~(&2 divides n)
       ==> int_jacobi(--(&1),n) =
           if (abs n == &1) (mod &4) then &1 else -- &1"
   (ONCE_REWRITE_TAC [← GSYM INT_JACOBI_RABS, ← GSYM INT_DIVIDES_RABS] THEN
    REWRITE_TAC [← GSYM INT_FORALL_ABS, ← GSYM num_divides, ← GSYM num_congruent] THEN
    SIMP_TAC [DIVIDES_2, NOT_EVEN, ← GSYM JACOBI_MINUS1_CASES] THEN
    X_GEN_TAC (← q "n:num") THEN
    ASM_CASES_TAC (← q r"n = 0") THEN ASM_REWRITE_TAC [ODD] THEN DISCH_TAC THEN
    TRANS_TAC EQ_TRANS (← q r"int_jacobi(&n - &1,&n)") THEN CONJ_TAC THENL
     [MATCH_MP_TAC INT_JACOBI_CONG THEN CONV_TAC INTEGER_RULE,
      ASM_SIMP_TAC [INT_OF_NUM_EQ, INT_OF_NUM_SUB, LE_1, INT_JACOBI_NUMS]])

  let INT_JACOBI_OF_2 ← prove
   r"!n. int_jacobi(&2,n) =
       if &2 divides n then &0
       else if (abs n == &1) (mod &8) \/ (abs n == &7) (mod &8) then &1
       else --(&1)"
   (ONCE_REWRITE_TAC [← GSYM INT_JACOBI_RABS, ← GSYM INT_DIVIDES_RABS] THEN
    REWRITE_TAC [← GSYM INT_FORALL_ABS, ← GSYM num_divides, ← GSYM num_congruent] THEN
    REWRITE_TAC [DIVIDES_2, ← GSYM JACOBI_OF_2_CASES] THEN
    SIMP_TAC [INT_JACOBI_NUMS] THEN CONV_TAC NUM_REDUCE_CONV)

  let INT_JACOBI_LNEG ← prove
   r"!n. ~(&2 divides n)
       ==> int_jacobi(--a,n) =
           if (abs n == &1) (mod &4) then int_jacobi(a,n)
           else --(int_jacobi(a,n))"
   (REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [INT_NEG_MINUS1] THEN
    ASM_SIMP_TAC [INT_JACOBI_LMUL, INT_JACOBI_MINUS1] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN INT_ARITH_TAC)

  let INT_JACOBI_SQUARED ← prove
   r"(!a n. int_jacobi(a pow 2,n) =
          if coprime(a,n) /\ ~(n = &0) then &1 else &0) /\
   (!a n. int_jacobi(a,n pow 2) =
          if coprime(a,n) /\ ~(n = &0) then &1 else &0)"
   (← do
    let r1 ← INT_RING
     (← q r"(x:int = -- &1 \/ x = &0 \/ x = &1) /\ ~(x = &0) ==> x pow 2 = &1")
    pure (REWRITE_TAC [INT_JACOBI_LPOW, INT_JACOBI_RPOW] THEN
    REPEAT STRIP_TAC THEN ASM_CASES_TAC (← q r"n:int = &0") THEN
    ASM_REWRITE_TAC [INT_JACOBI_EQ_0, INT_POW_EQ_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_CASES_TAC (← q r"coprime(a:int,n)") THEN
    ASM_REWRITE_TAC [INT_JACOBI_EQ_0, INT_POW_EQ_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC r1 THEN
    REWRITE_TAC [INT_JACOBI_CASES] THEN ASM_REWRITE_TAC [INT_JACOBI_EQ_0]))

  -- @@RETURN BEGIN
  return { INT_JACOBI_RMUL, INT_JACOBI_LMUL, INT_JACOBI_RPOW, INT_JACOBI_LPOW,
           INT_JACOBI_2, INT_JACOBI_POW_2, INT_JACOBI_EQ_0, INT_JACOBI_MINUS1,
           INT_JACOBI_OF_2, INT_JACOBI_LNEG, INT_JACOBI_SQUARED }
  -- @@RETURN END

end HolLibrary.Jacobi
