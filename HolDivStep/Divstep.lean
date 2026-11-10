/- ========================================================================= -/
/- The Bernstein-Yang divstep iteration for gcd, modular inverse etc.      -/
/- ========================================================================= -/
/- File: HolDivStep/Divstep.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Divstep/divstep.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/integer.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionDivStep.Divstep fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, INT_ARITH, TAUT, SET_RULE, ...) they are
  bound first, in OCaml's order.
-/

import HolLibrary.Iter
import HolLibrary.Integer

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolDivStep.Divstep

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD_SYM ARITH_EQ FORALL_PAIR_THM IMP_CONJ INT_ADD_LID INT_ADD_REM
   INT_DIVISION_SIMP INT_DIV_LT_EQ INT_DIV_ZERO INT_GCD_EQ INT_LE_DIV_EQ
   INT_LT_DIV_EQ INT_MUL_DIV_EQ INT_MUL_LID INT_MUL_LZERO INT_OF_NUM_EQ
   INT_REM_2_CASES INT_REM_EQ_0 INT_REM_LNEG INT_REM_ZERO INT_SUB_REM ITER_ADD
   ITER_ALT LEFT_AND_EXISTS_THM LEFT_IMP_EXISTS_THM LE_EXISTS LE_REFL PAIR
   PAIR_EQ o_THM : thm)
  deriving Inhabited

/-- What divstep.ml uses from Session besides theorems. -/
structure DivstepDeps where
  new_definition : String → ExceptT String IO thm
  define : String → ExceptT String IO thm
  ARITH_RULE : term → ExceptT String IO thm
  ARITH_TAC : tactic
  ASM_ARITH_TAC : tactic
  MESON : List thm → term → ExceptT String IO thm
  MESON_TAC : List thm → tactic
  ASM_MESON_TAC : List thm → tactic
  METIS_TAC : List thm → tactic
  ASM_METIS_TAC : List thm → tactic
  SET_RULE : term → ExceptT String IO thm
  SET_TAC : List thm → tactic
  TAUT : term → ExceptT String IO thm
  ITAUT : term → ExceptT String IO thm
  REAL_ARITH : term → ExceptT String IO thm
  REAL_FIELD : term → ExceptT String IO thm
  REAL_ARITH_TAC : tactic
  ASM_REAL_ARITH_TAC : tactic
  INDUCT_TAC : tactic
  INT_ARITH : term → ExceptT String IO thm
  INT_ARITH_TAC : tactic
  ASM_INT_ARITH_TAC : tactic
  INTEGER_RULE : term → ExceptT String IO thm  -- ints.ml's INTEGER_RULE
  INTEGER_TAC : tactic
  NUMBER_RULE : ioconv  -- ints.ml's NUMBER_RULE
  NUM_REDUCE_CONV : ioconv
  INT_REDUCE_CONV : ioconv
  INT_RED_CONV : ioconv
  INT_REM_DOWN_CONV : ioconv
  HAS_SIZE_CONV : ioconv  -- card.ml's HAS_SIZE_CONV
  let_CONV : ioconv
  num_CONV : ioconv
  mk_numeral : Rat → Except String term
  LET_TAC : tactic
  basic_ss : List thm → IO (Except String HolCore.Simp.simpset)
  NUM_SUB_CONV : ioconv
  REAL_RAT_REDUCE_CONV : ioconv
  NUM_EQ_CONV : ioconv
  NUM_DIV_CONV : ioconv
  EXP_MOD_CONV : ioconv
  EXPAND_CASES_CONV : ioconv
  core1 : CoreThms1

/-- RingTheory's `wPart` (copied verbatim).  `W(MP_TAC o PART_MATCH f th o g
    o snd)`: match `th`'s part `f` against the part `g` of the goal, and
    MP_TAC the instance. -/
def wPart [HolBase] (g : term → Except String term) (f : term → Except String term)
    (th : thm) : tactic := fun gl =>
  ExceptT.run do
    let t ← liftExcept (g gl.2)
    ExceptT.mk (MP_TAC (← PART_MATCH f th t) gl)

/-- tactics.ml's NO_TAC. -/
def NO_TAC : tactic := HolCore.Tactics.NO_TAC



/- ------------------------------------------------------------------------- -/
/- The core divstep iteration for integers f and g (section 8, page 21), its -/
/- subdivision into two operations (8.2, page 22), the invariants (f stays   -/
/- odd, g stays zero if hit, the gcds stay the same), sizes, and the         -/
/- extension to n-fold iteration.  (divstep.ml 1-173)                        -/
/- ------------------------------------------------------------------------- -/

structure DivstepThms where
  -- @@FIELDS
  divstep : thm
  divstep1 : thm
  divstep2 : thm
  DIVSTEP1_DIVSTEP2 : thm
  DIVSTEP_STAYS_ODD : thm
  DIVSTEP_STAYS_ZERO : thm
  DIVSTEP_MAINTAINS_GCD : thm
  DIVSTEP_RANGE_2SCOMPLEMENT : thm
  DIVSTEP_RANGE_SIGNMAGNITUDE : thm
  ITER_DIVSTEP_ODD : thm
  ITER_DIVSTEP_ZERO : thm
  ITER_DIVSTEP_GCD : thm
  ITER_DIVSTEP_BOUND_ALT : thm
  deriving Inhabited

@[nospecialize]
def setupDivstepThms [HolBase] (D : DivstepDeps) :
    ExceptT String IO DivstepThms := do
  -- @@SCOPE BEGIN
  let { ASM_INT_ARITH_TAC, ASM_METIS_TAC, INDUCT_TAC, INTEGER_RULE, INT_ARITH,
        INT_ARITH_TAC, INT_REDUCE_CONV, MESON_TAC, new_definition, .. } := D
  let { ADD_SYM, ARITH_EQ, FORALL_PAIR_THM, IMP_CONJ, INT_ADD_LID, INT_ADD_REM,
        INT_DIVISION_SIMP, INT_DIV_LT_EQ, INT_DIV_ZERO, INT_GCD_EQ, INT_LE_DIV_EQ,
        INT_LT_DIV_EQ, INT_MUL_DIV_EQ, INT_MUL_LID, INT_MUL_LZERO, INT_OF_NUM_EQ,
        INT_REM_2_CASES, INT_REM_EQ_0, INT_REM_LNEG, INT_REM_ZERO, INT_SUB_REM,
        ITER_ADD, ITER_ALT, LEFT_AND_EXISTS_THM, LEFT_IMP_EXISTS_THM, LE_EXISTS,
        LE_REFL, PAIR, PAIR_EQ, o_THM, .. } := D.core1
  -- @@SCOPE END

  /- Here d is a real number, to allow possibilities like d = 1/2. -/

  let divstep ← new_definition
   r"divstep(d:real,f:int,g:int) =
        if d > &0 /\ g rem &2 = &1
        then &1 - d, g, (g - f) div &2
        else &1 + d, f, (g + (g rem &2) * f) div &2"

  /- As remarked in 8.2, page 22, we can subdivide into separate operations. -/

  let divstep1 ← new_definition
   r"divstep1(d:real,f:int,g:int) =
        if d > &0 /\ g rem &2 = &1
        then --d, g, --f
        else d, f, g"

  let divstep2 ← new_definition
   r"divstep2(d:real,f:int,g:int) =
        &1 + d,f,(g + (g rem &2) * f) div &2"

  let DIVSTEP1_DIVSTEP2 ← prove
   r"!d f g.
        f rem &2 = &1
        ==> (divstep2 o divstep1) (d,f,g) = divstep (d,f,g)"
   (← do
    pure (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [o_THM, divstep1, divstep] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [divstep2] THEN
    ASM_REWRITE_TAC [INT_REM_LNEG, PAIR_EQ] THEN
    CONJ_TAC THENL [INT_ARITH_TAC, CONV_TAC INT_REDUCE_CONV] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC))

  /- Invariants: f stays odd, g stays zero if hit, the gcds stay the same. -/

  let DIVSTEP_STAYS_ODD ← prove
   r"!d f g d' f' g'.
        f rem &2 = &1 /\
        divstep(d,f,g) = d',f',g'
        ==> f' rem &2 = &1"
   (← do
    pure (REWRITE_TAC [divstep] THEN MESON_TAC [PAIR_EQ]))

  let DIVSTEP_STAYS_ZERO ← prove
   r"!d f g d' f' g'.
        g = &0 /\
        divstep(d,f,g) = d',f',g'
        ==> g' = &0"
   (← do
    pure (SIMP_TAC [divstep, IMP_CONJ, INT_REM_ZERO, INT_OF_NUM_EQ, ARITH_EQ] THEN
    REWRITE_TAC [INT_MUL_LZERO, INT_ADD_LID, INT_DIV_ZERO, PAIR_EQ] THEN
    MESON_TAC []))

  let DIVSTEP_MAINTAINS_GCD ← prove
   r"!d f g d' f' g'.
        f rem &2 = &1 /\
        divstep(d,f,g) = d',f',g'
        ==> gcd(f',g') = gcd(f,g)"
   (← do
    -- `let lemma = prove ... in` first; `CONV_TAC INTEGER_RULE` runs later,
    -- as a conversion
    let lemma ← prove
     r"!m n. m rem &2 = &1 /\ n rem &2 = &0 ==> gcd(m,n div &2) = gcd(m,n)"
     (← do
      let i1 ← INTEGER_RULE
       (← q r"coprime(k:int,m)
        ==> (d divides m /\ d divides p <=>
             d divides m /\ d divides (k * p))")
      pure (REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [INT_REM_EQ_0]) THEN
      REWRITE_TAC [← GSYM (← CONJUNCT1 INT_MUL_DIV_EQ)] THEN
      DISCH_THEN (fun th => tactic_of do
        pure (GEN_REWRITE_TAC (funpow 3 RAND_CONV) [← SYM th])) THEN
      MATCH_MP_TAC INT_GCD_EQ THEN GEN_TAC THEN MATCH_MP_TAC i1 THEN
      MP_TAC (← SPECL [← q r"m:int", ← q r"&2:int"] INT_DIVISION_SIMP) THEN
      ASM_REWRITE_TAC [] THEN SPEC_TAC (← q r"&2:int", ← q r"p:int") THEN
      CONV_TAC (fun t => (INTEGER_RULE t).run)))
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE LAND_CONV [divstep]) THEN
    COND_CASES_TAC THEN REWRITE_TAC [PAIR_EQ] THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
    wPart lhand (fun t => do lhand (← rand t)) lemma THEN
    ONCE_REWRITE_TAC [← GSYM INT_SUB_REM, ← GSYM INT_ADD_REM] THEN
    MP_TAC (← SPEC (← q r"g:int") INT_REM_2_CASES) THEN
    ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV THEN
    TRY (DISCH_THEN (DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
    ASM_REWRITE_TAC [INT_MUL_LZERO, INT_MUL_LID] THEN
    CONV_TAC INT_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC INT_GCD_EQ THEN CONV_TAC (fun t => (INTEGER_RULE t).run)))

  /- Sizes; cf the remarks on p22. -/

  let DIVSTEP_RANGE_2SCOMPLEMENT ← prove
   r"!B d f g d' f' g'.
        divstep(d,f,g) = d',f',g' /\
        --B <= f /\ f < B /\
        --B <= g /\ g < B
        ==> --B <= f' /\ f' < B /\
            --B <= g' /\ g' < B"
   (← do
    let i1 ← INT_ARITH (← q r"&0:int < &2")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE LAND_CONV [divstep]) THEN
    COND_CASES_TAC THEN REWRITE_TAC [PAIR_EQ] THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
    ASM_SIMP_TAC [INT_DIV_LT_EQ, INT_LE_DIV_EQ, i1] THENL
     [ASM_INT_ARITH_TAC, ALL_TAC] THEN
    DISJ_CASES_THEN SUBST1_TAC (← SPEC (← q r"g:int") INT_REM_2_CASES) THEN
    ASM_INT_ARITH_TAC))

  let DIVSTEP_RANGE_SIGNMAGNITUDE ← prove
   r"!B d f g d' f' g'.
        divstep(d,f,g) = d',f',g' /\
        --B < f /\ f < B /\
        --B < g /\ g < B
        ==> --B < f' /\ f' < B /\
            --B < g' /\ g' < B"
   (← do
    let i1 ← INT_ARITH (← q r"&0:int < &2")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE LAND_CONV [divstep]) THEN
    COND_CASES_TAC THEN REWRITE_TAC [PAIR_EQ] THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
    ASM_SIMP_TAC [INT_DIV_LT_EQ, INT_LT_DIV_EQ, i1] THENL
     [ASM_INT_ARITH_TAC, ALL_TAC] THEN
    DISJ_CASES_THEN SUBST1_TAC (← SPEC (← q r"g:int") INT_REM_2_CASES) THEN
    ASM_INT_ARITH_TAC))

  /- Extend invariant lemmas to n-fold iteration of divstep. -/

  let ITER_DIVSTEP_ODD ← prove
   r"!n d f g d' f' g'.
        f rem &2 = &1 /\
        ITER n divstep (d,f,g) = d',f',g'
        ==> f' rem &2 = &1"
   (← do
    pure (INDUCT_TAC THEN ASM_SIMP_TAC [ITER_ALT, PAIR_EQ] THENL
     [MESON_TAC [], REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC] THEN
    ASM_METIS_TAC [DIVSTEP_STAYS_ODD, PAIR]))

  let ITER_DIVSTEP_ZERO ← prove
   r"!n d f g d' f' g'.
        g = &0 /\
        ITER n divstep (d,f,g) = d',f',g'
        ==> g' = &0"
   (← do
    pure (INDUCT_TAC THEN REWRITE_TAC [ITER_ALT, PAIR_EQ] THENL
     [MESON_TAC [], REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC] THEN
    ASM_METIS_TAC [DIVSTEP_STAYS_ZERO, PAIR]))

  let ITER_DIVSTEP_GCD ← prove
   r"!n d f g d' f' g'.
        f rem &2 = &1 /\
        ITER n divstep (d,f,g) = d',f',g'
        ==> gcd(f',g') = gcd(f,g)"
   (← do
    pure (INDUCT_TAC THEN ASM_SIMP_TAC [ITER_ALT, PAIR_EQ] THEN
    ASM_METIS_TAC [DIVSTEP_STAYS_ODD, DIVSTEP_MAINTAINS_GCD, PAIR]))

  /- So we can express termination with g = 0 in two equivalent ways. -/

  let ITER_DIVSTEP_BOUND_ALT ← prove
   r"!t m. (?n. n <= m /\ SND(SND(ITER n divstep t)) = &0) <=>
         SND(SND(ITER m divstep t)) = &0"
   (← do
    pure (REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC, MESON_TAC [LE_REFL]] THEN
    REWRITE_TAC [LE_EXISTS, LEFT_IMP_EXISTS_THM, LEFT_AND_EXISTS_THM] THEN
    SIMP_TAC [← ONCE_REWRITE_RULE [ADD_SYM] (← GSYM ITER_ADD)] THEN
    REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o CONJUNCT2) THEN
    SPEC_TAC (← q r"ITER n divstep t", ← q r"q:real#int#int") THEN
    REWRITE_TAC [FORALL_PAIR_THM] THEN MESON_TAC [ITER_DIVSTEP_ZERO, PAIR]))

  -- @@RETURN BEGIN
  return { divstep, divstep1, divstep2, DIVSTEP1_DIVSTEP2, DIVSTEP_STAYS_ODD,
           DIVSTEP_STAYS_ZERO, DIVSTEP_MAINTAINS_GCD, DIVSTEP_RANGE_2SCOMPLEMENT,
           DIVSTEP_RANGE_SIGNMAGNITUDE, ITER_DIVSTEP_ODD, ITER_DIVSTEP_ZERO,
           ITER_DIVSTEP_GCD, ITER_DIVSTEP_BOUND_ALT }
  -- @@RETURN END

end HolDivStep.Divstep
