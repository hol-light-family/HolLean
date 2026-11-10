/- ========================================================================= -/
/- Integer-only version of divstep with d = 2 * delta                      -/
/- ========================================================================= -/
/- File: HolDivStep/IDivstep.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `Divstep/idivstep.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/integer.ml, Divstep/divstep.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionDivStep.IDivstep fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, INT_ARITH, TAUT, SET_RULE, ...) they are
  bound first, in OCaml's order.
-/

import HolLibrary.Iter
import HolLibrary.Integer
import HolDivStep.Divstep

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolDivStep.IDivstep

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD_CLAUSES AND_FORALL_THM ARITH CART_EQ DIMINDEX_2 EL FINITE_RULES
   FORALL_PAIR_THM FUN_EQ_THM HD IMP_CONJ INT_2_DIVIDES_ADD INT_2_DIVIDES_MUL
   INT_2_DIVIDES_SUB INT_ADD_LDISTRIB INT_ADD_REM INT_ADD_RID INT_CONG_DIV2
   INT_CONG_LREM INT_CONG_REFL INT_DIVIDES_POW_LE_IMP INT_DIVISION_SIMP
   INT_DIV_LNEG INT_DIV_LT_EQ INT_GCD_EQ INT_LE_DIV_EQ INT_LT_DIV_EQ
   INT_MUL_ASSOC INT_MUL_DIV_EQ INT_MUL_LID INT_MUL_LZERO INT_OF_NUM_SUC INT_POW
   INT_REM_2_CASES INT_REM_2_DIVIDES INT_REM_2_NEG INT_REM_EQ INT_REM_EQ_0
   INT_REM_REM INT_SUB_LDISTRIB INT_SUB_REM IN_SING ISUM_CLAUSES ITER ITER_ADD
   I_THM LAMBDA_BETA LENGTH LE_REFL NOT_IN_EMPTY NUMSEG_CLAUSES NUMSEG_SING
   PAIR_EQ REAL_OF_INT_CLAUSES RIGHT_FORALL_IMP_THM SUB_0 SWAP_FORALL_THM TL
   divstep int_gt int_of_num_th o_THM vector : thm)
  deriving Inhabited

/-- What idivstep.ml uses from Session besides theorems. -/
structure IDivstepDeps where
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
/- A few ad-hoc results about integer 2x2 vectors and matrices (analogs of   -/
/- things in Multivariate/vectors.ml but for integers), the integer-only     -/
/- divstep with d scaled up by a factor of 2, and its iterated and           -/
/- componentwise versions.  (idivstep.ml 1-151)                              -/
/- ------------------------------------------------------------------------- -/

structure IDivstepDefs where
  -- @@FIELDS
  FORALL_2 : thm
  VECTOR_2 : thm
  ISUM_2 : thm
  imat_I : thm
  imat_mul : thm
  imat_vmul : thm
  IMAT_I : thm
  IMAT_MUL : thm
  IMAT_MUL_LID : thm
  IMAT_MUL_ASSOC : thm
  idivstep : thm
  IDIVSTEP_STAYS_ODD : thm
  IDIVSTEP_STAYS_ZERO : thm
  divstep_d : thm
  divstep_f : thm
  divstep_g : thm
  DIVSTEP_DFG : thm
  DIVSTEP_D : thm
  DIVSTEP_F : thm
  DIVSTEP_G : thm
  DIVSTEP_DFG_ADD : thm
  deriving Inhabited

@[nospecialize]
def setupIDivstepDefs [HolBase] (D : IDivstepDeps) :
    ExceptT String IO IDivstepDefs := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, INT_ARITH_TAC, INT_REDUCE_CONV, MESON_TAC, NUM_REDUCE_CONV, define,
        new_definition, num_CONV, .. } := D
  let { ARITH, CART_EQ, DIMINDEX_2, EL, FINITE_RULES, FORALL_PAIR_THM, FUN_EQ_THM, HD,
        INT_ADD_REM, INT_MUL_LZERO, INT_SUB_REM, IN_SING, ISUM_CLAUSES, ITER, ITER_ADD,
        I_THM, LAMBDA_BETA, LENGTH, NOT_IN_EMPTY, NUMSEG_CLAUSES, NUMSEG_SING, PAIR_EQ,
        TL, o_THM, vector, .. } := D.core1
  -- @@SCOPE END

  let FORALL_2 ← prove
   r"!P. (!i. 1 <= i /\ i <= 2 ==> P i) <=> P 1 /\ P 2"
   (← do
    let a1 ← ARITH_RULE (← q r"1 <= i /\ i <= 2 <=> i = 1 \/ i = 2")
    pure (MESON_TAC [a1]))

  let VECTOR_2 ← prove
   r"(vector[x;y]:A^2)$1 = x /\
   (vector[x;y]:A^2)$2 = y"
   (← do
    let n1 ← ExceptT.mk (num_CONV (← q r"1"))
    pure (SIMP_TAC [vector, LAMBDA_BETA, DIMINDEX_2, ARITH, LENGTH, EL] THEN
    REWRITE_TAC [n1, HD, TL, EL]))

  let ISUM_2 ← prove
   r"!t. isum(1..2) t = t(1) + t(2)"
   (← do
    let n2 ← ExceptT.mk (num_CONV (← q r"2"))
    pure (REWRITE_TAC [n2, NUMSEG_CLAUSES, NUMSEG_SING] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC [ISUM_CLAUSES, FINITE_RULES, NOT_IN_EMPTY, IN_SING] THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC))

  let imat_I ← define
   r"imat_I:int^2^2 = lambda i j. if i = j then &1 else &0"

  let imat_mul ← define
   r"(imat_mul:int^2^2->int^2^2->int^2^2) m n =
        lambda i j. isum(1..2) (\k. m$i$k * n$k$j)"

  let imat_vmul ← define
   r"(imat_vmul:int^2^2->int^2->int^2) m v =
        lambda i. isum(1..2) (\j. m$i$j * v$j)"

  let IMAT_I ← prove
   r"imat_vmul imat_I = I"
   (← do
    pure (REWRITE_TAC [FUN_EQ_THM, I_THM, imat_vmul, imat_I] THEN
    SIMP_TAC [CART_EQ, LAMBDA_BETA, DIMINDEX_2, ARITH, FORALL_2, ISUM_2] THEN
    INT_ARITH_TAC))

  let IMAT_MUL ← prove
   r"!m1 m2. imat_vmul (imat_mul m1 m2) = imat_vmul m1 o imat_vmul m2"
   (← do
    pure (REWRITE_TAC [FUN_EQ_THM, o_THM, imat_vmul, imat_mul] THEN
    SIMP_TAC [CART_EQ, LAMBDA_BETA, DIMINDEX_2, ARITH, FORALL_2, ISUM_2] THEN
    INT_ARITH_TAC))

  let IMAT_MUL_LID ← prove
   r"!m. imat_mul imat_I m = m"
   (← do
    pure (SIMP_TAC [CART_EQ, DIMINDEX_2, FORALL_2, imat_I, LAMBDA_BETA,
                    imat_mul, ARITH, ISUM_2] THEN
    INT_ARITH_TAC))

  let IMAT_MUL_ASSOC ← prove
   r"!m1 m2 m3. imat_mul m1 (imat_mul m2 m3) = imat_mul (imat_mul m1 m2) m3"
   (← do
    pure (SIMP_TAC [CART_EQ, DIMINDEX_2, FORALL_2, imat_I, LAMBDA_BETA,
                    imat_mul, ARITH, ISUM_2] THEN
    INT_ARITH_TAC))

  /- A integer-only divstep with d scaled up by a factor of 2. To maintain
     the connection with "divstep", the initial d should be odd, in which
     case it stays odd (so the d >= 0 versus d > 0 distinction makes no
     difference). In practice we assume the iterations start with d = 1,
     corresponding to the real delta = 1/2 in the canonical "divstep", which
     seems to give the best bounds. -/

  let idivstep ← new_definition
   r"idivstep(d:int,f:int,g:int) =
        if d >= &0 /\ g rem &2 = &1
        then &2 - d, g, (g - f) div &2
        else &2 + d, f, (g + (g rem &2) * f) div &2"

  let IDIVSTEP_STAYS_ODD ← prove
   r"!d f g d' f' g'.
         d rem &2 = &1 /\ idivstep(d,f,g) = d',f',g' ==> d' rem &2 = &1"
   (← do
    pure (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC [idivstep] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [PAIR_EQ] THEN
    DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← GSYM th])) THEN
    ONCE_REWRITE_TAC [← GSYM INT_ADD_REM, ← GSYM INT_SUB_REM] THEN
    ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV))

  let IDIVSTEP_STAYS_ZERO ← prove
   r"!d f g d' f' g'.
         g = &0 /\ idivstep(d,f,g) = d',f',g' ==> g' = &0"
   (← do
    pure (REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC [idivstep] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC [PAIR_EQ, INT_MUL_LZERO] THEN INT_ARITH_TAC))

  /- Iterated and componentwise versions of idivstep -/

  let divstep_d ← define
   r"divstep_d n t = FST(ITER n idivstep t)"

  let divstep_f ← define
   r"divstep_f n t = FST(SND(ITER n idivstep t))"

  let divstep_g ← define
   r"divstep_g n t = SND(SND(ITER n idivstep t))"

  let DIVSTEP_DFG ← prove
   r"(divstep_d n t,divstep_f n t,divstep_g n t) = ITER n idivstep t"
   (← do
    pure (REWRITE_TAC [divstep_d, divstep_f, divstep_g]))

  let DIVSTEP_D ← prove
   r"divstep_d 0 (d,f,g) = d /\
   divstep_d (SUC n) t =
   if divstep_d n t >= &0 /\ divstep_g n t rem &2 = &1
   then &2 - divstep_d n t else &2 + divstep_d n t"
   (← do
    pure (REWRITE_TAC [ITER, divstep_d, divstep_g] THEN
    SPEC_TAC (← q r"ITER n idivstep t", ← q r"p:int#int#int") THEN
    REWRITE_TAC [FORALL_PAIR_THM, idivstep] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC []))

  let DIVSTEP_F ← prove
   r"divstep_f 0 (d,f,g) = f /\
   divstep_f (SUC n) t =
   if divstep_d n t >= &0 /\ divstep_g n t rem &2 = &1
   then divstep_g n t else divstep_f n t"
   (← do
    pure (REWRITE_TAC [ITER, divstep_d, divstep_f, divstep_g] THEN
    SPEC_TAC (← q r"ITER n idivstep t", ← q r"p:int#int#int") THEN
    REWRITE_TAC [FORALL_PAIR_THM, idivstep] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC []))

  let DIVSTEP_G ← prove
   r"divstep_g 0 (d,f,g) = g /\
   divstep_g (SUC n) t =
   if divstep_d n t >= &0 /\ divstep_g n t rem &2 = &1
   then (divstep_g n t - divstep_f n t) div &2
   else (divstep_g n t + divstep_g n t rem &2 * divstep_f n t) div &2"
   (← do
    pure (REWRITE_TAC [ITER, divstep_d, divstep_f, divstep_g] THEN
    SPEC_TAC (← q r"ITER n idivstep t", ← q r"p:int#int#int") THEN
    REWRITE_TAC [FORALL_PAIR_THM, idivstep] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC []))

  let DIVSTEP_DFG_ADD ← prove
   r"divstep_d (m + n) t =
   divstep_d m (divstep_d n t,divstep_f n t,divstep_g n t) /\
   divstep_f (m + n) t =
   divstep_f m (divstep_d n t,divstep_f n t,divstep_g n t) /\
   divstep_g (m + n) t =
   divstep_g m (divstep_d n t,divstep_f n t,divstep_g n t)"
   (← do
    pure (REWRITE_TAC [divstep_d, divstep_f, divstep_g] THEN
    REWRITE_TAC [← GSYM PAIR_EQ, ITER_ADD]))

  -- @@RETURN BEGIN
  return { FORALL_2, VECTOR_2, ISUM_2, imat_I, imat_mul, imat_vmul, IMAT_I, IMAT_MUL,
           IMAT_MUL_LID, IMAT_MUL_ASSOC, idivstep, IDIVSTEP_STAYS_ODD,
           IDIVSTEP_STAYS_ZERO, divstep_d, divstep_f, divstep_g, DIVSTEP_DFG, DIVSTEP_D,
           DIVSTEP_F, DIVSTEP_G, DIVSTEP_DFG_ADD }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- The basic invariance and bound properties, often similar to pure divstep, -/
/- and the precise connection with divstep when starting at delta = 1/2.     -/
/- (idivstep.ml 152-281)                                                     -/
/- ------------------------------------------------------------------------- -/

structure IDivstepBounds where
  -- @@FIELDS
  DIVSTEP_D_PARITY : thm
  DIVSTEP_D_BOUND : thm
  DIVSTEP_F_ODD : thm
  DIVSTEP_G_ZERO : thm
  DIVSTEP_FG_GCD : thm
  DIVSTEP_F_BOUNDS : thm
  DIVSTEP_G_BOUNDS : thm
  DIVSTEP_F_BOUNDS_LT : thm
  DIVSTEP_G_BOUNDS_LT : thm
  ITER_DIVSTEP_INTEGER : thm
  deriving Inhabited

@[nospecialize]
def setupIDivstepBounds [HolBase] (D : IDivstepDeps) (BIDivstepDefs : IDivstepDefs) :
    ExceptT String IO IDivstepBounds := do
  -- @@SCOPE BEGIN
  let { ASM_INT_ARITH_TAC, INDUCT_TAC, INTEGER_RULE, INT_ARITH, INT_REDUCE_CONV, MESON,
        REAL_ARITH, TAUT, .. } := D
  let { AND_FORALL_THM, INT_ADD_REM, INT_ADD_RID, INT_DIVISION_SIMP, INT_DIV_LT_EQ,
        INT_GCD_EQ, INT_LE_DIV_EQ, INT_LT_DIV_EQ, INT_MUL_DIV_EQ, INT_MUL_LID,
        INT_MUL_LZERO, INT_OF_NUM_SUC, INT_REM_2_CASES, INT_REM_2_DIVIDES,
        INT_REM_EQ_0, INT_SUB_REM, ITER, REAL_OF_INT_CLAUSES, RIGHT_FORALL_IMP_THM,
        SWAP_FORALL_THM, divstep, int_of_num_th, .. } := D.core1
  let { DIVSTEP_D, DIVSTEP_F, DIVSTEP_G, .. } := BIDivstepDefs
  -- @@SCOPE END

  let DIVSTEP_D_PARITY ← prove
   r"!n d f g. divstep_d n (d,f,g) rem &2 = d rem &2"
   (← do
    -- right to left: the two INTEGER_RULEs from the last, then the MESON
    -- (whose list, with its INT_REDUCE_CONV, is evaluated first)
    let i164 ← INTEGER_RULE (← q r"p divides (p - x:int) <=> p divides x")
    let i163 ← INTEGER_RULE (← q r"p divides (p + x:int) <=> p divides x")
    let c159 ← ExceptT.mk (INT_REDUCE_CONV (← q r"&1:int = &0"))
    let m159 ← MESON [INT_REM_2_DIVIDES, c159]
        (← q r"x rem &2 = y rem &2 <=> (&2 divides x <=> &2 divides y)")
    pure (REWRITE_TAC [m159] THEN
    INDUCT_TAC THEN REWRITE_TAC [DIVSTEP_D] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC [i163] THEN
    REWRITE_TAC [i164] THEN
    ASM_REWRITE_TAC []))

  let DIVSTEP_D_BOUND ← prove
   r"!n d f g. abs(abs(divstep_d n (d,f,g)) - abs(d)) <= &2 * &n"
   (← do
    pure (REPLICATE_TAC 3 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC [DIVSTEP_D, ← GSYM INT_OF_NUM_SUC] THEN
    ASM_INT_ARITH_TAC))

  let DIVSTEP_F_ODD ← prove
   r"!n d f g. f rem &2 = &1 ==> divstep_f n (d,f,g) rem &2 = &1"
   (← do
    pure (INDUCT_TAC THEN REWRITE_TAC [DIVSTEP_F] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC []))

  let DIVSTEP_G_ZERO ← prove
   r"!n d f g. g = &0 ==> divstep_g n (d,f,g) = &0"
   (← do
    pure (INDUCT_TAC THEN REWRITE_TAC [DIVSTEP_G] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    ASM_SIMP_TAC [INT_MUL_LZERO, INT_ADD_RID] THEN
    CONV_TAC INT_REDUCE_CONV))

  let DIVSTEP_FG_GCD ← prove
   r"!n d f g.
        f rem &2 = &1
        ==> gcd(divstep_f n (d,f,g),divstep_g n (d,f,g)) = gcd(f,g)"
   (← do
    -- `let lemma = prove ... in` first; the two `CONV_TAC INTEGER_RULE`s
    -- run later, as conversions
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
    pure (REPLICATE_TAC 3 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC [DIVSTEP_F, DIVSTEP_G] THEN
     DISJ_CASES_TAC (← SPEC (← q r"divstep_g n (d,f,g)") INT_REM_2_CASES) THEN
    ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV THEN
    TRY (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    wPart lhand (fun t => do lhand (← rand t)) lemma THEN
    ONCE_REWRITE_TAC [← GSYM INT_SUB_REM, ← GSYM INT_ADD_REM] THEN
    ASM_SIMP_TAC [DIVSTEP_F_ODD, INT_MUL_LID, INT_MUL_LZERO] THEN
    CONV_TAC INT_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      pure (GEN_REWRITE_TAC RAND_CONV [← SYM th])) THEN
    MATCH_MP_TAC INT_GCD_EQ THEN CONV_TAC (fun t => (INTEGER_RULE t).run)))

  -- `let A,B = (CONJ_PAIR o prove) (...)`
  let (DIVSTEP_F_BOUNDS, DIVSTEP_G_BOUNDS) ← do
    -- right to left: the INT_ARITH, then the TAUT
    let i230 ← INT_ARITH (← q r"&0:int < &2")
    let t223 ← TAUT (← q r"(p ==> q) /\ (p ==> r) <=> p ==> q /\ r")
    let th ← prove
     r"(!B n d f g.
        --B <= f /\ f < B /\ --B <= g /\ g < B
        ==> --B <= divstep_f n (d,f,g) /\ divstep_f n (d,f,g) < B) /\
   (!B n d f g.
        --B <= f /\ f < B /\ --B <= g /\ g < B
        ==> --B <= divstep_g n (d,f,g) /\ divstep_g n (d,f,g) < B)"
     (REWRITE_TAC [AND_FORALL_THM, t223] THEN
      GEN_TAC THEN
      REPLICATE_TAC 3 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
      REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
      INDUCT_TAC THEN ASM_REWRITE_TAC [DIVSTEP_F, DIVSTEP_G] THEN
      COND_CASES_TAC THEN
      ASM_SIMP_TAC [INT_DIV_LT_EQ, INT_LE_DIV_EQ, i230] THEN
      DISJ_CASES_THEN SUBST1_TAC (← SPEC (← q r"divstep_g n (d,f,g)") INT_REM_2_CASES) THEN
      ASM_INT_ARITH_TAC)
    CONJ_PAIR th

  let (DIVSTEP_F_BOUNDS_LT, DIVSTEP_G_BOUNDS_LT) ← do
    let i248 ← INT_ARITH (← q r"&0:int < &2")
    let t241 ← TAUT (← q r"(p ==> q) /\ (p ==> r) <=> p ==> q /\ r")
    let th ← prove
     r"(!B n d f g.
        --B < f /\ f < B /\ --B < g /\ g < B
        ==> --B < divstep_f n (d,f,g) /\ divstep_f n (d,f,g) < B) /\
   (!B n d f g.
        --B < f /\ f < B /\ --B < g /\ g < B
        ==> --B < divstep_g n (d,f,g) /\ divstep_g n (d,f,g) < B)"
     (REWRITE_TAC [AND_FORALL_THM, t241] THEN
      GEN_TAC THEN
      REPLICATE_TAC 3 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
      REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
      INDUCT_TAC THEN ASM_REWRITE_TAC [DIVSTEP_F, DIVSTEP_G] THEN
      COND_CASES_TAC THEN
      ASM_SIMP_TAC [INT_DIV_LT_EQ, INT_LT_DIV_EQ, i248] THEN
      DISJ_CASES_THEN SUBST1_TAC (← SPEC (← q r"divstep_g n (d,f,g)") INT_REM_2_CASES) THEN
      ASM_INT_ARITH_TAC)
    CONJ_PAIR th

  /- The precise connection with with divstep, when starting at delta = 1/2. -/

  let ITER_DIVSTEP_INTEGER ← prove
   r"!f g n.
        ITER n divstep (&1 / &2,f,g) =
        (real_of_int(divstep_d n (&1,f,g)) / &2,
         divstep_f n (&1,f,g),
         divstep_g n (&1,f,g))"
   (← do
    -- right to left: the INT_ARITH, then the REAL_ARITHs from the last
    let i269 ← INT_ARITH (← q r"(x:int > &0) <=> ~(x = &0) /\ x >= &0")
    let r267 ← REAL_ARITH (← q r"&1 + x / &2 = (&2 + x) / &2")
    let r266 ← REAL_ARITH (← q r"&1 - x / &2 = (&2 - x) / &2")
    let r265 ← REAL_ARITH (← q r"x / &2 > &0 <=> x > &0")
    pure (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC [divstep, ITER, DIVSTEP_D, DIVSTEP_F, DIVSTEP_G] THEN
    ASM_REWRITE_TAC [int_of_num_th, divstep] THEN
    REWRITE_TAC [r265] THEN
    REWRITE_TAC [r266] THEN
    REWRITE_TAC [r267] THEN
    REWRITE_TAC [REAL_OF_INT_CLAUSES] THEN
    REWRITE_TAC [i269] THEN
    MP_TAC (← SPECL [← q r"n:num", ← q r"&1:int", ← q r"f:int", ← q r"g:int"] DIVSTEP_D_PARITY) THEN
    ASM_CASES_TAC (← q r"divstep_d n (&1,f,g) = &0") THEN
    ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV THEN
    DISCH_THEN (K ALL_TAC : thm → tactic) THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC []))

  -- @@RETURN BEGIN
  return { DIVSTEP_D_PARITY, DIVSTEP_D_BOUND, DIVSTEP_F_ODD, DIVSTEP_G_ZERO,
           DIVSTEP_FG_GCD, DIVSTEP_F_BOUNDS, DIVSTEP_G_BOUNDS, DIVSTEP_F_BOUNDS_LT,
           DIVSTEP_G_BOUNDS_LT, ITER_DIVSTEP_INTEGER }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Extended version of divstep with matrix updates; invariance of divstep_d  -/
/- and divstep_mat under congruences and under negation; and the variant     -/
/- "hddivstep" of https://github.com/sipa/safegcd-bounds, which uses > and   -/
/- so corresponds more exactly to the canonical divstep regardless of the    -/
/- parity of d, but is the same as idivstep when d is odd.                   -/
/- (idivstep.ml 282-528)                                                     -/
/- ------------------------------------------------------------------------- -/

structure IDivstepMat where
  -- @@FIELDS
  divstep_mat : thm
  DIVSTEP_MAT : thm
  DIVSTEP_MAT_BOUNDS : thm
  DIVSTEP_MAT_ABS_BOUNDS : thm
  DIVSTEP_MAT_ADD : thm
  DIVSTEP_MAT_DIAGONAL : thm
  DIVSTEP_MAT_DIAGONAL_1 : thm
  DIVSTEP_MAT_DIAGONAL_2 : thm
  DIVSTEP_CONGRUENCE : thm
  DIVSTEP_D_CONGRUENCE : thm
  DIVSTEP_D_CONGRUENCE_GEN : thm
  DIVSTEP_MAT_CONGRUENCE : thm
  DIVSTEP_MAT_CONGRUENCE_GEN : thm
  DIVSTEP_D_MOD : thm
  DIVSTEP_MAT_MOD : thm
  DIVSTEP_D_NEG : thm
  DIVSTEP_MAT_NEG : thm
  DIVSTEP_F_NEG : thm
  DIVSTEP_G_NEG : thm
  DIVSTEP_CONGRUENCE_NEG : thm
  hdivstep : thm
  HDIVSTEP_DIVSTEP : thm
  HDIVSTEP_IDIVSTEP : thm
  deriving Inhabited

@[nospecialize]
def setupIDivstepMat [HolBase] (D : IDivstepDeps) (BIDivstepDefs : IDivstepDefs) (BIDivstepBounds : IDivstepBounds) :
    ExceptT String IO IDivstepMat := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ASM_ARITH_TAC, ASM_INT_ARITH_TAC, INDUCT_TAC, INTEGER_RULE,
        INT_ARITH, INT_ARITH_TAC, INT_REDUCE_CONV, MESON_TAC, REAL_ARITH, define,
        new_definition, .. } := D
  let { ADD_CLAUSES, AND_FORALL_THM, ARITH, CART_EQ, DIMINDEX_2, IMP_CONJ,
        INT_2_DIVIDES_ADD, INT_2_DIVIDES_MUL, INT_2_DIVIDES_SUB, INT_ADD_LDISTRIB,
        INT_CONG_DIV2, INT_CONG_LREM, INT_CONG_REFL, INT_DIVIDES_POW_LE_IMP,
        INT_DIV_LNEG, INT_MUL_ASSOC, INT_MUL_DIV_EQ, INT_MUL_LID, INT_POW,
        INT_REM_2_CASES, INT_REM_2_DIVIDES, INT_REM_2_NEG, INT_REM_EQ, INT_REM_REM,
        INT_SUB_LDISTRIB, I_THM, LAMBDA_BETA, LE_REFL, PAIR_EQ, REAL_OF_INT_CLAUSES,
        RIGHT_FORALL_IMP_THM, SUB_0, SWAP_FORALL_THM, divstep, int_gt, int_of_num_th,
        o_THM, .. } := D.core1
  let { DIVSTEP_D, DIVSTEP_DFG_ADD, DIVSTEP_F, DIVSTEP_G, FORALL_2, IMAT_I, IMAT_MUL,
        IMAT_MUL_ASSOC, IMAT_MUL_LID, ISUM_2, VECTOR_2, idivstep, imat_I, imat_mul,
        imat_vmul, .. } := BIDivstepDefs
  let { DIVSTEP_F_ODD, DIVSTEP_G_ZERO, .. } := BIDivstepBounds
  -- @@SCOPE END

  let divstep_mat ← define
   r"divstep_mat 0 t = imat_I /\
  divstep_mat (SUC n) t =
    imat_mul
     (if divstep_d n t >= &0 /\ divstep_g n t rem &2 = &1
      then vector[vector[&0; &2]; vector[-- &1; &1]]
      else vector[vector[&2; &0];vector[divstep_g n t rem &2; &1]])
     (divstep_mat n t)"

  let DIVSTEP_MAT ← prove
   r"!d f g n.
        f rem &2 = &1
        ==> imat_vmul (divstep_mat n (d,f,g)) (vector[f;g]) =
            vector[&2 pow n * divstep_f n (d,f,g);
                   &2 pow n * divstep_g n (d,f,g)]"
   (← do
    -- right to left: the INT_ARITHs from the last
    let i309 ← INT_ARITH (← q r"x + &1 * y:int = y + x")
    let i308 ← INT_ARITH (← q r"-- &1 * x + &1 * y:int = y - x")
    let i305 ← INT_ARITH (← q r"(a:int) * x pow n * b = x pow n * a * b")
    let i304 ← INT_ARITH (← q r"(a:int) * x pow n = x pow n * a")
    pure (REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
    DISCH_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC [divstep_mat, DIVSTEP_F, DIVSTEP_G, IMAT_I, I_THM,
                     INT_POW, INT_MUL_LID] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [IMAT_MUL, o_THM] THEN
    SIMP_TAC [imat_vmul, ISUM_2, FORALL_2, VECTOR_2, LAMBDA_BETA,
              DIMINDEX_2, CART_EQ] THEN
    (CONJ_TAC THENL [INT_ARITH_TAC, ALL_TAC]) THEN
    REWRITE_TAC [← GSYM INT_MUL_ASSOC] THEN
    REWRITE_TAC [i304] THEN
    REWRITE_TAC [i305] THEN
    REWRITE_TAC [← GSYM INT_ADD_LDISTRIB, ← GSYM INT_SUB_LDISTRIB] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC [i308] THEN
    REWRITE_TAC [i309] THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC [INT_MUL_DIV_EQ] THEN
    REWRITE_TAC [INT_2_DIVIDES_ADD, INT_2_DIVIDES_SUB, INT_2_DIVIDES_MUL] THEN
    REWRITE_TAC [← GSYM (← CONJUNCT1 INT_REM_2_DIVIDES)] THEN
    ASM_SIMP_TAC [DIVSTEP_F_ODD, INT_REM_REM] THEN INT_ARITH_TAC))

  let DIVSTEP_MAT_BOUNDS ← prove
   r"!n t.
    --(&2 pow n) < divstep_mat n t$1$1 /\ divstep_mat n t$1$1 <= &2 pow n /\
    --(&2 pow n) < divstep_mat n t$1$2 /\ divstep_mat n t$1$2 <= &2 pow n /\
    --(&2 pow n) < divstep_mat n t$2$1 /\ divstep_mat n t$2$1 <= &2 pow n /\
    --(&2 pow n) < divstep_mat n t$2$2 /\ divstep_mat n t$2$2 <= &2 pow n"
   (← do
    pure (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC [divstep_mat, imat_I] THEN
    SIMP_TAC [LAMBDA_BETA, DIMINDEX_2, ARITH] THEN
    CONV_TAC INT_REDUCE_CONV THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [imat_mul, LAMBDA_BETA, DIMINDEX_2, ARITH, ISUM_2, VECTOR_2] THEN
    DISJ_CASES_THEN SUBST1_TAC (← SPEC (← q r"divstep_g n t") INT_REM_2_CASES) THEN
    REWRITE_TAC [INT_POW] THEN ASM_INT_ARITH_TAC))

  let DIVSTEP_MAT_ABS_BOUNDS ← prove
   r"!n t.
    --(&2 pow n) < divstep_mat n t$1$1 /\ divstep_mat n t$1$1 <= &2 pow n /\
    --(&2 pow n) < divstep_mat n t$1$2 /\ divstep_mat n t$1$2 <= &2 pow n /\
    --(&2 pow n) < divstep_mat n t$2$1 /\ divstep_mat n t$2$1 <= &2 pow n /\
    --(&2 pow n) < divstep_mat n t$2$2 /\ divstep_mat n t$2$2 <= &2 pow n /\
    abs(divstep_mat n t$1$1) + abs(divstep_mat n t$1$2) <= &2 pow n /\
    abs(divstep_mat n t$2$1) + abs(divstep_mat n t$2$2) <= &2 pow n"
   (← do
    pure (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC [divstep_mat, imat_I] THEN
    SIMP_TAC [LAMBDA_BETA, DIMINDEX_2, ARITH] THEN
    CONV_TAC INT_REDUCE_CONV THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [imat_mul, LAMBDA_BETA, DIMINDEX_2, ARITH, ISUM_2, VECTOR_2] THEN
    DISJ_CASES_THEN SUBST1_TAC (← SPEC (← q r"divstep_g n t") INT_REM_2_CASES) THEN
    REWRITE_TAC [INT_POW] THEN ASM_INT_ARITH_TAC))

  let DIVSTEP_MAT_ADD ← prove
   r"divstep_mat (m + n) t =
   imat_mul (divstep_mat m (divstep_d n t,divstep_f n t,divstep_g n t))
            (divstep_mat n t)"
   (← do
    pure (SPEC_TAC (← q r"m:num", ← q r"m:num") THEN INDUCT_TAC THEN
    REWRITE_TAC [ADD_CLAUSES, divstep_mat, DIVSTEP_DFG_ADD, IMAT_MUL_LID] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [IMAT_MUL_LID, IMAT_MUL_ASSOC]))

  let DIVSTEP_MAT_DIAGONAL ← prove
   r"!d f n.
        divstep_mat n (d,f,&0) $1$2 = &0 /\
        divstep_mat n (d,f,&0) $2$1 = &0"
   (← do
    pure (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
    ASM_SIMP_TAC [divstep_mat, imat_I, LAMBDA_BETA, DIMINDEX_2, ARITH] THEN
    SIMP_TAC [DIVSTEP_G_ZERO] THEN CONV_TAC INT_REDUCE_CONV THEN
    ASM_SIMP_TAC [imat_mul, VECTOR_2, ISUM_2, LAMBDA_BETA, DIMINDEX_2, ARITH] THEN
    INT_ARITH_TAC))

  let DIVSTEP_MAT_DIAGONAL_1 ← prove
   r"!d f g n. g = &0 ==> divstep_mat n (d,f,g) $1$2 = &0"
   (← do
    pure (MESON_TAC [DIVSTEP_MAT_DIAGONAL]))

  let DIVSTEP_MAT_DIAGONAL_2 ← prove
   r"!d f g n. g = &0 ==> divstep_mat n (d,f,g) $2$1 = &0"
   (← do
    pure (MESON_TAC [DIVSTEP_MAT_DIAGONAL]))

  /- Invariance of divstep_d and divstep_mat under congruences. -/

  let DIVSTEP_CONGRUENCE ← prove
   r"!m d f g f' g' n.
        (f == f') (mod (&2 pow m)) /\ (g == g') (mod (&2 pow m)) /\ n <= m
        ==> divstep_d n (d,f,g) = divstep_d n (d,f',g') /\
            divstep_mat n (d,f,g) = divstep_mat n (d,f',g') /\
            (divstep_f n (d,f,g) == divstep_f n (d,f',g'))
            (mod (&2 pow (m - n))) /\
            (divstep_g n (d,f,g) == divstep_g n (d,f',g'))
            (mod (&2 pow (m - n)))"
   (← do
    -- right to left: the INTEGER_RULE, then the ARITH_RULE (the final
    -- `CONV_TAC INTEGER_RULE` runs later, as a conversion)
    let i396 ← INTEGER_RULE
     (← q r"(a == b) (mod (c * d:int)) ==> (a == b) (mod c)")
    let a389 ← ARITH_RULE (← q r"SUC n <= m ==> n <= m")
    pure (REPLICATE_TAC 6 GEN_TAC THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
    INDUCT_TAC THEN
    ASM_REWRITE_TAC [divstep_mat, DIVSTEP_D, DIVSTEP_F, DIVSTEP_G, SUB_0] THEN
    DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o check (fun th => is_imp (concl th))) THEN
    FIRST_ASSUM (ASSUME_TAC o MATCH_MP a389) THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN (← q r"m - n = SUC(m - SUC n)") SUBST1_TAC THENL
     [ASM_ARITH_TAC, REWRITE_TAC [INT_POW]] THEN
    REPLICATE_TAC 2 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_TAC THEN
    FIRST_ASSUM (CONJUNCTS_THEN (fun th => tactic_of do
      pure (SUBST1_TAC (← REWRITE_RULE [← GSYM INT_REM_EQ] (← MATCH_MP i396 th))))) THEN
    ASM_REWRITE_TAC [] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
    REPEAT CONJ_TAC THEN TRY (MATCH_MP_TAC INT_CONG_DIV2) THEN
    POP_ASSUM_LIST (fun ths => tactic_of do
      pure (MP_TAC (← HolLight.end_itlist CONJ ths.reverse))) THEN
    CONV_TAC (fun t => (INTEGER_RULE t).run)))

  let DIVSTEP_D_CONGRUENCE ← prove
   r"!d f g f' g' n.
        (f == f') (mod (&2 pow n)) /\ (g == g') (mod (&2 pow n))
        ==> divstep_d n (d,f,g) = divstep_d n (d,f',g')"
   (← do
    pure (MESON_TAC [DIVSTEP_CONGRUENCE, LE_REFL]))

  let DIVSTEP_D_CONGRUENCE_GEN ← prove
   r"!d f g d' f' g' n.
        d = d' /\ (f == f') (mod (&2 pow n)) /\ (g == g') (mod (&2 pow n))
        ==> divstep_d n (d,f,g) = divstep_d n (d',f',g')"
   (← do
    pure (MESON_TAC [DIVSTEP_CONGRUENCE, LE_REFL]))

  let DIVSTEP_MAT_CONGRUENCE ← prove
   r"!d f g f' g' n.
        (f == f') (mod (&2 pow n)) /\ (g == g') (mod (&2 pow n))
        ==> divstep_mat n (d,f,g) = divstep_mat n (d,f',g')"
   (← do
    pure (MESON_TAC [DIVSTEP_CONGRUENCE, LE_REFL]))

  let DIVSTEP_MAT_CONGRUENCE_GEN ← prove
   r"!d f g d' f' g' n.
        d = d' /\ (f == f') (mod (&2 pow n)) /\ (g == g') (mod (&2 pow n))
        ==> divstep_mat n (d,f,g) = divstep_mat n (d',f',g')"
   (← do
    pure (MESON_TAC [DIVSTEP_CONGRUENCE, LE_REFL]))

  let DIVSTEP_D_MOD ← prove
   r"!m n d f g.
        m <= n
        ==> divstep_d m (d,f rem &2 pow n,g rem &2 pow n) =
            divstep_d m (d,f,g)"
   (← do
    let i1 ← INTEGER_RULE
     (← q r"!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)")
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC DIVSTEP_D_CONGRUENCE THEN
    CONJ_TAC THEN MATCH_MP_TAC i1 THEN
    EXISTS_TAC (← q r"(&2:int) pow n") THEN
    ASM_REWRITE_TAC [INT_CONG_LREM, INT_CONG_REFL] THEN
    ASM_SIMP_TAC [INT_DIVIDES_POW_LE_IMP]))

  let DIVSTEP_MAT_MOD ← prove
   r"!m n d f g.
        m <= n
        ==> divstep_mat m (d,f rem &2 pow n,g rem &2 pow n) =
            divstep_mat m (d,f,g)"
   (← do
    let i1 ← INTEGER_RULE
     (← q r"!m:int. (x == y) (mod m) /\ n divides m ==> (x == y) (mod n)")
    pure (REPEAT STRIP_TAC THEN MATCH_MP_TAC DIVSTEP_MAT_CONGRUENCE THEN
    CONJ_TAC THEN MATCH_MP_TAC i1 THEN
    EXISTS_TAC (← q r"(&2:int) pow n") THEN
    ASM_REWRITE_TAC [INT_CONG_LREM, INT_CONG_REFL] THEN
    ASM_SIMP_TAC [INT_DIVIDES_POW_LE_IMP]))

  /- Invariance of divstep_d and divstep_mat under negation. -/

  -- `let [A; B; C; D] = (CONJUNCTS o prove) (...)`
  let (DIVSTEP_D_NEG, DIVSTEP_MAT_NEG, DIVSTEP_F_NEG, DIVSTEP_G_NEG) ← do
    -- right to left: the INT_ARITHs from the last
    let i472 ← INT_ARITH (← q r"--x + y * --z:int = --(x + y * z)")
    let i471 ← INT_ARITH (← q r"--x - --y:int = --(x - y)")
    let th ← prove
     r"(!n d f g.
      f rem &2 = &1 ==> divstep_d n (d,--f,--g) = divstep_d n (d,f,g)) /\
   (!n d f g.
      f rem &2 = &1 ==>  divstep_mat n (d,--f,--g) = divstep_mat n (d,f,g)) /\
   (!n d f g.
      f rem &2 = &1 ==> divstep_f n (d,--f,--g) = --(divstep_f n (d,f,g))) /\
   (!n d f g.
      f rem &2 = &1 ==> divstep_g n (d,--f,--g) = --(divstep_g n (d,f,g)))"
     (REWRITE_TAC [AND_FORALL_THM] THEN
      REPLICATE_TAC 3 (GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC) THEN
      ASM_CASES_TAC (← q r"f rem &2 = &1") THEN ASM_REWRITE_TAC [] THEN
      INDUCT_TAC THEN
      ASM_REWRITE_TAC [DIVSTEP_D, DIVSTEP_F, DIVSTEP_G, divstep_mat] THEN
      REWRITE_TAC [INT_REM_2_NEG] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [i471] THEN
      REWRITE_TAC [i472] THEN
      ASM_REWRITE_TAC [INT_DIV_LNEG] THEN REWRITE_TAC [INT_REM_2_DIVIDES] THEN
      REWRITE_TAC [INT_2_DIVIDES_ADD, INT_2_DIVIDES_SUB, INT_2_DIVIDES_MUL] THEN
      REWRITE_TAC [← GSYM (← CONJUNCT1 INT_REM_2_DIVIDES)] THEN
      ASM_SIMP_TAC [INT_REM_REM, DIVSTEP_F_ODD] THEN
      CONV_TAC INT_REDUCE_CONV)
    match CONJUNCTS th with
    | [a, b, c, d] => pure (a, b, c, d)
    | _ => throw "Match_failure"

  let DIVSTEP_CONGRUENCE_NEG ← prove
   r"!m d f g f' g' n.
        (f == --f') (mod (&2 pow m)) /\ (g == --g') (mod (&2 pow m)) /\
        f rem &2 = &1 /\ n <= m
        ==> divstep_d n (d,f,g) = divstep_d n (d,f',g') /\
            divstep_mat n (d,f,g) = divstep_mat n (d,f',g') /\
            (divstep_f n (d,f,g) == --(divstep_f n (d,f',g')))
            (mod (&2 pow (m - n))) /\
            (divstep_g n (d,f,g) == --(divstep_g n (d,f',g')))
            (mod (&2 pow (m - n)))"
   (← do
    let i1 ← INTEGER_RULE
     (← q r"(--x:int == y) (mod p) <=> (x == --y) (mod p)")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (← SPECL
      [← q r"m:num", ← q r"d:int", ← q r"--f:int", ← q r"--g:int", ← q r"f':int",
       ← q r"g':int", ← q r"n:num"]
      DIVSTEP_CONGRUENCE) THEN
    ASM_SIMP_TAC [DIVSTEP_D_NEG, DIVSTEP_MAT_NEG,
                  DIVSTEP_F_NEG, DIVSTEP_G_NEG] THEN
    ASM_REWRITE_TAC [i1]))

  /- A slightly different version called "hddivstep" and analyzed here
     https://github.com/sipa/safegcd-bounds
     This uses > and so corresponds more exactly to the canonical divstep
     regardless of the parity of d. But when d is odd, it is the same as
     the main "idivstep" here. -/

  let hdivstep ← new_definition
   r"hdivstep(d:int,f:int,g:int) =
        if d > &0 /\ g rem &2 = &1
        then &2 - d, g, (g - f) div &2
        else &2 + d, f, (g + (g rem &2) * f) div &2"

  let HDIVSTEP_DIVSTEP ← prove
   r"hdivstep(d,f,g) = d',f',g' <=>
   divstep(real_of_int d / &2,f,g) = real_of_int d' / &2,f',g'"
   (← do
    -- right to left: the list's two REAL_ARITHs (last first), then the
    -- first REAL_ARITH
    let r520 ← REAL_ARITH (← q r"&1 + x / &2 = y / &2 <=> &2 + x = y")
    let r519 ← REAL_ARITH (← q r"&1 - x / &2 = y / &2 <=> &2 - x = y")
    let r515 ← REAL_ARITH (← q r"(x:real) / &2 > &0 <=> x > &0")
    pure (REWRITE_TAC [hdivstep, divstep] THEN
    REWRITE_TAC [r515] THEN
    REWRITE_TAC [int_gt, int_of_num_th] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [PAIR_EQ] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC [r519,
                 r520] THEN
    REWRITE_TAC [← GSYM REAL_OF_INT_CLAUSES]))

  let HDIVSTEP_IDIVSTEP ← prove
   r"!d f g. d rem &2 = &1 ==> hdivstep(d,f,g) = idivstep(d,f,g)"
   (← do
    let i1 ← INT_ARITH (← q r"d >= &0 <=> d:int = &0 \/ d > &0")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [idivstep, hdivstep] THEN
    REWRITE_TAC [i1] THEN
    ASM_CASES_TAC (← q r"d:int = &0") THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC INT_REDUCE_CONV))

  -- @@RETURN BEGIN
  return { divstep_mat, DIVSTEP_MAT, DIVSTEP_MAT_BOUNDS, DIVSTEP_MAT_ABS_BOUNDS,
           DIVSTEP_MAT_ADD, DIVSTEP_MAT_DIAGONAL, DIVSTEP_MAT_DIAGONAL_1,
           DIVSTEP_MAT_DIAGONAL_2, DIVSTEP_CONGRUENCE, DIVSTEP_D_CONGRUENCE,
           DIVSTEP_D_CONGRUENCE_GEN, DIVSTEP_MAT_CONGRUENCE, DIVSTEP_MAT_CONGRUENCE_GEN,
           DIVSTEP_D_MOD, DIVSTEP_MAT_MOD, DIVSTEP_D_NEG, DIVSTEP_MAT_NEG, DIVSTEP_F_NEG,
           DIVSTEP_G_NEG, DIVSTEP_CONGRUENCE_NEG, hdivstep, HDIVSTEP_DIVSTEP,
           HDIVSTEP_IDIVSTEP }
  -- @@RETURN END

end HolDivStep.IDivstep
