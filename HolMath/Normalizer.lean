/- File: Normalizer.lean
Relatively efficient HOL conversions for canonical polynomial form.
Original (c) Copyright, John Harrison 1998-2007
Lean4 translation by Chris Walton 2026 -/

import HolCore.Bool
import HolCore.Equal
import HolCore.Drule
import HolCore.Tactics
import HolCore.Itab
import HolCore.Simp
import HolCore.Parser
import HolCore.Printer
import HolCore.Nets
import HolCore.Theorems
import HolCore.IndDefs
import HolCore.Classic
import HolCore.Canon
import HolCore.Meson
import HolMath.Pair
import HolMath.Nums
import HolMath.Recursion
import HolMath.Arith
import HolMath.Wf
import HolMath.CalcNum
import HolMath.Base


namespace HolMath.Normalizer

set_option maxRecDepth 8000

section Structures

open HolCore HolCore.Kernel HolCore.Basics HolCore.Lib HolCore.Bool HolCore.Equal
     HolCore.Drule HolCore.Tactics HolCore.Itab HolCore.Simp HolCore.Parser
     HolCore.Theorems HolCore.IndDefs HolCore.Classic HolCore.Canon


/- ---------------------------------------------------------------------- -/
/- Relatively efficient HOL conversions for canonical polynomial form.    -/
/- ---------------------------------------------------------------------- -/

/-- The context captured by the currying layers of `SEMIRING_NORMALIZERS_CONV`.

    The OCaml is one deeply nested closure:
      `fun sth rth (is_semiring_constant, SEMIRING_ADD_CONV, SEMIRING_MUL_CONV,
        SEMIRING_POW_CONV) -> ... fun variable_order -> ...`
    capturing the 38 proformas obtained from `CONJUNCTS(MATCH_MP SEMIRING_PTHS
    sth)`, the term constants read back out of those proformas, the proforma
    variables, and the `rth`-dependent negation/subtraction data.  Lean has no
    closure conversion of that shape available at library level, so the captured
    environment is reified into this structure and every conversion takes it as
    a parameter.  Field names match the OCaml identifiers exactly. -/
structure SemiringCtx where
  /- `pthm_01 .. pthm_38 = CONJUNCTS(MATCH_MP SEMIRING_PTHS sth)`. -/
  pthm01 : thm
  pthm02 : thm
  pthm03 : thm
  pthm04 : thm
  pthm05 : thm
  pthm06 : thm
  pthm07 : thm
  pthm08 : thm
  pthm09 : thm
  pthm10 : thm
  pthm11 : thm
  pthm12 : thm
  pthm13 : thm
  pthm14 : thm
  pthm15 : thm
  pthm16 : thm
  pthm17 : thm
  pthm18 : thm
  pthm19 : thm
  pthm20 : thm
  pthm21 : thm
  pthm22 : thm
  pthm23 : thm
  pthm24 : thm
  pthm25 : thm
  pthm26 : thm
  pthm27 : thm
  pthm28 : thm
  pthm29 : thm
  pthm30 : thm
  pthm31 : thm
  pthm32 : thm
  pthm33 : thm
  pthm34 : thm
  pthm35 : thm
  pthm36 : thm
  pthm37 : thm
  pthm38 : thm
  /- Term constants read back out of the proformas (normalizer.ml 100-105). -/
  add_tm   : term
  mul_tm   : term
  pow_tm   : term
  zero_tm  : term
  one_tm   : term
  ty       : hol_type
  /- The proforma variables (normalizer.ml 107-121). -/
  p_tm     : term
  q_tm     : term
  zeron_tm : term
  onen_tm  : term
  a_tm     : term
  b_tm     : term
  c_tm     : term
  d_tm     : term
  lx_tm    : term
  ly_tm    : term
  m_tm     : term
  rx_tm    : term
  ry_tm    : term
  x_tm     : term
  y_tm     : term
  z_tm     : term
  /- The `rth`-dependent negation/subtraction data (normalizer.ml 131-142).
     When `concl rth = concl TRUTH` the OCaml supplies DUMMY values: `nthm_1`
     and `nthm_2` are `rth` itself, `sub_tm` and `neg_tm` are `true_tm`,
     `dest_sub` is `fun t -> t,t` and `is_sub` is `K false`.  `hasNeg` records
     which branch was taken so `dest_sub`/`is_sub` can reproduce it. -/
  nthm_1   : thm
  nthm_2   : thm
  sub_tm   : term
  neg_tm   : term
  hasNeg   : Bool
  /- The caller-supplied semiring operations. -/
  is_semiring_constant : term → Bool
  SEMIRING_ADD_CONV    : ioconv
  SEMIRING_MUL_CONV    : ioconv
  SEMIRING_POW_CONV    : ioconv
  /- The caller-supplied variable ordering (the innermost curried argument). -/
  variable_order       : term → term → Bool
  deriving Inhabited

/-- The six conversions returned by `SEMIRING_NORMALIZERS_CONV`
    (normalizer.ml 537-538). -/
structure PolynomialConvs where
  POLYNOMIAL_NEG_CONV : ioconv
  POLYNOMIAL_ADD_CONV : ioconv
  POLYNOMIAL_SUB_CONV : ioconv
  POLYNOMIAL_MUL_CONV : ioconv
  POLYNOMIAL_POW_CONV : ioconv
  POLYNOMIAL_CONV     : ioconv

/- ---------------------------------------------------------------------- -/
/- `SEMIRING_PTHS` (normalizer.ml 10-89): the 10-conjunct semiring         -/
/- hypothesis implying the 38-conjunct conclusion.  The conclusion order   -/
/- defines the `pthm_01 .. pthm_38` numbering the whole file indexes by,   -/
/- so it is reproduced verbatim and in order.  `add`, `mul`, `pwr`, `r0`,  -/
/- `r1` are FREE VARIABLES of type `A` (a generic semiring).               -/
/- ---------------------------------------------------------------------- -/

end Structures

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/-- `SEMIRING_PTHS` (normalizer.ml 10-89): the proforma theorems, for a
    generic semiring with operations `add`, `mul`, `pwr` and constants `r0`,
    `r1` as free variables of type `A`. -/
def SEMIRING_PTHS [HolBase] (ADD_CLAUSES MULT_CLAUSES : thm)
    (ASM_MESON_TAC : List thm → tactic)
    (INDUCT_TAC : tactic)
    (num_CONV' : term → IO (Except String thm)) :
    ExceptT String IO thm := do
  let num_CONV (t : term) : ExceptT String IO thm := num_CONV' t
  prove
   r"(!x:A y z. add x (add y z) = add (add x y) z) /\
     (!x y. add x y = add y x) /\
     (!x. add r0 x = x) /\
     (!x y z. mul x (mul y z) = mul (mul x y) z) /\
     (!x y. mul x y = mul y x) /\
     (!x. mul r1 x = x) /\
     (!x. mul r0 x = r0) /\
     (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
     (!x. pwr x 0 = r1) /\
     (!x n. pwr x (SUC n) = mul x (pwr x n))
     ==> (mul r1 x = x) /\
         (add (mul a m) (mul b m) = mul (add a b) m) /\
         (add (mul a m) m = mul (add a r1) m) /\
         (add m (mul a m) = mul (add a r1) m) /\
         (add m m = mul (add r1 r1) m) /\
         (mul r0 m = r0) /\
         (add r0 a = a) /\
         (add a r0 = a) /\
         (mul a b = mul b a) /\
         (mul (add a b) c = add (mul a c) (mul b c)) /\
         (mul r0 a = r0) /\
         (mul a r0 = r0) /\
         (mul r1 a = a) /\
         (mul a r1 = a) /\
         (mul (mul lx ly) (mul rx ry) = mul (mul lx rx) (mul ly ry)) /\
         (mul (mul lx ly) (mul rx ry) = mul lx (mul ly (mul rx ry))) /\
         (mul (mul lx ly) (mul rx ry) = mul rx (mul (mul lx ly) ry)) /\
         (mul (mul lx ly) rx = mul (mul lx rx) ly) /\
         (mul (mul lx ly) rx = mul lx (mul ly rx)) /\
         (mul lx rx = mul rx lx) /\
         (mul lx (mul rx ry) = mul (mul lx rx) ry) /\
         (mul lx (mul rx ry) = mul rx (mul lx ry)) /\
         (add (add a b) (add c d) = add (add a c) (add b d)) /\
         (add (add a b) c = add a (add b c)) /\
         (add a (add c d) = add c (add a d)) /\
         (add (add a b) c = add (add a c) b) /\
         (add a c = add c a) /\
         (add a (add c d) = add (add a c) d) /\
         (mul (pwr x p) (pwr x q) = pwr x (p + q)) /\
         (mul x (pwr x q) = pwr x (SUC q)) /\
         (mul (pwr x q) x = pwr x (SUC q)) /\
         (mul x x = pwr x 2) /\
         (pwr (mul x y) q = mul (pwr x q) (pwr y q)) /\
         (pwr (pwr x p) q = pwr x (p * q)) /\
         (pwr x 0 = r1) /\
         (pwr x 1 = x) /\
         (mul x (add y z) = add (mul x y) (mul x z)) /\
         (pwr x (SUC q) = mul x (pwr x q))"
   (STRIP_TAC THEN
    SUBGOAL_THEN
     (← q r"(!m:A n. add m n = add n m) /\
      (!m n p. add (add m n) p = add m (add n p)) /\
      (!m n p. add m (add n p) = add n (add m p)) /\
      (!x. add x r0 = x) /\
      (!m n. mul m n = mul n m) /\
      (!m n p. mul (mul m n) p = mul m (mul n p)) /\
      (!m n p. mul m (mul n p) = mul n (mul m p)) /\
      (!m n p. mul (add m n) p = add (mul m p) (mul n p)) /\
      (!x. mul x r1 = x) /\
      (!x. mul x r0 = r0)")
    MP_TAC THENL
     [ASM_MESON_TAC [],
      MAP_EVERY (fun t => UNDISCH_THEN t (K ALL_TAC : thm → tactic))
       [← q r"!x:A y z. add x (add y z) = add (add x y) z",
        ← q r"!x:A y. add x y :A = add y x",
        ← q r"!x:A y z. mul x (mul y z) = mul (mul x y) z",
        ← q r"!x:A y. mul x y :A = mul y x"] THEN
      STRIP_TAC] THEN
    ASM_REWRITE_TAC [← num_CONV (← q r"2"), ← num_CONV (← q r"1")] THEN
    SUBGOAL_THEN (← q r"!m n:num x:A. pwr x (m + n) :A = mul (pwr x m) (pwr x n)")
    ASSUME_TAC THENL
     [GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [ADD_CLAUSES], ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x:A y:A n:num. pwr (mul x y) n = mul (pwr x n) (pwr y n)")
    ASSUME_TAC THENL
     [GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"!x:A m:num n. pwr (pwr x m) n = pwr x (m * n)")
     (fun th => ASM_MESON_TAC [th]) THEN
    GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC [MULT_CLAUSES])

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic goal)
open HolLight

/-- `setupSemiringCtx` with `SEMIRING_PTHS` already proved.  In
    normalizer.ml `SEMIRING_PTHS` is proved once, when
    `SEMIRING_NORMALIZERS_CONV` itself is defined, not on each call; a
    caller that applies `SEMIRING_NORMALIZERS_CONV` after the core library
    loads (ringtheory.ml's RING_POLY_UNIVERSAL_CONV) passes the proved
    theorem here. -/
@[nospecialize]
def setupSemiringCtxFrom [HolBase]
    (SEMIRING_PTHS : thm)
    (TRUTH : thm)
    (sth rth : thm)
    (is_semiring_constant : term → Bool)
    (SEMIRING_ADD_CONV SEMIRING_MUL_CONV SEMIRING_POW_CONV : ioconv)
    (variable_order : term → term → Bool) :
    ExceptT String IO SemiringCtx := do
  let true_tm := concl TRUTH
  let pthms := (CONJUNCTS (← MATCH_MP SEMIRING_PTHS sth)).toArray
  if pthms.size != 38 then throw "SEMIRING_NORMALIZERS_CONV: expected 38 conjuncts"
  let pthm01 := pthms[0]!
  let pthm02 := pthms[1]!
  let pthm03 := pthms[2]!
  let pthm04 := pthms[3]!
  let pthm05 := pthms[4]!
  let pthm06 := pthms[5]!
  let pthm07 := pthms[6]!
  let pthm08 := pthms[7]!
  let pthm09 := pthms[8]!
  let pthm10 := pthms[9]!
  let pthm11 := pthms[10]!
  let pthm12 := pthms[11]!
  let pthm13 := pthms[12]!
  let pthm14 := pthms[13]!
  let pthm15 := pthms[14]!
  let pthm16 := pthms[15]!
  let pthm17 := pthms[16]!
  let pthm18 := pthms[17]!
  let pthm19 := pthms[18]!
  let pthm20 := pthms[19]!
  let pthm21 := pthms[20]!
  let pthm22 := pthms[21]!
  let pthm23 := pthms[22]!
  let pthm24 := pthms[23]!
  let pthm25 := pthms[24]!
  let pthm26 := pthms[25]!
  let pthm27 := pthms[26]!
  let pthm28 := pthms[27]!
  let pthm29 := pthms[28]!
  let pthm30 := pthms[29]!
  let pthm31 := pthms[30]!
  let pthm32 := pthms[31]!
  let pthm33 := pthms[32]!
  let pthm34 := pthms[33]!
  let pthm35 := pthms[34]!
  let pthm36 := pthms[35]!
  let pthm37 := pthms[36]!
  let pthm38 := pthms[37]!
  let add_tm ← liftExcept (do rator (← rator (← lhand (concl pthm07))))
  let mul_tm ← liftExcept (do rator (← rator (← lhand (concl pthm13))))
  let pow_tm ← liftExcept (do rator (← rator (← rand (concl pthm32))))
  let zero_tm ← liftExcept (rand (concl pthm06))
  let one_tm ← liftExcept (do rand (← lhand (concl pthm14)))
  let ty := type_of (← liftExcept (rand (concl pthm01)))
  let p_tm ← q r"p:num"
  let q_tm ← q r"q:num"
  let zeron_tm ← q r"0"
  let onen_tm ← q r"1"
  let a_tm := mk_var "a" ty
  let b_tm := mk_var "b" ty
  let c_tm := mk_var "c" ty
  let d_tm := mk_var "d" ty
  let lx_tm := mk_var "lx" ty
  let ly_tm := mk_var "ly" ty
  let m_tm := mk_var "m" ty
  let rx_tm := mk_var "rx" ty
  let ry_tm := mk_var "ry" ty
  let x_tm := mk_var "x" ty
  let y_tm := mk_var "y" ty
  let z_tm := mk_var "z" ty
  let (nthm_1, nthm_2, sub_tm, neg_tm, hasNeg) ←
    if concl rth == true_tm then pure (rth, rth, true_tm, true_tm, false)
    else do
      let nthm_1 ← SPEC x_tm (← CONJUNCT1 rth)
      let nthm_2 ← SPECL [x_tm, y_tm] (← CONJUNCT2 rth)
      let sub_tm ← liftExcept (do rator (← rator (← lhand (concl nthm_2))))
      let neg_tm ← liftExcept (do rator (← lhand (concl nthm_1)))
      pure (nthm_1, nthm_2, sub_tm, neg_tm, true)
  return {
    pthm01, pthm02, pthm03, pthm04, pthm05, pthm06, pthm07, pthm08, pthm09,
    pthm10, pthm11, pthm12, pthm13, pthm14, pthm15, pthm16, pthm17, pthm18,
    pthm19, pthm20, pthm21, pthm22, pthm23, pthm24, pthm25, pthm26, pthm27,
    pthm28, pthm29, pthm30, pthm31, pthm32, pthm33, pthm34, pthm35, pthm36,
    pthm37, pthm38,
    add_tm, mul_tm, pow_tm, zero_tm, one_tm, ty,
    p_tm, q_tm, zeron_tm, onen_tm, a_tm, b_tm, c_tm, d_tm, lx_tm, ly_tm, m_tm,
    rx_tm, ry_tm, x_tm, y_tm, z_tm,
    nthm_1, nthm_2, sub_tm, neg_tm, hasNeg,
    is_semiring_constant, SEMIRING_ADD_CONV, SEMIRING_MUL_CONV,
    SEMIRING_POW_CONV, variable_order }


/-- Build a `SemiringCtx` from `sth`, `rth`, the semiring operations and the
    variable ordering (normalizer.ml 90-142), from the `SEMIRING_PTHS` proved once
    in normalizer.ml. -/
@[nospecialize]
def setupSemiringCtx [HolBase]
    (TRUTH SEMIRING_PTHS : thm)
    (sth rth : thm)
    (is_semiring_constant : term → Bool)
    (SEMIRING_ADD_CONV SEMIRING_MUL_CONV SEMIRING_POW_CONV : ioconv)
    (variable_order : term → term → Bool) :
    ExceptT String IO SemiringCtx := do
  setupSemiringCtxFrom SEMIRING_PTHS TRUTH sth rth is_semiring_constant
    SEMIRING_ADD_CONV SEMIRING_MUL_CONV SEMIRING_POW_CONV variable_order

/-- `dest_add = dest_binop add_tm` (normalizer.ml 123). -/
def dest_add (K : SemiringCtx) (tm : term) : Except String (term × term) :=
  dest_binop K.add_tm tm

/-- `dest_mul = dest_binop mul_tm` (normalizer.ml 124). -/
def dest_mul (K : SemiringCtx) (tm : term) : Except String (term × term) :=
  dest_binop K.mul_tm tm

/-- `dest_pow` (normalizer.ml 125-127): fails unless the exponent is a
    numeral; callers use the failure to pick a branch. -/
def dest_pow (K : SemiringCtx) (tm : term) : Except String (term × term) := do
  let (l, r) ← dest_binop K.pow_tm tm
  if HolMath.Nums.is_numeral r then .ok (l, r) else failwith "dest_pow"

/-- `is_add = is_binop add_tm` (normalizer.ml 128). -/
def is_add (K : SemiringCtx) (tm : term) : Bool := is_binop K.add_tm tm

/-- `is_mul = is_binop mul_tm` (normalizer.ml 129). -/
def is_mul (K : SemiringCtx) (tm : term) : Bool := is_binop K.mul_tm tm

/-- `dest_sub` (normalizer.ml 134/141): `fun t -> t,t` when there is no
    negation. -/
def dest_sub (K : SemiringCtx) (tm : term) : Except String (term × term) :=
  if K.hasNeg then dest_binop K.sub_tm tm else .ok (tm, tm)

/-- `is_sub` (normalizer.ml 134/142): `K false` when there is no negation. -/
def is_sub (K : SemiringCtx) (tm : term) : Bool :=
  if K.hasNeg then is_binop K.sub_tm tm else false

/- ---------------------------------------------------------------------- -/
/- Conversion for "x^n * x^m", with either x^n = x and/or x^m = x possible.-/
/- Also deals with "const * const", but both terms must involve powers of -/
/- the same variable, or both be constants, or behaviour may be incorrect.-/
/- ---------------------------------------------------------------------- -/

/-- `POWVAR_MUL_CONV` (normalizer.ml 153-172). -/
def POWVAR_MUL_CONV [HolBase] (K : SemiringCtx) (NUM_ADD_CONV NUM_SUC_CONV : ioconv) : ioconv :=
  fun tm => ExceptT.run do
  let (l, r) ← liftExcept (dest_mul K tm)
  if K.is_semiring_constant l && K.is_semiring_constant r
  then ExceptT.mk (K.SEMIRING_MUL_CONV tm) else
  try
    let (lx, ln) ← liftExcept (dest_pow K l)
    tryWith (do
      let (_rx, rn) ← liftExcept (dest_pow K r)
      let th1 ← INST [(lx, K.x_tm), (ln, K.p_tm), (rn, K.q_tm)] K.pthm29
      let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
      TRANS th1 (← AP_TERM tm1 (← ExceptT.mk (NUM_ADD_CONV tm2))))
      (do
        let th1 ← INST [(lx, K.x_tm), (ln, K.q_tm)] K.pthm31
        let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
        TRANS th1 (← AP_TERM tm1 (← ExceptT.mk (NUM_SUC_CONV tm2))))
  catch _ =>
    try
      let (rx, rn) ← liftExcept (dest_pow K r)
      let th1 ← INST [(rx, K.x_tm), (rn, K.q_tm)] K.pthm30
      let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
      TRANS th1 (← AP_TERM tm1 (← ExceptT.mk (NUM_SUC_CONV tm2)))
    catch _ =>
      INST [(l, K.x_tm)] K.pthm32

/- ---------------------------------------------------------------------- -/
/- Remove "1 * m" from a monomial, and just leave m.                      -/
/- ---------------------------------------------------------------------- -/

/-- `MONOMIAL_DEONE` (normalizer.ml 178-182). -/
def MONOMIAL_DEONE [HolBase] (K : SemiringCtx) (th : thm) : ExceptT String IO thm := do
  try
    let (l, r) ← liftExcept (dest_mul K (← liftExcept (rand (concl th))))
    if l == K.one_tm then TRANS th (← INST [(r, K.x_tm)] K.pthm01) else pure th
  catch _ => pure th

/- ---------------------------------------------------------------------- -/
/- Conversion for "(monomial)^n", where n is a numeral.                   -/
/- ---------------------------------------------------------------------- -/

/-- `MONOMIAL_POW_CONV` (normalizer.ml 187-213). -/
partial def MONOMIAL_POW_CONV [HolBase] (K : SemiringCtx) (NUM_MULT_CONV : ioconv) : ioconv :=
  let rec MONOMIAL_POW (tm bod ntm : term) : ExceptT String IO thm := do
    if !(is_comb bod) then return REFL tm
    if K.is_semiring_constant bod then return ← ExceptT.mk (K.SEMIRING_POW_CONV tm)
    let (lop, r) ← liftExcept (dest_comb bod)
    if !(is_comb lop) then return REFL tm
    let (op, l) ← liftExcept (dest_comb lop)
    if op == K.pow_tm && HolMath.Nums.is_numeral r then
      let th1 ← INST [(l, K.x_tm), (r, K.p_tm), (ntm, K.q_tm)] K.pthm34
      let (l, r) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
      TRANS th1 (← AP_TERM l (← ExceptT.mk (NUM_MULT_CONV r)))
    else if op == K.mul_tm then
      let th1 ← INST [(l, K.x_tm), (r, K.y_tm), (ntm, K.q_tm)] K.pthm33
      let (xy, z) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
      let (x, y) ← liftExcept (dest_comb xy)
      let thl ← MONOMIAL_POW y l ntm
      let thr ← MONOMIAL_POW z r ntm
      TRANS th1 (← MK_COMB (← AP_TERM x thl, thr))
    else return REFL tm
  fun tm => ExceptT.run do
    let (lop, r) ← liftExcept (dest_comb tm)
    let (op, l) ← liftExcept (dest_comb lop)
    if op != K.pow_tm || !(HolMath.Nums.is_numeral r) then throw "MONOMIAL_POW_CONV"
    else if r == K.zeron_tm then INST [(l, K.x_tm)] K.pthm35
    else if r == K.onen_tm then INST [(l, K.x_tm)] K.pthm36
    else MONOMIAL_DEONE K (← MONOMIAL_POW tm l r)

/- ---------------------------------------------------------------------- -/
/- Multiplication of canonical monomials.                                 -/
/- ---------------------------------------------------------------------- -/

/-- `MONOMIAL_MUL_CONV` (normalizer.ml 218-292). -/
partial def MONOMIAL_MUL_CONV [HolBase] (K : SemiringCtx)
    (NUM_ADD_CONV NUM_SUC_CONV : ioconv) : ioconv :=
  let POWVAR_MUL_CONV := POWVAR_MUL_CONV K NUM_ADD_CONV NUM_SUC_CONV
  let powvar (tm : term) : term :=
    if K.is_semiring_constant tm then K.one_tm else
    match (do
      let (lop, r) ← dest_comb tm
      let (op, l) ← dest_comb lop
      if op == K.pow_tm && HolMath.Nums.is_numeral r then .ok l else failwith ""
      : Except String term) with
    | .ok v => v
    | .error _ => tm
  let vorder (x y : term) : Int :=
    if x == y then 0
    else if x == K.one_tm then -1
    else if y == K.one_tm then 1
    else if K.variable_order x y then -1 else 1
  let rec MONOMIAL_MUL (tm l r : term) : ExceptT String IO thm := do
    try
      let (lx, ly) ← liftExcept (dest_mul K l)
      let vl := powvar lx
      tryWith (do
        let (rx, ry) ← liftExcept (dest_mul K r)
        let vr := powvar rx
        let ord := vorder vl vr
        if ord == 0 then
          let th1 ← INST [(lx, K.lx_tm), (ly, K.ly_tm), (rx, K.rx_tm), (ry, K.ry_tm)] K.pthm15
          let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
          let (tm3, tm4) ← liftExcept (dest_comb tm1)
          let th2 ← AP_THM (← AP_TERM tm3 (← ExceptT.mk (POWVAR_MUL_CONV tm4))) tm2
          let th3 ← TRANS th1 th2
          let (tm5, tm6) ← liftExcept (dest_comb (← liftExcept (rand (concl th3))))
          let (tm7, tm8) ← liftExcept (dest_comb tm6)
          let th4 ← MONOMIAL_MUL tm6 (← liftExcept (rand tm7)) tm8
          TRANS th3 (← AP_TERM tm5 th4)
        else
          let th0 := if ord < 0 then K.pthm16 else K.pthm17
          let th1 ← INST [(lx, K.lx_tm), (ly, K.ly_tm), (rx, K.rx_tm), (ry, K.ry_tm)] th0
          let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
          let (tm3, tm4) ← liftExcept (dest_comb tm2)
          TRANS th1 (← AP_TERM tm1 (← MONOMIAL_MUL tm2 (← liftExcept (rand tm3)) tm4)))
        (do
          let vr := powvar r
          let ord := vorder vl vr
          if ord == 0 then
            let th1 ← INST [(lx, K.lx_tm), (ly, K.ly_tm), (r, K.rx_tm)] K.pthm18
            let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
            let (tm3, tm4) ← liftExcept (dest_comb tm1)
            let th2 ← AP_THM (← AP_TERM tm3 (← ExceptT.mk (POWVAR_MUL_CONV tm4))) tm2
            TRANS th1 th2
          else if ord < 0 then
            let th1 ← INST [(lx, K.lx_tm), (ly, K.ly_tm), (r, K.rx_tm)] K.pthm19
            let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
            let (tm3, tm4) ← liftExcept (dest_comb tm2)
            TRANS th1 (← AP_TERM tm1 (← MONOMIAL_MUL tm2 (← liftExcept (rand tm3)) tm4))
          else INST [(l, K.lx_tm), (r, K.rx_tm)] K.pthm20)
    catch _ =>
      let vl := powvar l
      try
        let (rx, ry) ← liftExcept (dest_mul K r)
        let vr := powvar rx
        let ord := vorder vl vr
        if ord == 0 then
          let th1 ← INST [(l, K.lx_tm), (rx, K.rx_tm), (ry, K.ry_tm)] K.pthm21
          let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
          let (tm3, tm4) ← liftExcept (dest_comb tm1)
          TRANS th1 (← AP_THM (← AP_TERM tm3 (← ExceptT.mk (POWVAR_MUL_CONV tm4))) tm2)
        else if ord > 0 then
          let th1 ← INST [(l, K.lx_tm), (rx, K.rx_tm), (ry, K.ry_tm)] K.pthm22
          let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
          let (tm3, tm4) ← liftExcept (dest_comb tm2)
          TRANS th1 (← AP_TERM tm1 (← MONOMIAL_MUL tm2 (← liftExcept (rand tm3)) tm4))
        else return REFL tm
      catch _ =>
        let vr := powvar r
        let ord := vorder vl vr
        if ord == 0 then ExceptT.mk (POWVAR_MUL_CONV tm)
        else if ord > 0 then INST [(l, K.lx_tm), (r, K.rx_tm)] K.pthm20
        else return REFL tm
  fun tm => ExceptT.run do
    let (l, r) ← liftExcept (dest_mul K tm)
    MONOMIAL_DEONE K (← MONOMIAL_MUL tm l r)

/- ---------------------------------------------------------------------- -/
/- Multiplication by monomial of a polynomial.                            -/
/- ---------------------------------------------------------------------- -/

/-- `POLYNOMIAL_MONOMIAL_MUL_CONV` (normalizer.ml 298-308). -/
partial def POLYNOMIAL_MONOMIAL_MUL_CONV [HolBase] (K : SemiringCtx)
    (NUM_ADD_CONV NUM_SUC_CONV : ioconv) : ioconv :=
  let MONOMIAL_MUL_CONV := MONOMIAL_MUL_CONV K NUM_ADD_CONV NUM_SUC_CONV
  let rec PMM_CONV (tm : term) : IO (Except String thm) := ExceptT.run do
    let (l, r) ← liftExcept (dest_mul K tm)
    try
      let (y, z) ← liftExcept (dest_add K r)
      let th1 ← INST [(l, K.x_tm), (y, K.y_tm), (z, K.z_tm)] K.pthm37
      let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
      let (tm3, tm4) ← liftExcept (dest_comb tm1)
      let thr ← ExceptT.mk (PMM_CONV tm2)
      let th2 ← MK_COMB (← AP_TERM tm3 (← ExceptT.mk (MONOMIAL_MUL_CONV tm4)), thr)
      TRANS th1 th2
    catch _ => ExceptT.mk (MONOMIAL_MUL_CONV tm)
  PMM_CONV

/- ---------------------------------------------------------------------- -/
/- Addition of two monomials identical except for constant multiples.     -/
/- ---------------------------------------------------------------------- -/

/-- `MONOMIAL_ADD_CONV` (normalizer.ml 314-334). -/
def MONOMIAL_ADD_CONV [HolBase] (K : SemiringCtx) : ioconv := fun tm => ExceptT.run do
  let (l, r) ← liftExcept (dest_add K tm)
  if K.is_semiring_constant l && K.is_semiring_constant r
  then return ← ExceptT.mk (K.SEMIRING_ADD_CONV tm)
  let lhandE (t : term) : ExceptT String IO term := liftExcept (lhand t)
  -- `is_mul t && is_semiring_constant(lhand t)`: `lhand` only runs when `is_mul` holds.
  let mulConst (t : term) : Bool :=
    is_mul K t && (match lhand t with
                   | .ok c => K.is_semiring_constant c
                   | .error _ => false)
  let th1 ← do
    if mulConst l then
      if mulConst r then
        INST [(← lhandE l, K.a_tm), (← lhandE r, K.b_tm), (← liftExcept (rand r), K.m_tm)] K.pthm02
      else
        INST [(← lhandE l, K.a_tm), (r, K.m_tm)] K.pthm03
    else
      if mulConst r then
        INST [(← lhandE r, K.a_tm), (l, K.m_tm)] K.pthm04
      else
        INST [(r, K.m_tm)] K.pthm05
  let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
  let (tm3, tm4) ← liftExcept (dest_comb tm1)
  let th2 ← AP_TERM tm3 (← ExceptT.mk (K.SEMIRING_ADD_CONV tm4))
  let th3 ← TRANS th1 (← AP_THM th2 tm2)
  let tm5 ← liftExcept (rand (concl th3))
  if (← lhandE tm5) == K.zero_tm then TRANS th3 (← INST [(← liftExcept (rand tm5), K.m_tm)] K.pthm06)
  else MONOMIAL_DEONE K th3

/- ---------------------------------------------------------------------- -/
/- Ordering on monomials.                                                 -/
/- ---------------------------------------------------------------------- -/

/-- `powervars` (normalizer.ml 340-342). -/
def powervars (K : SemiringCtx) (tm : term) : List term :=
  let ptms := striplist (dest_mul K) tm
  match ptms with
  | h :: t => if K.is_semiring_constant h then t else ptms
  | [] => ptms

/-- `dest_varpow` (normalizer.ml 344-347). -/
def dest_varpow (K : SemiringCtx) (tm : term) : term × Rat :=
  match (do let (x, n) ← dest_pow K tm; pure (x, ← dest_numeral n) : Except String (term × Rat)) with
  | .ok p => p
  | .error _ => (tm, if K.is_semiring_constant tm then num_0 else num_1)

/-- `morder` (normalizer.ml 349-367). -/
def morder (K : SemiringCtx) (tm1 tm2 : term) : Int :=
  let rec lexorder : List (term × Rat) → List (term × Rat) → Int
    | [], [] => 0
    | _ :: _, [] => -1
    | [], _ :: _ => 1
    | (x1, n1) :: vs1, (x2, n2) :: vs2 =>
      if K.variable_order x1 x2 then 1
      else if K.variable_order x2 x1 then -1
      else if n1 < n2 then -1
      else if n2 < n1 then 1
      else lexorder vs1 vs2
  let vdegs1 := (powervars K tm1).map (dest_varpow K)
  let vdegs2 := (powervars K tm2).map (dest_varpow K)
  let deg1 := itlist (fun (p : term × Rat) acc => p.2 + acc) vdegs1 num_0
  let deg2 := itlist (fun (p : term × Rat) acc => p.2 + acc) vdegs2 num_0
  if deg1 < deg2 then -1 else if deg1 > deg2 then 1
  else lexorder vdegs1 vdegs2

/- ---------------------------------------------------------------------- -/
/- Addition of two polynomials.                                           -/
/- ---------------------------------------------------------------------- -/

/-- `POLYNOMIAL_ADD_CONV` (normalizer.ml 373-440). -/
partial def POLYNOMIAL_ADD_CONV [HolBase] (K : SemiringCtx) : ioconv :=
  let MONOMIAL_ADD_CONV := MONOMIAL_ADD_CONV K
  let DEZERO_RULE (th : thm) : ExceptT String IO thm := do
    let tm ← liftExcept (rand (concl th))
    if !(is_add K tm) then return th
    let (lop, r) ← liftExcept (dest_comb tm)
    let l ← liftExcept (rand lop)
    if l == K.zero_tm then TRANS th (← INST [(r, K.a_tm)] K.pthm07)
    else if r == K.zero_tm then TRANS th (← INST [(l, K.a_tm)] K.pthm08)
    else return th
  let rec PADD (tm : term) : IO (Except String thm) := ExceptT.run do
    let (l, r) ← liftExcept (dest_add K tm)
    if l == K.zero_tm then return ← INST [(r, K.a_tm)] K.pthm07
    if r == K.zero_tm then return ← INST [(l, K.a_tm)] K.pthm08
    if is_add K l then
      let (a, b) ← liftExcept (dest_add K l)
      if is_add K r then
        let (c, d) ← liftExcept (dest_add K r)
        let ord := morder K a c
        if ord == 0 then
          let th1 ← INST [(a, K.a_tm), (b, K.b_tm), (c, K.c_tm), (d, K.d_tm)] K.pthm23
          let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
          let (tm3, tm4) ← liftExcept (dest_comb tm1)
          let th2 ← AP_TERM tm3 (← ExceptT.mk (MONOMIAL_ADD_CONV tm4))
          DEZERO_RULE (← TRANS th1 (← MK_COMB (th2, ← ExceptT.mk (PADD tm2))))
        else
          let th1 ←
            if ord > 0 then INST [(a, K.a_tm), (b, K.b_tm), (r, K.c_tm)] K.pthm24
            else INST [(l, K.a_tm), (c, K.c_tm), (d, K.d_tm)] K.pthm25
          let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
          DEZERO_RULE (← TRANS th1 (← AP_TERM tm1 (← ExceptT.mk (PADD tm2))))
      else
        let ord := morder K a r
        if ord == 0 then
          let th1 ← INST [(a, K.a_tm), (b, K.b_tm), (r, K.c_tm)] K.pthm26
          let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
          let (tm3, tm4) ← liftExcept (dest_comb tm1)
          let th2 ← AP_THM (← AP_TERM tm3 (← ExceptT.mk (MONOMIAL_ADD_CONV tm4))) tm2
          DEZERO_RULE (← TRANS th1 th2)
        else if ord > 0 then
          let th1 ← INST [(a, K.a_tm), (b, K.b_tm), (r, K.c_tm)] K.pthm24
          let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
          DEZERO_RULE (← TRANS th1 (← AP_TERM tm1 (← ExceptT.mk (PADD tm2))))
        else
          DEZERO_RULE (← INST [(l, K.a_tm), (r, K.c_tm)] K.pthm27)
    else
      if is_add K r then
        let (c, d) ← liftExcept (dest_add K r)
        let ord := morder K l c
        if ord == 0 then
          let th1 ← INST [(l, K.a_tm), (c, K.c_tm), (d, K.d_tm)] K.pthm28
          let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
          let (tm3, tm4) ← liftExcept (dest_comb tm1)
          let th2 ← AP_THM (← AP_TERM tm3 (← ExceptT.mk (MONOMIAL_ADD_CONV tm4))) tm2
          DEZERO_RULE (← TRANS th1 th2)
        else if ord > 0 then
          return REFL tm
        else
          let th1 ← INST [(l, K.a_tm), (c, K.c_tm), (d, K.d_tm)] K.pthm25
          let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
          DEZERO_RULE (← TRANS th1 (← AP_TERM tm1 (← ExceptT.mk (PADD tm2))))
      else
        let ord := morder K l r
        if ord == 0 then ExceptT.mk (MONOMIAL_ADD_CONV tm)
        else if ord > 0 then DEZERO_RULE (REFL tm)
        else DEZERO_RULE (← INST [(l, K.a_tm), (r, K.c_tm)] K.pthm27)
  PADD

/- ---------------------------------------------------------------------- -/
/- Multiplication of two polynomials.                                     -/
/- ---------------------------------------------------------------------- -/

/-- `POLYNOMIAL_MUL_CONV` (normalizer.ml 446-468). -/
partial def POLYNOMIAL_MUL_CONV [HolBase] (K : SemiringCtx)
    (NUM_ADD_CONV NUM_SUC_CONV : ioconv) : ioconv :=
  let POLYNOMIAL_MONOMIAL_MUL_CONV := POLYNOMIAL_MONOMIAL_MUL_CONV K NUM_ADD_CONV NUM_SUC_CONV
  let POLYNOMIAL_ADD_CONV := POLYNOMIAL_ADD_CONV K
  let rec PMUL (tm : term) : IO (Except String thm) := ExceptT.run do
    let (l, r) ← liftExcept (dest_mul K tm)
    if !(is_add K l) then ExceptT.mk (POLYNOMIAL_MONOMIAL_MUL_CONV tm)
    else if !(is_add K r) then
      let th1 ← INST [(l, K.a_tm), (r, K.b_tm)] K.pthm09
      TRANS th1 (← ExceptT.mk (POLYNOMIAL_MONOMIAL_MUL_CONV (← liftExcept (rand (concl th1)))))
    else
      let (a, b) ← liftExcept (dest_add K l)
      let th1 ← INST [(a, K.a_tm), (b, K.b_tm), (r, K.c_tm)] K.pthm10
      let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
      let (tm3, tm4) ← liftExcept (dest_comb tm1)
      let th2 ← AP_TERM tm3 (← ExceptT.mk (POLYNOMIAL_MONOMIAL_MUL_CONV tm4))
      let th3 ← TRANS th1 (← MK_COMB (th2, ← ExceptT.mk (PMUL tm2)))
      TRANS th3 (← ExceptT.mk (POLYNOMIAL_ADD_CONV (← liftExcept (rand (concl th3)))))
  fun tm => ExceptT.run do
    let (l, r) ← liftExcept (dest_mul K tm)
    if l == K.zero_tm then INST [(r, K.a_tm)] K.pthm11
    else if r == K.zero_tm then INST [(l, K.a_tm)] K.pthm12
    else if l == K.one_tm then INST [(r, K.a_tm)] K.pthm13
    else if r == K.one_tm then INST [(l, K.a_tm)] K.pthm14
    else ExceptT.mk (PMUL tm)

/- ---------------------------------------------------------------------- -/
/- Power of polynomial (optimized for the monomial and trivial cases).    -/
/- ---------------------------------------------------------------------- -/

/-- `POLYNOMIAL_POW_CONV` (normalizer.ml 474-487). -/
partial def POLYNOMIAL_POW_CONV [HolBase] (K : SemiringCtx)
    (NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV : ioconv)
    (num_CONV : term → IO (Except String thm)) : ioconv :=
  let POLYNOMIAL_MUL_CONV := POLYNOMIAL_MUL_CONV K NUM_ADD_CONV NUM_SUC_CONV
  let rec PPOW (tm : term) : IO (Except String thm) := ExceptT.run do
    let (l, n) ← liftExcept (dest_pow K tm)
    if n == K.zeron_tm then return ← INST [(l, K.x_tm)] K.pthm35
    if n == K.onen_tm then return ← INST [(l, K.x_tm)] K.pthm36
    let th1 ← ExceptT.mk (num_CONV n)
    let th2 ← INST [(l, K.x_tm), (← liftExcept (do rand (← rand (concl th1))), K.q_tm)] K.pthm38
    let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th2))))
    let th3 ← TRANS th2 (← AP_TERM tm1 (← ExceptT.mk (PPOW tm2)))
    let th4 ← TRANS (← AP_TERM (← liftExcept (rator tm)) th1) th3
    TRANS th4 (← ExceptT.mk (POLYNOMIAL_MUL_CONV (← liftExcept (rand (concl th4)))))
  fun tm => ExceptT.run do
    if is_add K (← liftExcept (lhand tm)) then ExceptT.mk (PPOW tm)
    else ExceptT.mk (MONOMIAL_POW_CONV K NUM_MULT_CONV tm)

/- ---------------------------------------------------------------------- -/
/- Negation.                                                              -/
/- ---------------------------------------------------------------------- -/

/-- `POLYNOMIAL_NEG_CONV` (normalizer.ml 493-498). -/
def POLYNOMIAL_NEG_CONV [HolBase] (K : SemiringCtx)
    (NUM_ADD_CONV NUM_SUC_CONV : ioconv) : ioconv := fun tm => ExceptT.run do
  let (l, r) ← liftExcept (dest_comb tm)
  if l != K.neg_tm then throw "POLYNOMIAL_NEG_CONV"
  let th1 ← INST [(r, K.x_tm)] K.nthm_1
  TRANS th1 (← ExceptT.mk (POLYNOMIAL_MONOMIAL_MUL_CONV K NUM_ADD_CONV NUM_SUC_CONV
                             (← liftExcept (rand (concl th1)))))

/- ---------------------------------------------------------------------- -/
/- Subtraction.                                                           -/
/- ---------------------------------------------------------------------- -/

/-- `POLYNOMIAL_SUB_CONV` (normalizer.ml 504-510). -/
def POLYNOMIAL_SUB_CONV [HolBase] (K : SemiringCtx)
    (NUM_ADD_CONV NUM_SUC_CONV : ioconv) : ioconv := fun tm => ExceptT.run do
  let (l, r) ← liftExcept (dest_sub K tm)
  let th1 ← INST [(l, K.x_tm), (r, K.y_tm)] K.nthm_2
  let (tm1, tm2) ← liftExcept (dest_comb (← liftExcept (rand (concl th1))))
  let th2 ← AP_TERM tm1 (← ExceptT.mk (POLYNOMIAL_MONOMIAL_MUL_CONV K NUM_ADD_CONV NUM_SUC_CONV tm2))
  TRANS th1 (← TRANS th2 (← ExceptT.mk (POLYNOMIAL_ADD_CONV K (← liftExcept (rand (concl th2))))))

/- ---------------------------------------------------------------------- -/
/- Conversion from HOL term.                                              -/
/- ---------------------------------------------------------------------- -/

/-- `POLYNOMIAL_CONV` (normalizer.ml 516-536). -/
partial def POLYNOMIAL_CONV [HolBase] (K : SemiringCtx)
    (NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV : ioconv)
    (num_CONV : term → IO (Except String thm)) : ioconv := fun tm => ExceptT.run do
  let POLYNOMIAL_CONV := POLYNOMIAL_CONV K NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV num_CONV
  if !(is_comb tm) || K.is_semiring_constant tm then return REFL tm
  let (lop, r) ← liftExcept (dest_comb tm)
  if lop == K.neg_tm then
    let th1 ← AP_TERM lop (← ExceptT.mk (POLYNOMIAL_CONV r))
    TRANS th1 (← ExceptT.mk (POLYNOMIAL_NEG_CONV K NUM_ADD_CONV NUM_SUC_CONV
                               (← liftExcept (rand (concl th1)))))
  else if !(is_comb lop) then return REFL tm
  else
    let (op, l) ← liftExcept (dest_comb lop)
    if op == K.pow_tm && HolMath.Nums.is_numeral r then
      let th1 ← AP_THM (← AP_TERM op (← ExceptT.mk (POLYNOMIAL_CONV l))) r
      TRANS th1 (← ExceptT.mk (POLYNOMIAL_POW_CONV K NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV
                                 num_CONV (← liftExcept (rand (concl th1)))))
    else if op == K.add_tm || op == K.mul_tm || op == K.sub_tm then
      let thr ← ExceptT.mk (POLYNOMIAL_CONV r)
      let th1 ← MK_COMB (← AP_TERM op (← ExceptT.mk (POLYNOMIAL_CONV l)), thr)
      let fn : ioconv :=
        if op == K.add_tm then POLYNOMIAL_ADD_CONV K
        else if op == K.mul_tm then POLYNOMIAL_MUL_CONV K NUM_ADD_CONV NUM_SUC_CONV
        else POLYNOMIAL_SUB_CONV K NUM_ADD_CONV NUM_SUC_CONV
      TRANS th1 (← ExceptT.mk (fn (← liftExcept (rand (concl th1)))))
    else return REFL tm

/-- `SEMIRING_NORMALIZERS_CONV` returns the six conversions in the OCaml
    tuple order (normalizer.ml 537-538).  `NUM_ADD_CONV`, `NUM_SUC_CONV`,
    `NUM_MULT_CONV` and `num_CONV` are calc_num's globals. -/
def SEMIRING_NORMALIZERS_CONV [HolBase] (K : SemiringCtx)
    (NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV : ioconv)
    (num_CONV : term → IO (Except String thm)) : PolynomialConvs :=
  { POLYNOMIAL_NEG_CONV := POLYNOMIAL_NEG_CONV K NUM_ADD_CONV NUM_SUC_CONV
    POLYNOMIAL_ADD_CONV := POLYNOMIAL_ADD_CONV K
    POLYNOMIAL_SUB_CONV := POLYNOMIAL_SUB_CONV K NUM_ADD_CONV NUM_SUC_CONV
    POLYNOMIAL_MUL_CONV := POLYNOMIAL_MUL_CONV K NUM_ADD_CONV NUM_SUC_CONV
    POLYNOMIAL_POW_CONV := POLYNOMIAL_POW_CONV K NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV num_CONV
    POLYNOMIAL_CONV     := POLYNOMIAL_CONV K NUM_ADD_CONV NUM_SUC_CONV NUM_MULT_CONV num_CONV }

/-- The OCaml `variable_order = (<)` on terms (normalizer.ml 563): `term`
    has the same constructor order as HOL Light's and derives `Ord`, so this
    is OCaml's polymorphic `<` on terms. -/
def variable_order (x y : term) : Bool := compare x y == Ordering.lt

end

section

open HolCore HolCore.Basics
open HolCore.Lib hiding rev end_itlist F_F
open HolCore.Kernel hiding ASSUME INST INST_TYPE TRANS EQ_MP MK_COMB
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Bool (BoolThms mk_neg mk_conj mk_disj mk_imp list_mk_forall list_mk_conj)
open HolCore.Classic (ClassThms)
open HolCore.Theorems (TheoremThms DSLThms)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal THEN)
open HolCore.Parser (parse_term)
open HolLight HolLight.Syntax

/-- The natural-number `SemiringCtx` (normalizer.ml 541-565): `sth` is the
    semiring theorem for `num`, `rth = TRUTH`, `is_semiring_constant =
    is_numeral`, the conversions are `NUM_ADD_CONV`, `NUM_MULT_CONV`,
    `NUM_EXP_CONV`, and `variable_order = (<)`. -/
@[nospecialize]
def setupNumNormalizeCtx' [HolBase]
    (TRUTH ADD_CLAUSES MULT_CLAUSES EXP LEFT_ADD_DISTRIB ADD_AC MULT_AC : thm)
    (ASM_MESON_TAC : List thm → tactic)
    (INDUCT_TAC : tactic)
    (num_CONV : term → IO (Except String thm))
    (NUM_ADD_CONV NUM_MULT_CONV NUM_EXP_CONV : ioconv) :
    ExceptT String IO (SemiringCtx × thm) := do
  let sth ← prove
   r"(!x y z. x + (y + z) = (x + y) + z) /\
     (!x y. x + y = y + x) /\
     (!x. 0 + x = x) /\
     (!x y z. x * (y * z) = (x * y) * z) /\
     (!x y. x * y = y * x) /\
     (!x. 1 * x = x) /\
     (!x. 0 * x = 0) /\
     (!x y z. x * (y + z) = x * y + x * z) /\
     (!x. x EXP 0 = 1) /\
     (!x n. x EXP (SUC n) = x * x EXP n)"
   (REWRITE_TAC [EXP, MULT_CLAUSES, ADD_CLAUSES, LEFT_ADD_DISTRIB] THEN
    REWRITE_TAC [ADD_AC, MULT_AC])
  let rth := TRUTH
  let SEMIRING_PTHS ← SEMIRING_PTHS ADD_CLAUSES MULT_CLAUSES ASM_MESON_TAC INDUCT_TAC num_CONV
  let ctx ← setupSemiringCtxFrom SEMIRING_PTHS TRUTH sth rth HolMath.Nums.is_numeral
    NUM_ADD_CONV NUM_MULT_CONV NUM_EXP_CONV variable_order
  return (ctx, SEMIRING_PTHS)


/-- `setupNumNormalizeCtx'` without the `SEMIRING_PTHS` result. -/
@[nospecialize]
def setupNumNormalizeCtx [HolBase]
    (TRUTH ADD_CLAUSES MULT_CLAUSES EXP LEFT_ADD_DISTRIB ADD_AC MULT_AC : thm)
    (ASM_MESON_TAC : List thm → tactic)
    (INDUCT_TAC : tactic)
    (num_CONV : term → IO (Except String thm))
    (NUM_ADD_CONV NUM_MULT_CONV NUM_EXP_CONV : ioconv) :
    ExceptT String IO SemiringCtx := do
  return (← setupNumNormalizeCtx' TRUTH ADD_CLAUSES MULT_CLAUSES EXP LEFT_ADD_DISTRIB
    ADD_AC MULT_AC ASM_MESON_TAC INDUCT_TAC num_CONV NUM_ADD_CONV NUM_MULT_CONV
    NUM_EXP_CONV).1

end

end HolMath.Normalizer
