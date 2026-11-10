/- ========================================================================= -/
/- Specific formulas for evaluating (X,Z)-only projective point operations -/
/- ========================================================================= -/
/- File: HolEC/FormularyXZProjective.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/formulary_xzprojective.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/montgomery.ml, EC/xzprojective.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.FormularyXZProjective fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, INT_ARITH, TAUT, SET_RULE, ...) they are
  bound first, in OCaml's order.
-/

import HolLibrary.Iter
import HolLibrary.Prime
import HolLibrary.Pocklington
import HolLibrary.Integer
import HolLibrary.Isum
import HolLibrary.Binomial
import HolLibrary.Products
import HolLibrary.Multiplicative
import HolLibrary.Primitive
import HolLibrary.Frag
import HolLibrary.Wo
import HolLibrary.Card
import HolLibrary.GroupTheory
import HolLibrary.RingTheory
import HolEC.Misc
import HolEC.Montgomery
import HolEC.XZProjective

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolEC.FormularyXZProjective

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CONJ_ASSOC FIELD_CHAR_NOT2 FIELD_MUL_EQ_0 FORALL_OPTION_THM FORALL_PAIR_THM
   LET_DEF LET_END_DEF PAIR_EQ RING_0 RING_ADD RING_MUL RING_MUL_LZERO
   RING_MUL_RZERO RING_OF_NUM RING_OF_NUM_EQ_0 montgomery_add montgomery_curve
   montgomery_xz montgomery_xzdiffadd montgomery_xzdouble option_DISTINCT
   option_INJ : thm)
  deriving Inhabited

/-- What formulary_xzprojective.ml uses from Session besides theorems. -/
structure FormularyXZProjectiveDeps where
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
  PRIME_CONV : term → ExceptT String IO thm  -- pocklington.ml's PRIME_CONV
  RING_RULE : term → ExceptT String IO thm  -- ringtheory.ml's RING_RULE
  INTEGRAL_DOMAIN_RULE : term → ExceptT String IO thm
  FIELD_TAC : tactic  -- ringtheory.ml's FIELD_TAC
  RING_CARRIER_TAC : tactic
  RING_TAC : tactic
  RING_PULL_DIV_TAC : tactic
  LET_TAC : tactic
  GROUP_RULE : term → ExceptT String IO thm  -- grouptheory.ml's GROUP_RULE
  basic_ss : List thm → IO (Except String HolCore.Simp.simpset)
  INTEGER_MOD_RING_RED_CONV : ioconv
  NOT_RING_CHAR_DIVIDES_TAC : tactic  -- misc.ml's NOT_RING_CHAR_DIVIDES_TAC
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
/- Specific formulas for evaluating (X,Z)-only projective point operations.  -/
/- (formulary_xzprojective.ml 1-137)                                         -/
/- ------------------------------------------------------------------------- -/

structure FormularyXZProjectiveThms where
  -- @@FIELDS
  mladd_1987_m : thm
  MLADD_1987_M : thm
  okeya_sakurai_1 : thm
  OKEYA_SAKURAI_1 : thm
  deriving Inhabited

@[nospecialize]
def setupFormularyXZProjectiveThms [HolBase] (D : FormularyXZProjectiveDeps) :
    ExceptT String IO FormularyXZProjectiveThms := do
  -- @@SCOPE BEGIN
  let { FIELD_TAC, NOT_RING_CHAR_DIVIDES_TAC, RING_PULL_DIV_TAC, RING_RULE, basic_ss,
        let_CONV, new_definition, .. } := D
  let { CONJ_ASSOC, FIELD_CHAR_NOT2, FIELD_MUL_EQ_0, FORALL_OPTION_THM,
        FORALL_PAIR_THM, LET_DEF, LET_END_DEF, PAIR_EQ, RING_0, RING_ADD, RING_MUL,
        RING_MUL_LZERO, RING_MUL_RZERO, RING_OF_NUM, RING_OF_NUM_EQ_0, montgomery_add,
        montgomery_curve, montgomery_xz, montgomery_xzdiffadd, montgomery_xzdouble,
        option_DISTINCT, option_INJ, .. } := D.core1
  -- @@SCOPE END

  /- Montgomery ladder step, XZ-coordinate differential addition and
     doubling.

     Source: Montgomery [1987] "Speeding the Pollard and elliptic curve..."

     http://hyperelliptic.org/EFD/g1p/auto-code/montgom/xz/ladder/mladd-1987-m.op3 -/

  let mladd_1987_m ← new_definition
   r"mladd_1987_m (f:A ring,a:A,b:A) a24 X1 (X2,Z2) (X3,Z3) =
        let A = ring_add f X2 Z2 in
        let AA = ring_pow f A 2 in
        let B = ring_sub f X2 Z2 in
        let BB = ring_pow f B 2 in
        let E = ring_sub f AA BB in
        let C = ring_add f X3 Z3 in
        let D = ring_sub f X3 Z3 in
        let DA = ring_mul f D A in
        let CB = ring_mul f C B in
        let t0 = ring_add f DA CB in
        let X5 = ring_pow f t0 2 in
        let t1 = ring_sub f DA CB in
        let t2 = ring_pow f t1 2 in
        let Z5 = ring_mul f X1 t2 in
        let X4 = ring_mul f AA BB in
        let t3 = ring_mul f a24 E in
        let t4 = ring_add f BB t3 in
        let Z4 = ring_mul f E t4 in
        (X4,Z4),(X5,Z5)"

  let MLADD_1987_M ← prove
   r"!f (a:A) b a24 X1 X2 Z2 X3 Z3.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        a24 IN ring_carrier f /\ X1 IN ring_carrier f /\
        X2 IN ring_carrier f /\ Z2 IN ring_carrier f /\
        X3 IN ring_carrier f /\ Z3 IN ring_carrier f /\
        ring_mul f (ring_of_num f 4) a24 = ring_add f a (ring_of_num f 2)
        ==> mladd_1987_m (f,a,b) a24 X1 (X2,Z2) (X3,Z3) =
                (montgomery_xzdouble (f,a,b) (X2,Z2),
                 montgomery_xzdiffadd (f,a,b) (X1,ring_1 f) (X2,Z2) (X3,Z3))"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT2] THEN
    REWRITE_TAC [mladd_1987_m, montgomery_xzdouble, montgomery_xzdiffadd] THEN
    REPEAT STRIP_TAC THEN CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC [PAIR_EQ] THEN FIELD_TAC THEN
    NOT_RING_CHAR_DIVIDES_TAC))

  /- Recovering y coordinate within the projective representation.

     Source: Okeya and Sakurai [2001] "Efficient Elliptic Curve...", Alg. 1. -/

  let okeya_sakurai_1 ← new_definition
   r"okeya_sakurai_1 (f:A ring,a:A,b:A) (x,y) (X1,Z1) (X2,Z2) =
        let a2 = ring_add f a a
        and b2 = ring_add f b b in
        let t1 = ring_mul f x Z1 in
        let t2 = ring_add f X1 t1 in
        let t3 = ring_sub f X1 t1 in
        let t3 = ring_mul f t3 t3 in
        let t3 = ring_mul f t3 X2 in
        let t1 = ring_mul f a2 Z1 in
        let t2 = ring_add f t2 t1 in
        let t4 = ring_mul f x X1 in
        let t4 = ring_add f t4 Z1 in
        let t2 = ring_mul f t2 t4 in
        let t1 = ring_mul f t1 Z1 in
        let t2 = ring_sub f t2 t1 in
        let t2 = ring_mul f t2 Z2 in
        let y' = ring_sub f t2 t3 in
        let t1 = ring_mul f b2 y in
        let t1 = ring_mul f t1 Z1 in
        let t1 = ring_mul f t1 Z2 in
        let x' = ring_mul f t1 X1 in
        let z' = ring_mul f t1 Z1 in
        (x',y',z')"

  /- Note the overarching assumption that the initial point is non-trivial
     and has nonzero y coordinate, although we do handle degeneracy in the
     result point. -/

  let OKEYA_SAKURAI_1 ← prove
   r"!f (a:A) b x y p X1 Z1 X2 Z2.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\ ~(b = ring_0 f) /\
        montgomery_curve (f,a,b) (SOME(x,y)) /\ ~(y = ring_0 f) /\
        montgomery_curve (f,a,b) p /\
        montgomery_xz f p (X1,Z1) /\
        montgomery_xz f (montgomery_add(f,a,b) (SOME(x,y)) p) (X2,Z2)
        ==> let x',y',z' = okeya_sakurai_1 (f,a,b) (x,y) (X1,Z1) (X2,Z2) in
            p = if z' = ring_0 f then
                 (if Z1 = ring_0 f then NONE else SOME(x,ring_neg f y))
                else SOME(ring_div f x' z',ring_div f y' z')"
   (← do
    -- right to left: in `ASM (CONV_TAC o GEN_SIMPLIFY_CONV ..) [..]` the
    -- list (its RING_RULE) is evaluated before `basic_ss []`
    let r1 ← RING_RULE (← q r"ring_add f b b:A = ring_mul f (ring_of_num f 2) b")
    let ss ← ExceptT.mk (basic_ss [])
    pure (MAP_EVERY X_GEN_TAC [← q r"f:A ring", ← q r"a:A", ← q r"b:A", ← q r"x:A",
                               ← q r"y:A"] THEN
    REWRITE_TAC [FIELD_CHAR_NOT2, FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    REWRITE_TAC [montgomery_curve, montgomery_xz, okeya_sakurai_1] THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN
      REPEAT (DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
      SPEC_TAC (← q r"montgomery_add (f,a:A,b) (SOME(x,y)) NONE",
                ← q r"q:(A#A)option") THEN
      REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, montgomery_xz] THEN
      REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC [RING_MUL_LZERO, RING_MUL_RZERO, RING_0, RING_ADD, RING_MUL],
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [← q r"x1:A", ← q r"y1:A", ← q r"X1:A", ← q r"Z1:A",
                         ← q r"X2:A", ← q r"Z2:A"] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    ASM_SIMP_TAC [FIELD_MUL_EQ_0, RING_ADD, RING_MUL] THEN
    ASM_CASES_TAC (← q r"(X2:A) IN ring_carrier f /\ Z2 IN ring_carrier f") THENL
     [FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC) THEN
      ASM (HolLibrary.RingTheory.simpTac ss 5)
        [FIELD_MUL_EQ_0, RING_ADD, RING_MUL, RING_OF_NUM, RING_OF_NUM_EQ_0, r1],
      ASM_REWRITE_TAC [montgomery_add, LET_DEF, LET_END_DEF] THEN
      REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [montgomery_xz]) THEN
      ASM_REWRITE_TAC [CONJ_ASSOC]] THEN
    REWRITE_TAC [montgomery_add, LET_DEF, LET_END_DEF] THEN
    REPEAT (COND_CASES_TAC THEN
      ASM_REWRITE_TAC [montgomery_xz, option_DISTINCT, option_INJ, PAIR_EQ])
    THENL [FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC, FIELD_TAC, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(ring_of_num f 2:A = ring_0 f)") ASSUME_TAC THENL
     [FIELD_TAC, RING_PULL_DIV_TAC THEN DISCH_THEN SUBST1_TAC] THEN
    CONJ_TAC THENL [FIELD_TAC, ALL_TAC] THEN
    SUBGOAL_THEN (← q r"~(ring_sub f x1 x:A = ring_0 f)") ASSUME_TAC THENL
     [FIELD_TAC, RING_PULL_DIV_TAC THEN FIELD_TAC]))

  -- @@RETURN BEGIN
  return { mladd_1987_m, MLADD_1987_M, okeya_sakurai_1, OKEYA_SAKURAI_1 }
  -- @@RETURN END

end HolEC.FormularyXZProjective
