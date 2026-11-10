/- ========================================================================= -/
/- Jacobian coordinates, (x,y,z) |-> (x/z^2,y/z^3), (1,1,0) |-> infinity.  -/
/- ========================================================================= -/
/- File: HolEC/Jacobian.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/jacobian.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/weierstrass.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.Jacobian fills them).

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
import HolEC.Weierstrass

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolEC.Jacobian

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (DE_MORGAN_THM FIELD_CHAR_NOT23 FIELD_IMP_INTEGRAL_DOMAIN FORALL_OPTION_THM
   FORALL_PAIR_THM LET_DEF LET_END_DEF PAIR_EQ RING_0 RING_1 RING_DIV RING_DIV_1
   RING_INV_POW RING_MUL_RZERO RING_POW RING_POW_ONE WEIERSTRASS_CURVE_IMP_POINT
   WEIERSTRASS_POINT_ADD WEIERSTRASS_POINT_NEG field option_DISTINCT option_INJ
   ring_div weierstrass_add weierstrass_curve weierstrass_neg weierstrass_point : thm)
  deriving Inhabited

/-- What jacobian.ml uses from Session besides theorems. -/
structure JacobianDeps where
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
/- Jacobian coordinates, (x,y,z) |-> (x/z^2,y/z^3) and (1,1,0) |-> infinity: -/
/- definitions and the correspondence with Weierstrass points.               -/
/- (jacobian.ml 1-195)                                                       -/
/- ------------------------------------------------------------------------- -/

structure JacobianDefs where
  -- @@FIELDS
  jacobian_point : thm
  jacobian_curve : thm
  weierstrass_of_jacobian : thm
  jacobian_of_weierstrass : thm
  jacobian_eq : thm
  jacobian_0 : thm
  jacobian_neg : thm
  jacobian_add : thm
  JACOBIAN_CURVE_IMP_POINT : thm
  JACOBIAN_OF_WEIERSTRASS_POINT_EQ : thm
  JACOBIAN_OF_WEIERSTRASS_POINT : thm
  WEIERSTRASS_OF_JACOBIAN_POINT : thm
  JACOBIAN_OF_WEIERSTRASS_EQ : thm
  WEIERSTRASS_OF_JACOBIAN_EQ : thm
  WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS : thm
  JACOBIAN_OF_WEIERSTRASS_OF_JACOBIAN : thm
  JACOBIAN_OF_WEIERSTRASS_CURVE_EQ : thm
  JACOBIAN_OF_WEIERSTRASS_CURVE : thm
  WEIERSTRASS_OF_JACOBIAN_CURVE : thm
  deriving Inhabited

@[nospecialize]
def setupJacobianDefs [HolBase] (D : JacobianDeps) :
    ExceptT String IO JacobianDefs := do
  -- @@SCOPE BEGIN
  let { FIELD_TAC, INTEGRAL_DOMAIN_RULE, MESON_TAC, define, new_definition, .. } := D
  let { FIELD_IMP_INTEGRAL_DOMAIN, FORALL_OPTION_THM, FORALL_PAIR_THM, PAIR_EQ, RING_0,
        RING_1, RING_DIV, RING_DIV_1, RING_MUL_RZERO, RING_POW, RING_POW_ONE,
        WEIERSTRASS_CURVE_IMP_POINT, field, option_DISTINCT, option_INJ,
        weierstrass_curve, weierstrass_point, .. } := D.core1
  -- @@SCOPE END

  let jacobian_point ← define
   r"jacobian_point f (x,y,z) <=>
        x IN ring_carrier f /\ y IN ring_carrier f /\ z IN ring_carrier f"

  let jacobian_curve ← define
   r"jacobian_curve (f,a:A,b) (x,y,z) <=>
        x IN ring_carrier f /\
        y IN ring_carrier f /\
        z IN ring_carrier f /\
        ring_pow f y 2 =
        ring_add f (ring_pow f x 3)
                   (ring_add f (ring_mul f a (ring_mul f x (ring_pow f z 4)))
                               (ring_mul f b (ring_pow f z 6)))"

  let weierstrass_of_jacobian ← define
   r"weierstrass_of_jacobian (f:A ring) (x,y,z) =
        if z = ring_0 f then NONE
        else SOME(ring_div f x (ring_pow f z 2),
                  ring_div f y (ring_pow f z 3))"

  let jacobian_of_weierstrass ← define
   r"jacobian_of_weierstrass (f:A ring) NONE = (ring_1 f,ring_1 f,ring_0 f) /\
  jacobian_of_weierstrass f (SOME(x,y)) = (x,y,ring_1 f)"

  let jacobian_eq ← define
   r"jacobian_eq (f:A ring) (x,y,z) (x',y',z') <=>
        (z = ring_0 f <=> z' = ring_0 f) /\
        ring_mul f x (ring_pow f z' 2) = ring_mul f x' (ring_pow f z 2) /\
        ring_mul f y (ring_pow f z' 3) = ring_mul f y' (ring_pow f z 3)"

  let jacobian_0 ← new_definition
   r"jacobian_0 (f:A ring,a:A,b:A) = (ring_1 f,ring_1 f,ring_0 f)"

  let jacobian_neg ← new_definition
   r"jacobian_neg (f,a:A,b:A) (x,y,z) = (x:A,ring_neg f y:A,z:A)"

  let jacobian_add ← new_definition
   r"jacobian_add (f:A ring,a,b) (x1,y1,z1) (x2,y2,z2) =
   if z1 = ring_0 f then (x2,y2,z2)
   else if z2 = ring_0 f then (x1,y1,z1)
   else if jacobian_eq f (x1,y1,z1) (x2,y2,z2) then
     let v = ring_mul f (ring_of_num f 4) (ring_mul f x1 (ring_pow f y1 2))
     and w =
       ring_add f (ring_mul f (ring_of_num f 3) (ring_pow f x1 2))
       (ring_mul f a (ring_pow f z1 4)) in
     let x3 =
       ring_add f (ring_mul f (ring_neg f (ring_of_num f 2)) v)
       (ring_pow f w 2) in
     x3,
     ring_add f (ring_mul f (ring_neg f (ring_of_num f 8)) (ring_pow f y1 4))
     (ring_mul f (ring_sub f v x3) w),
     ring_mul f (ring_of_num f 2) (ring_mul f y1 z1)
   else if jacobian_eq f (jacobian_neg (f,a,b) (x1,y1,z1)) (x2,y2,z2) then
     jacobian_0 (f,a,b)
   else
     let r = ring_mul f x1 (ring_pow f z2 2)
     and s = ring_mul f x2 (ring_pow f z1 2)
     and t = ring_mul f y1 (ring_pow f z2 3)
     and u = ring_mul f y2 (ring_pow f z1 3) in
     let v = ring_sub f s r
     and w = ring_sub f u t in
     let x3 =
         ring_add f
         (ring_sub f (ring_neg f (ring_pow f v 3))
         (ring_mul f (ring_of_num f 2) (ring_mul f r (ring_pow f v 2))))
         (ring_pow f w 2) in
     x3,
     ring_add f (ring_mul f (ring_neg f t) (ring_pow f v 3))
     (ring_mul f (ring_sub f (ring_mul f r (ring_pow f v 2)) x3) w),
     ring_mul f v (ring_mul f z1 z2)"

  let JACOBIAN_CURVE_IMP_POINT ← prove
   r"!f a b p. jacobian_curve(f,a,b) p ==> jacobian_point f p"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    SIMP_TAC [jacobian_curve, jacobian_point]))

  let JACOBIAN_OF_WEIERSTRASS_POINT_EQ ← prove
   r"!(f:A ring) p.
        jacobian_point f (jacobian_of_weierstrass f p) <=>
        weierstrass_point f p"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    REWRITE_TAC [weierstrass_point, jacobian_of_weierstrass] THEN
    SIMP_TAC [jacobian_point, RING_0, RING_1]))

  let JACOBIAN_OF_WEIERSTRASS_POINT ← prove
   r"!(f:A ring) p.
        weierstrass_point f p
        ==> jacobian_point f (jacobian_of_weierstrass f p)"
   (← do
    pure (REWRITE_TAC [JACOBIAN_OF_WEIERSTRASS_POINT_EQ]))

  let WEIERSTRASS_OF_JACOBIAN_POINT ← prove
   r"!(f:A ring) p.
        jacobian_point f p
        ==> weierstrass_point f (weierstrass_of_jacobian f p)"
   (← do
    pure (SIMP_TAC [FORALL_PAIR_THM, weierstrass_of_jacobian, jacobian_point] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [weierstrass_point, RING_DIV, RING_POW]))

  let JACOBIAN_OF_WEIERSTRASS_EQ ← prove
   r"!(f:A ring) p q.
        field f
        ==> (jacobian_of_weierstrass f p = jacobian_of_weierstrass f q <=>
             p = q)"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, field] THEN
    REWRITE_TAC [jacobian_of_weierstrass, option_DISTINCT, option_INJ] THEN
    SIMP_TAC [PAIR_EQ]))

  let WEIERSTRASS_OF_JACOBIAN_EQ ← prove
   r"!(f:A ring) p q.
        field f /\ jacobian_point f p /\ jacobian_point f q
        ==> (weierstrass_of_jacobian f p = weierstrass_of_jacobian f q <=>
             jacobian_eq f p q)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, jacobian_point] THEN
    REWRITE_TAC [weierstrass_of_jacobian, jacobian_eq] THEN
    REPEAT STRIP_TAC THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [option_INJ, option_DISTINCT]) THEN
    ASM_SIMP_TAC [RING_MUL_RZERO, PAIR_EQ] THEN
    FIELD_TAC))

  let WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS ← prove
   r"!(f:A ring) p.
        field f /\ weierstrass_point f p
        ==> weierstrass_of_jacobian f (jacobian_of_weierstrass f p) = p"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, field] THEN
    SIMP_TAC [weierstrass_of_jacobian, jacobian_of_weierstrass,
             weierstrass_point, RING_POW_ONE, RING_DIV_1]))

  let JACOBIAN_OF_WEIERSTRASS_OF_JACOBIAN ← prove
   r"!(f:A ring) p.
        field f /\ jacobian_point f p
        ==> jacobian_eq f
             (jacobian_of_weierstrass f (weierstrass_of_jacobian f p)) p"
   (← do
    pure (SIMP_TAC [← GSYM WEIERSTRASS_OF_JACOBIAN_EQ,
             WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS,
             JACOBIAN_OF_WEIERSTRASS_POINT_EQ,
             WEIERSTRASS_OF_JACOBIAN_POINT]))

  let JACOBIAN_OF_WEIERSTRASS_CURVE_EQ ← prove
   r"!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p
        ==> (jacobian_curve (f,a,b) (jacobian_of_weierstrass f p) <=>
             weierstrass_curve (f,a,b) p)"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, weierstrass_point] THEN
    REWRITE_TAC [weierstrass_curve, jacobian_of_weierstrass] THEN
    SIMP_TAC [jacobian_curve, RING_0, RING_1] THEN
    REPEAT STRIP_TAC THEN REPEAT (FIRST_X_ASSUM (MP_TAC o SYM)) THEN
    W (fun (_asl, w) => tactic_of do pure (MATCH_MP_TAC (← INTEGRAL_DOMAIN_RULE w))) THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))

  let JACOBIAN_OF_WEIERSTRASS_CURVE ← prove
   r"!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve (f,a,b) p
        ==> jacobian_curve (f,a,b) (jacobian_of_weierstrass f p)"
   (← do
    pure (MESON_TAC [JACOBIAN_OF_WEIERSTRASS_CURVE_EQ,
              WEIERSTRASS_CURVE_IMP_POINT]))

  let WEIERSTRASS_OF_JACOBIAN_CURVE ← prove
   r"!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_curve (f,a,b) p
        ==> weierstrass_curve (f,a,b) (weierstrass_of_jacobian f p)"
   (← do
    pure (SIMP_TAC [FORALL_PAIR_THM, weierstrass_of_jacobian, jacobian_curve] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [weierstrass_curve, RING_DIV, RING_POW] THEN
    FIELD_TAC))

  -- @@RETURN BEGIN
  return { jacobian_point, jacobian_curve, weierstrass_of_jacobian,
           jacobian_of_weierstrass, jacobian_eq, jacobian_0, jacobian_neg, jacobian_add,
           JACOBIAN_CURVE_IMP_POINT, JACOBIAN_OF_WEIERSTRASS_POINT_EQ,
           JACOBIAN_OF_WEIERSTRASS_POINT, WEIERSTRASS_OF_JACOBIAN_POINT,
           JACOBIAN_OF_WEIERSTRASS_EQ, WEIERSTRASS_OF_JACOBIAN_EQ,
           WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS, JACOBIAN_OF_WEIERSTRASS_OF_JACOBIAN,
           JACOBIAN_OF_WEIERSTRASS_CURVE_EQ, JACOBIAN_OF_WEIERSTRASS_CURVE,
           WEIERSTRASS_OF_JACOBIAN_CURVE }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Jacobian coordinates: negation and addition.  (jacobian.ml 196-343)     -/
/- ------------------------------------------------------------------------- -/

structure JacobianOps where
  -- @@FIELDS
  JACOBIAN_POINT_NEG : thm
  JACOBIAN_CURVE_NEG : thm
  WEIERSTRASS_OF_JACOBIAN_NEG : thm
  JACOBIAN_EQ_NEG : thm
  WEIERSTRASS_OF_JACOBIAN_NEG_OF_WEIERSTRASS : thm
  JACOBIAN_OF_WEIERSTRASS_NEG : thm
  JACOBIAN_POINT_ADD : thm
  JACOBIAN_CURVE_ADD : thm
  WEIERSTRASS_OF_JACOBIAN_ADD : thm
  JACOBIAN_EQ_ADD : thm
  WEIERSTRASS_OF_JACOBIAN_ADD_OF_WEIERSTRASS : thm
  JACOBIAN_OF_WEIERSTRASS_ADD : thm
  deriving Inhabited

@[nospecialize]
def setupJacobianOps [HolBase] (D : JacobianDeps) (BJacobianDefs : JacobianDefs) :
    ExceptT String IO JacobianOps := do
  -- @@SCOPE BEGIN
  let { FIELD_TAC, INTEGRAL_DOMAIN_RULE, LET_TAC, NOT_RING_CHAR_DIVIDES_TAC,
        RING_CARRIER_TAC, .. } := D
  let { DE_MORGAN_THM, FIELD_CHAR_NOT23, FIELD_IMP_INTEGRAL_DOMAIN, FORALL_PAIR_THM,
        LET_DEF, LET_END_DEF, PAIR_EQ, RING_INV_POW, WEIERSTRASS_POINT_ADD,
        WEIERSTRASS_POINT_NEG, option_DISTINCT, option_INJ, ring_div, weierstrass_add,
        weierstrass_neg, .. } := D.core1
  let { JACOBIAN_OF_WEIERSTRASS_POINT, WEIERSTRASS_OF_JACOBIAN_EQ,
        WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS, jacobian_0, jacobian_add,
        jacobian_curve, jacobian_eq, jacobian_neg, jacobian_point,
        weierstrass_of_jacobian, .. } := BJacobianDefs
  -- @@SCOPE END

  let JACOBIAN_POINT_NEG ← prove
   r"!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p
        ==> jacobian_point f (jacobian_neg (f,a,b) p)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, jacobian_neg, jacobian_point] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o SYM)) THEN
    W (fun (_asl, w) => tactic_of do pure (MATCH_MP_TAC (← INTEGRAL_DOMAIN_RULE w))) THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))

  let JACOBIAN_CURVE_NEG ← prove
   r"!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_curve (f,a,b) p
        ==> jacobian_curve (f,a,b) (jacobian_neg (f,a,b) p)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, jacobian_neg, jacobian_curve] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o SYM)) THEN
    W (fun (_asl, w) => tactic_of do pure (MATCH_MP_TAC (← INTEGRAL_DOMAIN_RULE w))) THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))

  let WEIERSTRASS_OF_JACOBIAN_NEG ← prove
   r"!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p
        ==> weierstrass_of_jacobian f (jacobian_neg (f,a,b) p) =
            weierstrass_neg (f,a,b) (weierstrass_of_jacobian f p)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, jacobian_neg, weierstrass_of_jacobian,
                jacobian_point] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [weierstrass_neg, option_INJ, PAIR_EQ] THEN
    FIELD_TAC))

  let JACOBIAN_EQ_NEG ← prove
   r"!(f:A ring) a b p p'.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p /\ jacobian_point f p' /\ jacobian_eq f p p'
        ==> jacobian_eq f
              (jacobian_neg (f,a,b) p) (jacobian_neg (f,a,b) p')"
   (← do
    pure (REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC [← GSYM WEIERSTRASS_OF_JACOBIAN_EQ, JACOBIAN_POINT_NEG] THEN
    ASM_SIMP_TAC [WEIERSTRASS_OF_JACOBIAN_NEG]))

  let WEIERSTRASS_OF_JACOBIAN_NEG_OF_WEIERSTRASS ← prove
   r"!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p
        ==> weierstrass_of_jacobian f
             (jacobian_neg (f,a,b) (jacobian_of_weierstrass f p)) =
            weierstrass_neg (f,a,b) p"
   (← do
    pure (SIMP_TAC [WEIERSTRASS_OF_JACOBIAN_NEG,
             JACOBIAN_OF_WEIERSTRASS_POINT,
             WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS]))

  let JACOBIAN_OF_WEIERSTRASS_NEG ← prove
   r"!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p
        ==> jacobian_eq f
             (jacobian_of_weierstrass f (weierstrass_neg (f,a,b) p))
             (jacobian_neg (f,a,b) (jacobian_of_weierstrass f p))"
   (← do
    pure (SIMP_TAC [← GSYM WEIERSTRASS_OF_JACOBIAN_EQ,
             JACOBIAN_OF_WEIERSTRASS_POINT,
             JACOBIAN_POINT_NEG, WEIERSTRASS_POINT_NEG,
             WEIERSTRASS_OF_JACOBIAN_NEG,
             WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS]))

  let JACOBIAN_POINT_ADD ← prove
   r"!(f:A ring) a b p q.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p /\ jacobian_point f q
        ==> jacobian_point f (jacobian_add (f,a,b) p q)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, jacobian_add, jacobian_point,
                jacobian_0, jacobian_eq, LET_DEF, LET_END_DEF] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    REPEAT (COND_CASES_TAC THEN
     ASM_REWRITE_TAC [jacobian_add, jacobian_point,
                jacobian_eq, LET_DEF, LET_END_DEF]) THEN
    REPEAT STRIP_TAC THEN RING_CARRIER_TAC))

  let JACOBIAN_CURVE_ADD ← prove
   r"!(f:A ring) a b p q.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_curve (f,a,b) p /\ jacobian_curve (f,a,b) q
        ==> jacobian_curve (f,a,b) (jacobian_add (f,a,b) p q)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, jacobian_add, jacobian_curve,
                jacobian_0, jacobian_eq, LET_DEF, LET_END_DEF] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    REPEAT (COND_CASES_TAC THEN
     ASM_REWRITE_TAC [jacobian_add, jacobian_curve,
                jacobian_eq, LET_DEF, LET_END_DEF]) THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o SYM)) THEN
    W (fun (_asl, w) => tactic_of do pure (MATCH_MP_TAC (← INTEGRAL_DOMAIN_RULE w))) THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))

  let WEIERSTRASS_OF_JACOBIAN_ADD ← prove
   r"!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p /\ jacobian_point f q
        ==> weierstrass_of_jacobian f (jacobian_add (f,a,b) p q) =
            weierstrass_add (f,a,b)
             (weierstrass_of_jacobian f p)
             (weierstrass_of_jacobian f q)"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT23, FORALL_PAIR_THM, jacobian_point] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"f:A ring", ← q r"a:A", ← q r"b:A", ← q r"x1:A", ← q r"y1:A", ← q r"z1:A",
      ← q r"x2:A", ← q r"y2:A", ← q r"z2:A"] THEN
    STRIP_TAC THEN REWRITE_TAC [weierstrass_of_jacobian, jacobian_add] THEN
    MAP_EVERY ASM_CASES_TAC [← q r"z1:A = ring_0 f", ← q r"z2:A = ring_0 f"] THEN
    ASM_REWRITE_TAC [weierstrass_of_jacobian, weierstrass_add] THEN
    ASM_REWRITE_TAC [jacobian_eq, jacobian_neg, jacobian_0] THEN
    ASM_SIMP_TAC [ring_div, RING_INV_POW] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REWRITE_TAC [LET_DEF, LET_END_DEF] THEN
    REPEAT LET_TAC THEN REWRITE_TAC [weierstrass_of_jacobian] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REWRITE_TAC [option_DISTINCT, option_INJ, PAIR_EQ] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [DE_MORGAN_THM]) THEN
    REPEAT (FIRST_X_ASSUM DISJ_CASES_TAC ORELSE
           FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  let JACOBIAN_EQ_ADD ← prove
   r"!(f:A ring) a b p p' q q'.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p /\ jacobian_point f p' /\
        jacobian_point f q /\ jacobian_point f q' /\
        jacobian_eq f p p' /\ jacobian_eq f q q'
        ==> jacobian_eq f
              (jacobian_add (f,a,b) p q) (jacobian_add (f,a,b) p' q')"
   (← do
    pure (REPEAT GEN_TAC THEN
    REPLICATE_TAC 9 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC [← GSYM WEIERSTRASS_OF_JACOBIAN_EQ, JACOBIAN_POINT_ADD] THEN
    ASM_SIMP_TAC [WEIERSTRASS_OF_JACOBIAN_ADD]))

  let WEIERSTRASS_OF_JACOBIAN_ADD_OF_WEIERSTRASS ← prove
   r"!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p /\ weierstrass_point f q
        ==> weierstrass_of_jacobian f
             (jacobian_add (f,a,b)
               (jacobian_of_weierstrass f p)
               (jacobian_of_weierstrass f q)) =
            weierstrass_add (f,a,b) p q"
   (← do
    pure (SIMP_TAC [WEIERSTRASS_OF_JACOBIAN_ADD,
             JACOBIAN_OF_WEIERSTRASS_POINT,
             WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS]))

  let JACOBIAN_OF_WEIERSTRASS_ADD ← prove
   r"!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p /\ weierstrass_point f q
        ==> jacobian_eq f
             (jacobian_of_weierstrass f (weierstrass_add (f,a,b) p q))
             (jacobian_add (f,a,b)
               (jacobian_of_weierstrass f p)
               (jacobian_of_weierstrass f q))"
   (← do
    pure (SIMP_TAC [← GSYM WEIERSTRASS_OF_JACOBIAN_EQ,
             JACOBIAN_OF_WEIERSTRASS_POINT,
             JACOBIAN_POINT_ADD, WEIERSTRASS_POINT_ADD,
             WEIERSTRASS_OF_JACOBIAN_ADD,
             WEIERSTRASS_OF_JACOBIAN_OF_WEIERSTRASS]))

  -- @@RETURN BEGIN
  return { JACOBIAN_POINT_NEG, JACOBIAN_CURVE_NEG, WEIERSTRASS_OF_JACOBIAN_NEG,
           JACOBIAN_EQ_NEG, WEIERSTRASS_OF_JACOBIAN_NEG_OF_WEIERSTRASS,
           JACOBIAN_OF_WEIERSTRASS_NEG, JACOBIAN_POINT_ADD, JACOBIAN_CURVE_ADD,
           WEIERSTRASS_OF_JACOBIAN_ADD, JACOBIAN_EQ_ADD,
           WEIERSTRASS_OF_JACOBIAN_ADD_OF_WEIERSTRASS, JACOBIAN_OF_WEIERSTRASS_ADD }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Some simpler variants that don't take such care over special cases.       -/
/- (jacobian.ml 344-438)                                                     -/
/- ------------------------------------------------------------------------- -/

structure JacobianUnexc where
  -- @@FIELDS
  jacobian_add_unexceptional : thm
  WEIERSTRASS_OF_JACOBIAN_ADD_UNEXCEPTIONAL : thm
  jacobian_double_unexceptional : thm
  WEIERSTRASS_OF_JACOBIAN_DOUBLE_UNEXCEPTIONAL : thm
  deriving Inhabited

@[nospecialize]
def setupJacobianUnexc [HolBase] (D : JacobianDeps) (BJacobianDefs : JacobianDefs) :
    ExceptT String IO JacobianUnexc := do
  -- @@SCOPE BEGIN
  let { FIELD_TAC, LET_TAC, NOT_RING_CHAR_DIVIDES_TAC, new_definition, .. } := D
  let { DE_MORGAN_THM, FIELD_CHAR_NOT23, FORALL_PAIR_THM, LET_DEF, LET_END_DEF,
        PAIR_EQ, RING_INV_POW, option_DISTINCT, option_INJ, ring_div, weierstrass_add, .. } := D.core1
  let { jacobian_0, jacobian_eq, jacobian_neg, jacobian_point, weierstrass_of_jacobian, .. } := BJacobianDefs
  -- @@SCOPE END

  let jacobian_add_unexceptional ← new_definition
   r"jacobian_add_unexceptional (f:A ring,a:A,b:A) (x1,y1,z1) (x2,y2,z2) =
   if z1 = ring_0 f then (x2,y2,z2)
   else if z2 = ring_0 f then (x1,y1,z1)
   else
     let r = ring_mul f x1 (ring_pow f z2 2)
     and s = ring_mul f x2 (ring_pow f z1 2)
     and t = ring_mul f y1 (ring_pow f z2 3)
     and u = ring_mul f y2 (ring_pow f z1 3) in
     let v = ring_sub f s r
     and w = ring_sub f u t in
     let x3 =
         ring_add f
         (ring_sub f (ring_neg f (ring_pow f v 3))
         (ring_mul f (ring_of_num f 2) (ring_mul f r (ring_pow f v 2))))
         (ring_pow f w 2) in
     x3,
     ring_add f (ring_mul f (ring_neg f t) (ring_pow f v 3))
     (ring_mul f (ring_sub f (ring_mul f r (ring_pow f v 2)) x3) w),
     ring_mul f v (ring_mul f z1 z2)"

  let WEIERSTRASS_OF_JACOBIAN_ADD_UNEXCEPTIONAL ← prove
   r"!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f p /\ jacobian_point f q /\
        ~(jacobian_eq f p q)
        ==> weierstrass_of_jacobian f (jacobian_add_unexceptional (f,a,b) p q) =
            weierstrass_add (f,a,b)
             (weierstrass_of_jacobian f p)
             (weierstrass_of_jacobian f q)"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT23, FORALL_PAIR_THM, jacobian_point] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"f:A ring", ← q r"a:A", ← q r"b:A", ← q r"x1:A", ← q r"y1:A", ← q r"z1:A",
      ← q r"x2:A", ← q r"y2:A", ← q r"z2:A"] THEN
    REWRITE_TAC [weierstrass_of_jacobian, jacobian_add_unexceptional] THEN
    REWRITE_TAC [jacobian_eq] THEN
    MAP_EVERY ASM_CASES_TAC [← q r"z1:A = ring_0 f", ← q r"z2:A = ring_0 f"] THEN
    ASM_REWRITE_TAC [weierstrass_of_jacobian, weierstrass_add] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [jacobian_neg, jacobian_0] THEN
    ASM_SIMP_TAC [ring_div, RING_INV_POW] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REWRITE_TAC [LET_DEF, LET_END_DEF] THEN
    REPEAT LET_TAC THEN REWRITE_TAC [weierstrass_of_jacobian] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REWRITE_TAC [option_DISTINCT, option_INJ, PAIR_EQ] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [DE_MORGAN_THM]) THEN
    REPEAT (FIRST_X_ASSUM DISJ_CASES_TAC ORELSE
           FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  let jacobian_double_unexceptional ← new_definition
   r"jacobian_double_unexceptional (f:A ring,a:A,b:A) (x1,y1,z1) =
     let v = ring_mul f (ring_of_num f 4) (ring_mul f x1 (ring_pow f y1 2))
     and w =
       ring_add f (ring_mul f (ring_of_num f 3) (ring_pow f x1 2))
       (ring_mul f a (ring_pow f z1 4)) in
     let x3 =
       ring_add f (ring_mul f (ring_neg f (ring_of_num f 2)) v)
       (ring_pow f w 2) in
     x3,
     ring_add f (ring_mul f (ring_neg f (ring_of_num f 8)) (ring_pow f y1 4))
     (ring_mul f (ring_sub f v x3) w),
     ring_mul f (ring_of_num f 2) (ring_mul f y1 z1)"

  let WEIERSTRASS_OF_JACOBIAN_DOUBLE_UNEXCEPTIONAL ← prove
   r"!(f:A ring) a b p.
      field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      jacobian_point f p
      ==> weierstrass_of_jacobian f (jacobian_double_unexceptional (f,a,b) p) =
          weierstrass_add (f,a,b)
           (weierstrass_of_jacobian f p)
           (weierstrass_of_jacobian f p)"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT23, FORALL_PAIR_THM, jacobian_point] THEN
    MAP_EVERY X_GEN_TAC [← q r"f:A ring", ← q r"a:A", ← q r"b:A", ← q r"x1:A",
                         ← q r"y1:A", ← q r"z1:A"] THEN
    REWRITE_TAC [weierstrass_of_jacobian, jacobian_double_unexceptional] THEN
    ASM_CASES_TAC (← q r"z1:A = ring_0 f") THEN
    ASM_REWRITE_TAC [weierstrass_of_jacobian, weierstrass_add] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [jacobian_neg, jacobian_0] THEN
    ASM_SIMP_TAC [ring_div, RING_INV_POW] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REWRITE_TAC [LET_DEF, LET_END_DEF] THEN
    REPEAT LET_TAC THEN REWRITE_TAC [weierstrass_of_jacobian] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REWRITE_TAC [option_DISTINCT, option_INJ, PAIR_EQ] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [DE_MORGAN_THM]) THEN
    REPEAT (FIRST_X_ASSUM DISJ_CASES_TAC ORELSE
           FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  -- @@RETURN BEGIN
  return { jacobian_add_unexceptional, WEIERSTRASS_OF_JACOBIAN_ADD_UNEXCEPTIONAL,
           jacobian_double_unexceptional, WEIERSTRASS_OF_JACOBIAN_DOUBLE_UNEXCEPTIONAL }
  -- @@RETURN END

end HolEC.Jacobian
