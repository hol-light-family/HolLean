/- ========================================================================= -/
/- Projective coordinates, (x,y,z) |-> (x/z,y/z), (0,1,0) |-> infinity.    -/
/- ========================================================================= -/
/- File: HolEC/Projective.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/projective.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/weierstrass.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.Projective fills them).

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

namespace HolEC.Projective

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (CONJ_ASSOC DE_MORGAN_THM FIELD_CHAR_NOT23 FIELD_IMP_INTEGRAL_DOMAIN
   FIELD_MUL_LINV FORALL_OPTION_THM FORALL_PAIR_THM IMP_CONJ_ALT LET_DEF
   LET_END_DEF PAIR_EQ RING_0 RING_1 RING_DIV RING_DIV_1 RING_INV RING_MUL_RZERO
   WEIERSTRASS_CURVE_IMP_POINT WEIERSTRASS_POINT_ADD WEIERSTRASS_POINT_NEG field
   option_DISTINCT option_INJ ring_div weierstrass_add weierstrass_curve
   weierstrass_neg weierstrass_point : thm)
  deriving Inhabited

/-- What projective.ml uses from Session besides theorems. -/
structure ProjectiveDeps where
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
/- Projective coordinates, (x,y,z) |-> (x/z,y/z) and (0,1,0) |-> infinity:   -/
/- definitions and the correspondence with Weierstrass points.               -/
/- (projective.ml 1-201)                                                     -/
/- ------------------------------------------------------------------------- -/

structure ProjectiveDefs where
  -- @@FIELDS
  projective_point : thm
  projective_curve : thm
  weierstrass_of_projective : thm
  projective_of_weierstrass : thm
  projective_eq : thm
  projective_0 : thm
  projective_neg : thm
  projective_add : thm
  PROJECTIVE_CURVE_IMP_POINT : thm
  PROJECTIVE_OF_WEIERSTRASS_POINT_EQ : thm
  PROJECTIVE_OF_WEIERSTRASS_POINT : thm
  WEIERSTRASS_OF_PROJECTIVE_POINT : thm
  PROJECTIVE_OF_WEIERSTRASS_EQ : thm
  WEIERSTRASS_OF_PROJECTIVE_EQ : thm
  WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS : thm
  PROJECTIVE_OF_WEIERSTRASS_OF_PROJECTIVE : thm
  PROJECTIVE_OF_WEIERSTRASS_CURVE_EQ : thm
  PROJECTIVE_OF_WEIERSTRASS_CURVE : thm
  WEIERSTRASS_OF_PROJECTIVE_CURVE : thm
  deriving Inhabited

@[nospecialize]
def setupProjectiveDefs [HolBase] (D : ProjectiveDeps) :
    ExceptT String IO ProjectiveDefs := do
  -- @@SCOPE BEGIN
  let { INTEGRAL_DOMAIN_RULE, MESON_TAC, define, new_definition, .. } := D
  let { CONJ_ASSOC, FIELD_IMP_INTEGRAL_DOMAIN, FIELD_MUL_LINV, FORALL_OPTION_THM,
        FORALL_PAIR_THM, IMP_CONJ_ALT, PAIR_EQ, RING_0, RING_1, RING_DIV, RING_DIV_1,
        RING_INV, RING_MUL_RZERO, WEIERSTRASS_CURVE_IMP_POINT, field, option_DISTINCT,
        option_INJ, ring_div, weierstrass_curve, weierstrass_point, .. } := D.core1
  -- @@SCOPE END

  let projective_point ← define
   r"projective_point f (x,y,z) <=>
        x IN ring_carrier f /\ y IN ring_carrier f /\ z IN ring_carrier f"

  let projective_curve ← define
   r"projective_curve (f,a:A,b) (x,y,z) <=>
        x IN ring_carrier f /\
        y IN ring_carrier f /\
        z IN ring_carrier f /\
        ring_mul f (ring_pow f y 2) z =
        ring_add f (ring_pow f x 3)
                   (ring_add f (ring_mul f a (ring_mul f x (ring_pow f z 2)))
                               (ring_mul f b (ring_pow f z 3)))"

  let weierstrass_of_projective ← define
   r"weierstrass_of_projective (f:A ring) (x,y,z) =
        if z = ring_0 f then NONE
        else SOME(ring_div f x z,ring_div f y z)"

  let projective_of_weierstrass ← define
   r"projective_of_weierstrass (f:A ring) NONE = (ring_0 f,ring_1 f,ring_0 f) /\
  projective_of_weierstrass f (SOME(x,y)) = (x,y,ring_1 f)"

  let projective_eq ← define
   r"projective_eq (f:A ring) (x,y,z) (x',y',z') <=>
        (z = ring_0 f <=> z' = ring_0 f) /\
        ring_mul f x z' = ring_mul f x' z /\
        ring_mul f y z' = ring_mul f y' z"

  let projective_0 ← new_definition
   r"projective_0 (f:A ring,a:A,b:A) = (ring_0 f,ring_1 f,ring_0 f)"

  let projective_neg ← new_definition
   r"projective_neg (f,a:A,b:A) (x,y,z) = (x:A,ring_neg f y:A,z:A)"

  let projective_add ← new_definition
   r"projective_add (f,a,b) (x1,y1,z1) (x2,y2,z2) =
    if z1 = ring_0 f then (x2,y2,z2)
    else if z2 = ring_0 f then (x1,y1,z1)
    else if projective_eq f (x1,y1,z1) (x2,y2,z2) then
      let t =
          ring_add f (ring_mul f a (ring_pow f z1 2))
          (ring_mul f (ring_of_num f 3) (ring_pow f x1 2))
      and u = ring_mul f y1 z1 in
      let v = ring_mul f u (ring_mul f x1 y1) in
      let w = ring_sub f (ring_pow f t 2) (ring_mul f (ring_of_num f 8) v) in
      (ring_mul f (ring_of_num f 2) (ring_mul f u w),
       ring_sub f (ring_mul f t (ring_sub f (ring_mul f (ring_of_num f 4) v) w))
       (ring_mul f (ring_of_num f 8)
       (ring_mul f (ring_pow f y1 2) (ring_pow f u 2))),
       ring_mul f (ring_of_num f 8) (ring_pow f u 3))
    else if projective_eq f (projective_neg (f,a,b) (x1,y1,z1)) (x2,y2,z2) then
      projective_0 (f,a,b)
    else
      let u = ring_sub f (ring_mul f y2 z1) (ring_mul f y1 z2)
      and v = ring_sub f (ring_mul f x2 z1) (ring_mul f x1 z2) in
      let w =
          ring_sub f
          (ring_sub f (ring_mul f (ring_pow f u 2) (ring_mul f z1 z2))
          (ring_pow f v 3))
          (ring_mul f (ring_of_num f 2)
          (ring_mul f (ring_pow f v 2) (ring_mul f x1 z2))) in
      (ring_mul f v w,
       ring_sub f
       (ring_mul f u
       (ring_sub f (ring_mul f (ring_pow f v 2) (ring_mul f x1 z2)) w))
       (ring_mul f (ring_pow f v 3) (ring_mul f y1 z2)),
       ring_mul f (ring_pow f v 3) (ring_mul f z1 z2))"

  let PROJECTIVE_CURVE_IMP_POINT ← prove
   r"!f a b p. projective_curve(f,a,b) p ==> projective_point f p"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    SIMP_TAC [projective_curve, projective_point]))

  let PROJECTIVE_OF_WEIERSTRASS_POINT_EQ ← prove
   r"!(f:A ring) p.
        projective_point f (projective_of_weierstrass f p) <=>
        weierstrass_point f p"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    REWRITE_TAC [weierstrass_point, projective_of_weierstrass] THEN
    SIMP_TAC [projective_point, RING_0, RING_1]))

  let PROJECTIVE_OF_WEIERSTRASS_POINT ← prove
   r"!(f:A ring) p.
        weierstrass_point f p
        ==> projective_point f (projective_of_weierstrass f p)"
   (← do
    pure (REWRITE_TAC [PROJECTIVE_OF_WEIERSTRASS_POINT_EQ]))

  let WEIERSTRASS_OF_PROJECTIVE_POINT ← prove
   r"!(f:A ring) p.
        projective_point f p
        ==> weierstrass_point f (weierstrass_of_projective f p)"
   (← do
    pure (SIMP_TAC [FORALL_PAIR_THM, weierstrass_of_projective, projective_point] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [weierstrass_point, RING_DIV]))

  let PROJECTIVE_OF_WEIERSTRASS_EQ ← prove
   r"!(f:A ring) p q.
        field f
        ==> (projective_of_weierstrass f p = projective_of_weierstrass f q <=>
             p = q)"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, field] THEN
    REWRITE_TAC [projective_of_weierstrass, option_DISTINCT, option_INJ] THEN
    SIMP_TAC [PAIR_EQ]))

  let WEIERSTRASS_OF_PROJECTIVE_EQ ← prove
   r"!(f:A ring) p q.
        field f /\ projective_point f p /\ projective_point f q
        ==> (weierstrass_of_projective f p = weierstrass_of_projective f q <=>
             projective_eq f p q)"
   (← do
    let linv ← ONCE_REWRITE_RULE [IMP_CONJ_ALT] (← REWRITE_RULE [CONJ_ASSOC] FIELD_MUL_LINV)
    pure (REWRITE_TAC [FORALL_PAIR_THM, projective_point] THEN
    REWRITE_TAC [weierstrass_of_projective, projective_eq] THEN
    REPEAT STRIP_TAC THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [option_INJ, option_DISTINCT]) THEN
    ASM_SIMP_TAC [RING_MUL_RZERO, PAIR_EQ] THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP linv)) THEN
    ASM_REWRITE_TAC [ring_div] THEN
    W (fun (_asl, w) => tactic_of do pure (MATCH_MP_TAC (← INTEGRAL_DOMAIN_RULE w))) THEN
    ASM_SIMP_TAC [RING_INV, FIELD_IMP_INTEGRAL_DOMAIN]))

  let WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS ← prove
   r"!(f:A ring) p.
        field f /\ weierstrass_point f p
        ==> weierstrass_of_projective f (projective_of_weierstrass f p) = p"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, field] THEN
    SIMP_TAC [weierstrass_of_projective, projective_of_weierstrass,
             weierstrass_point, RING_DIV_1]))

  let PROJECTIVE_OF_WEIERSTRASS_OF_PROJECTIVE ← prove
   r"!(f:A ring) p.
        field f /\ projective_point f p
        ==> projective_eq f
             (projective_of_weierstrass f (weierstrass_of_projective f p)) p"
   (← do
    pure (SIMP_TAC [← GSYM WEIERSTRASS_OF_PROJECTIVE_EQ,
             WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS,
             PROJECTIVE_OF_WEIERSTRASS_POINT_EQ,
             WEIERSTRASS_OF_PROJECTIVE_POINT]))

  let PROJECTIVE_OF_WEIERSTRASS_CURVE_EQ ← prove
   r"!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p
        ==> (projective_curve (f,a,b) (projective_of_weierstrass f p) <=>
             weierstrass_curve (f,a,b) p)"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, weierstrass_point] THEN
    REWRITE_TAC [weierstrass_curve, projective_of_weierstrass] THEN
    SIMP_TAC [projective_curve, RING_0, RING_1] THEN
    REPEAT STRIP_TAC THEN REPEAT (FIRST_X_ASSUM (MP_TAC o SYM)) THEN
    W (fun (_asl, w) => tactic_of do pure (MATCH_MP_TAC (← INTEGRAL_DOMAIN_RULE w))) THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))

  let PROJECTIVE_OF_WEIERSTRASS_CURVE ← prove
   r"!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve (f,a,b) p
        ==> projective_curve (f,a,b) (projective_of_weierstrass f p)"
   (← do
    pure (MESON_TAC [PROJECTIVE_OF_WEIERSTRASS_CURVE_EQ,
              WEIERSTRASS_CURVE_IMP_POINT]))

  let WEIERSTRASS_OF_PROJECTIVE_CURVE ← prove
   r"!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_curve (f,a,b) p
        ==> weierstrass_curve (f,a,b) (weierstrass_of_projective f p)"
   (← do
    let linv ← ONCE_REWRITE_RULE [IMP_CONJ_ALT] (← REWRITE_RULE [CONJ_ASSOC] FIELD_MUL_LINV)
    pure (SIMP_TAC [FORALL_PAIR_THM, weierstrass_of_projective, projective_curve] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC [weierstrass_curve, RING_DIV] THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o SYM)) THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o MATCH_MP linv)) THEN
    ASM_REWRITE_TAC [ring_div] THEN
    W (fun (_asl, w) => tactic_of do pure (MATCH_MP_TAC (← INTEGRAL_DOMAIN_RULE w))) THEN
    ASM_SIMP_TAC [RING_INV, FIELD_IMP_INTEGRAL_DOMAIN]))

  -- @@RETURN BEGIN
  return { projective_point, projective_curve, weierstrass_of_projective,
           projective_of_weierstrass, projective_eq, projective_0, projective_neg,
           projective_add, PROJECTIVE_CURVE_IMP_POINT,
           PROJECTIVE_OF_WEIERSTRASS_POINT_EQ, PROJECTIVE_OF_WEIERSTRASS_POINT,
           WEIERSTRASS_OF_PROJECTIVE_POINT, PROJECTIVE_OF_WEIERSTRASS_EQ,
           WEIERSTRASS_OF_PROJECTIVE_EQ, WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS,
           PROJECTIVE_OF_WEIERSTRASS_OF_PROJECTIVE, PROJECTIVE_OF_WEIERSTRASS_CURVE_EQ,
           PROJECTIVE_OF_WEIERSTRASS_CURVE, WEIERSTRASS_OF_PROJECTIVE_CURVE }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Projective coordinates: negation and addition.  (projective.ml 202-349)   -/
/- ------------------------------------------------------------------------- -/

structure ProjectiveOps where
  -- @@FIELDS
  PROJECTIVE_POINT_NEG : thm
  PROJECTIVE_CURVE_NEG : thm
  WEIERSTRASS_OF_PROJECTIVE_NEG : thm
  PROJECTIVE_EQ_NEG : thm
  WEIERSTRASS_OF_PROJECTIVE_NEG_OF_WEIERSTRASS : thm
  PROJECTIVE_OF_WEIERSTRASS_NEG : thm
  PROJECTIVE_POINT_ADD : thm
  PROJECTIVE_CURVE_ADD : thm
  WEIERSTRASS_OF_PROJECTIVE_ADD : thm
  PROJECTIVE_EQ_ADD : thm
  WEIERSTRASS_OF_PROJECTIVE_ADD_OF_WEIERSTRASS : thm
  PROJECTIVE_OF_WEIERSTRASS_ADD : thm
  deriving Inhabited

@[nospecialize]
def setupProjectiveOps [HolBase] (D : ProjectiveDeps) (BProjectiveDefs : ProjectiveDefs) :
    ExceptT String IO ProjectiveOps := do
  -- @@SCOPE BEGIN
  let { FIELD_TAC, INTEGRAL_DOMAIN_RULE, LET_TAC, NOT_RING_CHAR_DIVIDES_TAC,
        RING_CARRIER_TAC, .. } := D
  let { DE_MORGAN_THM, FIELD_CHAR_NOT23, FIELD_IMP_INTEGRAL_DOMAIN, FORALL_PAIR_THM,
        LET_DEF, LET_END_DEF, PAIR_EQ, WEIERSTRASS_POINT_ADD, WEIERSTRASS_POINT_NEG,
        option_DISTINCT, option_INJ, weierstrass_add, weierstrass_neg, .. } := D.core1
  let { PROJECTIVE_OF_WEIERSTRASS_POINT, WEIERSTRASS_OF_PROJECTIVE_EQ,
        WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS, projective_0, projective_add,
        projective_curve, projective_eq, projective_neg, projective_point,
        weierstrass_of_projective, .. } := BProjectiveDefs
  -- @@SCOPE END

  let PROJECTIVE_POINT_NEG ← prove
   r"!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f p
        ==> projective_point f (projective_neg (f,a,b) p)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, projective_neg, projective_point] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o SYM)) THEN
    W (fun (_asl, w) => tactic_of do pure (MATCH_MP_TAC (← INTEGRAL_DOMAIN_RULE w))) THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))

  let PROJECTIVE_CURVE_NEG ← prove
   r"!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_curve (f,a,b) p
        ==> projective_curve (f,a,b) (projective_neg (f,a,b) p)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, projective_neg, projective_curve] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o SYM)) THEN
    W (fun (_asl, w) => tactic_of do pure (MATCH_MP_TAC (← INTEGRAL_DOMAIN_RULE w))) THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))

  let WEIERSTRASS_OF_PROJECTIVE_NEG ← prove
   r"!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f p
        ==> weierstrass_of_projective f (projective_neg (f,a,b) p) =
            weierstrass_neg (f,a,b) (weierstrass_of_projective f p)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, projective_neg, weierstrass_of_projective,
                projective_point] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC [weierstrass_neg, option_INJ, PAIR_EQ] THEN
    FIELD_TAC))

  let PROJECTIVE_EQ_NEG ← prove
   r"!(f:A ring) a b p p'.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f p /\ projective_point f p' /\ projective_eq f p p'
        ==> projective_eq f
              (projective_neg (f,a,b) p) (projective_neg (f,a,b) p')"
   (← do
    pure (REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC [← GSYM WEIERSTRASS_OF_PROJECTIVE_EQ, PROJECTIVE_POINT_NEG] THEN
    ASM_SIMP_TAC [WEIERSTRASS_OF_PROJECTIVE_NEG]))

  let WEIERSTRASS_OF_PROJECTIVE_NEG_OF_WEIERSTRASS ← prove
   r"!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p
        ==> weierstrass_of_projective f
             (projective_neg (f,a,b) (projective_of_weierstrass f p)) =
            weierstrass_neg (f,a,b) p"
   (← do
    pure (SIMP_TAC [WEIERSTRASS_OF_PROJECTIVE_NEG,
             PROJECTIVE_OF_WEIERSTRASS_POINT,
             WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS]))

  let PROJECTIVE_OF_WEIERSTRASS_NEG ← prove
   r"!(f:A ring) a b p.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p
        ==> projective_eq f
             (projective_of_weierstrass f (weierstrass_neg (f,a,b) p))
             (projective_neg (f,a,b) (projective_of_weierstrass f p))"
   (← do
    pure (SIMP_TAC [← GSYM WEIERSTRASS_OF_PROJECTIVE_EQ,
             PROJECTIVE_OF_WEIERSTRASS_POINT,
             PROJECTIVE_POINT_NEG, WEIERSTRASS_POINT_NEG,
             WEIERSTRASS_OF_PROJECTIVE_NEG,
             WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS]))

  let PROJECTIVE_POINT_ADD ← prove
   r"!(f:A ring) a b p q.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f p /\ projective_point f q
        ==> projective_point f (projective_add (f,a,b) p q)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, projective_add, projective_point,
                projective_0, projective_eq, LET_DEF, LET_END_DEF] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    REPEAT (COND_CASES_TAC THEN
     ASM_REWRITE_TAC [projective_add, projective_point,
                projective_eq, LET_DEF, LET_END_DEF]) THEN
    REPEAT STRIP_TAC THEN RING_CARRIER_TAC))

  let PROJECTIVE_CURVE_ADD ← prove
   r"!(f:A ring) a b p q.
        field f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_curve (f,a,b) p /\ projective_curve (f,a,b) q
        ==> projective_curve (f,a,b) (projective_add (f,a,b) p q)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, projective_add, projective_curve,
                projective_0, projective_eq, LET_DEF, LET_END_DEF] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    REPEAT (COND_CASES_TAC THEN
     ASM_REWRITE_TAC [projective_add, projective_curve,
                projective_eq, LET_DEF, LET_END_DEF]) THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o SYM)) THEN
    W (fun (_asl, w) => tactic_of do pure (MATCH_MP_TAC (← INTEGRAL_DOMAIN_RULE w))) THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))

  let WEIERSTRASS_OF_PROJECTIVE_ADD ← prove
   r"!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f p /\ projective_point f q
        ==> weierstrass_of_projective f (projective_add (f,a,b) p q) =
            weierstrass_add (f,a,b)
             (weierstrass_of_projective f p)
             (weierstrass_of_projective f q)"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT23, FORALL_PAIR_THM, projective_point] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"f:A ring", ← q r"a:A", ← q r"b:A", ← q r"x1:A", ← q r"y1:A", ← q r"z1:A",
      ← q r"x2:A", ← q r"y2:A", ← q r"z2:A"] THEN
    STRIP_TAC THEN REWRITE_TAC [weierstrass_of_projective, projective_add] THEN
    MAP_EVERY ASM_CASES_TAC [← q r"z1:A = ring_0 f", ← q r"z2:A = ring_0 f"] THEN
    ASM_REWRITE_TAC [weierstrass_of_projective, weierstrass_add] THEN
    ASM_REWRITE_TAC [projective_eq, projective_neg, projective_0] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REWRITE_TAC [LET_DEF, LET_END_DEF] THEN
    REPEAT LET_TAC THEN REWRITE_TAC [weierstrass_of_projective] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REWRITE_TAC [option_DISTINCT, option_INJ, PAIR_EQ] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [DE_MORGAN_THM]) THEN
    REPEAT (FIRST_X_ASSUM DISJ_CASES_TAC ORELSE
           FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  let PROJECTIVE_EQ_ADD ← prove
   r"!(f:A ring) a b p p' q q'.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f p /\ projective_point f p' /\
        projective_point f q /\ projective_point f q' /\
        projective_eq f p p' /\ projective_eq f q q'
        ==> projective_eq f
              (projective_add (f,a,b) p q) (projective_add (f,a,b) p' q')"
   (← do
    pure (REPEAT GEN_TAC THEN
    REPLICATE_TAC 9 (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC [← GSYM WEIERSTRASS_OF_PROJECTIVE_EQ, PROJECTIVE_POINT_ADD] THEN
    ASM_SIMP_TAC [WEIERSTRASS_OF_PROJECTIVE_ADD]))

  let WEIERSTRASS_OF_PROJECTIVE_ADD_OF_WEIERSTRASS ← prove
   r"!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p /\ weierstrass_point f q
        ==> weierstrass_of_projective f
             (projective_add (f,a,b)
               (projective_of_weierstrass f p)
               (projective_of_weierstrass f q)) =
            weierstrass_add (f,a,b) p q"
   (← do
    pure (SIMP_TAC [WEIERSTRASS_OF_PROJECTIVE_ADD,
             PROJECTIVE_OF_WEIERSTRASS_POINT,
             WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS]))

  let PROJECTIVE_OF_WEIERSTRASS_ADD ← prove
   r"!(f:A ring) a b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p /\ weierstrass_point f q
        ==> projective_eq f
             (projective_of_weierstrass f (weierstrass_add (f,a,b) p q))
             (projective_add (f,a,b)
               (projective_of_weierstrass f p)
               (projective_of_weierstrass f q))"
   (← do
    pure (SIMP_TAC [← GSYM WEIERSTRASS_OF_PROJECTIVE_EQ,
             PROJECTIVE_OF_WEIERSTRASS_POINT,
             PROJECTIVE_POINT_ADD, WEIERSTRASS_POINT_ADD,
             WEIERSTRASS_OF_PROJECTIVE_ADD,
             WEIERSTRASS_OF_PROJECTIVE_OF_WEIERSTRASS]))

  -- @@RETURN BEGIN
  return { PROJECTIVE_POINT_NEG, PROJECTIVE_CURVE_NEG, WEIERSTRASS_OF_PROJECTIVE_NEG,
           PROJECTIVE_EQ_NEG, WEIERSTRASS_OF_PROJECTIVE_NEG_OF_WEIERSTRASS,
           PROJECTIVE_OF_WEIERSTRASS_NEG, PROJECTIVE_POINT_ADD, PROJECTIVE_CURVE_ADD,
           WEIERSTRASS_OF_PROJECTIVE_ADD, PROJECTIVE_EQ_ADD,
           WEIERSTRASS_OF_PROJECTIVE_ADD_OF_WEIERSTRASS, PROJECTIVE_OF_WEIERSTRASS_ADD }
  -- @@RETURN END

end HolEC.Projective
