/- ========================================================================= -/
/- Twisted Edwards curves in general, a x^2 + y^2 = 1 + d x^2 y^2.         -/
/- ========================================================================= -/
/- File: HolEC/Edwards.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/edwards.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.Edwards fills them).

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

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolEC.Edwards

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ARITH_EQ ARITH_EVEN CARD_SUBSET DE_MORGAN_THM DIVIDES_2 DIVIDES_REFL
   FIELD_CHAR_NOT2 FIELD_IMP_INTEGRAL_DOMAIN FINITE_PRODUCT
   FINITE_QUADRATIC_CURVE FINITE_SUBSET FORALL_PAIR_THM FORALL_UNPAIR_THM
   GROUP_ELEMENT_ORDER_EQ_2_ALT GROUP_ELEMENT_ORDER_EQ_MUL GROUP_POW GROUP_POW_2
   IMP_CONJ IN IN_ELIM_PAIR_THM LEFT_IMP_EXISTS_THM LET_DEF LET_END_DEF LE_TRANS
   NOT_EXISTS_THM PAIR PAIR_EQ RIGHT_FORALL_IMP_THM RIGHT_OR_FORALL_THM RING_0
   RING_1 RING_INV RING_MUL RING_NEG SUBSET abelian_group group_carrier group_id
   group_inv group_mul group_tybij : thm)
  deriving Inhabited

/-- What edwards.ml uses from Session besides theorems. -/
structure EdwardsDeps where
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
/- Twisted Edwards curves in general, a * x^2 + y^2 = 1 + d * x^2 * y^2:     -/
/- basic definitions and naive cardinality bounds.  (edwards.ml 1-102)       -/
/- ------------------------------------------------------------------------- -/

structure EdwardsDefs where
  -- @@FIELDS
  edwards_point : thm
  edwards_curve : thm
  edwards_nonsingular : thm
  edwards_0 : thm
  edwards_neg : thm
  edwards_add : thm
  edwards_group : thm
  EDWARDS_NONSINGULAR_ALT : thm
  FINITE_EDWARDS_CURVE : thm
  CARD_BOUND_EDWARDS_CURVE : thm
  deriving Inhabited

@[nospecialize]
def setupEdwardsDefs [HolBase] (D : EdwardsDeps) :
    ExceptT String IO EdwardsDefs := do
  -- @@SCOPE BEGIN
  let { FIELD_TAC, MESON, define, .. } := D
  let { CARD_SUBSET, FIELD_IMP_INTEGRAL_DOMAIN, FINITE_PRODUCT, FINITE_QUADRATIC_CURVE,
        FINITE_SUBSET, FORALL_PAIR_THM, IN, IN_ELIM_PAIR_THM, LE_TRANS, NOT_EXISTS_THM,
        RIGHT_OR_FORALL_THM, RING_INV, SUBSET, .. } := D.core1
  -- @@SCOPE END

  let edwards_point ← define
   r"edwards_point f (x:A,y) <=>
        x IN ring_carrier f /\ y IN ring_carrier f"

  let edwards_curve ← define
   r"edwards_curve(f:A ring,a:A,d:A) (x,y) <=>
        x IN ring_carrier f /\ y IN ring_carrier f /\
        ring_add f (ring_mul f a (ring_pow f x 2)) (ring_pow f y 2) =
        ring_add f (ring_1 f)
          (ring_mul f d (ring_mul f (ring_pow f x 2) (ring_pow f y 2)))"

  let edwards_nonsingular ← define
   r"edwards_nonsingular (f:A ring,a:A,d:A) <=>
        (?b. b IN ring_carrier f /\ ring_pow f b 2 = a) /\
        (d = ring_0 f \/ ~(?c. c IN ring_carrier f /\ ring_pow f c 2 = d))"

  let edwards_0 ← define
   r"edwards_0 (f:A ring,a:A,d:A) = (ring_0 f,ring_1 f)"

  let edwards_neg ← define
   r"edwards_neg (f:A ring,a:A,d:A) (x,y:A) = (ring_neg f x,y)"

  let edwards_add ← define
   r"edwards_add (f:A ring,a:A,d:A) (x1,y1) (x2,y2) =
   ring_div f (ring_add f (ring_mul f x1 y2) (ring_mul f y1 x2))
   (ring_add f (ring_1 f)
   (ring_mul f d (ring_mul f x1 (ring_mul f y1 (ring_mul f x2 y2))))),
   ring_div f
   (ring_sub f (ring_mul f y1 y2) (ring_mul f a (ring_mul f x1 x2)))
   (ring_sub f (ring_1 f)
   (ring_mul f d (ring_mul f x1 (ring_mul f y1 (ring_mul f x2 y2)))))"

  let edwards_group ← define
   r"edwards_group (f:A ring,a:A,d:A) =
        group(edwards_curve(f,a,d),
              edwards_0(f,a,d),
              edwards_neg(f,a,d),
              edwards_add(f,a,d))"

  let EDWARDS_NONSINGULAR_ALT ← prove
   r"!f a (d:A).
    field f /\ a IN ring_carrier f /\ d IN ring_carrier f
    ==> (edwards_nonsingular (f,a,d) <=>
        (?b. b IN ring_carrier f /\ ring_pow f b 2 = a) /\
        ~(?c. c IN ring_carrier f /\ ~(c = ring_0 f) /\ ring_pow f c 2 = d))"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [edwards_nonsingular] THEN AP_TERM_TAC THEN
    ASM_CASES_TAC (← q r"d:A = ring_0 f") THEN ASM_REWRITE_TAC [] THENL
     [FIELD_TAC, AP_TERM_TAC THEN AP_TERM_TAC THEN ABS_TAC] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN FIELD_TAC))

  let FINITE_EDWARDS_CURVE ← prove
   r"!f a d:A. field f /\ FINITE(ring_carrier f)
             ==> FINITE(edwards_curve(f,a,d))"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
     (← q r"{(x,y) | (x:A) IN ring_carrier f /\ y IN ring_carrier f}") THEN
    ASM_SIMP_TAC [FINITE_PRODUCT] THEN
    REWRITE_TAC [edwards_curve, SUBSET, FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
    SIMP_TAC [edwards_curve, IN]))

  let CARD_BOUND_EDWARDS_CURVE ← prove
   r"!f a d:A. field f /\ FINITE(ring_carrier f) /\
             a IN ring_carrier f /\ d IN ring_carrier f /\
             edwards_nonsingular(f,a,d)
             ==> CARD(edwards_curve(f,a,d)) <= 2 * CARD(ring_carrier f)"
   (← do
    let m1 ← MESON [FINITE_SUBSET, CARD_SUBSET, LE_TRANS]
     (← q r"!s. t SUBSET s /\ FINITE s /\ CARD s <= n ==> CARD t <= n")
    pure (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC m1 THEN
    EXISTS_TAC
     (← q r"{(x,y) | (x:A) IN ring_carrier f /\ y IN ring_carrier f /\
               ring_pow f y 2 =
               ring_div f (ring_sub f (ring_1 f)
                              (ring_mul f a (ring_pow f x 2)))
                          (ring_sub f (ring_1 f)
                              (ring_mul f d (ring_pow f x 2)))}") THEN
    ASM_SIMP_TAC [FINITE_QUADRATIC_CURVE, FIELD_IMP_INTEGRAL_DOMAIN] THEN
    REWRITE_TAC [SUBSET, FORALL_PAIR_THM, IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN GEN_REWRITE_TAC LAND_CONV [IN] THEN
    REWRITE_TAC [edwards_curve] THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (fun th => tactic_of do pure (MP_TAC (← SYM (← SYM th)))) THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [edwards_nonsingular]) THEN
    REWRITE_TAC [NOT_EXISTS_THM, RIGHT_OR_FORALL_THM] THEN
    DISCH_THEN (MP_TAC o SPEC (← q r"ring_inv f x:A") o CONJUNCT2) THEN
    ASM_SIMP_TAC [RING_INV] THEN FIELD_TAC))

  -- @@RETURN BEGIN
  return { edwards_point, edwards_curve, edwards_nonsingular, edwards_0, edwards_neg,
           edwards_add, edwards_group, EDWARDS_NONSINGULAR_ALT, FINITE_EDWARDS_CURVE,
           CARD_BOUND_EDWARDS_CURVE }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Proof of the group properties by algebraic brute force. We do use a bit   -/
/- more delicacy than calling FIELD_TAC in order to avoid assuming anything  -/
/- about the characteristic of the field.  (edwards.ml 103-321)              -/
/- ------------------------------------------------------------------------- -/

structure EdwardsGroup where
  -- @@FIELDS
  EDWARDS_NONSINGULAR_DENOMINATORS : thm
  EDWARDS_NONSINGULAR_DENOMINATORS_POINTS : thm
  EDWARDS_CURVE_IMP_POINT : thm
  EDWARDS_POINT_NEG : thm
  EDWARDS_POINT_ADD : thm
  EDWARDS_CURVE_0 : thm
  EDWARDS_CURVE_NEG : thm
  EDWARDS_CURVE_ADD : thm
  EDWARDS_ADD_LID : thm
  EDWARDS_ADD_LNEG : thm
  EDWARDS_ADD_SYM : thm
  EDWARDS_ADD_ASSOC : thm
  EDWARDS_GROUP : thm
  ABELIAN_EDWARDS_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupEdwardsGroup [HolBase] (D : EdwardsDeps) (BEdwardsDefs : EdwardsDefs) :
    ExceptT String IO EdwardsGroup := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, FIELD_TAC, INTEGRAL_DOMAIN_RULE, MESON, RING_CARRIER_TAC,
        RING_PULL_DIV_TAC, RING_TAC, TAUT, .. } := D
  let { DE_MORGAN_THM, DIVIDES_REFL, FIELD_IMP_INTEGRAL_DOMAIN, FORALL_PAIR_THM,
        FORALL_UNPAIR_THM, IN, LEFT_IMP_EXISTS_THM, LET_DEF, LET_END_DEF, PAIR_EQ,
        RING_0, RING_1, RING_INV, RING_MUL, RING_NEG, abelian_group, group_carrier,
        group_id, group_inv, group_mul, group_tybij, .. } := D.core1
  let { EDWARDS_NONSINGULAR_ALT, edwards_0, edwards_add, edwards_curve, edwards_group,
        edwards_neg, edwards_nonsingular, edwards_point, .. } := BEdwardsDefs
  -- @@SCOPE END

  let EDWARDS_NONSINGULAR_DENOMINATORS ← prove
   r"!f a (d:A) x1 y1 x2 y2.
        field f /\ a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular(f,a,d) /\
        edwards_curve(f,a,d) (x1,y1) /\ edwards_curve(f,a,d) (x2,y2)
        ==> ~(ring_add f (ring_1 f)
              (ring_mul f d
                 (ring_mul f x1 (ring_mul f y1 (ring_mul f x2 y2)))) =
              ring_0 f) /\
            ~(ring_sub f (ring_1 f)
              (ring_mul f d
                 (ring_mul f x1 (ring_mul f y1 (ring_mul f x2 y2)))) =
              ring_0 f)"
   (← do
    -- right to left: the MESON, then the TAUT
    let m2 ← MESON [] (← q r"!a b. P a \/ P b ==> ?x. P x")
    let t1 ← TAUT (← q r"~(p /\ ~q) <=> p ==> q")
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [edwards_curve, ← GSYM DE_MORGAN_THM] THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN DISCH_TAC THEN
    UNDISCH_TAC (← q r"edwards_nonsingular(f,a:A,d)") THEN
    ASM_SIMP_TAC [EDWARDS_NONSINGULAR_ALT] THEN
    REWRITE_TAC [t1, LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC (← q r"e:A") THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (fun th => tactic_of do
      pure (SUBST_ALL_TAC (← SYM th)))) THEN
    MATCH_MP_TAC m2 THEN
    EXISTS_TAC (← q r"ring_inv f (ring_mul f x1 y2):A") THEN
    EXISTS_TAC (← q r"ring_inv f (ring_mul f e (ring_mul f x1 x2)):A") THEN
    ASM_SIMP_TAC [RING_INV, RING_MUL] THEN FIELD_TAC))

  let EDWARDS_NONSINGULAR_DENOMINATORS_POINTS ←
    GEN_REWRITE_RULE (funpow 4 BINDER_CONV) [FORALL_UNPAIR_THM]
     (← GEN_REWRITE_RULE (funpow 3 BINDER_CONV) [FORALL_UNPAIR_THM]
        EDWARDS_NONSINGULAR_DENOMINATORS)

  let EDWARDS_CURVE_IMP_POINT ← prove
   r"!f a d p. edwards_curve(f,a,d) p ==> edwards_point f p"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM] THEN SIMP_TAC [edwards_curve, edwards_point]))

  let EDWARDS_POINT_NEG ← prove
   r"!(f:A ring) a d p.
        edwards_point f p
        ==> edwards_point f (edwards_neg (f,a,d) p)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM] THEN
    SIMP_TAC [edwards_neg, edwards_point, RING_NEG]))

  let EDWARDS_POINT_ADD ← prove
   r"!(f:A ring) a d p q.
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_point f p /\ edwards_point f q
        ==> edwards_point f (edwards_add (f,a,d) p q)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM] THEN
    SIMP_TAC [edwards_add, edwards_point, LET_DEF, LET_END_DEF] THEN
    REPEAT STRIP_TAC THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [edwards_point]) THEN
    REPEAT STRIP_TAC THEN RING_CARRIER_TAC))

  let EDWARDS_CURVE_0 ← prove
   r"!f a d:A.
        a IN ring_carrier f /\ d IN ring_carrier f
        ==> edwards_curve(f,a,d) (edwards_0(f,a,d))"
   (← do
    pure (REWRITE_TAC [edwards_curve, edwards_0] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN RING_TAC))

  let EDWARDS_CURVE_NEG ← prove
   r"!f a (d:A) p.
        integral_domain f /\ a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_curve(f,a,d) p
        ==> edwards_curve(f,a,d) (edwards_neg (f,a,d) p)"
   (← do
    pure (SIMP_TAC [FORALL_PAIR_THM, RING_NEG, edwards_curve, edwards_neg] THEN
    REPEAT GEN_TAC THEN CONV_TAC (fun t => (INTEGRAL_DOMAIN_RULE t).run)))

  let EDWARDS_CURVE_ADD ← prove
   r"!f a (d:A) p q.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular (f,a,d) /\
        edwards_curve(f,a,d) p /\ edwards_curve(f,a,d) q
        ==> edwards_curve(f,a,d) (edwards_add (f,a,d) p q)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, edwards_curve, edwards_add, PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"x1:A", ← q r"y1:A", ← q r"x2:A",
      ← q r"y2:A"] THEN
    STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"x1:A", ← q r"y1:A",
                     ← q r"x2:A", ← q r"y2:A"]
      EDWARDS_NONSINGULAR_DENOMINATORS) THEN
    ASM_REWRITE_TAC [edwards_curve] THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      let _ ← GEN_REWRITE_RULE I [edwards_nonsingular] th; pure ALL_TAC) THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    RING_PULL_DIV_TAC THEN RING_TAC))

  let EDWARDS_ADD_LID ← prove
   r"!f a (d:A) p.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_curve(f,a,d) p
        ==> edwards_add(f,a,d) (edwards_0 (f,a,d)) p = p"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, edwards_curve, edwards_add,
                edwards_0, PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC))

  let EDWARDS_ADD_LNEG ← prove
   r"!f a (d:A) p.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular (f,a,d) /\
        edwards_curve(f,a,d) p
        ==> edwards_add(f,a,d) (edwards_neg (f,a,d) p) p = edwards_0(f,a,d)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, edwards_curve, edwards_add,
                edwards_neg, edwards_0, PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"x:A", ← q r"y:A"] THEN
    STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"f:A ring", ← q r"a:A", ← q r"d:A",
                     ← q r"edwards_neg (f,a,d) (x,y):A#A", ← q r"(x,y):A#A"]
          EDWARDS_NONSINGULAR_DENOMINATORS_POINTS) THEN
    ASM_REWRITE_TAC [edwards_curve, edwards_neg] THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      let _ ← GEN_REWRITE_RULE I [edwards_nonsingular] th; pure ALL_TAC) THEN
    ANTS_TAC THEN REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    FIELD_TAC))

  let EDWARDS_ADD_SYM ← prove
   r"!f a (d:A) p q.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular (f,a,d) /\
        edwards_curve(f,a,d) p /\ edwards_curve(f,a,d) q
        ==> edwards_add (f,a,d) p q = edwards_add (f,a,d) q p"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, edwards_curve, edwards_add, PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"x1:A", ← q r"y1:A", ← q r"x2:A",
      ← q r"y2:A"] THEN
    STRIP_TAC THEN
    MP_TAC (← SPECL [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"x1:A", ← q r"y1:A",
                     ← q r"x2:A", ← q r"y2:A"]
      EDWARDS_NONSINGULAR_DENOMINATORS) THEN
    MP_TAC (← SPECL [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"x2:A", ← q r"y2:A",
                     ← q r"x1:A", ← q r"y1:A"]
      EDWARDS_NONSINGULAR_DENOMINATORS) THEN
    ASM_REWRITE_TAC [edwards_curve] THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      let _ ← GEN_REWRITE_RULE I [edwards_nonsingular] th; pure ALL_TAC) THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    RING_PULL_DIV_TAC THEN RING_TAC))

  let EDWARDS_ADD_ASSOC ← prove
   r"!f a (d:A) p q r.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular (f,a,d) /\
        edwards_curve(f,a,d) p /\ edwards_curve(f,a,d) q /\
        edwards_curve(f,a,d) r
        ==> edwards_add (f,a,d) p (edwards_add (f,a,d) q r) =
            edwards_add (f,a,d) (edwards_add (f,a,d) p q) r"
   (← do
    -- the `let lemma = prove ... in` runs first
    let lemma ← prove
     r"field f /\
     x1 IN ring_carrier f /\ y1 IN ring_carrier f /\
     x2 IN ring_carrier f /\ y2 IN ring_carrier f /\
     ~(y1 = ring_0 f \/ y2 = ring_0 f) /\
     ring_mul f x1 y2 = ring_mul f x2 y1
     ==> ring_div f x1 y1 = ring_div f x2 y2"
     FIELD_TAC
    pure (REWRITE_TAC [FORALL_PAIR_THM, edwards_curve, edwards_add, PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC
     [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"x1:A", ← q r"y1:A",
      ← q r"x2:A", ← q r"y2:A", ← q r"x3:A", ← q r"y3:A"] THEN
    STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC lemma THEN
    ASM_REWRITE_TAC [] THEN
    REPLICATE_TAC 4 (CONJ_TAC THENL [RING_CARRIER_TAC, ALL_TAC]) THEN
    CONJ_TAC THENL
     [REWRITE_TAC [DE_MORGAN_THM] THEN CONJ_TAC THEN
      wPart pure (fun t => do lhand (← rand t)) EDWARDS_NONSINGULAR_DENOMINATORS THEN
      (ANTS_TAC THENL [ALL_TAC, DISCH_THEN (ACCEPT_TAC o CONJUNCT1)]) THEN
      REWRITE_TAC [← GSYM edwards_add] THEN ASM_REWRITE_TAC [] THEN
      REPEAT CONJ_TAC THEN TRY (MATCH_MP_TAC EDWARDS_CURVE_ADD) THEN
      ASM_REWRITE_TAC [edwards_curve] THEN ASM_MESON_TAC [DIVIDES_REFL],
      ALL_TAC,
      REWRITE_TAC [DE_MORGAN_THM] THEN CONJ_TAC THEN
      wPart pure (fun t => do rand (← rand t)) EDWARDS_NONSINGULAR_DENOMINATORS THEN
      (ANTS_TAC THENL [ALL_TAC, DISCH_THEN (ACCEPT_TAC o CONJUNCT2)]) THEN
      REWRITE_TAC [← GSYM edwards_add] THEN ASM_REWRITE_TAC [] THEN
      REPEAT CONJ_TAC THEN TRY (MATCH_MP_TAC EDWARDS_CURVE_ADD) THEN
      ASM_REWRITE_TAC [edwards_curve] THEN ASM_MESON_TAC [DIVIDES_REFL],
      ALL_TAC] THEN
    MP_TAC (← ISPECL [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"(x1,y1):A#A",
                      ← q r"(x2,y2):A#A"]
          EDWARDS_NONSINGULAR_DENOMINATORS_POINTS) THEN
    MP_TAC (← ISPECL [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"(x2,y2):A#A",
                      ← q r"(x3,y3):A#A"]
          EDWARDS_NONSINGULAR_DENOMINATORS_POINTS) THEN
    ASM_REWRITE_TAC [edwards_curve] THEN STRIP_TAC THEN STRIP_TAC THEN
    RING_PULL_DIV_TAC THEN RING_TAC))

  let EDWARDS_GROUP ← prove
   r"!f a (d:A).
      field f /\
      a IN ring_carrier f /\ d IN ring_carrier f /\
      edwards_nonsingular(f,a,d)
      ==> group_carrier(edwards_group(f,a,d)) = edwards_curve(f,a,d) /\
          group_id(edwards_group(f,a,d)) = edwards_0(f,a,d) /\
          group_inv(edwards_group(f,a,d)) = edwards_neg(f,a,d) /\
          group_mul(edwards_group(f,a,d)) = edwards_add(f,a,d)"
   (← do
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC [group_carrier, group_id, group_inv, group_mul, ← GSYM PAIR_EQ] THEN
    REWRITE_TAC [edwards_group, ← GSYM (← CONJUNCT2 group_tybij)] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [IN] THEN REWRITE_TAC [edwards_curve, edwards_0] THEN
      REWRITE_TAC [RING_0, RING_1] THEN RING_TAC,
      REWRITE_TAC [IN] THEN
      ASM_SIMP_TAC [EDWARDS_CURVE_NEG, FIELD_IMP_INTEGRAL_DOMAIN],
      REWRITE_TAC [IN] THEN ASM_SIMP_TAC [EDWARDS_CURVE_ADD],
      REWRITE_TAC [IN] THEN ASM_SIMP_TAC [EDWARDS_ADD_ASSOC],
      REWRITE_TAC [IN] THEN
      ASM_MESON_TAC [EDWARDS_ADD_LID, EDWARDS_ADD_SYM, EDWARDS_CURVE_0],
      REWRITE_TAC [IN] THEN
      ASM_MESON_TAC [EDWARDS_ADD_LNEG, EDWARDS_ADD_SYM, EDWARDS_CURVE_NEG,
                     FIELD_IMP_INTEGRAL_DOMAIN]]))

  let ABELIAN_EDWARDS_GROUP ← prove
   r"!f a (d:A).
      field f /\
      a IN ring_carrier f /\ d IN ring_carrier f /\
      edwards_nonsingular(f,a,d)
      ==> abelian_group(edwards_group(f,a,d))"
   (← do
    pure (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [abelian_group, EDWARDS_GROUP] THEN
    REWRITE_TAC [IN] THEN ASM_MESON_TAC [EDWARDS_ADD_SYM]))

  -- @@RETURN BEGIN
  return { EDWARDS_NONSINGULAR_DENOMINATORS, EDWARDS_NONSINGULAR_DENOMINATORS_POINTS,
           EDWARDS_CURVE_IMP_POINT, EDWARDS_POINT_NEG, EDWARDS_POINT_ADD,
           EDWARDS_CURVE_0, EDWARDS_CURVE_NEG, EDWARDS_CURVE_ADD, EDWARDS_ADD_LID,
           EDWARDS_ADD_LNEG, EDWARDS_ADD_SYM, EDWARDS_ADD_ASSOC, EDWARDS_GROUP,
           ABELIAN_EDWARDS_GROUP }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Characterizing low-order points on an Edwards curve.                      -/
/- (edwards.ml 322-405)                                                      -/
/- ------------------------------------------------------------------------- -/

structure EdwardsOrders where
  -- @@FIELDS
  EDWARDS_GROUP_ELEMENT_ORDER_EQ_2 : thm
  EDWARDS_GROUP_ELEMENT_ORDER_EQ_4_EQUIV : thm
  EDWARDS_GROUP_ELEMENT_ORDER_EQ_4 : thm
  EDWARDS_GROUP_ELEMENT_ORDER_EQ_8_EQUIV : thm
  deriving Inhabited

@[nospecialize]
def setupEdwardsOrders [HolBase] (D : EdwardsDeps) (BEdwardsDefs : EdwardsDefs) (BEdwardsGroup : EdwardsGroup) :
    ExceptT String IO EdwardsOrders := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, FIELD_TAC, .. } := D
  let { ARITH_EQ, ARITH_EVEN, DIVIDES_2, FIELD_CHAR_NOT2, FORALL_PAIR_THM,
        FORALL_UNPAIR_THM, GROUP_ELEMENT_ORDER_EQ_2_ALT, GROUP_ELEMENT_ORDER_EQ_MUL,
        GROUP_POW, GROUP_POW_2, IMP_CONJ, IN, PAIR, PAIR_EQ, RIGHT_FORALL_IMP_THM, .. } := D.core1
  let { edwards_0, edwards_add, edwards_curve, edwards_neg, .. } := BEdwardsDefs
  let { EDWARDS_GROUP, EDWARDS_NONSINGULAR_DENOMINATORS, .. } := BEdwardsGroup
  -- @@SCOPE END

  let EDWARDS_GROUP_ELEMENT_ORDER_EQ_2 ← prove
   r"!f (a:A) d p.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular (f,a,d) /\
        p IN group_carrier (edwards_group(f,a,d))
        ==> (group_element_order (edwards_group(f,a,d)) p = 2 <=>
             p = (ring_0 f,ring_neg f (ring_1 f)))"
   (← do
    pure (REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC [FIELD_CHAR_NOT2] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
    ASM_SIMP_TAC [GROUP_ELEMENT_ORDER_EQ_2_ALT] THEN
    ASM_SIMP_TAC [EDWARDS_GROUP, IMP_CONJ] THEN
    REWRITE_TAC [FORALL_PAIR_THM, edwards_0, edwards_neg, PAIR_EQ, IN] THEN
    REWRITE_TAC [edwards_curve] THEN FIELD_TAC))

  let EDWARDS_GROUP_ELEMENT_ORDER_EQ_4_EQUIV ← prove
   r"!f (a:A) d x y.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular (f,a,d) /\
        (x,y) IN group_carrier (edwards_group(f,a,d))
        ==> (group_element_order (edwards_group(f,a,d)) (x,y) = 4 <=>
             ring_mul f a (ring_pow f x 2) = ring_1 f /\ y = ring_0 f)"
   (← do
    let a1 ← ARITH_RULE (← q r"4 = 2 * 2")
    pure (REWRITE_TAC [a1] THEN
    SIMP_TAC [GROUP_ELEMENT_ORDER_EQ_MUL, DIVIDES_2, ARITH_EQ, ARITH_EVEN] THEN
    SIMP_TAC [EDWARDS_GROUP_ELEMENT_ORDER_EQ_2, GROUP_POW] THEN
    REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC [FIELD_CHAR_NOT2] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
    ASM_SIMP_TAC [GROUP_POW_2, FORALL_PAIR_THM] THEN
    ASM_SIMP_TAC [EDWARDS_GROUP] THEN REWRITE_TAC [IN] THEN
    REWRITE_TAC [edwards_curve, edwards_add, PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"x:A", ← q r"y:A",
                      ← q r"x:A", ← q r"y:A"]
      EDWARDS_NONSINGULAR_DENOMINATORS) THEN
    ASM_REWRITE_TAC [edwards_curve] THEN FIELD_TAC))

  let EDWARDS_GROUP_ELEMENT_ORDER_EQ_4 ← prove
   r"!f (a:A) d a' p.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        a' IN ring_carrier f /\ ring_mul f a (ring_pow f a' 2) = ring_1 f /\
        edwards_nonsingular (f,a,d) /\
        p IN group_carrier (edwards_group(f,a,d))
        ==> (group_element_order (edwards_group(f,a,d)) p = 4 <=>
             p = (a',ring_0 f) \/ p = (ring_neg f a',ring_0 f))"
   (← do
    let a1 ← ARITH_RULE (← q r"4 = 2 * 2")
    pure (REWRITE_TAC [a1] THEN
    SIMP_TAC [GROUP_ELEMENT_ORDER_EQ_MUL, DIVIDES_2, ARITH_EQ, ARITH_EVEN] THEN
    SIMP_TAC [EDWARDS_GROUP_ELEMENT_ORDER_EQ_2, GROUP_POW] THEN
    REPLICATE_TAC 4 GEN_TAC THEN REWRITE_TAC [FIELD_CHAR_NOT2] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
    ASM_SIMP_TAC [GROUP_POW_2, FORALL_PAIR_THM] THEN
    ASM_SIMP_TAC [EDWARDS_GROUP] THEN REWRITE_TAC [IN] THEN
    REWRITE_TAC [edwards_curve, edwards_add, PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"x:A", ← q r"y:A",
                      ← q r"x:A", ← q r"y:A"]
      EDWARDS_NONSINGULAR_DENOMINATORS) THEN
    ASM_REWRITE_TAC [edwards_curve] THEN FIELD_TAC))

  let EDWARDS_GROUP_ELEMENT_ORDER_EQ_8_EQUIV ← prove
   r"!f (a:A) d x y.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular (f,a,d) /\
        (x,y) IN group_carrier (edwards_group(f,a,d))
        ==> (group_element_order (edwards_group(f,a,d)) (x,y) = 8 <=>
             ring_mul f a (ring_pow f x 2) = ring_pow f y 2 /\
             ring_mul f (ring_of_num f 4)
                        (ring_mul f (ring_pow f a 2) (ring_pow f x 4)) =
             ring_pow f (ring_add f (ring_1 f)
                          (ring_mul f a (ring_mul f d (ring_pow f x 4)))) 2)"
   (← do
    -- right to left: the REWRITE_RULE's theorem, then the ARITH_RULE
    let e4 ← REWRITE_RULE [PAIR]
       (← GEN_REWRITE_RULE (funpow 3 BINDER_CONV) [FORALL_UNPAIR_THM]
         EDWARDS_GROUP_ELEMENT_ORDER_EQ_4_EQUIV)
    let a1 ← ARITH_RULE (← q r"8 = 2 * 4")
    pure (REWRITE_TAC [a1] THEN
    SIMP_TAC [GROUP_ELEMENT_ORDER_EQ_MUL, DIVIDES_2, ARITH_EQ, ARITH_EVEN] THEN
    SIMP_TAC [GROUP_POW, e4] THEN
    REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC [FIELD_CHAR_NOT2] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
    ASM_SIMP_TAC [GROUP_POW_2, FORALL_PAIR_THM] THEN
    ASM_SIMP_TAC [EDWARDS_GROUP] THEN REWRITE_TAC [IN] THEN
    REWRITE_TAC [edwards_curve, edwards_add, PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"x:A", ← q r"y:A",
                      ← q r"x:A", ← q r"y:A"]
      EDWARDS_NONSINGULAR_DENOMINATORS) THEN
    ASM_REWRITE_TAC [edwards_curve] THEN FIELD_TAC))

  -- @@RETURN BEGIN
  return { EDWARDS_GROUP_ELEMENT_ORDER_EQ_2, EDWARDS_GROUP_ELEMENT_ORDER_EQ_4_EQUIV,
           EDWARDS_GROUP_ELEMENT_ORDER_EQ_4, EDWARDS_GROUP_ELEMENT_ORDER_EQ_8_EQUIV }
  -- @@RETURN END

end HolEC.Edwards
