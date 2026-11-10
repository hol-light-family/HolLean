/- ========================================================================= -/
/- Elliptic curves in the basic Weierstrass form y^2 = x^3 + a x + b.      -/
/- ========================================================================= -/
/- File: HolEC/Weierstrass.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/weierstrass.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.Weierstrass fills them).

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

namespace HolEC.Weierstrass

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (AND_FORALL_THM ASSOCIATIVITY_LEMMA CARD_SING CONJ_ASSOC DE_MORGAN_THM
   FIELD_CHAR_NOT2 FIELD_CHAR_NOT23 FIELD_IMP_INTEGRAL_DOMAIN
   FINITE_CARD_LE_IMAGE FINITE_CARD_LE_SUBSET FINITE_CARD_LE_UNION
   FINITE_QUADRATIC_CURVE FINITE_SING FORALL_IN_IMAGE FORALL_OPTION_THM
   FORALL_PAIR_THM GROUP_HOMOMORPHISM GROUP_ID IMP_CONJ IMP_IMP IN IN_CROSS
   IN_ELIM_PAIR_THM IN_IMAGE IN_SING IN_UNION LET_DEF LET_END_DEF LE_REFL
   PAIR_EQ RIGHT_FORALL_IMP_THM RIGHT_IMP_FORALL_THM RING_ADD RING_NEG SUBSET
   UNWIND_THM1 group_carrier group_endomorphism group_id group_inv group_mul
   group_tybij option_DISTINCT option_INJ : thm)
  deriving Inhabited

/-- What weierstrass.ml uses from Session besides theorems. -/
structure WeierstrassDeps where
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
/- Basic definitions and naive cardinality bounds.  (weierstrass.ml 1-91)    -/
/- ------------------------------------------------------------------------- -/

structure WeierstrassDefs where
  -- @@FIELDS
  weierstrass_point : thm
  weierstrass_curve : thm
  weierstrass_neg : thm
  weierstrass_add : thm
  weierstrass_nonsingular : thm
  weierstrass_group : thm
  FINITE_WEIERSTRASS_CURVE : thm
  CARD_BOUND_WEIERSTRASS_CURVE : thm
  deriving Inhabited

@[nospecialize]
def setupWeierstrassDefs [HolBase] (D : WeierstrassDeps) :
    ExceptT String IO WeierstrassDefs := do
  -- @@SCOPE BEGIN
  let { TAUT, define, .. } := D
  let { AND_FORALL_THM, CARD_SING, FIELD_IMP_INTEGRAL_DOMAIN, FINITE_CARD_LE_IMAGE,
        FINITE_CARD_LE_SUBSET, FINITE_CARD_LE_UNION, FINITE_QUADRATIC_CURVE,
        FINITE_SING, FORALL_OPTION_THM, FORALL_PAIR_THM, IN, IN_CROSS,
        IN_ELIM_PAIR_THM, IN_IMAGE, IN_SING, IN_UNION, LE_REFL, SUBSET, UNWIND_THM1,
        option_DISTINCT, option_INJ, .. } := D.core1
  -- @@SCOPE END

  let weierstrass_point ← define
   r"(weierstrass_point f NONE <=> T) /\
  (weierstrass_point f (SOME(x:A,y)) <=>
        x IN ring_carrier f /\ y IN ring_carrier f)"

  let weierstrass_curve ← define
   r"(weierstrass_curve(f:A ring,a:A,b:A) NONE <=> T) /\
  (weierstrass_curve(f:A ring,a:A,b:A) (SOME(x,y)) <=>
        x IN ring_carrier f /\ y IN ring_carrier f /\
        ring_pow f y 2 =
        ring_add f (ring_pow f x 3) (ring_add f (ring_mul f a x) b))"

  let weierstrass_neg ← define
   r"(weierstrass_neg (f:A ring,a:A,b:A) NONE = NONE) /\
  (weierstrass_neg (f:A ring,a:A,b:A) (SOME(x:A,y)) = SOME(x,ring_neg f y))"

  let weierstrass_add ← define
   r"(!y. weierstrass_add (f:A ring,a:A,b:A) NONE y = y) /\
  (!x. weierstrass_add (f:A ring,a:A,b:A) x NONE = x) /\
  (!x1 y1 x2 y2.
        weierstrass_add (f:A ring,a:A,b:A) (SOME(x1,y1)) (SOME(x2,y2)) =
        if x1 = x2 then
          if y1 = y2 /\ ~(y1 = ring_0 f) then
            let m = ring_div f
              (ring_add f (ring_mul f (ring_of_num f 3) (ring_pow f x1 2)) a)
              (ring_mul f (ring_of_num f 2) y1) in
            let x3 = ring_sub f (ring_pow f m 2)
                                (ring_mul f (ring_of_num f 2) x1) in
            let y3 = ring_sub f (ring_mul f m (ring_sub f x1 x3)) y1 in
            SOME(x3,y3)
          else NONE
        else
          let m = ring_div f (ring_sub f y2 y1) (ring_sub f x2 x1) in
          let x3 = ring_sub f (ring_pow f m 2)
                              (ring_add f x1 x2) in
          let y3 = ring_sub f (ring_mul f m (ring_sub f x1 x3)) y1 in
          SOME(x3,y3))"

  let weierstrass_nonsingular ← define
   r"weierstrass_nonsingular (f:A ring,a:A,b:A) <=>
        ~(ring_add f (ring_mul f (ring_of_num f 4) (ring_pow f a 3))
                     (ring_mul f (ring_of_num f 27) (ring_pow f b 2)) =
          ring_0 f)"

  let weierstrass_group ← define
   r"weierstrass_group (f:A ring,a:A,b:A) =
        group(weierstrass_curve(f,a,b),
              NONE,
              weierstrass_neg(f,a,b),
              weierstrass_add(f,a,b))"

  let (FINITE_WEIERSTRASS_CURVE, CARD_BOUND_WEIERSTRASS_CURVE) ← do
    let th ← prove
     r"(!f a b:A. field f /\ FINITE(ring_carrier f)
              ==> FINITE(weierstrass_curve(f,a,b))) /\
   (!f a b:A. field f /\ FINITE(ring_carrier f)
              ==> CARD(weierstrass_curve(f,a,b))
                   <= 2 * CARD(ring_carrier f) + 1)"
     (← do
      let t1 ← TAUT (← q r"(p ==> q) /\ (p ==> r) <=> p ==> q /\ r")
      pure (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
      REWRITE_TAC [t1] THEN
      STRIP_TAC THEN MATCH_MP_TAC FINITE_CARD_LE_SUBSET THEN EXISTS_TAC
       (← q r"IMAGE SOME
         {(x,y) | (x:A) IN ring_carrier f /\ y IN ring_carrier f /\
                  ring_pow f y 2 =
                  ring_add f (ring_pow f x 3) (ring_add f (ring_mul f a x) b)}
        UNION {NONE}") THEN
      CONJ_TAC THENL
       [REWRITE_TAC [weierstrass_curve, SUBSET, FORALL_OPTION_THM,
          IN_UNION, IN_SING, IN_IMAGE, option_INJ, FORALL_PAIR_THM,
          IN_ELIM_PAIR_THM, UNWIND_THM1] THEN
        REWRITE_TAC [option_DISTINCT, IN_CROSS] THEN REWRITE_TAC [IN] THEN
        REWRITE_TAC [weierstrass_curve] THEN SIMP_TAC [IN],
        MATCH_MP_TAC FINITE_CARD_LE_UNION] THEN
      REWRITE_TAC [FINITE_SING, CARD_SING, LE_REFL] THEN
      MATCH_MP_TAC FINITE_CARD_LE_IMAGE THEN
      MATCH_MP_TAC FINITE_QUADRATIC_CURVE THEN
      ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))
    CONJ_PAIR th

  -- @@RETURN BEGIN
  return { weierstrass_point, weierstrass_curve, weierstrass_neg, weierstrass_add,
           weierstrass_nonsingular, weierstrass_group, FINITE_WEIERSTRASS_CURVE,
           CARD_BOUND_WEIERSTRASS_CURVE }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Proof of the group properties. This is just done by algebraic brute       -/
/- force except for the use of ASSOCIATIVITY_LEMMA to reduce the explosion   -/
/- of case distinctions.  (weierstrass.ml 92-295)                            -/
/- ------------------------------------------------------------------------- -/

structure WeierstrassGroup where
  -- @@FIELDS
  WEIERSTRASS_CURVE_IMP_POINT : thm
  WEIERSTRASS_POINT_NEG : thm
  WEIERSTRASS_POINT_ADD : thm
  WEIERSTRASS_CURVE_0 : thm
  WEIERSTRASS_CURVE_NEG : thm
  WEIERSTRASS_CURVE_ADD : thm
  WEIERSTRASS_ADD_LNEG : thm
  WEIERSTRASS_ADD_SYM : thm
  WEIERSTRASS_ADD_ASSOC : thm
  WEIERSTRASS_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupWeierstrassGroup [HolBase] (D : WeierstrassDeps) (BWeierstrassDefs : WeierstrassDefs) :
    ExceptT String IO WeierstrassGroup := do
  -- @@SCOPE BEGIN
  let { FIELD_TAC, INTEGRAL_DOMAIN_RULE, LET_TAC, MESON, NOT_RING_CHAR_DIVIDES_TAC,
        RING_CARRIER_TAC, RING_PULL_DIV_TAC, RING_TAC, let_CONV, .. } := D
  let { ASSOCIATIVITY_LEMMA, CONJ_ASSOC, DE_MORGAN_THM, FIELD_CHAR_NOT2,
        FIELD_CHAR_NOT23, FIELD_IMP_INTEGRAL_DOMAIN, FORALL_OPTION_THM,
        FORALL_PAIR_THM, IMP_CONJ, IMP_IMP, IN, LET_DEF, LET_END_DEF, PAIR_EQ,
        RIGHT_FORALL_IMP_THM, RIGHT_IMP_FORALL_THM, RING_ADD, RING_NEG, group_carrier,
        group_id, group_inv, group_mul, group_tybij, option_DISTINCT, option_INJ, .. } := D.core1
  let { weierstrass_add, weierstrass_curve, weierstrass_group, weierstrass_neg,
        weierstrass_nonsingular, weierstrass_point, .. } := BWeierstrassDefs
  -- @@SCOPE END

  let WEIERSTRASS_CURVE_IMP_POINT ← prove
   r"!f a b p. weierstrass_curve(f,a,b) p ==> weierstrass_point f p"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    SIMP_TAC [weierstrass_curve, weierstrass_point]))

  let WEIERSTRASS_POINT_NEG ← prove
   r"!(f:A ring) a b p.
        weierstrass_point f p
        ==> weierstrass_point f (weierstrass_neg (f,a,b) p)"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    SIMP_TAC [weierstrass_neg, weierstrass_point, RING_NEG]))

  let WEIERSTRASS_POINT_ADD ← prove
   r"!(f:A ring) a b p q.
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_point f p /\ weierstrass_point f q
        ==> weierstrass_point f (weierstrass_add (f,a,b) p q)"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    SIMP_TAC [weierstrass_add, weierstrass_point, LET_DEF, LET_END_DEF] THEN
    REPEAT STRIP_TAC THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [weierstrass_point]) THEN
    REPEAT STRIP_TAC THEN RING_CARRIER_TAC))

  let WEIERSTRASS_CURVE_0 ← prove
   r"!f a b:A. weierstrass_curve(f,a,b) NONE"
   (← do
    pure (REWRITE_TAC [weierstrass_curve]))

  let WEIERSTRASS_CURVE_NEG ← prove
   r"!f a (b:A) p.
        integral_domain f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve(f,a,b) p
        ==> weierstrass_curve(f,a,b) (weierstrass_neg (f,a,b) p)"
   (← do
    pure (SIMP_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, RING_NEG,
                weierstrass_curve, weierstrass_neg] THEN
    REPEAT GEN_TAC THEN CONV_TAC (fun t => (INTEGRAL_DOMAIN_RULE t).run)))

  let WEIERSTRASS_CURVE_ADD ← prove
   r"!f a (b:A) p q.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve(f,a,b) p /\ weierstrass_curve(f,a,b) q
        ==> weierstrass_curve(f,a,b) (weierstrass_add (f,a,b) p q)"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT2] THEN REPLICATE_TAC 3 GEN_TAC THEN
    SIMP_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, RING_ADD,
                weierstrass_curve, weierstrass_add] THEN
    MAP_EVERY X_GEN_TAC [← q r"x1:A", ← q r"y1:A", ← q r"x2:A", ← q r"y2:A"] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [DE_MORGAN_THM]) THEN
    REPEAT (FIRST_X_ASSUM (DISJ_CASES_THEN ASSUME_TAC)) THEN
    REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THENL
     [CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC [weierstrass_curve] THEN
      REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
      SUBGOAL_THEN (← q r"~(ring_of_num f 2:A = ring_0 f)") ASSUME_TAC THENL
       [FIELD_TAC, RING_PULL_DIV_TAC THEN RING_TAC],
      ALL_TAC, ALL_TAC, ALL_TAC] THEN
    REPEAT LET_TAC THEN REWRITE_TAC [weierstrass_curve] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  let WEIERSTRASS_ADD_LNEG ← prove
   r"!f a (b:A) p.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve(f,a,b) p
        ==> weierstrass_add(f,a,b) (weierstrass_neg (f,a,b) p) p = NONE"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT2] THEN REPLICATE_TAC 3 GEN_TAC THEN
    SIMP_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, RING_ADD,
                weierstrass_curve, weierstrass_neg, weierstrass_add] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [DE_MORGAN_THM]) THEN
    REPEAT (FIRST_X_ASSUM (DISJ_CASES_THEN ASSUME_TAC)) THEN
    REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN
    REPEAT LET_TAC THEN REWRITE_TAC [option_DISTINCT] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    FIELD_TAC))

  let WEIERSTRASS_ADD_SYM ← prove
   r"!f a (b:A) p q.
        field f /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve(f,a,b) p /\ weierstrass_curve(f,a,b) q
        ==> weierstrass_add (f,a,b) p q = weierstrass_add (f,a,b) q p"
   (← do
    pure (REPLICATE_TAC 3 GEN_TAC THEN
    SIMP_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, RING_ADD,
                weierstrass_curve, weierstrass_add] THEN
    MAP_EVERY X_GEN_TAC [← q r"x1:A", ← q r"y1:A", ← q r"x2:A", ← q r"y2:A"] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [DE_MORGAN_THM]) THEN
    REPEAT (FIRST_X_ASSUM (DISJ_CASES_THEN ASSUME_TAC)) THEN
    REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    REPEAT LET_TAC THEN
    REWRITE_TAC [option_DISTINCT, option_INJ, PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    FIELD_TAC))

  let WEIERSTRASS_ADD_ASSOC ← prove
   r"!f a (b:A) p q r.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        weierstrass_nonsingular(f,a,b) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_curve(f,a,b) p /\
        weierstrass_curve(f,a,b) q /\
        weierstrass_curve(f,a,b) r
        ==> weierstrass_add (f,a,b) p (weierstrass_add (f,a,b) q r) =
            weierstrass_add (f,a,b) (weierstrass_add (f,a,b) p q) r"
   (← do
    -- the `let assoclemma = prove ... in` runs first
    let assoclemma ← prove
     r"!f (a:A) b x1 y1 x2 y2.
          field f /\
          a IN ring_carrier f /\ b IN ring_carrier f /\
          weierstrass_curve(f,a,b) (SOME(x1,y1)) /\
          weierstrass_curve(f,a,b) (SOME(x2,y2))
          ==> (~(SOME(x2,y2) = SOME(x1,y1)) /\
               ~(SOME(x2,y2) = weierstrass_neg (f,a,b) (SOME(x1,y1))) <=>
               ~(x1 = x2))"
     (REWRITE_TAC [weierstrass_curve, weierstrass_neg, option_INJ, PAIR_EQ] THEN
      FIELD_TAC)
    let addFirst2 := (← liftExcept (chop_list 2 (CONJUNCTS weierstrass_add))).1
    let isVarEq (th : thm) : Bool :=
      let c := concl th
      is_eq c && (match lhand c, rand c with
                  | .ok l, .ok r => is_var l && is_var r
                  | _, _ => false)
    pure (REWRITE_TAC [FIELD_CHAR_NOT23] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    X_GEN_TAC (← q r"f:A ring") THEN REPEAT DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"a:A", ← q r"b:A"] THEN REPEAT DISCH_TAC THEN
    REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC, RIGHT_IMP_FORALL_THM] THEN
    MATCH_MP_TAC ASSOCIATIVITY_LEMMA THEN
    MAP_EVERY EXISTS_TAC [← q r"weierstrass_neg(f,a:A,b)", ← q r"NONE:(A#A)option"] THEN
    REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    REWRITE_TAC ((← CONJUNCT1 weierstrass_curve) :: (← CONJUNCT1 weierstrass_neg) ::
                 addFirst2) THEN
    REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THEN REWRITE_TAC [← GSYM CONJ_ASSOC] THENL
     [REPEAT CONJ_TAC THEN
      MAP_EVERY X_GEN_TAC [← q r"x1:A", ← q r"y1:A"] THEN
      TRY (MAP_EVERY X_GEN_TAC [← q r"x2:A", ← q r"y2:A"]) THEN
      TRY (MAP_EVERY X_GEN_TAC [← q r"x3:A", ← q r"y3:A"]),
      MAP_EVERY X_GEN_TAC [← q r"x1:A", ← q r"y1:A", ← q r"x2:A", ← q r"y2:A",
                           ← q r"x3:A", ← q r"y3:A"] THEN
      ASM_SIMP_TAC [assoclemma, DE_MORGAN_THM] THEN
      REWRITE_TAC [option_DISTINCT] THEN
      REPEAT GEN_TAC THEN REWRITE_TAC [weierstrass_curve] THEN
      STRIP_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [weierstrass_add]] THEN
    REWRITE_TAC [weierstrass_curve, weierstrass_add, weierstrass_neg] THEN
    REPEAT (GEN_TAC ORELSE CONJ_TAC) THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REPEAT LET_TAC THEN
    REWRITE_TAC [option_DISTINCT, option_INJ, PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [weierstrass_curve, weierstrass_add, weierstrass_neg] THEN
    REPEAT (GEN_TAC ORELSE CONJ_TAC) THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REPEAT LET_TAC THEN
    REWRITE_TAC [option_DISTINCT, option_INJ, PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN
    REPEAT (FIRST_X_ASSUM (fun th => tactic_of do
      pure (SUBST_ALL_TAC (← SYM (← liftExcept (check isVarEq th)))))) THEN
    TRY RING_CARRIER_TAC THEN
    (FIELD_TAC ORELSE
     (RULE_ASSUM_TAC (REWRITE_RULE [weierstrass_nonsingular]) THEN FIELD_TAC)) THEN
    NOT_RING_CHAR_DIVIDES_TAC))

  let WEIERSTRASS_GROUP ← prove
   r"!f a (b:A).
      field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      weierstrass_nonsingular(f,a,b)
      ==> group_carrier(weierstrass_group(f,a,b)) = weierstrass_curve(f,a,b) /\
          group_id(weierstrass_group(f,a,b)) = NONE /\
          group_inv(weierstrass_group(f,a,b)) = weierstrass_neg(f,a,b) /\
          group_mul(weierstrass_group(f,a,b)) = weierstrass_add(f,a,b)"
   (← do
    let m1 ← MESON [] (← q r"x = a /\ x = y ==> x = a /\ y = a")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC [group_carrier, group_id, group_inv, group_mul, ← GSYM PAIR_EQ] THEN
    REWRITE_TAC [weierstrass_group, ← GSYM (← CONJUNCT2 group_tybij)] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [IN, weierstrass_curve],
      REWRITE_TAC [IN] THEN
      ASM_SIMP_TAC [WEIERSTRASS_CURVE_NEG, FIELD_IMP_INTEGRAL_DOMAIN],
      REWRITE_TAC [IN] THEN ASM_SIMP_TAC [WEIERSTRASS_CURVE_ADD],
      REWRITE_TAC [IN] THEN ASM_SIMP_TAC [WEIERSTRASS_ADD_ASSOC],
      REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, weierstrass_add],
      REWRITE_TAC [IN] THEN GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC m1 THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC [WEIERSTRASS_ADD_LNEG],
        MATCH_MP_TAC WEIERSTRASS_ADD_SYM THEN
        ASM_SIMP_TAC [WEIERSTRASS_CURVE_NEG, FIELD_IMP_INTEGRAL_DOMAIN]]]))

  -- @@RETURN BEGIN
  return { WEIERSTRASS_CURVE_IMP_POINT, WEIERSTRASS_POINT_NEG, WEIERSTRASS_POINT_ADD,
           WEIERSTRASS_CURVE_0, WEIERSTRASS_CURVE_NEG, WEIERSTRASS_CURVE_ADD,
           WEIERSTRASS_ADD_LNEG, WEIERSTRASS_ADD_SYM, WEIERSTRASS_ADD_ASSOC,
           WEIERSTRASS_GROUP }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Easily computable endomorphisms in some special Weierstrass curves.       -/
/- (x,y) |-> (c * x,y) where c^3 = 1 for curves y^2 = x^3 + b.               -/
/- (x,y) |-> (-x, c * y) where c^4 = 1 for curves y^2 = x^3 + a * x.         -/
/- (weierstrass.ml 296-343)                                                  -/
/- ------------------------------------------------------------------------- -/

structure WeierstrassEndo where
  -- @@FIELDS
  weierstrass_triplex : thm
  GROUP_ENDOMORPHISM_TRIPLEX : thm
  weierstrass_quady : thm
  GROUP_ENDOMORPHISM_QUADY : thm
  deriving Inhabited

@[nospecialize]
def setupWeierstrassEndo [HolBase] (D : WeierstrassDeps) (BWeierstrassDefs : WeierstrassDefs) (BWeierstrassGroup : WeierstrassGroup) :
    ExceptT String IO WeierstrassEndo := do
  -- @@SCOPE BEGIN
  let { FIELD_TAC, LET_TAC, NOT_RING_CHAR_DIVIDES_TAC, RING_CARRIER_TAC, define, .. } := D
  let { FIELD_CHAR_NOT23, FORALL_IN_IMAGE, FORALL_OPTION_THM, FORALL_PAIR_THM,
        GROUP_HOMOMORPHISM, GROUP_ID, IN, PAIR_EQ, SUBSET, group_endomorphism,
        option_DISTINCT, option_INJ, .. } := D.core1
  let { weierstrass_add, weierstrass_curve, weierstrass_nonsingular, .. } := BWeierstrassDefs
  let { WEIERSTRASS_GROUP, .. } := BWeierstrassGroup
  -- @@SCOPE END

  let weierstrass_triplex ← define
   r"weierstrass_triplex f (c:A) NONE = NONE /\
  weierstrass_triplex f c (SOME(x:A,y:A)) = SOME(ring_mul f c x,y)"

  let GROUP_ENDOMORPHISM_TRIPLEX ← prove
   r"!f a b c:A.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_nonsingular (f,a,b) /\
        c IN ring_carrier f /\ ring_pow f c 3 = ring_1 f /\ a = ring_0 f
        ==> group_endomorphism (weierstrass_group(f,a,b))
                               (weierstrass_triplex f c)"
   (← do
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"a:A = ring_0 f") THEN
    ASM_SIMP_TAC [group_endomorphism, GROUP_HOMOMORPHISM] THEN
    SIMP_TAC [SUBSET, FORALL_IN_IMAGE, WEIERSTRASS_GROUP, GROUP_ID] THEN
    POP_ASSUM (K ALL_TAC : thm → tactic) THEN REWRITE_TAC [FIELD_CHAR_NOT23] THEN STRIP_TAC THEN
    REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, IN] THEN
    REWRITE_TAC [weierstrass_curve, weierstrass_triplex, weierstrass_add] THEN
    REPEAT STRIP_TAC THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REPEAT LET_TAC THEN REWRITE_TAC [weierstrass_triplex] THEN
    TRY RING_CARRIER_TAC THEN
    REWRITE_TAC [option_DISTINCT, option_INJ, PAIR_EQ] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [weierstrass_nonsingular]) THEN FIELD_TAC))

  let weierstrass_quady ← define
   r"weierstrass_quady f (c:A) NONE = NONE /\
  weierstrass_quady f c (SOME(x:A,y:A)) = SOME(ring_neg f x,ring_mul f c y)"

  let GROUP_ENDOMORPHISM_QUADY ← prove
   r"!f a b c:A.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        weierstrass_nonsingular (f,a,b) /\
        c IN ring_carrier f /\ b = ring_0 f /\
        ring_pow f c 4 = ring_1 f /\ ~(ring_pow f c 2 = ring_1 f)
        ==> group_endomorphism (weierstrass_group(f,a,b))
                               (weierstrass_quady f c)"
   (← do
    pure (REPEAT GEN_TAC THEN ASM_CASES_TAC (← q r"b:A = ring_0 f") THEN
    ASM_SIMP_TAC [group_endomorphism, GROUP_HOMOMORPHISM] THEN
    SIMP_TAC [SUBSET, FORALL_IN_IMAGE, WEIERSTRASS_GROUP, GROUP_ID] THEN
    POP_ASSUM (K ALL_TAC : thm → tactic) THEN REWRITE_TAC [FIELD_CHAR_NOT23] THEN STRIP_TAC THEN
    REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, IN] THEN
    REWRITE_TAC [weierstrass_curve, weierstrass_quady, weierstrass_add] THEN
    REPEAT STRIP_TAC THEN REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REPEAT LET_TAC THEN REWRITE_TAC [weierstrass_quady] THEN
    TRY RING_CARRIER_TAC THEN
    REWRITE_TAC [option_DISTINCT, option_INJ, PAIR_EQ] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [weierstrass_nonsingular]) THEN FIELD_TAC THEN
    NOT_RING_CHAR_DIVIDES_TAC))

  -- @@RETURN BEGIN
  return { weierstrass_triplex, GROUP_ENDOMORPHISM_TRIPLEX, weierstrass_quady,
           GROUP_ENDOMORPHISM_QUADY }
  -- @@RETURN END

end HolEC.Weierstrass
