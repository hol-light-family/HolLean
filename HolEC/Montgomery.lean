/- ========================================================================= -/
/- Montgomery curves in general, B * y^2 = x^3 + A * x^2 + x.              -/
/- ========================================================================= -/
/- File: HolEC/Montgomery.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/montgomery.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.Montgomery fills them).

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

namespace HolEC.Montgomery

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ASSOCIATIVITY_LEMMA CARD_SING CARD_SUBSET COND_SWAP CONJ_ASSOC DE_MORGAN_THM
   EVEN FIELD_CHAR_NOT2 FIELD_IMP_INTEGRAL_DOMAIN FINITE_CARD_LE_IMAGE
   FINITE_CARD_LE_UNION FINITE_IMAGE FINITE_PRODUCT FINITE_QUADRATIC_CURVE
   FINITE_SING FINITE_SUBSET FINITE_UNION FORALL_AND_THM FORALL_OPTION_THM
   FORALL_PAIR_THM FORALL_UNWIND_THM2 IMP_CONJ IMP_IMP IN IN_CROSS
   IN_ELIM_PAIR_THM IN_IMAGE IN_SING IN_UNION LET_DEF LET_END_DEF LE_REFL
   LE_TRANS NOT_EXISTS_THM NOT_IMP PAIR_EQ RIGHT_FORALL_IMP_THM
   RIGHT_IMP_FORALL_THM RING_0 RING_ADD RING_NEG SUBSET UNWIND_THM1
   abelian_group group_carrier group_id group_inv group_mul group_pow
   group_tybij option_DISTINCT option_INJ : thm)
  deriving Inhabited

/-- What montgomery.ml uses from Session besides theorems. -/
structure MontgomeryDeps where
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
/- Montgomery curves in general, B * y^2 = x^3 + A * x^2 + x: basic          -/
/- definitions and naive cardinality bounds; strong nonsingularity.          -/
/- (montgomery.ml 1-161)                                                     -/
/- ------------------------------------------------------------------------- -/

structure MontgomeryDefs where
  -- @@FIELDS
  montgomery_point : thm
  montgomery_curve : thm
  montgomery_nonsingular : thm
  montgomery_neg : thm
  montgomery_add : thm
  montgomery_group : thm
  FINITE_MONTGOMERY_CURVE : thm
  CARD_BOUND_MONTGOMERY_CURVE : thm
  montgomery_strongly_nonsingular : thm
  MONTGOMERY_STRONGLY_NONSINGULAR : thm
  MONTGOMERY_STRONGLY_NONSINGULAR_IMP_NONSINGULAR : thm
  deriving Inhabited

@[nospecialize]
def setupMontgomeryDefs [HolBase] (D : MontgomeryDeps) :
    ExceptT String IO MontgomeryDefs := do
  -- @@SCOPE BEGIN
  let { FIELD_TAC, MESON, NOT_RING_CHAR_DIVIDES_TAC, RING_CARRIER_TAC, RING_TAC, TAUT,
        define, .. } := D
  let { CARD_SING, CARD_SUBSET, FIELD_CHAR_NOT2, FIELD_IMP_INTEGRAL_DOMAIN,
        FINITE_CARD_LE_IMAGE, FINITE_CARD_LE_UNION, FINITE_IMAGE, FINITE_PRODUCT,
        FINITE_QUADRATIC_CURVE, FINITE_SING, FINITE_SUBSET, FINITE_UNION,
        FORALL_AND_THM, FORALL_OPTION_THM, FORALL_PAIR_THM, FORALL_UNWIND_THM2, IN,
        IN_CROSS, IN_ELIM_PAIR_THM, IN_IMAGE, IN_SING, IN_UNION, LE_REFL, LE_TRANS,
        NOT_EXISTS_THM, NOT_IMP, RIGHT_FORALL_IMP_THM, RING_0, SUBSET, UNWIND_THM1,
        option_DISTINCT, option_INJ, .. } := D.core1
  -- @@SCOPE END

  let montgomery_point ← define
   r"(montgomery_point f NONE <=> T) /\
  (montgomery_point f (SOME(x:A,y)) <=>
        x IN ring_carrier f /\ y IN ring_carrier f)"

  let montgomery_curve ← define
   r"(montgomery_curve(f:A ring,a:A,b:A) NONE <=> T) /\
  (montgomery_curve(f:A ring,a:A,b:A) (SOME(x,y)) <=>
        x IN ring_carrier f /\ y IN ring_carrier f /\
        ring_mul f b (ring_pow f y 2) =
        ring_add f (ring_pow f x 3)
                   (ring_add f (ring_mul f a (ring_pow f x 2)) x))"

  let montgomery_nonsingular ← define
   r"montgomery_nonsingular (f:A ring,a:A,b:A) <=>
        ~(b = ring_0 f) /\ ~(ring_pow f a 2 = ring_of_num f 4)"

  let montgomery_neg ← define
   r"(montgomery_neg (f:A ring,a:A,b:A) NONE = NONE) /\
  (montgomery_neg (f:A ring,a:A,b:A) (SOME(x:A,y)) = SOME(x,ring_neg f y))"

  let montgomery_add ← define
   r"(!y. montgomery_add (f:A ring,a:A,b:A) NONE y = y) /\
  (!x. montgomery_add (f:A ring,a:A,b:A) x NONE = x) /\
  (!x1 y1 x2 y2.
        montgomery_add (f:A ring,a:A,b:A) (SOME(x1,y1)) (SOME(x2,y2)) =
        if x1 = x2 then
          if y1 = y2 /\ ~(y1 = ring_0 f) then
            let l = ring_div f
                (ring_add f (ring_mul f (ring_of_num f 3) (ring_pow f x1 2))
                            (ring_add f (ring_mul f (ring_of_num f 2)
                                                    (ring_mul f a x1))
                                        (ring_of_num f 1)))
                (ring_mul f (ring_of_num f 2) (ring_mul f b y1)) in
            let x3 = ring_sub f (ring_sub f (ring_mul f b (ring_pow f l 2)) a)
                                (ring_mul f (ring_of_num f 2) x1) in
            let y3 = ring_sub f (ring_mul f l (ring_sub f x1 x3)) y1 in
            SOME(x3,y3)
          else NONE
        else
          let l = ring_div f (ring_sub f y2 y1) (ring_sub f x2 x1) in
          let x3 = ring_sub f (ring_sub f (ring_mul f b (ring_pow f l 2)) a)
                              (ring_add f x1 x2) in
          let y3 = ring_sub f (ring_mul f l (ring_sub f x1 x3)) y1 in
          SOME(x3,y3))"

  let montgomery_group ← define
   r"montgomery_group (f:A ring,a:A,b:A) =
        group(montgomery_curve(f,a,b),
              NONE,
              montgomery_neg(f,a,b),
              montgomery_add(f,a,b))"

  let FINITE_MONTGOMERY_CURVE ← prove
   r"!f a b:A. field f /\ FINITE(ring_carrier f)
             ==> FINITE(montgomery_curve(f,a,b))"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
     (← q r"IMAGE SOME {(x,y) | (x:A) IN ring_carrier f /\ y IN ring_carrier f} UNION
      {NONE}") THEN
    ASM_SIMP_TAC [FINITE_UNION, FINITE_IMAGE, FINITE_SING, FINITE_PRODUCT] THEN
    REWRITE_TAC [montgomery_curve, SUBSET, FORALL_OPTION_THM,
                 IN_UNION, IN_SING, IN_IMAGE, option_INJ, FORALL_PAIR_THM,
                 IN_ELIM_PAIR_THM, UNWIND_THM1] THEN
    SIMP_TAC [montgomery_curve, IN]))

  let CARD_BOUND_MONTGOMERY_CURVE ← prove
   r"!f a b:A. field f /\ FINITE(ring_carrier f) /\
             a IN ring_carrier f /\ b IN ring_carrier f /\ ~(b = ring_0 f)
             ==> CARD(montgomery_curve(f,a,b))
                   <= 2 * CARD(ring_carrier f) + 1"
   (← do
    let m1 ← MESON [FINITE_SUBSET, CARD_SUBSET, LE_TRANS]
     (← q r"!s. t SUBSET s /\ FINITE s /\ CARD s <= n ==> CARD t <= n")
    pure (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC m1 THEN
    EXISTS_TAC
     (← q r"IMAGE SOME
       {(x,y) | (x:A) IN ring_carrier f /\ y IN ring_carrier f /\
                ring_pow f y 2 =
                ring_div f (ring_add f (ring_pow f x 3)
                             (ring_add f (ring_mul f a (ring_pow f x 2)) x)) b}
      UNION {NONE}") THEN
    CONJ_TAC THENL
     [REWRITE_TAC [montgomery_curve, SUBSET, FORALL_OPTION_THM,
        IN_UNION, IN_SING, IN_IMAGE, option_INJ, FORALL_PAIR_THM,
        IN_ELIM_PAIR_THM, UNWIND_THM1] THEN
      REWRITE_TAC [option_DISTINCT, IN_CROSS] THEN
      REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [IN] THEN
      ASM_REWRITE_TAC [montgomery_curve] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC [] THEN FIELD_TAC,
      MATCH_MP_TAC FINITE_CARD_LE_UNION] THEN
    REWRITE_TAC [FINITE_SING, CARD_SING, LE_REFL] THEN
    MATCH_MP_TAC FINITE_CARD_LE_IMAGE THEN
    MATCH_MP_TAC FINITE_QUADRATIC_CURVE THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))

  /- A stronger form of nonsingularity, implying not only that the core cubic
     doesn't have repeated roots but has no roots at all except for (0,0). -/

  let montgomery_strongly_nonsingular ← define
   r"montgomery_strongly_nonsingular(f,a:A,b:A) <=>
      ~(b = ring_0 f) /\
      ~(?z. z IN ring_carrier f /\
            ring_pow f z 2 = ring_sub f (ring_pow f a 2) (ring_of_num f 4))"

  let MONTGOMERY_STRONGLY_NONSINGULAR ← prove
   r"!f a b:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f
        ==> (montgomery_strongly_nonsingular(f,a,b) <=>
             !x y. montgomery_curve(f,a,b) (SOME(x,y))
                   ==> (y = ring_0 f <=> x = ring_0 f))"
   (← do
    -- right to left: the third TAUT, the second, then the first
    let t3 ← TAUT (← q r"p ==> q <=> ~(p /\ ~q)")
    let t2 ← TAUT (← q r"(~p ==> q) /\ (p ==> ~q) ==> (~p <=> q)")
    let t1 ← TAUT (← q r"p ==> (q <=> r) <=> (r ==> p ==> q) /\ (q ==> p ==> r)")
    pure (REWRITE_TAC [FIELD_CHAR_NOT2] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [montgomery_strongly_nonsingular] THEN
    REWRITE_TAC [FORALL_AND_THM, t1] THEN
    REWRITE_TAC [RIGHT_FORALL_IMP_THM, FORALL_UNWIND_THM2] THEN
    REWRITE_TAC [montgomery_curve] THEN BINOP_TAC THENL
     [MATCH_MP_TAC t2 THEN
      CONJ_TAC THENL
       [REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC,
        DISCH_THEN SUBST1_TAC THEN DISCH_THEN (MP_TAC o SPEC (← q r"ring_1 f:A")) THEN
        REWRITE_TAC [NOT_IMP] THEN
        REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC],
      REWRITE_TAC [← GSYM NOT_EXISTS_THM, montgomery_curve, t3] THEN
      AP_TERM_TAC THEN EQ_TAC THENL
       [DISCH_THEN (X_CHOOSE_THEN (← q r"z:A") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"ring_div f (ring_sub f z a) (ring_of_num f 2):A"),
        DISCH_THEN (X_CHOOSE_THEN (← q r"x:A") STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (← q r"ring_add f (ring_mul f (ring_of_num f 2) x) a:A")] THEN
      REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC THEN
      NOT_RING_CHAR_DIVIDES_TAC]))

  let MONTGOMERY_STRONGLY_NONSINGULAR_IMP_NONSINGULAR ← prove
   r"!f a b:A.
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_strongly_nonsingular(f,a,b)
        ==> montgomery_nonsingular(f,a,b)"
   (← do
    pure (REWRITE_TAC [montgomery_strongly_nonsingular, montgomery_nonsingular] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [NOT_EXISTS_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC (← q r"ring_0 f:A")) THEN
    ASM_REWRITE_TAC [RING_0] THEN RING_TAC))

  -- @@RETURN BEGIN
  return { montgomery_point, montgomery_curve, montgomery_nonsingular, montgomery_neg,
           montgomery_add, montgomery_group, FINITE_MONTGOMERY_CURVE,
           CARD_BOUND_MONTGOMERY_CURVE, montgomery_strongly_nonsingular,
           MONTGOMERY_STRONGLY_NONSINGULAR,
           MONTGOMERY_STRONGLY_NONSINGULAR_IMP_NONSINGULAR }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Proof of the group properties. This is just done by algebraic brute       -/
/- force except for the use of ASSOCIATIVITY_LEMMA to reduce the explosion   -/
/- of case distinctions.  (montgomery.ml 162-366)                            -/
/- ------------------------------------------------------------------------- -/

structure MontgomeryGroup where
  -- @@FIELDS
  MONTGOMERY_CURVE_IMP_POINT : thm
  MONTGOMERY_POINT_NEG : thm
  MONTGOMERY_POINT_ADD : thm
  MONTGOMERY_CURVE_0 : thm
  MONTGOMERY_CURVE_NEG : thm
  MONTGOMERY_CURVE_ADD : thm
  MONTGOMERY_ADD_LNEG : thm
  MONTGOMERY_ADD_SYM : thm
  MONTGOMERY_ADD_ASSOC : thm
  MONTGOMERY_GROUP : thm
  ABELIAN_MONTGOMERY_GROUP : thm
  GROUP_POW_MONTGOMERY_TORSION : thm
  deriving Inhabited

@[nospecialize]
def setupMontgomeryGroup [HolBase] (D : MontgomeryDeps) (BMontgomeryDefs : MontgomeryDefs) :
    ExceptT String IO MontgomeryGroup := do
  -- @@SCOPE BEGIN
  let { ASM_MESON_TAC, FIELD_TAC, INDUCT_TAC, INTEGRAL_DOMAIN_RULE, LET_TAC, MESON,
        NOT_RING_CHAR_DIVIDES_TAC, RING_CARRIER_TAC, .. } := D
  let { ASSOCIATIVITY_LEMMA, COND_SWAP, CONJ_ASSOC, DE_MORGAN_THM, EVEN,
        FIELD_CHAR_NOT2, FIELD_IMP_INTEGRAL_DOMAIN, FORALL_OPTION_THM, FORALL_PAIR_THM,
        IMP_CONJ, IMP_IMP, IN, LET_DEF, LET_END_DEF, PAIR_EQ, RIGHT_FORALL_IMP_THM,
        RIGHT_IMP_FORALL_THM, RING_ADD, RING_NEG, abelian_group, group_carrier,
        group_id, group_inv, group_mul, group_pow, group_tybij, option_DISTINCT,
        option_INJ, .. } := D.core1
  let { montgomery_add, montgomery_curve, montgomery_group, montgomery_neg,
        montgomery_nonsingular, montgomery_point, .. } := BMontgomeryDefs
  -- @@SCOPE END

  let MONTGOMERY_CURVE_IMP_POINT ← prove
   r"!f a b p. montgomery_curve(f,a,b) p ==> montgomery_point f p"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    SIMP_TAC [montgomery_curve, montgomery_point]))

  let MONTGOMERY_POINT_NEG ← prove
   r"!(f:A ring) a b p.
        montgomery_point f p
        ==> montgomery_point f (montgomery_neg (f,a,b) p)"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    SIMP_TAC [montgomery_neg, montgomery_point, RING_NEG]))

  let MONTGOMERY_POINT_ADD ← prove
   r"!(f:A ring) a b p q.
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_point f p /\ montgomery_point f q
        ==> montgomery_point f (montgomery_add (f,a,b) p q)"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    SIMP_TAC [montgomery_add, montgomery_point, LET_DEF, LET_END_DEF] THEN
    REPEAT STRIP_TAC THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [montgomery_point]) THEN
    REPEAT STRIP_TAC THEN RING_CARRIER_TAC))

  let MONTGOMERY_CURVE_0 ← prove
   r"!f a b:A. montgomery_curve(f,a,b) NONE"
   (← do
    pure (REWRITE_TAC [montgomery_curve]))

  let MONTGOMERY_CURVE_NEG ← prove
   r"!f a (b:A) p.
        integral_domain f /\ a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_curve(f,a,b) p
        ==> montgomery_curve(f,a,b) (montgomery_neg (f,a,b) p)"
   (← do
    pure (SIMP_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, RING_NEG,
                montgomery_curve, montgomery_neg] THEN
    REPEAT GEN_TAC THEN CONV_TAC (fun t => (INTEGRAL_DOMAIN_RULE t).run)))

  let MONTGOMERY_CURVE_ADD ← prove
   r"!f a (b:A) p q.
        field f /\ ~(ring_char f = 2) /\
        montgomery_nonsingular(f,a,b) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_curve(f,a,b) p /\ montgomery_curve(f,a,b) q
        ==> montgomery_curve(f,a,b) (montgomery_add (f,a,b) p q)"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT2] THEN REPLICATE_TAC 3 GEN_TAC THEN
    SIMP_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, RING_ADD,
             montgomery_nonsingular, montgomery_curve, montgomery_add] THEN
    REWRITE_TAC [← GSYM DE_MORGAN_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"x1:A", ← q r"y1:A", ← q r"x2:A", ← q r"y2:A"] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [DE_MORGAN_THM]) THEN
    REPEAT (FIRST_X_ASSUM (DISJ_CASES_THEN ASSUME_TAC)) THEN
    REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    REPEAT LET_TAC THEN REWRITE_TAC [montgomery_curve] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  let MONTGOMERY_ADD_LNEG ← prove
   r"!f a (b:A) p.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_curve(f,a,b) p
        ==> montgomery_add(f,a,b) (montgomery_neg (f,a,b) p) p = NONE"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT2] THEN REPLICATE_TAC 3 GEN_TAC THEN
    SIMP_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, RING_ADD,
                montgomery_curve, montgomery_neg, montgomery_add] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [DE_MORGAN_THM]) THEN
    REPEAT (FIRST_X_ASSUM (DISJ_CASES_THEN ASSUME_TAC)) THEN
    REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN
    REPEAT LET_TAC THEN REWRITE_TAC [option_DISTINCT] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    FIELD_TAC))

  let MONTGOMERY_ADD_SYM ← prove
   r"!f a (b:A) p q.
        field f /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_curve(f,a,b) p /\ montgomery_curve(f,a,b) q
        ==> montgomery_add (f,a,b) p q = montgomery_add (f,a,b) q p"
   (← do
    pure (REPLICATE_TAC 3 GEN_TAC THEN
    SIMP_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, RING_ADD,
                montgomery_curve, montgomery_add] THEN
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

  let MONTGOMERY_ADD_ASSOC ← prove
   r"!f a (b:A) p q r.
        field f /\ ~(ring_char f = 2) /\
        montgomery_nonsingular(f,a,b) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_curve(f,a,b) p /\
        montgomery_curve(f,a,b) q /\
        montgomery_curve(f,a,b) r
        ==> montgomery_add (f,a,b) p (montgomery_add (f,a,b) q r) =
            montgomery_add (f,a,b) (montgomery_add (f,a,b) p q) r"
   (← do
    -- the `let assoclemma = prove ... in` runs first
    let assoclemma ← prove
     r"!f (a:A) b x1 y1 x2 y2.
          field f /\
          montgomery_nonsingular(f,a,b) /\
          a IN ring_carrier f /\ b IN ring_carrier f /\
          montgomery_curve(f,a,b) (SOME(x1,y1)) /\
          montgomery_curve(f,a,b) (SOME(x2,y2))
          ==> (~(SOME(x2,y2) = SOME(x1,y1)) /\
               ~(SOME(x2,y2) = montgomery_neg (f,a,b) (SOME(x1,y1))) <=>
               ~(x1 = x2))"
     (REWRITE_TAC [montgomery_nonsingular] THEN
      REWRITE_TAC [montgomery_curve, montgomery_neg, option_INJ, PAIR_EQ] THEN
      FIELD_TAC)
    let addFirst2 := (← liftExcept (chop_list 2 (CONJUNCTS montgomery_add))).1
    let isVarEq (th : thm) : Bool :=
      let c := concl th
      is_eq c && (match lhand c, rand c with
                  | .ok l, .ok r => is_var l && is_var r
                  | _, _ => false)
    pure (REWRITE_TAC [FIELD_CHAR_NOT2] THEN
    REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM] THEN
    X_GEN_TAC (← q r"f:A ring") THEN REPEAT DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [← q r"a:A", ← q r"b:A"] THEN REPEAT DISCH_TAC THEN
    REWRITE_TAC [IMP_IMP, ← GSYM CONJ_ASSOC, RIGHT_IMP_FORALL_THM] THEN
    MATCH_MP_TAC ASSOCIATIVITY_LEMMA THEN
    MAP_EVERY EXISTS_TAC [← q r"montgomery_neg(f,a:A,b)", ← q r"NONE:(A#A)option"] THEN
    REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    REWRITE_TAC ((← CONJUNCT1 montgomery_curve) :: (← CONJUNCT1 montgomery_neg) ::
                 addFirst2) THEN
    REWRITE_TAC [CONJ_ASSOC] THEN CONJ_TAC THEN REWRITE_TAC [← GSYM CONJ_ASSOC] THENL
     [REPEAT CONJ_TAC THEN
      MAP_EVERY X_GEN_TAC [← q r"x1:A", ← q r"y1:A"] THEN REPEAT CONJ_TAC THEN
      TRY (MAP_EVERY X_GEN_TAC [← q r"x2:A", ← q r"y2:A"]) THEN REPEAT CONJ_TAC THEN
      TRY (MAP_EVERY X_GEN_TAC [← q r"x3:A", ← q r"y3:A"]) THEN REPEAT CONJ_TAC,
      MAP_EVERY X_GEN_TAC [← q r"x1:A", ← q r"y1:A", ← q r"x2:A", ← q r"y2:A",
                           ← q r"x3:A", ← q r"y3:A"] THEN
      ASM_SIMP_TAC [assoclemma, DE_MORGAN_THM] THEN
      REWRITE_TAC [option_DISTINCT] THEN
      REPEAT GEN_TAC THEN REWRITE_TAC [montgomery_curve] THEN
      STRIP_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC [montgomery_add]] THEN
    REWRITE_TAC [montgomery_curve, montgomery_add, montgomery_neg] THEN
    REPEAT (GEN_TAC ORELSE CONJ_TAC) THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REPEAT LET_TAC THEN
    REWRITE_TAC [option_DISTINCT, option_INJ, PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [montgomery_curve, montgomery_add, montgomery_neg] THEN
    REPEAT (GEN_TAC ORELSE CONJ_TAC) THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REPEAT LET_TAC THEN
    REWRITE_TAC [option_DISTINCT, option_INJ, PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC)) THEN
    REPEAT (FIRST_X_ASSUM (fun th => tactic_of do
      pure (SUBST_ALL_TAC (← SYM (← liftExcept (check isVarEq th)))))) THEN
    TRY RING_CARRIER_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE [montgomery_nonsingular]) THEN FIELD_TAC THEN
    NOT_RING_CHAR_DIVIDES_TAC))

  let MONTGOMERY_GROUP ← prove
   r"!f a (b:A).
      field f /\ ~(ring_char f = 2) /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      montgomery_nonsingular(f,a,b)
      ==> group_carrier(montgomery_group(f,a,b)) = montgomery_curve(f,a,b) /\
          group_id(montgomery_group(f,a,b)) = NONE /\
          group_inv(montgomery_group(f,a,b)) = montgomery_neg(f,a,b) /\
          group_mul(montgomery_group(f,a,b)) = montgomery_add(f,a,b)"
   (← do
    let m1 ← MESON [] (← q r"x = a /\ x = y ==> x = a /\ y = a")
    pure (REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC [group_carrier, group_id, group_inv, group_mul, ← GSYM PAIR_EQ] THEN
    REWRITE_TAC [montgomery_group, ← GSYM (← CONJUNCT2 group_tybij)] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC [IN, montgomery_curve],
      REWRITE_TAC [IN] THEN
      ASM_SIMP_TAC [MONTGOMERY_CURVE_NEG, FIELD_IMP_INTEGRAL_DOMAIN],
      REWRITE_TAC [IN] THEN ASM_SIMP_TAC [MONTGOMERY_CURVE_ADD],
      REWRITE_TAC [IN] THEN ASM_SIMP_TAC [MONTGOMERY_ADD_ASSOC],
      REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, montgomery_add],
      REWRITE_TAC [IN] THEN GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC m1 THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC [MONTGOMERY_ADD_LNEG],
        MATCH_MP_TAC MONTGOMERY_ADD_SYM THEN
        ASM_SIMP_TAC [MONTGOMERY_CURVE_NEG, FIELD_IMP_INTEGRAL_DOMAIN]]]))

  let ABELIAN_MONTGOMERY_GROUP ← prove
   r"!f a (b:A).
      field f /\ ~(ring_char f = 2) /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      montgomery_nonsingular(f,a,b)
      ==> abelian_group(montgomery_group(f,a,b))"
   (← do
    pure (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [abelian_group, MONTGOMERY_GROUP] THEN
    REWRITE_TAC [IN] THEN ASM_MESON_TAC [MONTGOMERY_ADD_SYM]))

  let GROUP_POW_MONTGOMERY_TORSION ← prove
   r"!(f:A ring) a b P n.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_nonsingular (f,a,b)
        ==> group_pow (montgomery_group(f,a,b)) (SOME (ring_0 f,ring_0 f)) n =
            if EVEN n then NONE else SOME(ring_0 f,ring_0 f)"
   (← do
    pure (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    INDUCT_TAC THEN
    ASM_SIMP_TAC [group_pow, EVEN, MONTGOMERY_GROUP, COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [montgomery_add]))

  -- @@RETURN BEGIN
  return { MONTGOMERY_CURVE_IMP_POINT, MONTGOMERY_POINT_NEG, MONTGOMERY_POINT_ADD,
           MONTGOMERY_CURVE_0, MONTGOMERY_CURVE_NEG, MONTGOMERY_CURVE_ADD,
           MONTGOMERY_ADD_LNEG, MONTGOMERY_ADD_SYM, MONTGOMERY_ADD_ASSOC,
           MONTGOMERY_GROUP, ABELIAN_MONTGOMERY_GROUP, GROUP_POW_MONTGOMERY_TORSION }
  -- @@RETURN END

end HolEC.Montgomery
