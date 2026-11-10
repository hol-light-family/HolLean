/- ========================================================================= -/
/- Isomorphic mappings from Montgomery to Weierstrass form and back again. -/
/- ========================================================================= -/
/- File: HolEC/Montwe.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/montwe.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/montgomery.ml, EC/weierstrass.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.Montwe fills them).

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
import HolEC.Weierstrass

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolEC.Montwe

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (DE_MORGAN_THM FIELD_CHAR_NOT23 FIELD_CHAR_NOT3 FORALL_IN_IMAGE
   FORALL_OPTION_THM FORALL_PAIR_THM GROUP_HOMOMORPHISM GROUP_ISOMORPHISMS
   GROUP_ISOMORPHISMS_IMP_ISOMORPHISM GROUP_ISOMORPHISMS_SYM IN
   ISOMORPHIC_GROUP_SYM MONTGOMERY_GROUP PAIR_EQ SUBSET WEIERSTRASS_GROUP
   isomorphic_group montgomery_add montgomery_curve montgomery_neg
   montgomery_nonsingular montgomery_point option_DISTINCT option_INJ
   weierstrass_add weierstrass_curve weierstrass_neg weierstrass_nonsingular
   weierstrass_point : thm)
  deriving Inhabited

/-- What montwe.ml uses from Session besides theorems. -/
structure MontweDeps where
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
/- Map from Montgomery to Weierstrass by (x,y) |-> ((x + A / 3) / B, y / B)  -/
/- and from Weierstrass to Montgomery by (x,y) |-> (B * x - A / 3, B * y),   -/
/- so a Montgomery(A,B) curve gives Weierstrass(a,b) where                   -/
/-     a = (1 - A^2 / 3) / B^2                                               -/
/-     b = A * (2 * A^2 - 9) / (27 * B^3)                                    -/
/- and the maps are mutually inverse.  (montwe.ml 1-112)                     -/
/- ------------------------------------------------------------------------- -/

structure MontweMaps where
  -- @@FIELDS
  wcurve_of_mcurve : thm
  WCURVE_OF_MCURVE_NONSINGULAR_EQ : thm
  WCURVE_OF_MCURVE_NONSINGULAR : thm
  weierstrass_of_montgomery : thm
  montgomery_of_weierstrass : thm
  MONTGOMERY_OF_WEIERSTRASS_OF_MONTGOMERY : thm
  WEIERSTRASS_OF_MONTGOMERY_OF_WEIERSTRASS : thm
  WEIERSTRASS_OF_MONTGOMERY : thm
  MONTGOMERY_OF_WEIERSTRASS : thm
  deriving Inhabited

@[nospecialize]
def setupMontweMaps [HolBase] (D : MontweDeps) :
    ExceptT String IO MontweMaps := do
  -- @@SCOPE BEGIN
  let { FIELD_TAC, NOT_RING_CHAR_DIVIDES_TAC, RING_CARRIER_TAC, define, .. } := D
  let { DE_MORGAN_THM, FIELD_CHAR_NOT23, FIELD_CHAR_NOT3, FORALL_OPTION_THM,
        FORALL_PAIR_THM, PAIR_EQ, montgomery_curve, montgomery_nonsingular,
        montgomery_point, option_INJ, weierstrass_curve, weierstrass_nonsingular,
        weierstrass_point, .. } := D.core1
  -- @@SCOPE END

  let wcurve_of_mcurve ← define
   r"wcurve_of_mcurve(f,(a:A),b) =
   (f,
    ring_div f (ring_sub f (ring_of_num f 1)
                           (ring_div f (ring_pow f a 2) (ring_of_num f 3)))
               (ring_pow f b 2),
    ring_div f (ring_mul f a (ring_sub f (ring_mul f (ring_of_num f 2)
                                                     (ring_pow f a 2))
                                         (ring_of_num f 9)))
               (ring_mul f (ring_of_num f 27) (ring_pow f b 3)))"

  let WCURVE_OF_MCURVE_NONSINGULAR_EQ ← prove
   r"!f a b:A.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\ ~(b = ring_0 f)
        ==> (weierstrass_nonsingular(wcurve_of_mcurve(f,a,b)) <=>
             ~(ring_pow f a 2 = ring_of_num f 4))"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT23] THEN
    REWRITE_TAC [montgomery_nonsingular,
                 weierstrass_nonsingular, wcurve_of_mcurve] THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  let WCURVE_OF_MCURVE_NONSINGULAR ← prove
   r"!f a b:A.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_nonsingular(f,a,b)
        ==> weierstrass_nonsingular(wcurve_of_mcurve(f,a,b))"
   (← do
    pure (SIMP_TAC [montgomery_nonsingular, DE_MORGAN_THM,
                    WCURVE_OF_MCURVE_NONSINGULAR_EQ]))

  let weierstrass_of_montgomery ← define
   r"weierstrass_of_montgomery(f,a:A,b) NONE = NONE /\
  weierstrass_of_montgomery(f,a:A,b) (SOME(x,y)) =
  SOME(ring_div f (ring_add f x (ring_div f a (ring_of_num f 3))) b,
       ring_div f y b)"

  let montgomery_of_weierstrass ← define
   r"montgomery_of_weierstrass(f,a:A,b) NONE = NONE /\
  montgomery_of_weierstrass(f,a:A,b) (SOME(x,y)) =
  SOME(ring_sub f (ring_mul f b x) (ring_div f a (ring_of_num f 3)),
       ring_mul f b y)"

  let MONTGOMERY_OF_WEIERSTRASS_OF_MONTGOMERY ← prove
   r"!f a (b:A) p.
        field f /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\ ~(b = ring_0 f) /\
        montgomery_point f p
        ==> montgomery_of_weierstrass(f,a,b)
              (weierstrass_of_montgomery(f,a,b) p) = p"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT3] THEN
    REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    REWRITE_TAC [montgomery_of_weierstrass, weierstrass_of_montgomery] THEN
    REWRITE_TAC [montgomery_point, option_INJ, PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN FIELD_TAC))

  let WEIERSTRASS_OF_MONTGOMERY_OF_WEIERSTRASS ← prove
   r"!f a (b:A) p.
        field f /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\ ~(b = ring_0 f) /\
        weierstrass_point f p
        ==> weierstrass_of_montgomery(f,a,b)
              (montgomery_of_weierstrass(f,a,b) p) = p"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT3] THEN
    REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    REWRITE_TAC [montgomery_of_weierstrass, weierstrass_of_montgomery] THEN
    REWRITE_TAC [weierstrass_point, option_INJ, PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN FIELD_TAC))

  let WEIERSTRASS_OF_MONTGOMERY ← prove
   r"!f (a:A) b p.
        field f /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_curve(f,a,b) p
        ==> weierstrass_curve (wcurve_of_mcurve(f,a,b))
                              (weierstrass_of_montgomery(f,a,b) p)"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    REWRITE_TAC [montgomery_curve, weierstrass_curve,
                 weierstrass_of_montgomery, wcurve_of_mcurve] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [FIELD_CHAR_NOT3] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  let MONTGOMERY_OF_WEIERSTRASS ← prove
   r"!f (a:A) b p.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\ ~(b = ring_0 f) /\
        weierstrass_curve (wcurve_of_mcurve(f,a,b)) p
        ==> montgomery_curve(f,a,b) (montgomery_of_weierstrass(f,a,b) p)"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    REWRITE_TAC [montgomery_curve, weierstrass_curve,
                 montgomery_of_weierstrass, wcurve_of_mcurve] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [FIELD_CHAR_NOT23] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  -- @@RETURN BEGIN
  return { wcurve_of_mcurve, WCURVE_OF_MCURVE_NONSINGULAR_EQ,
           WCURVE_OF_MCURVE_NONSINGULAR, weierstrass_of_montgomery,
           montgomery_of_weierstrass, MONTGOMERY_OF_WEIERSTRASS_OF_MONTGOMERY,
           WEIERSTRASS_OF_MONTGOMERY_OF_WEIERSTRASS, WEIERSTRASS_OF_MONTGOMERY,
           MONTGOMERY_OF_WEIERSTRASS }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- The maps respect negation and addition, giving the group isomorphisms.    -/
/- (montwe.ml 113-219)                                                       -/
/- ------------------------------------------------------------------------- -/

structure MontweIso where
  -- @@FIELDS
  WEIERSTRASS_OF_MONTGOMERY_NEG : thm
  WEIERSTRASS_OF_MONTGOMERY_ADD : thm
  GROUP_ISOMORPHISMS_MONTGOMERY_WEIERSTRASS_GROUP : thm
  GROUP_ISOMORPHISMS_WEIERSTRASS_MONTGOMERY_GROUP : thm
  ISOMORPHIC_MONTGOMERY_WEIERSTRASS_GROUP : thm
  ISOMORPHIC_WEIERSTRASS_MONTGOMERY_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupMontweIso [HolBase] (D : MontweDeps) (BMontweMaps : MontweMaps) :
    ExceptT String IO MontweIso := do
  -- @@SCOPE BEGIN
  let { FIELD_TAC, LET_TAC, MESON_TAC, NOT_RING_CHAR_DIVIDES_TAC, RING_CARRIER_TAC, .. } := D
  let { FIELD_CHAR_NOT23, FIELD_CHAR_NOT3, FORALL_IN_IMAGE, FORALL_OPTION_THM,
        FORALL_PAIR_THM, GROUP_HOMOMORPHISM, GROUP_ISOMORPHISMS,
        GROUP_ISOMORPHISMS_IMP_ISOMORPHISM, GROUP_ISOMORPHISMS_SYM, IN,
        ISOMORPHIC_GROUP_SYM, MONTGOMERY_GROUP, PAIR_EQ, SUBSET, WEIERSTRASS_GROUP,
        isomorphic_group, montgomery_add, montgomery_curve, montgomery_neg,
        montgomery_nonsingular, montgomery_point, option_DISTINCT, option_INJ,
        weierstrass_add, weierstrass_curve, weierstrass_neg, weierstrass_point, .. } := D.core1
  let { MONTGOMERY_OF_WEIERSTRASS, MONTGOMERY_OF_WEIERSTRASS_OF_MONTGOMERY,
        WCURVE_OF_MCURVE_NONSINGULAR, WEIERSTRASS_OF_MONTGOMERY,
        WEIERSTRASS_OF_MONTGOMERY_OF_WEIERSTRASS, montgomery_of_weierstrass,
        wcurve_of_mcurve, weierstrass_of_montgomery, .. } := BMontweMaps
  -- @@SCOPE END

  let WEIERSTRASS_OF_MONTGOMERY_NEG ← prove
   r"!f (a:A) b p.
        field f /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        ~(b = ring_0 f) /\
        montgomery_curve(f,a,b) p
        ==> weierstrass_of_montgomery(f,a,b) (montgomery_neg(f,a,b) p) =
            weierstrass_neg (wcurve_of_mcurve(f,a,b))
                            (weierstrass_of_montgomery(f,a,b) p)"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    REWRITE_TAC [montgomery_curve, weierstrass_of_montgomery,
                 montgomery_of_weierstrass,  wcurve_of_mcurve,
                 montgomery_neg, weierstrass_neg] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [option_INJ, PAIR_EQ, FIELD_CHAR_NOT3] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  let WEIERSTRASS_OF_MONTGOMERY_ADD ← prove
   r"!f (a:A) b p q.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        ~(b = ring_0 f) /\
        montgomery_curve(f,a,b) p /\ montgomery_curve(f,a,b) q
        ==> weierstrass_of_montgomery(f,a,b) (montgomery_add(f,a,b) p q) =
            weierstrass_add (wcurve_of_mcurve(f,a,b))
                            (weierstrass_of_montgomery(f,a,b) p)
                            (weierstrass_of_montgomery(f,a,b) q)"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    REWRITE_TAC [montgomery_curve, weierstrass_of_montgomery,
                 montgomery_of_weierstrass,  wcurve_of_mcurve,
                 montgomery_add, weierstrass_add] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC [option_INJ, PAIR_EQ] THEN
    REWRITE_TAC [FIELD_CHAR_NOT23] THEN REPEAT (GEN_TAC ORELSE CONJ_TAC) THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [weierstrass_of_montgomery]) THEN
    REPEAT LET_TAC THEN
    ASM_REWRITE_TAC [montgomery_of_weierstrass, weierstrass_of_montgomery] THEN
    REWRITE_TAC [option_INJ, option_DISTINCT, PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  let GROUP_ISOMORPHISMS_MONTGOMERY_WEIERSTRASS_GROUP ← prove
   r"!f a (b:A).
      field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      montgomery_nonsingular(f,a,b)
      ==> group_isomorphisms
           (montgomery_group(f,a,b),weierstrass_group(wcurve_of_mcurve(f,a,b)))
           (weierstrass_of_montgomery(f,a,b),
            montgomery_of_weierstrass(f,a,b))"
   (← do
    let wcArgs := striplist HolMath.Pair.dest_pair
      (← liftExcept (rand (concl wcurve_of_mcurve)))
    pure (REPEAT STRIP_TAC THEN
    MP_TAC (← ISPECL wcArgs
                  WEIERSTRASS_GROUP) THEN
    REWRITE_TAC [← GSYM wcurve_of_mcurve] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC [WCURVE_OF_MCURVE_NONSINGULAR] THEN
      REPEAT CONJ_TAC THEN RING_CARRIER_TAC,
      STRIP_TAC] THEN
    MP_TAC (← ISPECL [← q r"f:A ring", ← q r"a:A", ← q r"b:A"] MONTGOMERY_GROUP) THEN
    ASM_REWRITE_TAC [] THEN STRIP_TAC THEN
     ASM_REWRITE_TAC [GROUP_ISOMORPHISMS, GROUP_HOMOMORPHISM] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC [IN] THEN
    RULE_ASSUM_TAC (REWRITE_RULE [montgomery_nonsingular]) THEN
    SUBGOAL_THEN
     (← q r"(!x. weierstrass_curve (wcurve_of_mcurve (f,(a:A),b)) x
           ==> weierstrass_point f x) /\
      (!y. montgomery_curve (f,a,b) y ==> montgomery_point f y)")
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [FORALL_PAIR_THM, FORALL_OPTION_THM] THEN
      SIMP_TAC [weierstrass_curve, weierstrass_point, wcurve_of_mcurve,
                  montgomery_curve, montgomery_point],
      ALL_TAC] THEN
    ASM_SIMP_TAC [WEIERSTRASS_OF_MONTGOMERY, WEIERSTRASS_OF_MONTGOMERY_ADD,
                  MONTGOMERY_OF_WEIERSTRASS,
                  MONTGOMERY_OF_WEIERSTRASS_OF_MONTGOMERY,
                  WEIERSTRASS_OF_MONTGOMERY_OF_WEIERSTRASS]))

  let GROUP_ISOMORPHISMS_WEIERSTRASS_MONTGOMERY_GROUP ← prove
   r"!f a (b:A).
      field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      montgomery_nonsingular(f,a,b)
      ==> group_isomorphisms
           (weierstrass_group(wcurve_of_mcurve(f,a,b)),montgomery_group(f,a,b))
           (montgomery_of_weierstrass(f,a,b),
            weierstrass_of_montgomery(f,a,b))"
   (← do
    pure (ONCE_REWRITE_TAC [GROUP_ISOMORPHISMS_SYM] THEN
    ACCEPT_TAC GROUP_ISOMORPHISMS_MONTGOMERY_WEIERSTRASS_GROUP))

  let ISOMORPHIC_MONTGOMERY_WEIERSTRASS_GROUP ← prove
   r"!f a (b:A).
      field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      montgomery_nonsingular(f,a,b)
      ==> (montgomery_group(f,a,b)) isomorphic_group
          (weierstrass_group(wcurve_of_mcurve(f,a,b)))"
   (← do
    pure (REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o
      MATCH_MP GROUP_ISOMORPHISMS_MONTGOMERY_WEIERSTRASS_GROUP) THEN
    MESON_TAC [GROUP_ISOMORPHISMS_IMP_ISOMORPHISM, isomorphic_group]))

  let ISOMORPHIC_WEIERSTRASS_MONTGOMERY_GROUP ← prove
   r"!f a (b:A).
      field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      montgomery_nonsingular(f,a,b)
      ==> (weierstrass_group(wcurve_of_mcurve(f,a,b))) isomorphic_group
          (montgomery_group(f,a,b))"
   (← do
    pure (ONCE_REWRITE_TAC [ISOMORPHIC_GROUP_SYM] THEN
    ACCEPT_TAC ISOMORPHIC_MONTGOMERY_WEIERSTRASS_GROUP))

  -- @@RETURN BEGIN
  return { WEIERSTRASS_OF_MONTGOMERY_NEG, WEIERSTRASS_OF_MONTGOMERY_ADD,
           GROUP_ISOMORPHISMS_MONTGOMERY_WEIERSTRASS_GROUP,
           GROUP_ISOMORPHISMS_WEIERSTRASS_MONTGOMERY_GROUP,
           ISOMORPHIC_MONTGOMERY_WEIERSTRASS_GROUP,
           ISOMORPHIC_WEIERSTRASS_MONTGOMERY_GROUP }
  -- @@RETURN END

end HolEC.Montwe
