/- ========================================================================= -/
/- Extended projective coordinates for Edwards curves.                     -/
/- ========================================================================= -/
/- File: HolEC/EXProjective.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/exprojective.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/edwards.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.EXProjective fills them).

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
import HolEC.Edwards

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolEC.EXProjective

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (EDWARDS_NONSINGULAR_DENOMINATORS FIELD_CHAR_NOT2 FORALL_PAIR_THM IMP_CONJ
   LET_DEF LET_END_DEF PAIR_EQ edwards_add edwards_curve : thm)
  deriving Inhabited

/-- What exprojective.ml uses from Session besides theorems. -/
structure EXProjectiveDeps where
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
/- Extended projective coordinates for Edwards curves.                       -/
/-                                                                           -/
/- An affine (x,y) is represented by a triple (X,Y,Z,T) where                -/
/-                                                                           -/
/- x = X / Z, y = Y / Z and x * y = T / Z (so X * Y = T * Z)                 -/
/-                                                                           -/
/- We often use W in place of T to avoid inconvenience over "true" in HOL.   -/
/- There is also a pure projective analog without the T field.               -/
/- (exprojective.ml 1-133)                                                   -/
/- ------------------------------------------------------------------------- -/

structure EXProjectiveDefs where
  -- @@FIELDS
  exprojective : thm
  EXPROJECTIVE_ALT : thm
  projective : thm
  PROJECTIVE_ALT : thm
  PROJECTIVE_EXPROJECTIVE : thm
  EXPROJECTIVE_PROJECTIVE : thm
  EXPROJECTIVE_PROJECTIVE_ALT : thm
  edwards_excurve : thm
  EDWARDS_EXCURVE : thm
  edwards_pcurve : thm
  EDWARDS_PCURVE : thm
  deriving Inhabited

@[nospecialize]
def setupEXProjectiveDefs [HolBase] (D : EXProjectiveDeps) :
    ExceptT String IO EXProjectiveDefs := do
  -- @@SCOPE BEGIN
  let { FIELD_TAC, RING_CARRIER_TAC, define, .. } := D
  let { FORALL_PAIR_THM, edwards_curve, .. } := D.core1
  -- @@SCOPE END

  let exprojective ← define
   r"exprojective (f:A ring) (x,y) (X,Y,Z,W) <=>
        x IN ring_carrier f /\ y IN ring_carrier f /\
        X IN ring_carrier f /\ Y IN ring_carrier f /\
        W IN ring_carrier f /\ Z IN ring_carrier f /\
        ~(Z = ring_0 f) /\
        ring_div f X Z = x /\
        ring_div f Y Z = y /\
        ring_div f W Z = ring_mul f x y"

  let EXPROJECTIVE_ALT ← prove
   r"!f x y X Y Z W:A.
        field f
        ==> (exprojective f (x,y) (X,Y,Z,W) <=>
             x IN ring_carrier f /\ y IN ring_carrier f /\
             X IN ring_carrier f /\ Y IN ring_carrier f /\
             W IN ring_carrier f /\ Z IN ring_carrier f /\
             ~(Z = ring_0 f) /\
             ring_mul f x Z = X /\
             ring_mul f y Z = Y /\
             ring_mul f W Z = ring_mul f X Y)"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [exprojective] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN FIELD_TAC))

  let projective ← define
   r"projective (f:A ring) (x,y) (X,Y,Z) <=>
        x IN ring_carrier f /\ y IN ring_carrier f /\
        X IN ring_carrier f /\ Y IN ring_carrier f /\ Z IN ring_carrier f /\
        ~(Z = ring_0 f) /\
        ring_div f X Z = x /\
        ring_div f Y Z = y"

  let PROJECTIVE_ALT ← prove
   r"!f x y X Y Z:A.
        field f
        ==> (projective f (x,y) (X,Y,Z) <=>
             x IN ring_carrier f /\ y IN ring_carrier f /\
             X IN ring_carrier f /\ Y IN ring_carrier f /\
             Z IN ring_carrier f /\
             ~(Z = ring_0 f) /\
             ring_mul f x Z = X /\
             ring_mul f y Z = Y)"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [projective] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN FIELD_TAC))

  let PROJECTIVE_EXPROJECTIVE ← prove
   r"!f x y X Y Z:A.
        field f
        ==> (projective f (x,y) (X,Y,Z) <=>
             exprojective f (x,y)
              (X,Y,Z,ring_div f (ring_mul f X Y) Z))"
   (← do
    pure (REPEAT STRIP_TAC THEN SIMP_TAC [projective, exprojective] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC))

  let EXPROJECTIVE_PROJECTIVE ← prove
   r"!f x y X Y Z W:A.
        field f
        ==> (exprojective f (x,y) (X,Y,Z,W) <=>
             projective f (x,y) (X,Y,Z) /\
             ring_div f (ring_mul f X Y) Z = W)"
   (← do
    pure (REPEAT STRIP_TAC THEN SIMP_TAC [projective, exprojective] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC))

  let EXPROJECTIVE_PROJECTIVE_ALT ← prove
   r"!f x y X Y Z W:A.
        field f
        ==> (exprojective f (x,y) (X,Y,Z,W) <=>
             projective f (x,y) (X,Y,Z) /\
             W IN ring_carrier f /\
             ring_mul f X Y = ring_mul f W Z)"
   (← do
    pure (REPEAT STRIP_TAC THEN SIMP_TAC [projective, exprojective] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN FIELD_TAC))

  /- Characterizing when an (extended) projective point is on a curve -/

  let edwards_excurve ← define
   r"edwards_excurve (f,a,d) (X,Y,Z,W) <=>
     X IN ring_carrier f /\
     Y IN ring_carrier f /\
     Z IN ring_carrier f /\
     W IN ring_carrier f /\
     ~(Z = ring_0 f) /\
     ring_add f (ring_mul f a (ring_pow f X 2)) (ring_pow f Y 2) =
     ring_add f (ring_pow f Z 2) (ring_mul f d (ring_pow f W 2))"

  let EDWARDS_EXCURVE ← prove
   r"!f (a:A) d p Q.
        field f /\ a IN ring_carrier f /\ d IN ring_carrier f /\
        exprojective f p Q
        ==> (edwards_curve (f,a,d) p <=> edwards_excurve (f,a,d) Q)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, exprojective,
                edwards_curve, edwards_excurve] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN FIELD_TAC))

  let edwards_pcurve ← define
   r"edwards_pcurve (f,a,d) (X,Y,Z) <=>
     X IN ring_carrier f /\
     Y IN ring_carrier f /\
     Z IN ring_carrier f /\
     ~(Z = ring_0 f) /\
     ring_mul f (ring_pow f Z 2)
                (ring_add f (ring_mul f a (ring_pow f X 2)) (ring_pow f Y 2)) =
     ring_add f (ring_pow f Z 4)
     (ring_mul f d (ring_mul f (ring_pow f X 2) (ring_pow f Y 2)))"

  let EDWARDS_PCURVE ← prove
   r"!f (a:A) d p Q.
        field f /\ a IN ring_carrier f /\ d IN ring_carrier f /\
        projective f p Q
        ==> (edwards_curve (f,a,d) p <=> edwards_pcurve (f,a,d) Q)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, projective,
                edwards_curve, edwards_pcurve] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN FIELD_TAC))

  -- @@RETURN BEGIN
  return { exprojective, EXPROJECTIVE_ALT, projective, PROJECTIVE_ALT,
           PROJECTIVE_EXPROJECTIVE, EXPROJECTIVE_PROJECTIVE, EXPROJECTIVE_PROJECTIVE_ALT,
           edwards_excurve, EDWARDS_EXCURVE, edwards_pcurve, EDWARDS_PCURVE }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Unified addition formula from Hisal-Wong-Carter-Dawson, its scaled and    -/
/- negated variants, and the d-free doubling formula with its mixed and      -/
/- negated variants.  (exprojective.ml 134-410)                              -/
/- ------------------------------------------------------------------------- -/

structure EXProjectiveOps where
  -- @@FIELDS
  edwards_exprojadd : thm
  EDWARDS_EXPROJADD : thm
  edwards_exprojadd4 : thm
  EDWARDS_EXPROJADD4 : thm
  edwards_exprojaddn : thm
  EDWARDS_EXPROJADDN : thm
  edwards_prexprojdouble : thm
  EDWARDS_PREXPROJDOUBLE_EXPROJADD : thm
  EDWARDS_PREXPROJDOUBLE : thm
  edwards_exprojdouble : thm
  EDWARDS_EXPROJDOUBLE_EXPROJADD : thm
  EDWARDS_EXPROJDOUBLE : thm
  edwards_projdouble : thm
  EDWARDS_PROJDOUBLE : thm
  edwards_prexprojdoublen : thm
  EDWARDS_PREXPROJDOUBLEN_EXPROJADDN : thm
  EDWARDS_PREXPROJDOUBLEN : thm
  deriving Inhabited

@[nospecialize]
def setupEXProjectiveOps [HolBase] (D : EXProjectiveDeps) (BEXProjectiveDefs : EXProjectiveDefs) :
    ExceptT String IO EXProjectiveOps := do
  -- @@SCOPE BEGIN
  let { FIELD_TAC, NOT_RING_CHAR_DIVIDES_TAC, RING_CARRIER_TAC, RING_PULL_DIV_TAC,
        define, .. } := D
  let { EDWARDS_NONSINGULAR_DENOMINATORS, FIELD_CHAR_NOT2, FORALL_PAIR_THM, IMP_CONJ,
        LET_DEF, LET_END_DEF, PAIR_EQ, edwards_add, edwards_curve, .. } := D.core1
  let { EDWARDS_EXCURVE, EXPROJECTIVE_ALT, EXPROJECTIVE_PROJECTIVE,
        PROJECTIVE_EXPROJECTIVE, edwards_excurve, exprojective, .. } := BEXProjectiveDefs
  -- @@SCOPE END
  -- `check (is_var o rand o concl)`
  let randIsVar (th : thm) : Bool :=
    match rand (concl th) with
    | .ok r => is_var r
    | .error _ => false

  /- (X1,Y1,Z1,T1) + (X2,Y2,Z2,T2) =
       ((X1 * Y2 + Y1 * X2) * (Z1 * Z2 - d * T1 * T2),
        (Y1 * Y2 - a * X1 * X2) * (Z1 * Z2 + d * T1 * T2),
        (Z1 * Z2 - d * T1 * T2) * (Z1 * Z2 + d * T1 * T2),
        (Y1 * Y2 - a * X1 * X2) * (X1 * Y2 + Y1 * X2)) -/

  let edwards_exprojadd ← define
   r"edwards_exprojadd (f,a,d) (X1:A,Y1,Z1,T1) (X2,Y2,Z2,T2) =
  ring_mul f (ring_add f (ring_mul f X1 Y2) (ring_mul f Y1 X2))
   (ring_sub f (ring_mul f Z1 Z2) (ring_mul f d (ring_mul f T1 T2))),
   ring_mul f
   (ring_sub f (ring_mul f Y1 Y2) (ring_mul f a (ring_mul f X1 X2)))
   (ring_add f (ring_mul f Z1 Z2) (ring_mul f d (ring_mul f T1 T2))),
   ring_mul f
   (ring_sub f (ring_mul f Z1 Z2) (ring_mul f d (ring_mul f T1 T2)))
   (ring_add f (ring_mul f Z1 Z2) (ring_mul f d (ring_mul f T1 T2))),
   ring_mul f
   (ring_sub f (ring_mul f Y1 Y2) (ring_mul f a (ring_mul f X1 X2)))
   (ring_add f (ring_mul f X1 Y2) (ring_mul f Y1 X2))"

  let EDWARDS_EXPROJADD ← prove
   r"!(f:A ring) a d x1 y1 X1 Y1 Z1 T1 x2 y2 X2 Y2 Z2 T2.
        field f /\ a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular(f,a,d) /\
        edwards_curve(f,a,d) (x1,y1) /\ edwards_curve(f,a,d) (x2,y2) /\
        exprojective f (x1,y1) (X1,Y1,Z1,T1) /\
        exprojective f (x2,y2) (X2,Y2,Z2,T2)
        ==> exprojective f (edwards_add (f,a,d) (x1,y1) (x2,y2))
                           (edwards_exprojadd (f,a,d)
                             (X1,Y1,Z1,T1) (X2,Y2,Z2,T2))"
   (← do
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN
    ASM_SIMP_TAC [EXPROJECTIVE_ALT, edwards_add, edwards_exprojadd] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [exprojective, edwards_curve] THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"x1:A", ← q r"y1:A",
                      ← q r"x2:A", ← q r"y2:A"]
          EDWARDS_NONSINGULAR_DENOMINATORS) THEN
    ASM_REWRITE_TAC [edwards_curve] THEN STRIP_TAC THEN
    REPEAT (CONJ_TAC THENL [RING_CARRIER_TAC, ALL_TAC]) THEN
    RING_PULL_DIV_TAC THEN REPEAT (FIRST_X_ASSUM (fun th => tactic_of do
      pure (SUBST_ALL_TAC (← SYM (← liftExcept (check randIsVar th)))))) THEN
    RING_PULL_DIV_TAC THEN FIELD_TAC))

  /- A variant with everything scaled by 4, which can be faster to compute. -/

  let edwards_exprojadd4 ← define
   r"edwards_exprojadd4 (f,a,d) (X1:A,Y1,Z1,T1) (X2,Y2,Z2,T2) =
    let X3,Y3,Z3,T3 = edwards_exprojadd (f,a,d) (X1,Y1,Z1,T1) (X2,Y2,Z2,T2) in
    (ring_mul f (ring_of_num f 4) X3,
     ring_mul f (ring_of_num f 4) Y3,
     ring_mul f (ring_of_num f 4) Z3,
     ring_mul f (ring_of_num f 4) T3)"

  let EDWARDS_EXPROJADD4 ← prove
   r"!(f:A ring) a d x1 y1 X1 Y1 Z1 T1 x2 y2 X2 Y2 Z2 T2.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular(f,a,d) /\
        edwards_curve(f,a,d) (x1,y1) /\ edwards_curve(f,a,d) (x2,y2) /\
        exprojective f (x1,y1) (X1,Y1,Z1,T1) /\
        exprojective f (x2,y2) (X2,Y2,Z2,T2)
        ==> exprojective f (edwards_add (f,a,d) (x1,y1) (x2,y2))
                           (edwards_exprojadd4 (f,a,d)
                             (X1,Y1,Z1,T1) (X2,Y2,Z2,T2))"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [FIELD_CHAR_NOT2] THEN DISCH_TAC THEN
    ASM_SIMP_TAC [EXPROJECTIVE_ALT, edwards_add, edwards_exprojadd4,
                 edwards_exprojadd, LET_DEF, LET_END_DEF] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [exprojective, edwards_curve] THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"x1:A", ← q r"y1:A",
                      ← q r"x2:A", ← q r"y2:A"]
          EDWARDS_NONSINGULAR_DENOMINATORS) THEN
    ASM_REWRITE_TAC [edwards_curve] THEN STRIP_TAC THEN
    REPEAT (CONJ_TAC THENL [RING_CARRIER_TAC, ALL_TAC]) THEN
    RING_PULL_DIV_TAC THEN REPEAT (FIRST_X_ASSUM (fun th => tactic_of do
      pure (SUBST_ALL_TAC (← SYM (← liftExcept (check randIsVar th)))))) THEN
    RING_PULL_DIV_TAC THEN FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  /- Similarly, a variant with everything negated. -/

  let edwards_exprojaddn ← define
   r"edwards_exprojaddn (f,a,d) (X1:A,Y1,Z1,T1) (X2,Y2,Z2,T2) =
    let X3,Y3,Z3,T3 = edwards_exprojadd (f,a,d) (X1,Y1,Z1,T1) (X2,Y2,Z2,T2) in
    (ring_neg f X3,
     ring_neg f Y3,
     ring_neg f Z3,
     ring_neg f T3)"

  let EDWARDS_EXPROJADDN ← prove
   r"!(f:A ring) a d x1 y1 X1 Y1 Z1 T1 x2 y2 X2 Y2 Z2 T2.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular(f,a,d) /\
        edwards_curve(f,a,d) (x1,y1) /\ edwards_curve(f,a,d) (x2,y2) /\
        exprojective f (x1,y1) (X1,Y1,Z1,T1) /\
        exprojective f (x2,y2) (X2,Y2,Z2,T2)
        ==> exprojective f (edwards_add (f,a,d) (x1,y1) (x2,y2))
                           (edwards_exprojaddn (f,a,d)
                             (X1,Y1,Z1,T1) (X2,Y2,Z2,T2))"
   (← do
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN
    ASM_SIMP_TAC [EXPROJECTIVE_ALT, edwards_add, edwards_exprojaddn,
                 edwards_exprojadd, LET_DEF, LET_END_DEF] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [exprojective, edwards_curve] THEN
    STRIP_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"x1:A", ← q r"y1:A",
                      ← q r"x2:A", ← q r"y2:A"]
          EDWARDS_NONSINGULAR_DENOMINATORS) THEN
    ASM_REWRITE_TAC [edwards_curve] THEN STRIP_TAC THEN
    REPEAT (CONJ_TAC THENL [RING_CARRIER_TAC, ALL_TAC]) THEN
    RING_PULL_DIV_TAC THEN REPEAT (FIRST_X_ASSUM (fun th => tactic_of do
      pure (SUBST_ALL_TAC (← SYM (← liftExcept (check randIsVar th)))))) THEN
    RING_PULL_DIV_TAC THEN FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  /- d-free doubling formula from Hisal-Wong-Carter-Dawson.

     2 * (X1,Y1,Z1,T1) =
         (2 * X1 * Y1 * (2 * Z1^2 - Y1^2 - a * X1^2),
          (Y1^2 + a * X1^2) * (Y1^2 - a * X1^2),
          (Y1^2 + a * X1^2) * (2 * Z1^2 - Y1^2 - a * X1^2),
          2 * X1 * Y1 * (Y1^2 - a * X1^2))

     Since this doesn't use the T1 field, we have some mixed variants as
     well. -/

  let edwards_prexprojdouble ← define
   r"edwards_prexprojdouble (f,a:A,d:A) (X1,Y1,Z1) =
     (ring_mul f (ring_of_num f 2)
         (ring_mul f X1
         (ring_mul f Y1
         (ring_sub f
          (ring_sub f (ring_mul f (ring_of_num f 2) (ring_pow f Z1 2))
          (ring_pow f Y1 2))
         (ring_mul f a (ring_pow f X1 2))))),
      ring_mul f
         (ring_add f (ring_pow f Y1 2) (ring_mul f a (ring_pow f X1 2)))
         (ring_sub f (ring_pow f Y1 2) (ring_mul f a (ring_pow f X1 2))),
      ring_mul f
         (ring_add f (ring_pow f Y1 2) (ring_mul f a (ring_pow f X1 2)))
         (ring_sub f
          (ring_sub f (ring_mul f (ring_of_num f 2) (ring_pow f Z1 2))
          (ring_pow f Y1 2))
         (ring_mul f a (ring_pow f X1 2))),
      ring_mul f (ring_of_num f 2)
         (ring_mul f X1
         (ring_mul f Y1
         (ring_sub f (ring_pow f Y1 2)
                     (ring_mul f a (ring_pow f X1 2))))))"

  let EDWARDS_PREXPROJDOUBLE_EXPROJADD ← prove
   r"!f a d X1 Y1 Z1 T1.
     field f /\
     a IN ring_carrier f /\ d IN ring_carrier f /\
     edwards_excurve (f,a,d) (X1,Y1,Z1,T1)
     ==> edwards_prexprojdouble (f,a,d) (X1,Y1,Z1) =
         edwards_exprojadd (f,a,d) (X1,Y1,Z1,T1) (X1,Y1,Z1,T1)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, exprojective, LET_DEF, LET_END_DEF,
      edwards_excurve, edwards_exprojadd, edwards_prexprojdouble, PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN FIELD_TAC))

  let EDWARDS_PREXPROJDOUBLE ← prove
   r"!(f:A ring) a d x1 y1 X1 Y1 Z1.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular(f,a,d) /\
        edwards_curve(f,a,d) (x1,y1) /\
        projective f (x1,y1) (X1,Y1,Z1)
        ==> exprojective f (edwards_add (f,a,d) (x1,y1) (x1,y1))
                           (edwards_prexprojdouble (f,a,d) (X1,Y1,Z1))"
   (← do
    pure (REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC [PROJECTIVE_EXPROJECTIVE] THEN
    ABBREV_TAC (← q r"T1:A = ring_div f (ring_mul f X1 Y1) Z1") THEN
    MP_TAC (← ISPECL
     [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"X1:A", ← q r"Y1:A", ← q r"Z1:A",
      ← q r"T1:A"]
     EDWARDS_PREXPROJDOUBLE_EXPROJADD) THEN
    MP_TAC (← ISPECL
     [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"(x1:A,y1:A)",
      ← q r"(X1:A,Y1:A,Z1:A,T1:A)"]
     EDWARDS_EXCURVE) THEN
    ASM_SIMP_TAC [EDWARDS_EXPROJADD]))

  let edwards_exprojdouble ← define
   r"edwards_exprojdouble (f,a:A,d) (X1,Y1,Z1,T1:A) =
    edwards_prexprojdouble (f,a,d) (X1,Y1,Z1)"

  let EDWARDS_EXPROJDOUBLE_EXPROJADD ← prove
   r"!f a d X1 Y1 Z1 T1.
     field f /\
     a IN ring_carrier f /\ d IN ring_carrier f /\
     edwards_excurve (f,a,d) (X1,Y1,Z1,T1)
     ==> edwards_exprojdouble (f,a,d) (X1,Y1,Z1,T1) =
         edwards_exprojadd (f,a,d) (X1,Y1,Z1,T1) (X1,Y1,Z1,T1)"
   (← do
    pure (REWRITE_TAC [FORALL_PAIR_THM, exprojective, LET_DEF, LET_END_DEF,
      edwards_excurve, edwards_exprojadd,
      edwards_exprojdouble, edwards_prexprojdouble, PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN FIELD_TAC))

  let EDWARDS_EXPROJDOUBLE ← prove
   r"!(f:A ring) a d x1 y1 X1 Y1 Z1 T1.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular(f,a,d) /\
        edwards_curve(f,a,d) (x1,y1) /\
        exprojective f (x1,y1) (X1,Y1,Z1,T1)
        ==> exprojective f (edwards_add (f,a,d) (x1,y1) (x1,y1))
                           (edwards_exprojdouble (f,a,d) (X1,Y1,Z1,T1))"
   (← do
    pure (SIMP_TAC [IMP_CONJ, EXPROJECTIVE_PROJECTIVE,
             edwards_exprojdouble, EDWARDS_PREXPROJDOUBLE]))

  let edwards_projdouble ← define
   r"edwards_projdouble (f,a:A,d) (X1,Y1,Z1) =
    let X2,Y2,Z2,T2 = edwards_prexprojdouble (f,a,d) (X1,Y1,Z1) in
    (X2,Y2,Z2)"

  let EDWARDS_PROJDOUBLE ← prove
   r"!(f:A ring) a d x1 y1 X1 Y1 Z1.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular(f,a,d) /\
        edwards_curve(f,a,d) (x1,y1) /\
        projective f (x1,y1) (X1,Y1,Z1)
        ==> projective f (edwards_add (f,a,d) (x1,y1) (x1,y1))
                         (edwards_projdouble (f,a,d) (X1,Y1,Z1))"
   (← do
    pure (REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM (MP_TAC o MATCH_MP EDWARDS_PREXPROJDOUBLE) THEN
    REWRITE_TAC [edwards_projdouble, edwards_prexprojdouble,
                LET_DEF, LET_END_DEF] THEN
    ASM_SIMP_TAC [EXPROJECTIVE_PROJECTIVE, edwards_add]))

  /- A negated doubling variant. -/

  let edwards_prexprojdoublen ← define
   r"edwards_prexprojdoublen (f,a:A,d:A) (X1,Y1,Z1) =
    let X3,Y3,Z3,T3 = edwards_prexprojdouble (f,a,d) (X1,Y1,Z1) in
    (ring_neg f X3,
     ring_neg f Y3,
     ring_neg f Z3,
     ring_neg f T3)"

  let EDWARDS_PREXPROJDOUBLEN_EXPROJADDN ← prove
   r"!f a d X1 Y1 Z1 T1.
     field f /\
     a IN ring_carrier f /\ d IN ring_carrier f /\
     edwards_excurve (f,a,d) (X1,Y1,Z1,T1)
     ==> edwards_prexprojdoublen (f,a,d) (X1,Y1,Z1) =
         edwards_exprojaddn (f,a,d) (X1,Y1,Z1,T1) (X1,Y1,Z1,T1)"
   (← do
    pure (REWRITE_TAC [edwards_prexprojdoublen, edwards_exprojaddn] THEN
    ASM_SIMP_TAC [← GSYM EDWARDS_PREXPROJDOUBLE_EXPROJADD]))

  let EDWARDS_PREXPROJDOUBLEN ← prove
   r"!(f:A ring) a d x1 y1 X1 Y1 Z1.
        field f /\
        a IN ring_carrier f /\ d IN ring_carrier f /\
        edwards_nonsingular(f,a,d) /\
        edwards_curve(f,a,d) (x1,y1) /\
        projective f (x1,y1) (X1,Y1,Z1)
        ==> exprojective f (edwards_add (f,a,d) (x1,y1) (x1,y1))
                           (edwards_prexprojdoublen (f,a,d) (X1,Y1,Z1))"
   (← do
    pure (REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC [PROJECTIVE_EXPROJECTIVE] THEN
    ABBREV_TAC (← q r"T1:A = ring_div f (ring_mul f X1 Y1) Z1") THEN
    MP_TAC (← ISPECL
     [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"X1:A", ← q r"Y1:A", ← q r"Z1:A",
      ← q r"T1:A"]
     EDWARDS_PREXPROJDOUBLEN_EXPROJADDN) THEN
    MP_TAC (← ISPECL
     [← q r"f:A ring", ← q r"a:A", ← q r"d:A", ← q r"(x1:A,y1:A)",
      ← q r"(X1:A,Y1:A,Z1:A,T1:A)"]
     EDWARDS_EXCURVE) THEN
    ASM_SIMP_TAC [EDWARDS_EXPROJADDN]))

  -- @@RETURN BEGIN
  return { edwards_exprojadd, EDWARDS_EXPROJADD, edwards_exprojadd4, EDWARDS_EXPROJADD4,
           edwards_exprojaddn, EDWARDS_EXPROJADDN, edwards_prexprojdouble,
           EDWARDS_PREXPROJDOUBLE_EXPROJADD, EDWARDS_PREXPROJDOUBLE,
           edwards_exprojdouble, EDWARDS_EXPROJDOUBLE_EXPROJADD, EDWARDS_EXPROJDOUBLE,
           edwards_projdouble, EDWARDS_PROJDOUBLE, edwards_prexprojdoublen,
           EDWARDS_PREXPROJDOUBLEN_EXPROJADDN, EDWARDS_PREXPROJDOUBLEN }
  -- @@RETURN END

end HolEC.EXProjective
