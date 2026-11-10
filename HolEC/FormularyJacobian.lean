/- ========================================================================= -/
/- Specific formulas for evaluating Jacobian coordinate point operations.  -/
/- ========================================================================= -/
/- File: HolEC/FormularyJacobian.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/formulary_jacobian.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/weierstrass.ml, EC/jacobian.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.FormularyJacobian fills them).

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
import HolEC.Jacobian

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolEC.FormularyJacobian

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (FIELD_IMP_INTEGRAL_DOMAIN LET_DEF LET_END_DEF PAIR_EQ PRIME_2
   RING_CHAR_DIVIDES_PRIME jacobian_0 jacobian_add jacobian_eq jacobian_neg
   jacobian_point : thm)
  deriving Inhabited

/-- What formulary_jacobian.ml uses from Session besides theorems. -/
structure FormularyJacobianDeps where
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
/- Specific formulas for evaluating Jacobian coordinate point operations.    -/
/- (formulary_jacobian.ml 1-348)                                             -/
/- ------------------------------------------------------------------------- -/

structure FormularyJacobianThms where
  -- @@FIELDS
  ja_dbl_2007_bl : thm
  JA_DBL_2007_BL : thm
  JA_DBL_2007_BL' : thm
  j3_dbl_2001_b : thm
  J3_DBL_2001_B : thm
  J3_DBL_2001_B' : thm
  j0_dbl_2009_l : thm
  J0_DBL_2009_L : thm
  J0_DBL_2009_L' : thm
  ja_add_2007_bl : thm
  JA_ADD_2007_BL : thm
  ja_madd_2007_bl : thm
  JA_MADD_2007_BL : thm
  deriving Inhabited

@[nospecialize]
def setupFormularyJacobianThms [HolBase] (D : FormularyJacobianDeps) :
    ExceptT String IO FormularyJacobianThms := do
  -- @@SCOPE BEGIN
  let { FIELD_TAC, NOT_RING_CHAR_DIVIDES_TAC, new_definition, .. } := D
  let { FIELD_IMP_INTEGRAL_DOMAIN, LET_DEF, LET_END_DEF, PAIR_EQ, PRIME_2,
        RING_CHAR_DIVIDES_PRIME, jacobian_0, jacobian_add, jacobian_eq, jacobian_neg,
        jacobian_point, .. } := D.core1
  -- @@SCOPE END

  /- Point doubling in Jacobian coordinates.

     Source: Bernstein-Lange [2007] "Faster addition and doubling..."

     http://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian/doubling/dbl-2007-bl.op3 -/

  let ja_dbl_2007_bl ← new_definition
   r"ja_dbl_2007_bl (f:A ring,a:A,b:A) (x1,y1,z1) =
      let xx = ring_pow f x1 2 in
      let yy = ring_pow f y1 2 in
      let yyyy = ring_pow f yy 2 in
      let zz = ring_pow f z1 2 in
      let t0 = ring_add f x1 yy in
      let t1 = ring_pow f t0 2 in
      let t2 = ring_sub f t1 xx in
      let t3 = ring_sub f t2 yyyy in
      let s = ring_mul f (ring_of_num f 2) t3 in
      let t4 = ring_pow f zz 2 in
      let t5 = ring_mul f a t4 in
      let t6 = ring_mul f (ring_of_num f 3) xx in
      let m = ring_add f t6 t5 in
      let t7 = ring_pow f m 2 in
      let t8 = ring_mul f (ring_of_num f 2) s in
      let t = ring_sub f t7 t8 in
      let x3 = t in
      let t9 = ring_sub f s t in
      let t10 = ring_mul f (ring_of_num f 8) yyyy in
      let t11 = ring_mul f m t9 in
      let y3 = ring_sub f t11 t10 in
      let t12 = ring_add f y1 z1 in
      let t13 = ring_pow f t12 2 in
      let t14 = ring_sub f t13 yy in
      let z3 = ring_sub f t14 zz in
      (x3,y3,z3)"

  let JA_DBL_2007_BL ← prove
   r"!f a b x1 y1 z1:A.
        field f /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f (x1,y1,z1)
        ==> jacobian_eq f (ja_dbl_2007_bl (f,a,b) (x1,y1,z1))
                          (jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1))"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [jacobian_point] THEN STRIP_TAC THEN
    REWRITE_TAC [ja_dbl_2007_bl, jacobian_add, jacobian_eq,
                jacobian_neg, jacobian_0] THEN
    ASM_CASES_TAC (← q r"z1:A = ring_0 f") THEN
    ASM_REWRITE_TAC [jacobian_add, jacobian_eq,
                    jacobian_neg, jacobian_0] THEN
    ASM_REWRITE_TAC [LET_DEF, LET_END_DEF, PAIR_EQ, jacobian_eq] THEN
    FIELD_TAC THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))

  let JA_DBL_2007_BL' ← prove
   r"!f a b x1 y1 z1:A.
        field f /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f (x1,y1,z1) /\
        (z1 = ring_0 f ==> (x1,y1,z1) = jacobian_0 (f,a,b))
        ==> ja_dbl_2007_bl (f,a,b) (x1,y1,z1) =
            jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1)"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [jacobian_point] THEN
    ASM_CASES_TAC (← q r"z1:A = ring_0 f") THEN
    ASM_REWRITE_TAC [jacobian_add, jacobian_eq, jacobian_0, PAIR_EQ,
                    jacobian_neg, jacobian_0, ja_dbl_2007_bl] THEN
    STRIP_TAC THEN REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC [jacobian_add, jacobian_eq,
                    jacobian_neg, jacobian_0] THEN
    ASM_REWRITE_TAC [LET_DEF, LET_END_DEF, PAIR_EQ, jacobian_eq] THEN
    FIELD_TAC THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))

  /- Point doubling in Jacobian coordinates assuming a = -3.

     Source: Bernstein [2001] "A software implementation of NIST P-224".

     http://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian-3/doubling/dbl-2001-b.op3 -/

  let j3_dbl_2001_b ← new_definition
   r"j3_dbl_2001_b (f:A ring,a:A,b:A) (x1,y1,z1) =
      let delta = ring_pow f z1 2 in
      let gamma = ring_pow f y1 2 in
      let beta = ring_mul f x1 gamma in
      let t0 = ring_sub f x1 delta in
      let t1 = ring_add f x1 delta in
      let t2 = ring_mul f t0 t1 in
      let alpha = ring_mul f (ring_of_num f 3) t2 in
      let t3 = ring_pow f alpha 2 in
      let t4 = ring_mul f (ring_of_num f 8) beta in
      let x3 = ring_sub f t3 t4 in
      let t5 = ring_add f y1 z1 in
      let t6 = ring_pow f t5 2 in
      let t7 = ring_sub f t6 gamma in
      let z3 = ring_sub f t7 delta in
      let t8 = ring_mul f (ring_of_num f 4) beta in
      let t9 = ring_sub f t8 x3 in
      let t10 = ring_pow f gamma 2 in
      let t11 = ring_mul f (ring_of_num f 8) t10 in
      let t12 = ring_mul f alpha t9 in
      let y3 = ring_sub f t12 t11 in
      (x3,y3,z3)"

  let J3_DBL_2001_B ← prove
   r"!f a b x1 y1 z1:A.
        field f /\
        a = ring_of_int f (-- &3) /\ b IN ring_carrier f /\
        jacobian_point f (x1,y1,z1)
        ==> jacobian_eq f (j3_dbl_2001_b (f,a,b) (x1,y1,z1))
                          (jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1))"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [jacobian_point] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC [j3_dbl_2001_b, jacobian_add, jacobian_eq,
                jacobian_neg, jacobian_0] THEN
    ASM_CASES_TAC (← q r"z1:A = ring_0 f") THEN
    ASM_REWRITE_TAC [jacobian_add, jacobian_eq,
                    jacobian_neg, jacobian_0] THEN
    ASM_REWRITE_TAC [LET_DEF, LET_END_DEF, PAIR_EQ, jacobian_eq] THEN
    FIELD_TAC THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))

  let J3_DBL_2001_B' ← prove
   r"!f a b x1 y1 z1:A.
        field f /\
        a = ring_of_int f (-- &3) /\ b IN ring_carrier f /\
        jacobian_point f (x1,y1,z1) /\
        (z1 = ring_0 f ==> (x1,y1,z1) = jacobian_0 (f,a,b))
        ==> j3_dbl_2001_b (f,a,b) (x1,y1,z1) =
            jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1)"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [jacobian_point] THEN
    ASM_CASES_TAC (← q r"z1:A = ring_0 f") THEN
    ASM_REWRITE_TAC [jacobian_add, jacobian_eq, jacobian_0, PAIR_EQ,
                    jacobian_neg, jacobian_0, j3_dbl_2001_b] THEN
    STRIP_TAC THEN REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC [jacobian_add, jacobian_eq,
                    jacobian_neg, jacobian_0] THEN
    ASM_REWRITE_TAC [LET_DEF, LET_END_DEF, PAIR_EQ, jacobian_eq] THEN
    FIELD_TAC THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))

  /- Point doubling in Jacobian coordinates assuming a = 0.

     Source: Lange [2009].

     https://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian-0/doubling/dbl-2009-l.op3 -/

  let j0_dbl_2009_l ← new_definition
   r"j0_dbl_2009_l (f:A ring,a:A,b:A) (x1,y1,z1) =
      let a = ring_pow f x1 2 in
      let b = ring_pow f y1 2 in
      let c = ring_pow f b 2 in
      let t0 = ring_add f x1 b in
      let t1 = ring_pow f t0 2 in
      let t2 = ring_sub f t1 a in
      let t3 = ring_sub f t2 c in
      let d = ring_mul f (ring_of_num f 2) t3 in
      let e = ring_mul f (ring_of_num f 3) a in
      let g = ring_pow f e 2 in
      let t4 = ring_mul f (ring_of_num f 2) d in
      let x3 = ring_sub f g t4 in
      let t5 = ring_sub f d x3 in
      let t6 = ring_mul f (ring_of_num f 8) c in
      let t7 = ring_mul f e t5 in
      let y3 = ring_sub f t7 t6 in
      let t8 = ring_mul f y1 z1 in
      let z3 = ring_mul f (ring_of_num f 2) t8 in
      (x3,y3,z3)"

  let J0_DBL_2009_L ← prove
   r"!f a b x1 y1 z1:A.
        field f /\
        a = ring_0 f /\ b IN ring_carrier f /\
        jacobian_point f (x1,y1,z1)
        ==> jacobian_eq f (j0_dbl_2009_l (f,a,b) (x1,y1,z1))
                          (jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1))"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [jacobian_point] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC [j0_dbl_2009_l, jacobian_add, jacobian_eq,
                jacobian_neg, jacobian_0] THEN
    ASM_CASES_TAC (← q r"z1:A = ring_0 f") THEN
    ASM_REWRITE_TAC [jacobian_add, jacobian_eq,
                    jacobian_neg, jacobian_0] THEN
    ASM_REWRITE_TAC [LET_DEF, LET_END_DEF, PAIR_EQ, jacobian_eq] THEN
    FIELD_TAC THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))

  let J0_DBL_2009_L' ← prove
   r"!f a b x1 y1 z1:A.
        field f /\
        a = ring_0 f /\ b IN ring_carrier f /\
        jacobian_point f (x1,y1,z1) /\
        (z1 = ring_0 f ==> (x1,y1,z1) = jacobian_0 (f,a,b))
        ==> j0_dbl_2009_l (f,a,b) (x1,y1,z1) =
            jacobian_add (f,a,b) (x1,y1,z1) (x1,y1,z1)"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [jacobian_point] THEN
    ASM_CASES_TAC (← q r"z1:A = ring_0 f") THEN
    ASM_REWRITE_TAC [jacobian_add, jacobian_eq, jacobian_0, PAIR_EQ,
                    jacobian_neg, jacobian_0, j0_dbl_2009_l] THEN
    STRIP_TAC THEN REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC [jacobian_add, jacobian_eq,
                    jacobian_neg, jacobian_0] THEN
    ASM_REWRITE_TAC [LET_DEF, LET_END_DEF, PAIR_EQ, jacobian_eq] THEN
    FIELD_TAC THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))

  /- Pure point addition in Jacobian coordinates. This sequence never uses
     the value of "a" so there's no special optimized version for special
     "a".

     Source: Bernstein-Lange [2007] "Faster addition and doubling..."

     Note the correctness is not proved in cases where the points are equal
     (or projectively equivalent), or either input is 0 (point at infinity).

     http://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian/addition/add-2007-bl.op3 -/

  let ja_add_2007_bl ← new_definition
   r"ja_add_2007_bl (f:A ring,a:A,b:A) (x1,y1,z1) (x2,y2,z2) =
      let z1z1 = ring_pow f z1 2 in
      let z2z2 = ring_pow f z2 2 in
      let u1 = ring_mul f x1 z2z2 in
      let u2 = ring_mul f x2 z1z1 in
      let t0 = ring_mul f z2 z2z2 in
      let s1 = ring_mul f y1 t0 in
      let t1 = ring_mul f z1 z1z1 in
      let s2 = ring_mul f y2 t1 in
      let h = ring_sub f u2 u1 in
      let t2 = ring_mul f (ring_of_num f 2) h in
      let i = ring_pow f t2 2 in
      let j = ring_mul f h i in
      let t3 = ring_sub f s2 s1 in
      let r = ring_mul f (ring_of_num f 2) t3 in
      let v = ring_mul f u1 i in
      let t4 = ring_pow f r 2 in
      let t5 = ring_mul f (ring_of_num f 2) v in
      let t6 = ring_sub f t4 j in
      let x3 = ring_sub f t6 t5 in
      let t7 = ring_sub f v x3 in
      let t8 = ring_mul f s1 j in
      let t9 = ring_mul f (ring_of_num f 2) t8 in
      let t10 = ring_mul f r t7 in
      let y3 = ring_sub f t10 t9 in
      let t11 = ring_add f z1 z2 in
      let t12 = ring_pow f t11 2 in
      let t13 = ring_sub f t12 z1z1 in
      let t14 = ring_sub f t13 z2z2 in
      let z3 = ring_mul f t14 h in
      (x3,y3,z3)"

  let JA_ADD_2007_BL ← prove
   r"!f a b x1 y1 z1 x2 y2 z2:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f (x1,y1,z1) /\ jacobian_point f (x2,y2,z2) /\
        ~(z1 = ring_0 f) /\ ~(z2 = ring_0 f) /\
        ~(jacobian_eq f (x1,y1,z1) (x2,y2,z2))
        ==> jacobian_eq f (ja_add_2007_bl (f,a,b) (x1,y1,z1) (x2,y2,z2))
                          (jacobian_add (f,a,b) (x1,y1,z1) (x2,y2,z2))"
   (← do
    let eqA ← q r"(=):A->A->bool"
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [jacobian_point] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC [← GSYM RING_CHAR_DIVIDES_PRIME, PRIME_2] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC [jacobian_eq, ja_add_2007_bl, jacobian_add] THEN
    REPEAT (COND_CASES_TAC THEN
     ASM_REWRITE_TAC [jacobian_add, jacobian_eq,
                     jacobian_neg, jacobian_0, LET_DEF, LET_END_DEF]) THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o check (fun th => free_in eqA (concl th)))) THEN
    FIELD_TAC))

  /- Mixed point addition in Jacobian coordinates. Here "mixed" means
     assuming z2 = 1, which holds if the second point was directly injected
     from the Weierstrass coordinates via (x,y) |-> (x,y,1). This never uses
     the value of "a" so there's no special optimized version for special
     "a".

     Source: Bernstein-Lange [2007] "Faster addition and doubling..."

     Note the correctness is not proved in the case where the points are
     equal or projectively equivalent, nor where the first is the group
     identity (i.e. the point at infinity, anything with z1 = 0 in
     projective coords).

     http://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian-3/addition/add-2007-bl.op3 -/

  let ja_madd_2007_bl ← new_definition
   r"ja_madd_2007_bl (f:A ring,a:A,b:A) (x1,y1,z1) (x2,y2,z2) =
      let z1z1 = ring_pow f z1 2 in
      let u2 = ring_mul f x2 z1z1 in
      let t0 = ring_mul f z1 z1z1 in
      let s2 = ring_mul f y2 t0 in
      let h = ring_sub f u2 x1 in
      let hh = ring_pow f h 2 in
      let i = ring_mul f (ring_of_num f 4) hh in
      let j = ring_mul f h i in
      let t1 = ring_sub f s2 y1 in
      let r = ring_mul f (ring_of_num f 2) t1 in
      let v = ring_mul f x1 i in
      let t2 = ring_pow f r 2 in
      let t3 = ring_mul f (ring_of_num f 2) v in
      let t4 = ring_sub f t2 j in
      let x3 = ring_sub f t4 t3 in
      let t5 = ring_sub f v x3 in
      let t6 = ring_mul f y1 j in
      let t7 = ring_mul f (ring_of_num f 2) t6 in
      let t8 = ring_mul f r t5 in
      let y3 = ring_sub f t8 t7 in
      let t9 = ring_add f z1 h in
      let t10 = ring_pow f t9 2 in
      let t11 = ring_sub f t10 z1z1 in
      let z3 = ring_sub f t11 hh in
      (x3,y3,z3)"

  let JA_MADD_2007_BL ← prove
   r"!f a b x1 y1 z1 x2 y2 z2:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        jacobian_point f (x1,y1,z1) /\ jacobian_point f (x2,y2,z2) /\
        z2 = ring_1 f /\
        ~(z1 = ring_0 f) /\ ~(jacobian_eq f (x1,y1,z1) (x2,y2,z2))
        ==> jacobian_eq f (ja_madd_2007_bl (f,a,b) (x1,y1,z1) (x2,y2,z2))
                          (jacobian_add (f,a,b) (x1,y1,z1) (x2,y2,z2))"
   (← do
    let eqA ← q r"(=):A->A->bool"
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [jacobian_point] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC [← GSYM RING_CHAR_DIVIDES_PRIME, PRIME_2] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC [jacobian_eq, ja_madd_2007_bl, jacobian_add] THEN
    REPEAT (COND_CASES_TAC THEN
     ASM_REWRITE_TAC [jacobian_add, jacobian_eq,
                     jacobian_neg, jacobian_0, LET_DEF, LET_END_DEF]) THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o check (fun th => free_in eqA (concl th)))) THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  -- @@RETURN BEGIN
  return { ja_dbl_2007_bl, JA_DBL_2007_BL, JA_DBL_2007_BL', j3_dbl_2001_b, J3_DBL_2001_B,
           J3_DBL_2001_B', j0_dbl_2009_l, J0_DBL_2009_L, J0_DBL_2009_L', ja_add_2007_bl,
           JA_ADD_2007_BL, ja_madd_2007_bl, JA_MADD_2007_BL }
  -- @@RETURN END

end HolEC.FormularyJacobian
