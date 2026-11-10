/- ========================================================================= -/
/- Specific formulas for evaluating projective coordinate point operations -/
/- ========================================================================= -/
/- File: HolEC/FormularyProjective.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/formulary_projective.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/weierstrass.ml, EC/projective.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.FormularyProjective fills them).

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
import HolEC.Projective

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolEC.FormularyProjective

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (FIELD_IMP_INTEGRAL_DOMAIN LET_DEF LET_END_DEF PAIR_EQ PRIME_2
   RING_CHAR_DIVIDES_PRIME projective_0 projective_add projective_eq
   projective_neg projective_point : thm)
  deriving Inhabited

/-- What formulary_projective.ml uses from Session besides theorems. -/
structure FormularyProjectiveDeps where
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
/- Specific formulas for evaluating projective coordinate point operations.  -/
/- (formulary_projective.ml 1-286)                                           -/
/- ------------------------------------------------------------------------- -/

structure FormularyProjectiveThms where
  -- @@FIELDS
  pr_dbl_2007_bl : thm
  PR_DBL_2007_BL : thm
  p3_dbl_2007_bl_2 : thm
  P3_DBL_2007_BL_2 : thm
  p0_dbl_2007_bl : thm
  P0_DBL_2007_BL : thm
  pr_add_1998_cmo_2 : thm
  PR_ADD_1998_CMO_2 : thm
  pr_madd_1998_cmo : thm
  PR_MADD_1998_CMO : thm
  deriving Inhabited

@[nospecialize]
def setupFormularyProjectiveThms [HolBase] (D : FormularyProjectiveDeps) :
    ExceptT String IO FormularyProjectiveThms := do
  -- @@SCOPE BEGIN
  let { FIELD_TAC, new_definition, .. } := D
  let { FIELD_IMP_INTEGRAL_DOMAIN, LET_DEF, LET_END_DEF, PAIR_EQ, PRIME_2,
        RING_CHAR_DIVIDES_PRIME, projective_0, projective_add, projective_eq,
        projective_neg, projective_point, .. } := D.core1
  -- @@SCOPE END

  /- Point doubling in projective coordinates.

     Source: Bernstein-Lange [2007] "Faster addition and doubling..."

     http://hyperelliptic.org/EFD/g1p/auto-code/shortw/projective/doubling/dbl-2007-bl.op3 -/

  let pr_dbl_2007_bl ← new_definition
   r"pr_dbl_2007_bl (f:A ring,a:A,b:A) (x1,y1,z1) =
      let xx = ring_pow f x1 2 in
      let zz = ring_pow f z1 2 in
      let t0 = ring_mul f (ring_of_num f 3) xx in
      let t1 = ring_mul f a zz in
      let w = ring_add f t1 t0 in
      let t2 = ring_mul f y1 z1 in
      let s = ring_mul f (ring_of_num f 2) t2 in
      let ss = ring_pow f s 2 in
      let sss = ring_mul f s ss in
      let r = ring_mul f y1 s in
      let rr = ring_pow f r 2 in
      let t3 = ring_add f x1 r in
      let t4 = ring_pow f t3 2 in
      let t5 = ring_sub f t4 xx in
      let b = ring_sub f t5 rr in
      let t6 = ring_pow f w 2 in
      let t7 = ring_mul f (ring_of_num f 2) b in
      let h = ring_sub f t6 t7 in
      let x3 = ring_mul f h s in
      let t8 = ring_sub f b h in
      let t9 = ring_mul f (ring_of_num f 2) rr in
      let t10 = ring_mul f w t8 in
      let y3 = ring_sub f t10 t9 in
      let z3 = sss in
      (x3,y3,z3)"

  let PR_DBL_2007_BL ← prove
   r"!f a b x1 y1 z1:A.
        field f /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f (x1,y1,z1)
        ==> projective_eq f (pr_dbl_2007_bl (f,a,b) (x1,y1,z1))
                          (projective_add (f,a,b) (x1,y1,z1) (x1,y1,z1))"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [projective_point] THEN STRIP_TAC THEN
    REWRITE_TAC [pr_dbl_2007_bl, projective_add, projective_eq,
                projective_neg, projective_0] THEN
    ASM_CASES_TAC (← q r"z1:A = ring_0 f") THEN
    ASM_REWRITE_TAC [projective_add, projective_eq,
                    projective_neg, projective_0] THEN
    ASM_REWRITE_TAC [LET_DEF, LET_END_DEF, PAIR_EQ, projective_eq] THEN
    FIELD_TAC THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))

  /- Point doubling in projective coordinates assuming a = -3.

     Source: Bernstein-Lange [2007] "Faster addition and doubling..."

     http://hyperelliptic.org/EFD/g1p/auto-code/shortw/projective-3/doubling/dbl-2007-bl-2.op3 -/

  let p3_dbl_2007_bl_2 ← new_definition
   r"p3_dbl_2007_bl_2 (f:A ring,a:A,b:A) (x1,y1,z1) =
      let t0 = ring_sub f x1 z1 in
      let t1 = ring_add f x1 z1 in
      let t2 = ring_mul f t0 t1 in
      let w = ring_mul f (ring_of_num f 3) t2 in
      let t3 = ring_mul f y1 z1 in
      let s = ring_mul f (ring_of_num f 2) t3 in
      let ss = ring_pow f s 2 in
      let sss = ring_mul f s ss in
      let r = ring_mul f y1 s in
      let rr = ring_pow f r 2 in
      let t4 = ring_mul f x1 r in
      let b = ring_mul f (ring_of_num f 2) t4 in
      let t5 = ring_pow f w 2 in
      let t6 = ring_mul f (ring_of_num f 2) b in
      let h = ring_sub f t5 t6 in
      let x3 = ring_mul f h s in
      let t7 = ring_sub f b h in
      let t8 = ring_mul f (ring_of_num f 2) rr in
      let t9 = ring_mul f w t7 in
      let y3 = ring_sub f t9 t8 in
      let z3 = sss in
      (x3,y3,z3)"

  let P3_DBL_2007_BL_2 ← prove
   r"!f a b x1 y1 z1:A.
        field f /\
        a = ring_of_int f (-- &3) /\ b IN ring_carrier f /\
        projective_point f (x1,y1,z1)
        ==> projective_eq f (p3_dbl_2007_bl_2 (f,a,b) (x1,y1,z1))
                            (projective_add (f,a,b) (x1,y1,z1) (x1,y1,z1))"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [projective_point] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC [p3_dbl_2007_bl_2, projective_add, projective_eq,
                projective_neg, projective_0] THEN
    ASM_CASES_TAC (← q r"z1:A = ring_0 f") THEN
    ASM_REWRITE_TAC [projective_add, projective_eq,
                    projective_neg, projective_0] THEN
    ASM_REWRITE_TAC [LET_DEF, LET_END_DEF, PAIR_EQ, projective_eq] THEN
    FIELD_TAC THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))

  /- Point doubling in projective coordinates assuming a = 0.

     Source: Bernstein-Lange [2007] "Faster addition and doubling..." with
     trivial constant propagation from a = 0.

     http://hyperelliptic.org/EFD/g1p/auto-code/shortw/projective/doubling/dbl-2007-bl.op3
     plus trivial constant propagation -/

  let p0_dbl_2007_bl ← new_definition
   r"p0_dbl_2007_bl (f:A ring,a:A,b:A) (x1,y1,z1) =
      let xx = ring_pow f x1 2 in
      let zz = ring_pow f z1 2 in
      let w = ring_mul f (ring_of_num f 3) xx in
      let t2 = ring_mul f y1 z1 in
      let s = ring_mul f (ring_of_num f 2) t2 in
      let ss = ring_pow f s 2 in
      let sss = ring_mul f s ss in
      let r = ring_mul f y1 s in
      let rr = ring_pow f r 2 in
      let t3 = ring_add f x1 r in
      let t4 = ring_pow f t3 2 in
      let t5 = ring_sub f t4 xx in
      let b = ring_sub f t5 rr in
      let t6 = ring_pow f w 2 in
      let t7 = ring_mul f (ring_of_num f 2) b in
      let h = ring_sub f t6 t7 in
      let x3 = ring_mul f h s in
      let t8 = ring_sub f b h in
      let t9 = ring_mul f (ring_of_num f 2) rr in
      let t10 = ring_mul f w t8 in
      let y3 = ring_sub f t10 t9 in
      let z3 = sss in
      (x3,y3,z3)"

  let P0_DBL_2007_BL ← prove
   r"!f a b x1 y1 z1:A.
        field f /\
        a = ring_0 f /\ b IN ring_carrier f /\
        projective_point f (x1,y1,z1)
        ==> projective_eq f (p0_dbl_2007_bl (f,a,b) (x1,y1,z1))
                            (projective_add (f,a,b) (x1,y1,z1) (x1,y1,z1))"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [projective_point] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC [p0_dbl_2007_bl, projective_add, projective_eq,
                projective_neg, projective_0] THEN
    ASM_CASES_TAC (← q r"z1:A = ring_0 f") THEN
    ASM_REWRITE_TAC [projective_add, projective_eq,
                    projective_neg, projective_0] THEN
    ASM_REWRITE_TAC [LET_DEF, LET_END_DEF, PAIR_EQ, projective_eq] THEN
    FIELD_TAC THEN ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN]))

  /- Pure point addition in projective coordinates. This sequence never uses
     the value of "a" so there's no special optimized version for special
     "a".

     Source Cohen-Miyaji-Ono [1998] "Efficient elliptic curve
     exponentiation"

     Note the correctness is not proved in cases where the points are equal
     (or projectively equivalent), or either input is 0 (point at infinity).

     http://hyperelliptic.org/EFD/g1p/auto-code/shortw/projective/addition/add-1998-cmo-2.op3 -/

  let pr_add_1998_cmo_2 ← new_definition
   r"pr_add_1998_cmo_2 (f:A ring,a:A,b:A) (x1,y1,z1) (x2,y2,z2) =
      let y1z2 = ring_mul f y1 z2 in
      let x1z2 = ring_mul f x1 z2 in
      let z1z2 = ring_mul f z1 z2 in
      let t0 = ring_mul f y2 z1 in
      let u = ring_sub f t0 y1z2 in
      let uu = ring_pow f u 2 in
      let t1 = ring_mul f x2 z1 in
      let v = ring_sub f t1 x1z2 in
      let vv = ring_pow f v 2 in
      let vvv = ring_mul f v vv in
      let r = ring_mul f vv x1z2 in
      let t2 = ring_mul f (ring_of_num f 2) r in
      let t3 = ring_mul f uu z1z2 in
      let t4 = ring_sub f t3 vvv in
      let a = ring_sub f t4 t2 in
      let x3 = ring_mul f v a in
      let t5 = ring_sub f r a in
      let t6 = ring_mul f vvv y1z2 in
      let t7 = ring_mul f u t5 in
      let y3 = ring_sub f t7 t6 in
      let z3 = ring_mul f vvv z1z2 in
      (x3,y3,z3)"

  let PR_ADD_1998_CMO_2 ← prove
   r"!f a b x1 y1 z1 x2 y2 z2:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f (x1,y1,z1) /\ projective_point f (x2,y2,z2) /\
        ~(z1 = ring_0 f) /\ ~(z2 = ring_0 f) /\
        ~(projective_eq f (x1,y1,z1) (x2,y2,z2))
        ==> projective_eq f (pr_add_1998_cmo_2 (f,a,b) (x1,y1,z1) (x2,y2,z2))
                            (projective_add (f,a,b) (x1,y1,z1) (x2,y2,z2))"
   (← do
    let eqA ← q r"(=):A->A->bool"
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [projective_point] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC [← GSYM RING_CHAR_DIVIDES_PRIME, PRIME_2] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC [projective_eq, pr_add_1998_cmo_2, projective_add] THEN
    REPEAT (COND_CASES_TAC THEN
     ASM_REWRITE_TAC [projective_add, projective_eq,
                     projective_neg, projective_0, LET_DEF, LET_END_DEF]) THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o check (fun th => free_in eqA (concl th)))) THEN
    FIELD_TAC))

  /- Mixed point addition in projective coordinates. Here "mixed" means
     assuming z2 = 1, which holds if the second point was directly injected
     from the Weierstrass coordinates via (x,y) |-> (x,y,1). This never uses
     the value of "a" so there's no special optimized version for special
     "a".

     Source Cohen-Miyaji-Ono [1998] "Efficient elliptic curve
     exponentiation"

     Note the correctness is not proved in the case where the points are
     equal or projectively equivalent, nor where the first is the group
     identity (i.e. the point at infinity, anything with z1 = 0 in
     projective coords).

     http://hyperelliptic.org/EFD/g1p/auto-code/shortw/projective/addition/madd-1998-cmo.op3 -/

  let pr_madd_1998_cmo ← new_definition
   r"pr_madd_1998_cmo (f:A ring,a:A,b:A) (x1,y1,z1) (x2,y2,z2) =
      let t0 = ring_mul f y2 z1 in
      let u = ring_sub f t0 y1 in
      let uu = ring_pow f u 2 in
      let t1 = ring_mul f x2 z1 in
      let v = ring_sub f t1 x1 in
      let vv = ring_pow f v 2 in
      let vvv = ring_mul f v vv in
      let r = ring_mul f vv x1 in
      let t2 = ring_mul f (ring_of_num f 2) r in
      let t3 = ring_mul f uu z1 in
      let t4 = ring_sub f t3 vvv in
      let a = ring_sub f t4 t2 in
      let x3 = ring_mul f v a in
      let t5 = ring_sub f r a in
      let t6 = ring_mul f vvv y1 in
      let t7 = ring_mul f u t5 in
      let y3 = ring_sub f t7 t6 in
      let z3 = ring_mul f vvv z1 in
      (x3,y3,z3)"

  let PR_MADD_1998_CMO ← prove
   r"!f a b x1 y1 z1 x2 y2 z2:A.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        projective_point f (x1,y1,z1) /\ projective_point f (x2,y2,z2) /\
        z2 = ring_1 f /\
        ~(z1 = ring_0 f) /\ ~(projective_eq f (x1,y1,z1) (x2,y2,z2))
        ==> projective_eq f (pr_madd_1998_cmo (f,a,b) (x1,y1,z1) (x2,y2,z2))
                            (projective_add (f,a,b) (x1,y1,z1) (x2,y2,z2))"
   (← do
    let eqA ← q r"(=):A->A->bool"
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [projective_point] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC [← GSYM RING_CHAR_DIVIDES_PRIME, PRIME_2] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    REPEAT (FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC [projective_eq, pr_madd_1998_cmo, projective_add] THEN
    REPEAT (COND_CASES_TAC THEN
     ASM_REWRITE_TAC [projective_add, projective_eq,
                     projective_neg, projective_0, LET_DEF, LET_END_DEF]) THEN
    REPEAT (FIRST_X_ASSUM (MP_TAC o check (fun th => free_in eqA (concl th)))) THEN
    FIELD_TAC))

  -- @@RETURN BEGIN
  return { pr_dbl_2007_bl, PR_DBL_2007_BL, p3_dbl_2007_bl_2, P3_DBL_2007_BL_2,
           p0_dbl_2007_bl, P0_DBL_2007_BL, pr_add_1998_cmo_2, PR_ADD_1998_CMO_2,
           pr_madd_1998_cmo, PR_MADD_1998_CMO }
  -- @@RETURN END

end HolEC.FormularyProjective
