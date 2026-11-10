/- ========================================================================= -/
/- Projective coordinates, x = X / Z without y for Montgomery curves.      -/
/- ========================================================================= -/
/- File: HolEC/XZProjective.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/xzprojective.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/montgomery.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.XZProjective fills them).

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

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolEC.XZProjective

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD1 COND_SWAP DE_MORGAN_THM FIELD_CHAR_NOT2 FIELD_CHAR_NOT23
   FIELD_NONTRIVIAL FORALL_OPTION_THM FORALL_PAIR_THM GROUP_POW GROUP_POW_1
   GROUP_POW_ADD GROUP_POW_ID GROUP_POW_MONTGOMERY_TORSION IMP_CONJ IN LET_DEF
   LET_END_DEF MONTGOMERY_GROUP MULT_2 PAIR_EQ RING_1 RING_INV_1 RING_MUL_RID
   montgomery_add montgomery_curve montgomery_neg montgomery_nonsingular
   option_DISTINCT option_INJ ring_div : thm)
  deriving Inhabited

/-- What xzprojective.ml uses from Session besides theorems. -/
structure XZProjectiveDeps where
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
/- Projective coordinates, x = X / Z without y for Montgomery curves.        -/
/- (xzprojective.ml 1-225)                                                   -/
/- ------------------------------------------------------------------------- -/

structure XZProjectiveThms where
  -- @@FIELDS
  montgomery_xz : thm
  MONTGOMERY_XZ_IN_CARRIER : thm
  montgomery_xzdouble : thm
  montgomery_xzdiffadd : thm
  MONTGOMERY_XZDOUBLE : thm
  MONTGOMERY_XZDIFFADD : thm
  MONTGOMERY_XZDOUBLE_GROUP : thm
  MONTGOMERY_XZDIFFADD_GROUP : thm
  montgomery_xmap : thm
  MONTGOMERY_XZ_XMAP : thm
  MONTGOMERY_XMAP_EQ_0 : thm
  MONTGOMERY_XMAP_EQ_0_POW : thm
  MONTGOMERY_ADD_YRECOVERY : thm
  deriving Inhabited

@[nospecialize]
def setupXZProjectiveThms [HolBase] (D : XZProjectiveDeps) :
    ExceptT String IO XZProjectiveThms := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, FIELD_TAC, GROUP_RULE, MESON_TAC, NOT_RING_CHAR_DIVIDES_TAC,
        RING_CARRIER_TAC, SET_RULE, define, .. } := D
  let { ADD1, COND_SWAP, DE_MORGAN_THM, FIELD_CHAR_NOT2, FIELD_CHAR_NOT23,
        FIELD_NONTRIVIAL, FORALL_OPTION_THM, FORALL_PAIR_THM, GROUP_POW, GROUP_POW_1,
        GROUP_POW_ADD, GROUP_POW_ID, GROUP_POW_MONTGOMERY_TORSION, IMP_CONJ, IN,
        LET_DEF, LET_END_DEF, MONTGOMERY_GROUP, MULT_2, PAIR_EQ, RING_1, RING_INV_1,
        RING_MUL_RID, montgomery_add, montgomery_curve, montgomery_neg,
        montgomery_nonsingular, option_DISTINCT, option_INJ, ring_div, .. } := D.core1
  -- @@SCOPE END

  /- The representation is only relational as we throw away the y
     coordinate. -/

  let montgomery_xz ← define
   r"(montgomery_xz (f:A ring) NONE (X,Z) <=>
        X IN ring_carrier f /\ Z IN ring_carrier f /\
        ~(X = ring_0 f) /\ Z = ring_0 f) /\
  (montgomery_xz f (SOME(x,y:A)) (X,Z) <=>
        X IN ring_carrier f /\ Z IN ring_carrier f /\
        ~(Z = ring_0 f) /\ ring_div f X Z = x)"

  let MONTGOMERY_XZ_IN_CARRIER ← prove
   r"!P X Z.
        montgomery_xz f P (X,Z)
        ==> X IN ring_carrier f /\ Z IN ring_carrier f"
   (← do
    pure (SIMP_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, montgomery_xz]))

  /- However, doubling and *differential* addition are calculable. -/

  let montgomery_xzdouble ← define
   r"montgomery_xzdouble (f,a:A,b:A) (X,Z) =
        ring_pow f (ring_sub f (ring_pow f X 2) (ring_pow f Z 2)) 2,
        ring_mul f (ring_mul f (ring_of_num f 4) (ring_mul f X Z))
                   (ring_add f (ring_pow f X 2)
                   (ring_add f (ring_mul f a
                         (ring_mul f X Z)) (ring_pow f Z 2)))"

  let montgomery_xzdiffadd ← define
   r"montgomery_xzdiffadd (f:A ring,a:A,b:A) (X,Z) (Xm,Zm) (Xn,Zn) =
        ring_mul f (ring_mul f (ring_of_num f 4) Z)
                   (ring_pow f (ring_sub f (ring_mul f Xm Xn)
                                           (ring_mul f Zm Zn)) 2),
        ring_mul f (ring_mul f (ring_of_num f 4) X)
                   (ring_pow f (ring_sub f (ring_mul f Xm Zn)
                                           (ring_mul f Xn Zm)) 2)"

  let MONTGOMERY_XZDOUBLE ← prove
   r"!f (a:A) b p q.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_nonsingular(f,a,b) /\
        montgomery_curve(f,a,b) p /\
        montgomery_xz f p q
        ==> montgomery_xz f (montgomery_add(f,a,b) p p)
                            (montgomery_xzdouble(f,a,b) q)"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT2] THEN
    REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    REWRITE_TAC [montgomery_curve, montgomery_add, montgomery_xz,
      ← GSYM DE_MORGAN_THM, montgomery_xzdouble, montgomery_nonsingular] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [COND_SWAP] THEN
    TRY (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    REWRITE_TAC [LET_DEF, LET_END_DEF, montgomery_xz] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  let MONTGOMERY_XZDIFFADD ← prove
   r"!f (a:A) b p q pm qm pn qn.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_nonsingular(f,a,b) /\
        montgomery_curve(f,a,b) p /\
        montgomery_curve(f,a,b) pm /\
        montgomery_curve(f,a,b) pn /\
        montgomery_xz f p q /\
        montgomery_xz f pm qm /\
        montgomery_xz f pn qn /\
        ~(FST q = ring_0 f) /\ ~(SND q = ring_0 f) /\
        montgomery_add (f,a,b) pm (montgomery_neg (f,a,b) pn) = p
        ==> montgomery_xz f (montgomery_add(f,a,b) pm pn)
                            (montgomery_xzdiffadd(f,a,b) q qm qn)"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT23] THEN REPEAT GEN_TAC THEN ASM_CASES_TAC
     (← q r"p = montgomery_add (f,a:A,b) pm (montgomery_neg (f,a,b) pn)") THEN
    ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC : thm → tactic) THEN
    W (fun (_asl, w) => MAP_EVERY (fun t => SPEC_TAC (t, t)) (frees w)) THEN
    REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    REWRITE_TAC [montgomery_curve, montgomery_add, montgomery_xz, montgomery_neg,
      LET_DEF, LET_END_DEF, montgomery_xzdiffadd, montgomery_nonsingular] THEN
    REPEAT (GEN_TAC ORELSE CONJ_TAC) THEN
    REWRITE_TAC [COND_SWAP, option_DISTINCT, option_INJ, PAIR_EQ] THEN
    REPEAT (COND_CASES_TAC THEN
     ASM_REWRITE_TAC [option_DISTINCT, option_INJ, PAIR_EQ, montgomery_add,
                     LET_DEF, LET_END_DEF, montgomery_xz]) THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  let MONTGOMERY_XZDOUBLE_GROUP ← prove
   r"!f (a:A) b p n q.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_nonsingular(f,a,b) /\
        p IN group_carrier (montgomery_group(f,a,b)) /\
        montgomery_xz f (group_pow (montgomery_group(f,a,b)) p n) q
        ==> montgomery_xz f (group_pow (montgomery_group(f,a,b)) p (2 * n))
                            (montgomery_xzdouble(f,a,b) q)"
   (← do
    pure (REPEAT STRIP_TAC THEN ASM_SIMP_TAC [MULT_2, GROUP_POW_ADD] THEN
    ASM_SIMP_TAC [MONTGOMERY_GROUP] THEN
    MATCH_MP_TAC MONTGOMERY_XZDOUBLE THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM (MP_TAC o SPEC (← q r"n:num") o MATCH_MP GROUP_POW) THEN
    ASM_SIMP_TAC [MONTGOMERY_GROUP] THEN REWRITE_TAC [IN]))

  let MONTGOMERY_XZDIFFADD_GROUP ← prove
   r"!f (a:A) b p n q qm qn.
        field f /\ ~(ring_char f = 2) /\ ~(ring_char f = 3) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_nonsingular(f,a,b) /\
        ~(FST q = ring_0 f) /\ ~(SND q = ring_0 f) /\
        p IN group_carrier (montgomery_group(f,a,b)) /\
        montgomery_xz f p q /\
        montgomery_xz f (group_pow (montgomery_group(f,a,b)) p (n + 1)) qm /\
        montgomery_xz f (group_pow (montgomery_group(f,a,b)) p n) qn
        ==> montgomery_xz f (group_pow (montgomery_group(f,a,b)) p (2 * n + 1))
                            (montgomery_xzdiffadd(f,a,b) q qm qn)"
   (← do
    -- right to left: the GROUP_RULE, the second ARITH_RULE, the SET_RULE,
    -- then the first ARITH_RULE
    let g4 ← GROUP_RULE (← q r"group_mul G (group_mul G x y) (group_inv G y) = x")
    let a3 ← ARITH_RULE (← q r"n + 1 = 1 + n")
    let s2 ← SET_RULE (← q r"group_carrier G x <=> x IN group_carrier G")
    let a1 ← ARITH_RULE (← q r"2 * n + 1 = SUC n + n")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [a1] THEN
    ASM_SIMP_TAC [GROUP_POW_ADD] THEN
    MP_TAC (← SPECL [← q r"f:A ring", ← q r"a:A", ← q r"b:A"] MONTGOMERY_GROUP) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th => tactic_of do
      pure (SUBST1_TAC (← liftExcept (HolCore.Lib.last (CONJUNCTS th))))) THEN
    MATCH_MP_TAC MONTGOMERY_XZDIFFADD THEN EXISTS_TAC (← q r"p:(A#A)option") THEN
    ASM_REWRITE_TAC [ADD1] THEN
    MP_TAC (← SPECL [← q r"f:A ring", ← q r"a:A", ← q r"b:A"] MONTGOMERY_GROUP) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th => tactic_of do pure (REWRITE_TAC [← GSYM th])) THEN
    ONCE_REWRITE_TAC [s2] THEN
    ONCE_REWRITE_TAC [a3] THEN
    ASM_SIMP_TAC [GROUP_POW, GROUP_POW_ADD, GROUP_POW_1] THEN
    MATCH_MP_TAC g4 THEN
    ASM_SIMP_TAC [GROUP_POW]))

  /- A functional X coordinate mapping as used in the x25519 functions. -/

  let montgomery_xmap ← define
   r"montgomery_xmap (f:A ring) NONE = ring_0 f /\
  montgomery_xmap f (SOME(x:A,y:A)) = x"

  let MONTGOMERY_XZ_XMAP ← prove
   r"!(f:A ring) P X.
        field f /\ X IN ring_carrier f /\ ~(X = ring_0 f)
        ==> (montgomery_xz f P (X,ring_1 f) <=> montgomery_xmap f P = X)"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    SIMP_TAC [montgomery_xz, montgomery_xmap, FIELD_NONTRIVIAL, RING_1] THEN
    SIMP_TAC [ring_div, RING_INV_1, RING_MUL_RID] THEN MESON_TAC []))

  let MONTGOMERY_XMAP_EQ_0 ← prove
   r"!(f:A ring) a b P.
      field f /\ ~(ring_char f = 2) /\
      a IN ring_carrier f /\ b IN ring_carrier f /\
      montgomery_nonsingular (f,a,b) /\
      P IN group_carrier(montgomery_group(f,a,b))
      ==> (montgomery_xmap f P = ring_0 f <=>
           P = NONE \/ P = SOME(ring_0 f,ring_0 f))"
   (← do
    pure (REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM, montgomery_xmap] THEN
    REWRITE_TAC [option_DISTINCT, option_INJ, PAIR_EQ] THEN
    SIMP_TAC [IMP_CONJ, MONTGOMERY_GROUP] THEN
    MAP_EVERY X_GEN_TAC [← q r"f:A ring", ← q r"a:A", ← q r"b:A", ← q r"x:A",
                         ← q r"y:A"] THEN
    REPLICATE_TAC 5 DISCH_TAC THEN REWRITE_TAC [IN] THEN
    ASM_CASES_TAC (← q r"x:A = ring_0 f") THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [montgomery_curve] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    FIRST_X_ASSUM (MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I
      [montgomery_nonsingular]) THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (fun th => tactic_of do
      let _ ← liftExcept (check (fun th => is_neg (concl th)) th); pure ALL_TAC) THEN
    FIELD_TAC))

  let MONTGOMERY_XMAP_EQ_0_POW ← prove
   r"!(f:A ring) a b P n.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\
        montgomery_nonsingular (f,a,b) /\
        P IN group_carrier(montgomery_group(f,a,b)) /\
        montgomery_xmap f P = ring_0 f
        ==> montgomery_xmap f (group_pow (montgomery_group(f,a,b)) P n) =
            ring_0 f"
   (← do
    pure (REPEAT GEN_TAC THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MP_TAC (← ISPECL [← q r"f:A ring", ← q r"a:A", ← q r"b:A"] MONTGOMERY_XMAP_EQ_0) THEN
    ASM_SIMP_TAC [GROUP_POW] THEN DISCH_THEN (K ALL_TAC : thm → tactic) THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC [GROUP_POW_MONTGOMERY_TORSION] THENL
     [DISJ1_TAC, MESON_TAC []] THEN
    wPart (fun t => do rator (← rator (← lhand t)))
          (fun t => do rator (← rator (← lhand t))) GROUP_POW_ID THEN
    ASM_SIMP_TAC [MONTGOMERY_GROUP]))

  /- The y coordinate can be recovered from any nondegenerate addition (e.g.
     differential) where we know the y coordinate of one of the addends.
     This formula is from Okeya and Sakurai's paper in CHES 2001 (LNCS 2162,
     p129).

     Suppose (x1,y1) + (x,y) = (x2,y2). Then
     y1 = ((x1 * x + 1) * (x1 + x + 2 * A) - 2 * A - (x1 - x)^2 * x2) /
          (2 * B * y) -/

  let MONTGOMERY_ADD_YRECOVERY ← prove
   r"!f a (b:A) x y x1 y1 x2 y2.
        field f /\ ~(ring_char f = 2) /\
        a IN ring_carrier f /\ b IN ring_carrier f /\ ~(b = ring_0 f) /\
        montgomery_curve (f,a,b) (SOME(x,y)) /\ ~(y = ring_0 f) /\
        montgomery_curve (f,a,b) (SOME(x1,y1)) /\
        montgomery_add(f,a,b) (SOME(x,y)) (SOME(x1,y1)) = SOME(x2,y2)
        ==> y1 = ring_div f
                  (ring_sub f
                   (ring_sub f
                    (ring_mul f (ring_add f (ring_mul f x1 x) (ring_1 f))
                    (ring_add f x1
                      (ring_add f x (ring_mul f (ring_of_num f 2) a))))
                      (ring_mul f (ring_of_num f 2) a))
                     (ring_mul f (ring_pow f (ring_sub f x1 x) 2) x2))
                  (ring_mul f (ring_of_num f 2) (ring_mul f b y))"
   (← do
    pure (REWRITE_TAC [FIELD_CHAR_NOT2] THEN
    REWRITE_TAC [montgomery_nonsingular] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC [montgomery_curve, montgomery_add, LET_DEF, LET_END_DEF] THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC [option_DISTINCT]) THEN
    REWRITE_TAC [option_INJ, PAIR_EQ] THEN REPEAT STRIP_TAC THEN
    REPLICATE_TAC 2 (FIRST_X_ASSUM (fun th => tactic_of do
      pure (SUBST1_TAC (← SYM th)))) THEN
    FIELD_TAC THEN NOT_RING_CHAR_DIVIDES_TAC))

  -- @@RETURN BEGIN
  return { montgomery_xz, MONTGOMERY_XZ_IN_CARRIER, montgomery_xzdouble,
           montgomery_xzdiffadd, MONTGOMERY_XZDOUBLE, MONTGOMERY_XZDIFFADD,
           MONTGOMERY_XZDOUBLE_GROUP, MONTGOMERY_XZDIFFADD_GROUP, montgomery_xmap,
           MONTGOMERY_XZ_XMAP, MONTGOMERY_XMAP_EQ_0, MONTGOMERY_XMAP_EQ_0_POW,
           MONTGOMERY_ADD_YRECOVERY }
  -- @@RETURN END

end HolEC.XZProjective
