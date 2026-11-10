/- ========================================================================= -/
/- The x25519 function, and curve25519 over extensions of the prime field. -/
/- ========================================================================= -/
/- File: HolEC/X25519.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/x25519.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/montgomery.ml, EC/excluderoots.ml, EC/computegroup.ml, EC/curve25519.ml, EC/xzprojective.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.X25519 fills them).

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
import HolEC.ExcludeRoots
import HolEC.ComputeGroup
import HolEC.Curve25519
import HolEC.XZProjective

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolEC.X25519

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ADD_CLAUSES AND_FORALL_THM ARITH_EQ ARITH_LE ARITH_LT A_25519 COND_SWAP CONG
   CONG_SQUARE_1_PRIME_POWER CONTRAPOS_THM COPRIME_SYM CURVE25519_GROUP C_25519
   DIVIDES_LE DIVIDES_MOD DIVIDES_ONE EQ_IMP EULER_CRITERION EVEN
   EXISTS_OPTION_THM EXISTS_OR_THM EXISTS_PAIR_THM EXP_1 EXP_2 EXP_EXP
   FERMAT_LITTLE_PRIME FIELD_IMP_INTEGRAL_DOMAIN FIELD_INTEGER_MOD_RING
   FIELD_NONTRIVIAL FORALL_INT_CASES FORALL_IN_GSPEC FORALL_IN_IMAGE
   FORALL_OPTION_THM FORALL_PAIR_THM GENERATOR_IN_GROUP_CARRIER_CURVE25519
   GROUP_ELEMENT_ORDER_CURVE25519_C25519 GROUP_POW GROUP_POW_1 GROUP_POW_EQ_ID
   GROUP_POW_ID GROUP_POW_MUL IMP_CONJ IN INTEGER_MOD_RING_CHAR
   INTEGER_MOD_RING_CLAUSES INTEGER_MOD_RING_ROOT_EXISTS INTEGRAL_DOMAIN_CHAR
   INT_CONG INT_CONG_LMUL INT_CONG_REFL INT_CONG_RREM INT_CONG_TRANS
   INT_LT_REM_EQ INT_OF_NUM_CLAUSES INT_OF_NUM_EQ INT_OF_NUM_OF_INT
   INT_OF_NUM_REM INT_POS INT_REM_EQ INT_REM_EQ_0 INT_REM_POS_EQ INT_REM_REM
   INVERSE_MOD_LMUL_EQ INVERSE_MOD_RMUL_EQ IN_CROSS IN_INTEGER_MOD_RING_CARRIER
   MOD_0 MOD_LT MOD_LT_EQ_LT MOD_MOD_EXP_MIN MOD_MULT_ADD MOD_MULT_MOD2
   MONTGOMERY_GROUP MONTGOMERY_NONSINGULAR_CURVE25519 MONTGOMERY_XMAP_EQ_0
   MONTGOMERY_XZDIFFADD_GROUP MONTGOMERY_XZDOUBLE_GROUP MULT_CLAUSES MULT_EXP
   NOT_EXISTS_THM NOT_IMP PAIR_EQ PRIME_1 PRIME_COPRIME_EQ PRIME_DIVEXP_EQ
   PRIME_DIVPROD_EQ PRIME_P25519 RIGHT_FORALL_IMP_THM RING_1
   RING_CHAR_MONOMORPHIC_IMAGE RING_DIV RING_DIV_1 RING_HOMOMORPHISM
   RING_LINV_UNIQUE RING_MONOMORPHISM_ALT RING_MUL_LID RING_NEG_0 RING_OF_INT
   RING_OF_INT_CLAUSES RING_OF_INT_EQ RING_OF_INT_EQ_0 RING_OF_INT_NEG
   RING_OF_INT_OF_NUM RING_OF_INT_REM RING_OF_NUM RING_OF_NUM_0 RING_OF_NUM_1
   RING_OF_NUM_EQ RING_OF_NUM_EQ_0 RING_OF_NUM_MOD RING_OF_NUM_MUL RING_POW
   RING_POW_2 SELECT_UNIQUE SUBSET SUB_0 curve25519 curve25519_group field
   group_pow montgomery_add montgomery_curve montgomery_nonsingular
   montgomery_xmap montgomery_xz montgomery_xzdiffadd montgomery_xzdouble
   n_25519 num_WF num_congruent num_divides p_25519 ring_0 ring_1 ring_add
   ring_carrier ring_div ring_mul ring_neg ring_of_num ring_tybij : thm)
  deriving Inhabited

/-- What x25519.ml uses from Session besides theorems. -/
structure X25519Deps where
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
  PRIME_RULE : List String → term → ExceptT String IO thm  -- pocklington.ml's PRIME_RULE
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
  NUM_SUB_CONV : ioconv
  NUM_EQ_CONV : ioconv
  NUM_DIV_CONV : ioconv
  EXP_MOD_CONV : ioconv
  EXPAND_CASES_CONV : ioconv
  DIVIDES_CONV : ioconv  -- prime.ml's DIVIDES_CONV
  COPRIME_CONV : ioconv
  NOT_RING_CHAR_DIVIDES_TAC : tactic  -- misc.ml's NOT_RING_CHAR_DIVIDES_TAC
  EXCLUDE_MODULAR_CUBIC_ROOTS_TAC : thm → List thm → ExceptT String IO tactic  -- excluderoots.ml's EXCLUDE_MODULAR_CUBIC_ROOTS_TAC
  add_curve : thm → IO Unit  -- computegroup.ml's add_curve
  add_curvezero : thm → IO Unit
  add_curveneg : thm → IO Unit
  add_curveadd : thm → IO Unit
  add_ecgroup : List thm → thm → ExceptT String IO Unit
  ECGROUP_CARRIER_CONV : ioconv
  ECGROUP_ID_CONV : ioconv
  ECGROUP_INV_CONV : ioconv
  ECGROUP_MUL_CONV : ioconv
  ECGROUP_POW_CONV : ioconv
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
/- The generalization of curve25519 to any field, nonsingularity (in         -/
/- particular over extensions of the curve25519 prime field), a substitute   -/
/- for strong nonsingularity for an X coordinate in the prime subfield, and  -/
/- the curve group over the general field.  (x25519.ml 1-161)                -/
/- ------------------------------------------------------------------------- -/

structure X25519Curve where
  -- @@FIELDS
  curve25519x : thm
  curve25519x_curve25519 : thm
  MONTGOMERY_NONSINGULAR_CURVE25519X_GEN : thm
  MONTGOMERY_NONSINGULAR_CURVE25519X : thm
  SPECIALLY_NONSINGULAR_CURVE25519X : thm
  curve25519x_group : thm
  CURVE25519X_CURVE25519_GROUP : thm
  CURVE25519X_GROUP_GEN : thm
  CURVE25519X_GROUP : thm
  GROUP_POW_CURVE25519X_TORSION : thm
  deriving Inhabited

@[nospecialize]
def setupX25519Curve [HolBase] (D : X25519Deps) :
    ExceptT String IO X25519Curve := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, DIVIDES_CONV, EXP_MOD_CONV, FIELD_TAC, INDUCT_TAC,
        INTEGER_MOD_RING_RED_CONV, INTEGRAL_DOMAIN_RULE, INT_REDUCE_CONV, MESON,
        NUM_DIV_CONV, NUM_EQ_CONV, NUM_REDUCE_CONV, NUM_SUB_CONV, TAUT, define, .. } := D
  let { ARITH_EQ, A_25519, COND_SWAP, CONG, CONTRAPOS_THM, DIVIDES_ONE,
        EULER_CRITERION, EVEN, FIELD_IMP_INTEGRAL_DOMAIN, INTEGRAL_DOMAIN_CHAR,
        INT_CONG, INT_OF_NUM_CLAUSES, MONTGOMERY_GROUP, PAIR_EQ, PRIME_1,
        PRIME_DIVEXP_EQ, PRIME_DIVPROD_EQ, PRIME_P25519, RIGHT_FORALL_IMP_THM,
        RING_OF_INT_CLAUSES, RING_OF_INT_EQ, RING_OF_INT_EQ_0, RING_OF_INT_NEG,
        RING_OF_INT_OF_NUM, RING_OF_NUM, RING_OF_NUM_1, curve25519, curve25519_group,
        group_pow, montgomery_add, montgomery_curve, montgomery_nonsingular,
        num_congruent, num_divides, p_25519, .. } := D.core1
  -- @@SCOPE END

  /- The generalization of curve25519 to any field. -/

  let curve25519x ← define
   r"curve25519x (f:A ring) = (f,ring_of_num f A_25519,ring_of_num f 1)"

  let curve25519x_curve25519 ← prove
   r"curve25519x (integer_mod_ring p_25519) = curve25519"
   (← do
    pure (REWRITE_TAC [curve25519, curve25519x, PAIR_EQ, p_25519, A_25519] THEN
    CONV_TAC (DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN REWRITE_TAC []))

  /- Nonsingularity, in particular over extensions of curve25519 prime field. -/

  let MONTGOMERY_NONSINGULAR_CURVE25519X_GEN ← prove
   r"!f:A ring.
        field f /\
        ~(ring_char f divides 14802493890)
        ==> montgomery_nonsingular(curve25519x f)"
   (← do
    -- right to left: the three ARITH_RULEs from the last, the MESON, then
    -- the INTEGRAL_DOMAIN_RULE (`CONV_TAC TAUT` runs later, as a conversion)
    let a45 ← ARITH_RULE (← q r"486664 = 2 EXP 3 * 127 * 479")
    let a44 ← ARITH_RULE (← q r"486660 = 2 EXP 2 * 3 * 5 * 8111")
    let a43 ← ARITH_RULE (← q r"14802493890 = 2 * 3 * 5 * 127 * 479 * 8111")
    let m42 ← MESON [PRIME_1] (← q r"prime p ==> ~(p = 1)")
    let i30 ← INTEGRAL_DOMAIN_RULE
     (← q r"ring_pow f x 2 = ring_of_num f 4 <=>
      x = ring_of_num f 2 \/ x = ring_neg f (ring_of_num f 2)")
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [montgomery_nonsingular, curve25519x] THEN
    ASM_SIMP_TAC [FIELD_IMP_INTEGRAL_DOMAIN, RING_OF_NUM, i30] THEN
    REWRITE_TAC [← GSYM RING_OF_INT_NEG, ← GSYM RING_OF_INT_OF_NUM] THEN
    REWRITE_TAC [RING_OF_INT_EQ, RING_OF_INT_EQ_0] THEN REWRITE_TAC [INT_CONG] THEN
    REWRITE_TAC [A_25519] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC [← GSYM num_divides, DIVIDES_ONE] THEN POP_ASSUM MP_TAC THEN
    POP_ASSUM (MP_TAC o MATCH_MP INTEGRAL_DOMAIN_CHAR o
          MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
    SPEC_TAC (← q r"ring_char (f:A ring)", ← q r"p:num") THEN GEN_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [ARITH_EQ] THEN
    CONV_TAC (DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC [] THEN
    ASM_SIMP_TAC [m42] THEN
    REWRITE_TAC [a43,
                 a44,
                 a45] THEN
    ASM_SIMP_TAC [PRIME_DIVPROD_EQ, PRIME_DIVEXP_EQ] THEN
    CONV_TAC (ONCE_DEPTH_CONV NUM_EQ_CONV) THEN CONV_TAC (fun t => (TAUT t).run)))

  let MONTGOMERY_NONSINGULAR_CURVE25519X ← prove
   r"!f:A ring.
        field f /\ ring_char f = p_25519
        ==> montgomery_nonsingular(curve25519x f)"
   (← do
    pure (REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MONTGOMERY_NONSINGULAR_CURVE25519X_GEN THEN
    ASM_REWRITE_TAC [p_25519] THEN
    CONV_TAC (DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC []))

  /- We don't have strong nonsingularity in general but we do have this
     analogous property for an X coordinate belonging to the prime (sub)field. -/

  let SPECIALLY_NONSINGULAR_CURVE25519X ← prove
   r"!f X y:A.
        field f /\ ring_char f = p_25519 /\
        montgomery_curve (curve25519x f) (SOME(ring_of_num f X,y))
        ==> (y = ring_0 f <=> ring_of_num f X = ring_0 f)"
   (← do
    -- `let lemma = prove ... in` first, then the main tactic's MESON
    let lemma ← prove
     r"!f:A ring.
            field f /\
            A IN ring_carrier f /\
            x IN ring_carrier f /\
            y IN ring_carrier f /\
            ~(ring_pow f (ring_add f (ring_mul f (ring_of_num f 2) x) A) 2 =
              ring_sub f (ring_pow f A 2) (ring_of_num f 4))
            ==> ring_mul f (ring_1 f) (ring_pow f y 2) =
                ring_add f (ring_pow f x 3)
                (ring_add f (ring_mul f A (ring_pow f x 2)) x)
            ==> (y = ring_0 f <=> x = ring_0 f)"
     (← do
      pure FIELD_TAC)
    let m89 ← MESON []
     (← q r"(z EXP 2 == a) (mod p) ==> ?x:num. (x EXP 2 == a) (mod p)")
    pure (REPEAT GEN_TAC THEN
    REWRITE_TAC [montgomery_curve, curve25519x, RING_OF_NUM_1] THEN
    REPEAT (DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC [RING_OF_NUM] THEN
    REWRITE_TAC [← GSYM RING_OF_INT_OF_NUM, RING_OF_INT_CLAUSES] THEN
    ASM_REWRITE_TAC [RING_OF_INT_EQ, A_25519, p_25519] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC [← GSYM num_congruent, INT_OF_NUM_CLAUSES] THEN
    DISCH_THEN (MP_TAC o MATCH_MP m89) THEN
    SIMP_TAC [EULER_CRITERION, ← REWRITE_RULE [p_25519] PRIME_P25519] THEN
    CONV_TAC (DEPTH_CONV
     (NUM_SUB_CONV ORELSEC NUM_DIV_CONV ORELSEC DIVIDES_CONV)) THEN
    REWRITE_TAC [CONG] THEN CONV_TAC (ONCE_DEPTH_CONV EXP_MOD_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV))

  /- Definition of the curve group over the general field. -/

  let curve25519x_group ← define
   r"curve25519x_group (f:A ring) = montgomery_group(curve25519x f)"

  let CURVE25519X_CURVE25519_GROUP ← prove
   r"curve25519x_group (integer_mod_ring p_25519) = curve25519_group"
   (← do
    pure (REWRITE_TAC [curve25519_group, curve25519x_group, curve25519x] THEN
    REWRITE_TAC [p_25519, A_25519] THEN
    CONV_TAC (DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN REWRITE_TAC []))

  let CURVE25519X_GROUP_GEN ← prove
   r"!f:A ring.
        field f /\ ~(ring_char f divides 14802493890)
        ==> group_carrier (curve25519x_group f) =
              montgomery_curve (curve25519x f) /\
            group_id (curve25519x_group f) =
              NONE /\
            group_inv (curve25519x_group f) =
              montgomery_neg (curve25519x f) /\
            group_mul (curve25519x_group f) =
              montgomery_add (curve25519x f)"
   (← do
    pure (GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [curve25519x_group, curve25519x] THEN
    MATCH_MP_TAC MONTGOMERY_GROUP THEN ASM_REWRITE_TAC [RING_OF_NUM] THEN
    REWRITE_TAC [← GSYM curve25519x] THEN
    ASM_SIMP_TAC [MONTGOMERY_NONSINGULAR_CURVE25519X_GEN] THEN
    POP_ASSUM MP_TAC THEN SIMP_TAC [CONTRAPOS_THM] THEN
    CONV_TAC (DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC []))

  let CURVE25519X_GROUP ← prove
   r"!f:A ring.
        field f /\ ring_char f = p_25519
        ==> group_carrier (curve25519x_group f) =
              montgomery_curve (curve25519x f) /\
            group_id (curve25519x_group f) =
              NONE /\
            group_inv (curve25519x_group f) =
              montgomery_neg (curve25519x f) /\
            group_mul (curve25519x_group f) =
              montgomery_add (curve25519x f)"
   (← do
    pure (GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CURVE25519X_GROUP_GEN THEN
    ASM_REWRITE_TAC [p_25519] THEN
    CONV_TAC (DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC []))

  let GROUP_POW_CURVE25519X_TORSION ← prove
   r"!(f:A ring) n.
        field f /\ ring_char f = p_25519
        ==> group_pow (curve25519x_group f) (SOME(ring_0 f,ring_0 f)) n =
            if EVEN n then NONE else SOME(ring_0 f,ring_0 f)"
   (← do
    pure (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    INDUCT_TAC THEN
    ASM_SIMP_TAC [group_pow, EVEN, CURVE25519X_GROUP, COND_SWAP] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC [montgomery_add, curve25519x]))

  -- @@RETURN BEGIN
  return { curve25519x, curve25519x_curve25519, MONTGOMERY_NONSINGULAR_CURVE25519X_GEN,
           MONTGOMERY_NONSINGULAR_CURVE25519X, SPECIALLY_NONSINGULAR_CURVE25519X,
           curve25519x_group, CURVE25519X_CURVE25519_GROUP, CURVE25519X_GROUP_GEN,
           CURVE25519X_GROUP, GROUP_POW_CURVE25519X_TORSION }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- Construction of quadratic extension (Z/p_25519)/sqrt(2) as used           -/
/- in Bernstein's original https://cr.yp.to/ecdh/curve25519-20060209.pdf;    -/
/- this proceeds via a slightly more general quadratic_extension (which      -/
/- could be further subsumed by a general algebraic extension construction). -/
/- (x25519.ml 162-358)                                                       -/
/- ------------------------------------------------------------------------- -/

structure X25519Quadratic where
  -- @@FIELDS
  quadratic_extension : thm
  QUADRATIC_EXTENSION : thm
  RING_HOMOMORPHISM_INTO_QUADRATIC_EXTENSION : thm
  RING_MONOMORPHISM_INTO_QUADRATIC_EXTENSION : thm
  RING_OF_NUM_QUADRATIC_EXTENSION : thm
  RING_OF_INT_QUADRATIC_EXTENSION : thm
  RING_CHAR_QUADRATIC_EXTENSION : thm
  FIELD_QUADRATIC_EXTENSION : thm
  sqintmod_field : thm
  FIELD_SQINTMOD_FIELD : thm
  RING_CHAR_SQINTMOD_FIELD : thm
  SQUARE_ROOTS_SQINTMOD_FIELD : thm
  deriving Inhabited

@[nospecialize]
def setupX25519Quadratic [HolBase] (D : X25519Deps) :
    ExceptT String IO X25519Quadratic := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, COPRIME_CONV, DIVIDES_CONV, EXP_MOD_CONV, FIELD_TAC, INDUCT_TAC,
        INT_ARITH, INT_REM_DOWN_CONV, MESON, MESON_TAC, NUMBER_RULE, NUM_DIV_CONV,
        NUM_REDUCE_CONV, NUM_SUB_CONV, RING_CARRIER_TAC, RING_TAC, TAUT,
        new_definition, .. } := D
  let { ADD_CLAUSES, AND_FORALL_THM, ARITH_EQ, ARITH_LE, ARITH_LT, CONG,
        CONG_SQUARE_1_PRIME_POWER, COPRIME_SYM, EULER_CRITERION, EXISTS_OR_THM,
        EXISTS_PAIR_THM, EXP_1, EXP_2, EXP_EXP, FERMAT_LITTLE_PRIME,
        FIELD_INTEGER_MOD_RING, FIELD_NONTRIVIAL, FORALL_INT_CASES, FORALL_IN_IMAGE,
        FORALL_PAIR_THM, INTEGER_MOD_RING_CHAR, INTEGER_MOD_RING_CLAUSES,
        INTEGER_MOD_RING_ROOT_EXISTS, INT_LT_REM_EQ, INT_OF_NUM_CLAUSES,
        INT_OF_NUM_REM, INT_POS, INT_REM_POS_EQ, INVERSE_MOD_RMUL_EQ, IN_CROSS,
        IN_INTEGER_MOD_RING_CARRIER, MOD_0, MOD_LT, MOD_MULT_MOD2, MULT_CLAUSES,
        MULT_EXP, NOT_EXISTS_THM, NOT_IMP, PAIR_EQ, PRIME_COPRIME_EQ, PRIME_DIVPROD_EQ,
        PRIME_P25519, RING_CHAR_MONOMORPHIC_IMAGE, RING_DIV, RING_HOMOMORPHISM,
        RING_MONOMORPHISM_ALT, RING_NEG_0, RING_OF_INT_NEG, RING_OF_INT_OF_NUM,
        RING_POW_2, SUBSET, field, p_25519, ring_0, ring_1, ring_add, ring_carrier,
        ring_mul, ring_neg, ring_of_num, ring_tybij, .. } := D.core1
  -- @@SCOPE END

  let quadratic_extension ← new_definition
   r"quadratic_extension (r:A ring) a =
        ring((ring_carrier r CROSS ring_carrier r),
             (ring_0 r,ring_0 r),
             (ring_1 r,ring_0 r),
             (\(x,y). ring_neg r x,ring_neg r y),
             (\(x1,y1) (x2,y2). ring_add r x1 x2,ring_add r y1 y2),
             (\(x1,y1) (x2,y2).
                ring_add r (ring_mul r x1 x2)
                           (ring_mul r (ring_of_num r a) (ring_mul r y1 y2)),
                ring_add r (ring_mul r x1 y2) (ring_mul r x2 y1)))"

  let QUADRATIC_EXTENSION ← prove
   r"(!(r:A ring) a. ring_carrier(quadratic_extension r a) =
                   ring_carrier r CROSS ring_carrier r) /\
   (!(r:A ring) a. ring_0 (quadratic_extension r a) =
                   (ring_0 r,ring_0 r)) /\
   (!(r:A ring) a. ring_1 (quadratic_extension r a) =
                   (ring_1 r,ring_0 r)) /\
   (!(r:A ring) a. ring_neg (quadratic_extension r a) =
                   \(x,y). ring_neg r x,ring_neg r y) /\
   (!(r:A ring) a. ring_add (quadratic_extension r a) =
                   \(x1,y1) (x2,y2). ring_add r x1 x2,ring_add r y1 y2) /\
   (!(r:A ring) a. ring_mul (quadratic_extension r a) =
                   \(x1,y1) (x2,y2).
                     ring_add r (ring_mul r x1 x2)
                                (ring_mul r (ring_of_num r a)
                                            (ring_mul r y1 y2)),
                     ring_add r (ring_mul r x1 y2) (ring_mul r x2 y1))"
   (← do
    -- `rand(rand(snd(strip_forall(concl quadratic_extension))))`
    let qtm ← liftExcept (do
      rand (← rand (strip_forall (concl quadratic_extension)).2))
    pure (REWRITE_TAC [AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
    MP_TAC (← EQ_IMP_RULE
     (← ISPEC qtm
     (← CONJUNCT2 ring_tybij))).1 THEN
    REWRITE_TAC [← GSYM quadratic_extension] THEN ANTS_TAC THENL
     [REWRITE_TAC [FORALL_PAIR_THM, IN_CROSS, PAIR_EQ] THEN
      REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN RING_TAC,
      DISCH_TAC THEN
      ASM_REWRITE_TAC [ring_carrier, ring_0, ring_1, ring_neg,
                       ring_add, ring_mul]]))

  let RING_HOMOMORPHISM_INTO_QUADRATIC_EXTENSION ← prove
   r"!(r:A ring) a.
    ring_homomorphism (r,quadratic_extension r a) (\x. (x,ring_0 r))"
   (← do
    pure (REWRITE_TAC [RING_HOMOMORPHISM, QUADRATIC_EXTENSION, PAIR_EQ] THEN
    REWRITE_TAC [SUBSET, FORALL_IN_IMAGE, FORALL_PAIR_THM, IN_CROSS] THEN
    REPEAT STRIP_TAC THEN TRY RING_CARRIER_TAC THEN RING_TAC))

  let RING_MONOMORPHISM_INTO_QUADRATIC_EXTENSION ← prove
   r"!(r:A ring) a.
    ring_monomorphism (r,quadratic_extension r a) (\x. (x,ring_0 r))"
   (← do
    pure (REWRITE_TAC [RING_MONOMORPHISM_ALT] THEN
    REWRITE_TAC [RING_HOMOMORPHISM_INTO_QUADRATIC_EXTENSION] THEN
    SIMP_TAC [QUADRATIC_EXTENSION, PAIR_EQ]))

  let RING_OF_NUM_QUADRATIC_EXTENSION ← prove
   r"!(r:A ring) a n.
        ring_of_num (quadratic_extension r a) n = (ring_of_num r n,ring_0 r)"
   (← do
    pure (GEN_TAC THEN GEN_TAC THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC [ring_of_num, QUADRATIC_EXTENSION] THEN
    REWRITE_TAC [PAIR_EQ] THEN RING_TAC))

  let RING_OF_INT_QUADRATIC_EXTENSION ← prove
   r"!(r:A ring) a n.
        ring_of_int (quadratic_extension r a) n = (ring_of_int r n,ring_0 r)"
   (← do
    pure (REWRITE_TAC [FORALL_INT_CASES, RING_OF_INT_NEG, RING_OF_INT_OF_NUM] THEN
    REWRITE_TAC [RING_OF_NUM_QUADRATIC_EXTENSION, QUADRATIC_EXTENSION] THEN
    REWRITE_TAC [RING_NEG_0]))

  let RING_CHAR_QUADRATIC_EXTENSION ← prove
   r"!(r:A ring) a. ring_char (quadratic_extension r a) = ring_char r"
   (← do
    pure (REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RING_CHAR_MONOMORPHIC_IMAGE THEN
    MESON_TAC [RING_MONOMORPHISM_INTO_QUADRATIC_EXTENSION]))

  let FIELD_QUADRATIC_EXTENSION ← prove
   r"!(r:A ring) a.
        field r /\
        (!d. d IN ring_carrier r ==> ~(ring_pow r d 2 = ring_of_num r a))
        ==> field(quadratic_extension r a)"
   (← do
    pure (REPEAT STRIP_TAC THEN REWRITE_TAC [field, QUADRATIC_EXTENSION] THEN
    REWRITE_TAC [FORALL_PAIR_THM, EXISTS_PAIR_THM, IN_CROSS, PAIR_EQ] THEN
    ASM_SIMP_TAC [FIELD_NONTRIVIAL] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"] THEN STRIP_TAC THEN
    ABBREV_TAC (← q r"d:A = ring_sub r (ring_pow r x 2)
                                 (ring_mul r (ring_of_num r a)
                                             (ring_pow r y 2))") THEN
    SUBGOAL_THEN (← q r"~(d:A = ring_0 r)") ASSUME_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o SPEC (← q r"ring_div r x y:A")) THEN
      ASM_SIMP_TAC [RING_DIV] THEN
      POP_ASSUM (SUBST_ALL_TAC o SYM) THEN FIELD_TAC,
      MAP_EVERY EXISTS_TAC
       [← q r"ring_div r x d:A", ← q r"ring_div r (ring_neg r y) d:A"] THEN
      FIRST_X_ASSUM (SUBST_ALL_TAC o SYM) THEN
      REPEAT CONJ_TAC THEN TRY RING_CARRIER_TAC THEN
      FIRST_X_ASSUM (fun th => tactic_of do
        let _ ← SPEC (← q r"x:A") th; pure ALL_TAC) THEN FIELD_TAC]))

  let sqintmod_field ← new_definition
   r"sqintmod_field = quadratic_extension (integer_mod_ring p_25519) 2"

  let FIELD_SQINTMOD_FIELD ← prove
   r"field sqintmod_field"
   (← do
    let t1 ← TAUT (← q r"p ==> ~q <=> ~(p /\ q)")
    pure (REWRITE_TAC [sqintmod_field] THEN MATCH_MP_TAC FIELD_QUADRATIC_EXTENSION THEN
    REWRITE_TAC [t1, ← GSYM NOT_EXISTS_THM] THEN
    REWRITE_TAC [INTEGER_MOD_RING_ROOT_EXISTS] THEN
    REWRITE_TAC [← liftExcept (el 9 (CONJUNCTS INTEGER_MOD_RING_CLAUSES))] THEN
    REWRITE_TAC [INT_OF_NUM_REM, INTEGER_MOD_RING_ROOT_EXISTS] THEN
    SIMP_TAC [FIELD_INTEGER_MOD_RING, PRIME_P25519, EULER_CRITERION] THEN
    DISCH_THEN (MP_TAC o CONJUNCT2) THEN
    SIMP_TAC [p_25519, MOD_LT, ARITH_LE, ARITH_LT] THEN
    CONV_TAC (DEPTH_CONV
     (NUM_SUB_CONV ORELSEC NUM_DIV_CONV ORELSEC DIVIDES_CONV)) THEN
    REWRITE_TAC [CONG] THEN CONV_TAC (ONCE_DEPTH_CONV EXP_MOD_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV))

  let RING_CHAR_SQINTMOD_FIELD ← prove
   r"ring_char sqintmod_field = p_25519"
   (← do
    pure (REWRITE_TAC [sqintmod_field, RING_CHAR_QUADRATIC_EXTENSION] THEN
    REWRITE_TAC [INTEGER_MOD_RING_CHAR]))

  let SQUARE_ROOTS_SQINTMOD_FIELD ← prove
   r"!n. ?x. x IN ring_carrier sqintmod_field /\
           ring_pow sqintmod_field x 2 = ring_of_num sqintmod_field n"
   (← do
    -- `let lemma = prove ... in` first (with its TAUT); then the main
    -- tactic, right to left: NUMBER_RULE, the INT_ARITHs, MESON, TAUT
    let lemma ← prove
     r"!a. ?x. (x EXP 2 == a) (mod p_25519) \/ (x EXP 2 == 2 * a) (mod p_25519)"
     (← do
      let t1 ← TAUT (← q r"(q ==> q') ==> p \/ q ==> p \/ r \/ q'")
      pure (SIMP_TAC [EXISTS_OR_THM, EULER_CRITERION,
                      PRIME_P25519, PRIME_DIVPROD_EQ] THEN
      GEN_TAC THEN
      MP_TAC (← SPECL [← q r"p_25519", ← q r"1", ← q r"a EXP ((p_25519 - 1) DIV 2)"]
        CONG_SQUARE_1_PRIME_POWER) THEN
      MP_TAC (← ONCE_REWRITE_RULE [COPRIME_SYM]
       (← SPECL [← q r"a:num", ← q r"p_25519"] FERMAT_LITTLE_PRIME)) THEN
      MP_TAC (← SPECL [← q r"p_25519", ← q r"a:num"] PRIME_COPRIME_EQ) THEN
      REWRITE_TAC [PRIME_P25519] THEN
      ASM_CASES_TAC (← q r"p_25519 divides a") THEN ASM_REWRITE_TAC [] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC [EXP_1, EXP_EXP] THEN DISCH_TAC THEN
      ANTS_TAC THENL [REWRITE_TAC [p_25519, ARITH_EQ], ALL_TAC] THEN
      SUBGOAL_THEN (← q r"(p_25519 - 1) DIV 2 * 2 = p_25519 - 1") SUBST1_TAC THENL
       [REWRITE_TAC [p_25519] THEN ARITH_TAC, ASM_REWRITE_TAC []] THEN
      MATCH_MP_TAC t1 THEN
      REWRITE_TAC [MULT_EXP, CONG] THEN ONCE_REWRITE_TAC [← GSYM MOD_MULT_MOD2] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [p_25519] THEN
      CONV_TAC (DEPTH_CONV
       (NUM_SUB_CONV ORELSEC NUM_DIV_CONV ORELSEC DIVIDES_CONV)) THEN
      CONV_TAC (ONCE_DEPTH_CONV EXP_MOD_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV))
    let n323 ← ExceptT.mk (NUMBER_RULE
     (← q r"(m EXP 2 == t * n) (mod p) /\ (t * i == 1) (mod p)
      ==> (t * (m * i) EXP 2 == n) (mod p)"))
    let i314 ← INT_ARITH (← q r"&p:int = &0 \/ &0:int < &p")
    let i313 ← INT_ARITH (← q r"~(&p:int < &0)")
    let m310 ← MESON []
     (← q r"!p. (?x y. P (&x rem p) (&y rem p)) ==> (?x y. P x y)")
    let t305 ← TAUT (← q r"p /\ q <=> ~(p ==> ~q)")
    pure (GEN_TAC THEN ONCE_REWRITE_TAC [t305] THEN
    SIMP_TAC [RING_POW_2] THEN REWRITE_TAC [NOT_IMP] THEN
    REWRITE_TAC [sqintmod_field, QUADRATIC_EXTENSION] THEN
    REWRITE_TAC [RING_OF_NUM_QUADRATIC_EXTENSION, EXISTS_PAIR_THM, IN_CROSS] THEN
    REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER, INTEGER_MOD_RING_CLAUSES] THEN
    MATCH_MP_TAC m310 THEN
    EXISTS_TAC (← q r"&p_25519:int") THEN REWRITE_TAC [INT_LT_REM_EQ, PAIR_EQ] THEN
    SIMP_TAC [i313, INT_POS, INT_REM_POS_EQ] THEN
    REWRITE_TAC [i314] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN
    REWRITE_TAC [INT_OF_NUM_CLAUSES, INT_OF_NUM_REM] THEN
    MP_TAC (← SPEC (← q r"n:num") lemma) THEN
    DISCH_THEN (X_CHOOSE_THEN (← q r"m:num") STRIP_ASSUME_TAC) THENL
     [MAP_EVERY EXISTS_TAC [← q r"m:num", ← q r"0"],
      MAP_EVERY EXISTS_TAC [← q r"0", ← q r"m * inverse_mod p_25519 2"]] THEN
    REWRITE_TAC [ADD_CLAUSES, MULT_CLAUSES, MOD_0] THEN
    ASM_REWRITE_TAC [← GSYM EXP_2, ← GSYM CONG] THEN
    MATCH_MP_TAC n323 THEN
    ASM_REWRITE_TAC [INVERSE_MOD_RMUL_EQ] THEN
    REWRITE_TAC [p_25519] THEN CONV_TAC COPRIME_CONV))

  -- @@RETURN BEGIN
  return { quadratic_extension, QUADRATIC_EXTENSION,
           RING_HOMOMORPHISM_INTO_QUADRATIC_EXTENSION,
           RING_MONOMORPHISM_INTO_QUADRATIC_EXTENSION, RING_OF_NUM_QUADRATIC_EXTENSION,
           RING_OF_INT_QUADRATIC_EXTENSION, RING_CHAR_QUADRATIC_EXTENSION,
           FIELD_QUADRATIC_EXTENSION, sqintmod_field, FIELD_SQINTMOD_FIELD,
           RING_CHAR_SQINTMOD_FIELD, SQUARE_ROOTS_SQINTMOD_FIELD }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- An explicitly computational definition of the pure x25519 function as     -/
/- "purex25519_def" and then an equivalent "purex25519" corresponding to the -/
/- way Bernstein defines it in https://cr.yp.to/ecdh/curve25519-20060209.pdf -/
/- Theorem 2.1. The "pure" means it does not prenormalize n and q, although  -/
/- it does automatically/implicitly reduce the q input modulo p_25519.       -/
/- (x25519.ml 359-597)                                                       -/
/- ------------------------------------------------------------------------- -/

structure X25519Pure where
  -- @@FIELDS
  x25519_ladderstep : thm
  x25519_ladder : thm
  purex25519_def : thm
  PUREX25519_LADDER : thm
  PUREX25519_BOUND : thm
  PUREX25519 : thm
  PUREX25519_UNIQUE : thm
  purex25519 : thm
  PUREX25519_MOD : thm
  PUREX25519_UNIQUE_IMP : thm
  deriving Inhabited

@[nospecialize]
def setupX25519Pure [HolBase] (D : X25519Deps) (BX25519Curve : X25519Curve) (BX25519Quadratic : X25519Quadratic) :
    ExceptT String IO X25519Pure := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_MESON_TAC, INT_REM_DOWN_CONV, LET_TAC, MESON_TAC,
        NUM_REDUCE_CONV, TAUT, define, let_CONV, .. } := D
  let { ADD_CLAUSES, ARITH_EQ, CONG, DIVIDES_MOD, EQ_IMP, EXISTS_OPTION_THM,
        EXISTS_PAIR_THM, FIELD_NONTRIVIAL, FORALL_OPTION_THM, FORALL_PAIR_THM,
        GROUP_POW_1, GROUP_POW_ID, IMP_CONJ, IN, INTEGER_MOD_RING_CLAUSES,
        INT_CONG_LMUL, INT_CONG_REFL, INT_CONG_RREM, INT_CONG_TRANS,
        INT_OF_NUM_CLAUSES, INT_OF_NUM_EQ, INT_OF_NUM_OF_INT, INT_REM_EQ, INT_REM_EQ_0,
        INT_REM_POS_EQ, INT_REM_REM, INVERSE_MOD_LMUL_EQ, MOD_LT, MOD_LT_EQ_LT,
        MONTGOMERY_XZDIFFADD_GROUP, MONTGOMERY_XZDOUBLE_GROUP, NOT_IMP, PAIR_EQ,
        PRIME_COPRIME_EQ, PRIME_P25519, RIGHT_FORALL_IMP_THM, RING_1, RING_DIV_1,
        RING_LINV_UNIQUE, RING_MUL_LID, RING_OF_INT, RING_OF_INT_CLAUSES,
        RING_OF_INT_EQ, RING_OF_INT_EQ_0, RING_OF_INT_OF_NUM, RING_OF_INT_REM,
        RING_OF_NUM, RING_OF_NUM_0, RING_OF_NUM_1, RING_OF_NUM_EQ, RING_OF_NUM_EQ_0,
        RING_OF_NUM_MOD, RING_OF_NUM_MUL, RING_POW, SELECT_UNIQUE, curve25519,
        group_pow, montgomery_curve, montgomery_xmap, montgomery_xz,
        montgomery_xzdiffadd, montgomery_xzdouble, num_WF, num_congruent, num_divides,
        p_25519, ring_div, .. } := D.core1
  let { CURVE25519X_GROUP, GROUP_POW_CURVE25519X_TORSION,
        MONTGOMERY_NONSINGULAR_CURVE25519X, SPECIALLY_NONSINGULAR_CURVE25519X,
        curve25519x, curve25519x_group, .. } := BX25519Curve
  let { FIELD_SQINTMOD_FIELD, RING_CHAR_SQINTMOD_FIELD, SQUARE_ROOTS_SQINTMOD_FIELD, .. } := BX25519Quadratic
  -- @@SCOPE END

  let x25519_ladderstep ← define
   r"x25519_ladderstep b P (P0,P1) =
        if b then (montgomery_xzdiffadd curve25519 P P1 P0,
                   montgomery_xzdouble curve25519 P1)
        else (montgomery_xzdouble curve25519 P0,
              montgomery_xzdiffadd curve25519 P P1 P0)"

  let x25519_ladder ← define
   r"x25519_ladder n P =
    if n = 0 then ((&1,&0),P)
    else x25519_ladderstep (n MOD 2 = 1) P (x25519_ladder (n DIV 2) P)"

  let purex25519_def ← define
   r"purex25519(n,q) =
        if q MOD p_25519 = 0 then 0 else
        let (X,Z) = FST(x25519_ladder n (&q,&1)) in
        let x = num_of_int(X rem &p_25519)
        and z = num_of_int(Z rem &p_25519) in
        if z = 0 then 0 else
        (x * inverse_mod p_25519 z) MOD p_25519"

  let PUREX25519_LADDER ← prove
   r"!(f:A ring) x y n.
        field f /\ ring_char f = p_25519 /\
        SOME(ring_of_num f x,y) IN group_carrier (curve25519x_group f) /\
        ~(ring_of_num f x = ring_0 f)
        ==> let (X,Z),(X',Z') = x25519_ladder n (&x,&1) in
            montgomery_xz f (group_pow (curve25519x_group f)
                                       (SOME(ring_of_num f x,y)) n)
                            (ring_of_int f X,ring_of_int f Z) /\
            montgomery_xz f (group_pow (curve25519x_group f)
                                       (SOME(ring_of_num f x,y)) (n+1))
                            (ring_of_int f X',ring_of_int f Z')"
   (← do
    -- right to left: the ARITH_RULEs from the last
    let a412 ← ARITH_RULE (← q r"2 * (m + 1) = (2 * m + 1) + 1")
    let a399 ← ARITH_RULE (← q r"n MOD 2 = b ==> b = 1 \/ b = 0")
    let a381 ← ARITH_RULE (← q r"n DIV 2 < n <=> ~(n = 0)")
    pure (REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC num_WF THEN X_GEN_TAC (← q r"n:num") THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC [x25519_ladder] THEN COND_CASES_TAC THENL
     [ASM_SIMP_TAC [group_pow, GROUP_POW_1, ADD_CLAUSES] THEN
      ASM_SIMP_TAC [CURVE25519X_GROUP] THEN
      CONV_TAC let_CONV THEN REWRITE_TAC [montgomery_xz] THEN
      REWRITE_TAC [RING_OF_INT] THEN
      REWRITE_TAC [← GSYM RING_OF_INT_CLAUSES] THEN
      ASM_SIMP_TAC [FIELD_NONTRIVIAL, RING_DIV_1, RING_OF_INT] THEN
      REWRITE_TAC [RING_OF_INT_OF_NUM],
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"n DIV 2"))] THEN
    ASM_REWRITE_TAC [a381] THEN
    ABBREV_TAC (← q r"P = x25519_ladder (n DIV 2) (&x,&1)") THEN POP_ASSUM MP_TAC THEN
    SPEC_TAC (← q r"P:(int#int)#(int#int)", ← q r"P:(int#int)#(int#int)") THEN
    REWRITE_TAC [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"Xn:int", ← q r"Zn:int", ← q r"Xm:int", ← q r"Zm:int"] THEN
    DISCH_THEN SUBST1_TAC THEN
    CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV let_CONV)) THEN
    ABBREV_TAC (← q r"m = n DIV 2") THEN
    ABBREV_TAC (← q r"b = n MOD 2") THEN
    SUBGOAL_THEN (← q r"n = 2 * m + b") SUBST_ALL_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m", "b"] THEN ARITH_TAC, STRIP_TAC] THEN
      SUBGOAL_THEN
     (← q r"montgomery_xz (f:A ring)
                    (SOME (ring_of_num f x,y)) (ring_of_num f x,ring_1 f)")
    ASSUME_TAC THENL
     [REWRITE_TAC [montgomery_xz] THEN
      ASM_SIMP_TAC [RING_DIV_1, RING_OF_NUM, RING_1, FIELD_NONTRIVIAL],
      ALL_TAC] THEN
    FIRST_X_ASSUM (DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP a399) THEN
    REWRITE_TAC [ARITH_EQ, x25519_ladderstep] THEN LET_TAC THEN CONJ_TAC THENL
     [MP_TAC (← ISPECL [← q r"f:A ring", ← q r"ring_of_num f A_25519:A", ← q r"ring_of_num f 1:A",
                        ← q r"SOME(ring_of_num f x,y):(A#A)option", ← q r"m:num",
                        ← q r"(ring_of_num f x:A,ring_1 f)",
                        ← q r"ring_of_int f Xm:A,ring_of_int f Zm",
                        ← q r"ring_of_int f Xn:A,ring_of_int f Zn"]
          MONTGOMERY_XZDIFFADD_GROUP),
      MP_TAC (← ISPECL [← q r"f:A ring", ← q r"ring_of_num f A_25519:A", ← q r"ring_of_num f 1:A",
                        ← q r"SOME(ring_of_num f x,y):(A#A)option", ← q r"m + 1",
                        ← q r"ring_of_int f Xm:A,ring_of_int f Zm"]
          MONTGOMERY_XZDOUBLE_GROUP) THEN
      REWRITE_TAC [a412],
      MP_TAC (← ISPECL [← q r"f:A ring", ← q r"ring_of_num f A_25519:A", ← q r"ring_of_num f 1:A",
                        ← q r"SOME(ring_of_num f x,y):(A#A)option", ← q r"m:num",
                        ← q r"ring_of_int f Xn:A,ring_of_int f Zn"]
          MONTGOMERY_XZDOUBLE_GROUP) THEN
      REWRITE_TAC [ADD_CLAUSES],
      MP_TAC (← ISPECL [← q r"f:A ring", ← q r"ring_of_num f A_25519:A", ← q r"ring_of_num f 1:A",
                        ← q r"SOME(ring_of_num f x,y):(A#A)option", ← q r"m:num",
                        ← q r"(ring_of_num f x:A,ring_1 f)",
                        ← q r"ring_of_int f Xm:A,ring_of_int f Zm",
                        ← q r"ring_of_int f Xn:A,ring_of_int f Zn"]
          MONTGOMERY_XZDIFFADD_GROUP) THEN
      REWRITE_TAC [ADD_CLAUSES]] THEN
    ASM_REWRITE_TAC [← GSYM curve25519x, ← GSYM curve25519x_group] THEN
    ASM_SIMP_TAC [MONTGOMERY_NONSINGULAR_CURVE25519X] THEN
    REWRITE_TAC [p_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC [RING_OF_NUM, FIELD_NONTRIVIAL] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [PAIR_EQ]) THEN
    REWRITE_TAC [montgomery_xzdiffadd, montgomery_xzdouble,
                 curve25519, curve25519x] THEN
    REWRITE_TAC [PAIR_EQ, ← GSYM curve25519, curve25519x] THEN
    DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC [RING_OF_INT_CLAUSES, ← GSYM RING_OF_INT_OF_NUM] THEN
    REWRITE_TAC [INTEGER_MOD_RING_CLAUSES, RING_OF_INT_EQ] THEN
    ASM_REWRITE_TAC [← GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    ASM_REWRITE_TAC []))

  let PUREX25519_BOUND ← prove
   r"!n q. purex25519(n,q) < p_25519"
   (← do
    pure (REPEAT GEN_TAC THEN REWRITE_TAC [purex25519_def] THEN LET_TAC THEN
    CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC []) THEN
    ASM_REWRITE_TAC [MOD_LT_EQ_LT, p_25519] THEN
    CONV_TAC NUM_REDUCE_CONV))

  let PUREX25519 ← prove
   r"!(f:A ring) n q Q.
        field f /\ ring_char f = p_25519 /\
        Q IN group_carrier(curve25519x_group f) /\
        montgomery_xmap f Q = ring_of_num f q
        ==> montgomery_xmap f (group_pow (curve25519x_group f) Q n) =
            ring_of_num f (purex25519(n,q))"
   (← do
    pure (MAP_EVERY X_GEN_TAC [← q r"f:A ring", ← q r"n:num", ← q r"q:num"] THEN
    REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN CONJ_TAC THENL
     [SIMP_TAC [← GSYM CURVE25519X_GROUP, GROUP_POW_ID, IMP_CONJ] THEN
      SIMP_TAC [CURVE25519X_GROUP, purex25519_def, montgomery_xmap] THEN
      REPLICATE_TAC 3 DISCH_TAC THEN DISCH_THEN (MP_TAC o SYM) THEN
      ASM_SIMP_TAC [RING_OF_NUM_EQ_0, DIVIDES_MOD, RING_OF_NUM_0],
      MAP_EVERY X_GEN_TAC [← q r"x:A", ← q r"y:A"]] THEN
    ASM_CASES_TAC (← q r"ring_of_num f q:A = ring_0 f") THENL
     [ASM_REWRITE_TAC [montgomery_xmap] THEN STRIP_TAC THEN
      UNDISCH_THEN (← q r"x:A = ring_0 f") SUBST_ALL_TAC THEN
      MP_TAC (← ISPECL [← q r"f:A ring", ← q r"0", ← q r"y:A"]
         SPECIALLY_NONSINGULAR_CURVE25519X) THEN
      ASM_REWRITE_TAC [RING_OF_NUM_0] THEN
      ANTS_TAC THENL [ASM_MESON_TAC [CURVE25519X_GROUP, IN], ALL_TAC] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      MP_TAC (← ISPECL [← q r"f:A ring", ← q r"n:num"]
          GROUP_POW_CURVE25519X_TORSION) THEN
      ASM_REWRITE_TAC [] THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [RING_OF_NUM_EQ_0]) THEN
      ASM_SIMP_TAC [DIVIDES_MOD, purex25519_def, RING_OF_NUM_0] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC [montgomery_xmap],
      STRIP_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE LAND_CONV [montgomery_xmap]) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE RAND_CONV [RING_OF_NUM_EQ_0]) THEN
    ASM_SIMP_TAC [DIVIDES_MOD, purex25519_def, RING_OF_NUM_0] THEN
    DISCH_TAC THEN
    MP_TAC (← ISPECL [← q r"f:A ring", ← q r"q:num", ← q r"y:A", ← q r"n:num"]
          PUREX25519_LADDER) THEN
    ASM_REWRITE_TAC [RING_OF_NUM_EQ_0, DIVIDES_MOD, RING_OF_NUM_0] THEN
    ABBREV_TAC (← q r"P = x25519_ladder n (&q,&1)") THEN POP_ASSUM MP_TAC THEN
    SPEC_TAC (← q r"P:(int#int)#(int#int)", ← q r"P:(int#int)#(int#int)") THEN
    REWRITE_TAC [FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [← q r"Xn:int", ← q r"Zn:int", ← q r"Xm:int", ← q r"Zm:int"] THEN
    DISCH_THEN SUBST1_TAC THEN CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN
    DISCH_THEN (MP_TAC o CONJUNCT1) THEN
    SPEC_TAC (← q r"group_pow (curve25519x_group f) (SOME (ring_of_num f q,y:A)) n",
              ← q r"Q:(A#A)option") THEN
    REWRITE_TAC [FORALL_OPTION_THM, FORALL_PAIR_THM] THEN
    REWRITE_TAC [montgomery_xz, montgomery_xmap] THEN
    SUBGOAL_THEN
     (← q r"&(num_of_int(Xn rem &p_25519)) = Xn rem &p_25519 /\
      &(num_of_int(Zn rem &p_25519)) = Zn rem &p_25519")
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
      REWRITE_TAC [INT_REM_POS_EQ, p_25519, INT_OF_NUM_EQ, ARITH_EQ],
      ALL_TAC] THEN
    ASM_REWRITE_TAC [← GSYM INT_OF_NUM_EQ] THEN
    ASM_SIMP_TAC [RING_OF_INT_EQ_0, ← GSYM INT_REM_EQ_0, RING_OF_NUM_0] THEN
    GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    MP_TAC (← ISPEC (← q r"f:A ring") RING_OF_NUM_MOD) THEN ASM_SIMP_TAC [] THEN
    DISCH_THEN (K ALL_TAC : thm → tactic) THEN REWRITE_TAC [ring_div, RING_OF_NUM_MUL] THEN
    ASM_REWRITE_TAC [← GSYM RING_OF_INT_OF_NUM] THEN
    MP_TAC (← ISPEC (← q r"f:A ring") RING_OF_INT_REM) THEN ASM_SIMP_TAC [] THEN
    DISCH_THEN (K ALL_TAC : thm → tactic) THEN AP_TERM_TAC THEN
    MATCH_MP_TAC RING_LINV_UNIQUE THEN
    REWRITE_TAC [← GSYM RING_OF_INT_OF_NUM, RING_OF_INT] THEN
    ASM_REWRITE_TAC [RING_OF_INT_CLAUSES, RING_OF_INT_EQ] THEN
    MATCH_MP_TAC INT_CONG_TRANS THEN
    EXISTS_TAC
     (← q r"&(inverse_mod p_25519 (num_of_int (Zn rem &p_25519))) *
      &(num_of_int (Zn rem &p_25519)):int") THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INT_CONG_LMUL THEN
      ASM_REWRITE_TAC [INT_CONG_RREM, INT_CONG_REFL],
      REWRITE_TAC [INT_OF_NUM_CLAUSES, ← GSYM num_congruent] THEN
      REWRITE_TAC [INVERSE_MOD_LMUL_EQ]] THEN
    SIMP_TAC [PRIME_COPRIME_EQ, PRIME_P25519] THEN
    ASM_REWRITE_TAC [num_divides, ← GSYM INT_REM_EQ_0, INT_REM_REM]))

  let PUREX25519_UNIQUE ← prove
   r"!n q s. purex25519(n,q) = s <=>
           s < p_25519 /\
           !Q. Q IN group_carrier(curve25519x_group sqintmod_field) /\
               montgomery_xmap sqintmod_field Q =
               ring_of_num sqintmod_field q
               ==> montgomery_xmap sqintmod_field
                     (group_pow (curve25519x_group sqintmod_field) Q n) =
                   ring_of_num sqintmod_field s"
   (← do
    let t2 ← TAUT (← q r"p /\ q <=> ~(p ==> ~q)")
    pure (REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN (SUBST1_TAC o SYM) THEN REWRITE_TAC [PUREX25519_BOUND] THEN
      SIMP_TAC [PUREX25519, FIELD_SQINTMOD_FIELD, RING_CHAR_SQINTMOD_FIELD],
      STRIP_TAC] THEN
    SUBGOAL_THEN
     (← q r"ring_of_num sqintmod_field s =
      ring_of_num sqintmod_field (purex25519(n,q))")
    MP_TAC THENL
     [ALL_TAC,
      ASM_SIMP_TAC [RING_OF_NUM_EQ, PUREX25519_BOUND, MOD_LT, CONG,
                    RING_CHAR_SQINTMOD_FIELD]] THEN
    SUBGOAL_THEN
     (← q r"?Q. Q IN group_carrier (curve25519x_group sqintmod_field) /\
          montgomery_xmap sqintmod_field Q = ring_of_num sqintmod_field q")
    STRIP_ASSUME_TAC THENL
     [ALL_TAC,
      FIRST_X_ASSUM (MP_TAC o SPEC (← q r"Q:((int#int)#(int#int))option")) THEN
      MP_TAC (← ISPECL [← q r"sqintmod_field", ← q r"n:num", ← q r"q:num",
                        ← q r"Q:((int#int)#(int#int))option"] PUREX25519) THEN
      ASM_SIMP_TAC [FIELD_SQINTMOD_FIELD, RING_CHAR_SQINTMOD_FIELD]] THEN
    ASM_SIMP_TAC [FIELD_SQINTMOD_FIELD, RING_CHAR_SQINTMOD_FIELD,
                  CURVE25519X_GROUP] THEN
    REWRITE_TAC [IN] THEN REWRITE_TAC [EXISTS_OPTION_THM] THEN
    REWRITE_TAC [montgomery_curve, curve25519x] THEN
    ASM_CASES_TAC (← q r"ring_of_num sqintmod_field q = ring_0 sqintmod_field") THEN
    ASM_REWRITE_TAC [montgomery_xmap] THEN ONCE_REWRITE_TAC [EXISTS_PAIR_THM] THEN
    REWRITE_TAC [montgomery_curve] THEN
    EXISTS_TAC (← q r"ring_of_num sqintmod_field q") THEN
    ASM_REWRITE_TAC [montgomery_xmap, RING_OF_NUM] THEN
    ONCE_REWRITE_TAC [t2] THEN
    SIMP_TAC [RING_OF_NUM_1, RING_MUL_LID, RING_POW] THEN
    REWRITE_TAC [NOT_IMP, ← GSYM RING_OF_INT_OF_NUM] THEN
    REWRITE_TAC [RING_OF_INT_CLAUSES] THEN
    REWRITE_TAC [INT_OF_NUM_CLAUSES, RING_OF_INT_OF_NUM] THEN
    REWRITE_TAC [SQUARE_ROOTS_SQINTMOD_FIELD]))

  let purex25519 ← prove
   r"!n q. purex25519(n,q) =
         @s. s < p_25519 /\
             !Q. Q IN group_carrier(curve25519x_group sqintmod_field) /\
                 montgomery_xmap sqintmod_field Q =
                 ring_of_num sqintmod_field q
                 ==> montgomery_xmap sqintmod_field
                       (group_pow (curve25519x_group sqintmod_field) Q n) =
                     ring_of_num sqintmod_field s"
   (← do
    pure (REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN
    REWRITE_TAC [← GSYM PUREX25519_UNIQUE] THEN MESON_TAC []))

  let PUREX25519_MOD ← prove
   r"!n q. purex25519(n,q MOD p_25519) = purex25519(n,q)"
   (← do
    pure (REWRITE_TAC [purex25519, ← GSYM RING_CHAR_SQINTMOD_FIELD, RING_OF_NUM_MOD]))

  let PUREX25519_UNIQUE_IMP ← prove
   r"!n q s. s < p_25519 /\
           (!(f:(int#int)ring) Q.
                field f /\ ring_char f = p_25519 /\
                Q IN group_carrier(curve25519x_group f) /\
                montgomery_xmap f Q = ring_of_num f q
                ==> montgomery_xmap f (group_pow (curve25519x_group f) Q n) =
                    ring_of_num f s)
           ==> purex25519(n,q) = s"
   (← do
    pure (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [PUREX25519_UNIQUE] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [FIELD_SQINTMOD_FIELD, RING_CHAR_SQINTMOD_FIELD]))

  -- @@RETURN BEGIN
  return { x25519_ladderstep, x25519_ladder, purex25519_def, PUREX25519_LADDER,
           PUREX25519_BOUND, PUREX25519, PUREX25519_UNIQUE, purex25519, PUREX25519_MOD,
           PUREX25519_UNIQUE_IMP }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- The final version "rfcx25519" includes the prenormalization of n and q    -/
/- as in https://www.rfc-editor.org/rfc/rfc7748. Note that this includes     -/
/- an explicit masking of q to 255 bits *before* reduction modulo p_25519,   -/
/- so in that respect is slightly different from Bernstein's original paper  -/
/- which just reduces any q < 2^256 modulo p_25519.  Then the overall        -/
/- function is never zero on the standard basepoint X = 9.                   -/
/- (x25519.ml 598-673)                                                       -/
/- ------------------------------------------------------------------------- -/

structure X25519Rfc where
  -- @@FIELDS
  rfcx25519 : thm
  RFCX25519_PUREX25519 : thm
  RFCX25519_BASE_NONZERO : thm
  deriving Inhabited

@[nospecialize]
def setupX25519Rfc [HolBase] (D : X25519Deps) (BX25519Curve : X25519Curve) (BX25519Pure : X25519Pure) :
    ExceptT String IO X25519Rfc := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, COPRIME_CONV, ECGROUP_POW_CONV,
        INT_REDUCE_CONV, NUMBER_RULE, NUM_REDUCE_CONV, define, .. } := D
  let { A_25519, CURVE25519_GROUP, C_25519, DIVIDES_LE, FIELD_INTEGER_MOD_RING,
        FORALL_IN_GSPEC, GENERATOR_IN_GROUP_CARRIER_CURVE25519,
        GROUP_ELEMENT_ORDER_CURVE25519_C25519, GROUP_POW, GROUP_POW_EQ_ID,
        GROUP_POW_MUL, IMP_CONJ, INTEGER_MOD_RING_CHAR, INTEGER_MOD_RING_CLAUSES,
        INT_OF_NUM_CLAUSES, IN_INTEGER_MOD_RING_CARRIER, MOD_LT, MOD_MOD_EXP_MIN,
        MOD_MULT_ADD, MONTGOMERY_NONSINGULAR_CURVE25519, MONTGOMERY_XMAP_EQ_0,
        PRIME_P25519, RIGHT_FORALL_IMP_THM, RING_OF_NUM_0, SUB_0, curve25519,
        curve25519_group, montgomery_xmap, n_25519, p_25519, .. } := D.core1
  let { CURVE25519X_CURVE25519_GROUP, .. } := BX25519Curve
  let { PUREX25519, .. } := BX25519Pure
  -- @@SCOPE END

  let rfcx25519 ← define
   r"rfcx25519(n,q) =
    purex25519(2 EXP 254 + (n MOD 2 EXP 254 - n MOD 8),
               q MOD 2 EXP 255)"

  let RFCX25519_PUREX25519 ← prove
   r"!n q. n IN {2 EXP 254 + 8 * i | i < 2 EXP 251} /\ q < 2 EXP 255
         ==> rfcx25519(n,q) = purex25519(n,q)"
   (← do
    let a1 ← ARITH_RULE (← q r"a + 8 * i = 1 * a + 8 * i")
    pure (REWRITE_TAC [IMP_CONJ, RIGHT_FORALL_IMP_THM, FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC [rfcx25519] THEN
    AP_TERM_TAC THEN BINOP_TAC THEN ASM_SIMP_TAC [MOD_LT] THEN
    ONCE_REWRITE_TAC [a1] THEN
    REWRITE_TAC [MOD_MULT_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC [SUB_0] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC))

  /- The overall function is never zero on the standard basepoint X = 9. -/

  let RFCX25519_BASE_NONZERO ← prove
   r"!n. ~(rfcx25519(n,9) = 0)"
   (← do
    -- right to left: the NUMBER_RULE, then the ARITH_RULEs from the last
    let n3 ← ExceptT.mk (NUMBER_RULE
     (← q r"p divides (d * n) * e ==> coprime(p:num,d * e) ==> p divides n"))
    let a2 ← ARITH_RULE
     (← q r"2 EXP 254 + n - n MOD 2 EXP 3 = 8 * (2 EXP 251 + n DIV 8)")
    let a1 ← ARITH_RULE (← q r"n MOD 2 EXP 254 < 2 EXP 254")
    pure (GEN_TAC THEN REWRITE_TAC [rfcx25519] THEN
    SUBGOAL_THEN (← q r"n MOD 8 = n MOD 2 EXP 254 MOD 2 EXP 3") SUBST1_TAC THENL
     [REWRITE_TAC [MOD_MOD_EXP_MIN] THEN ARITH_TAC, ALL_TAC] THEN
    MP_TAC a1 THEN
    SPEC_TAC (← q r"n MOD 2 EXP 254", ← q r"n:num") THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [a2] THEN
    ABBREV_TAC (← q r"m = 8 * (2 EXP 251 + n DIV 8)") THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
    SUBGOAL_THEN
     (← q r"group_pow curve25519_group C_25519 (m * 2) = group_id curve25519_group")
    MP_TAC THENL
     [SIMP_TAC [GROUP_POW_MUL, GENERATOR_IN_GROUP_CARRIER_CURVE25519],
      SIMP_TAC [GROUP_POW_EQ_ID, GENERATOR_IN_GROUP_CARRIER_CURVE25519] THEN
      REWRITE_TAC [GROUP_ELEMENT_ORDER_CURVE25519_C25519] THEN
      EXPAND_TAC "m" THEN DISCH_THEN (MP_TAC o MATCH_MP n3) THEN
      REWRITE_TAC [n_25519] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (ONCE_DEPTH_CONV COPRIME_CONV) THEN
      REWRITE_TAC [] THEN DISCH_THEN (MP_TAC o MATCH_MP DIVIDES_LE) THEN
      ASM_ARITH_TAC] THEN
    MP_TAC (← ISPECL
     [← q r"integer_mod_ring p_25519", ← q r"&A_25519:int", ← q r"&1:int",
      ← q r"group_pow curve25519_group C_25519 m"]
     MONTGOMERY_XMAP_EQ_0) THEN
    MP_TAC (← ISPECL
     [← q r"integer_mod_ring p_25519", ← q r"m:num", ← q r"9", ← q r"C_25519"]
      PUREX25519) THEN
    REWRITE_TAC [CURVE25519X_CURVE25519_GROUP] THEN
    SIMP_TAC [GROUP_POW, GENERATOR_IN_GROUP_CARRIER_CURVE25519] THEN
    REWRITE_TAC [FIELD_INTEGER_MOD_RING, PRIME_P25519] THEN
    ASM_REWRITE_TAC [INTEGER_MOD_RING_CHAR, RING_OF_NUM_0] THEN
    ANTS_TAC THENL
     [REWRITE_TAC [montgomery_xmap, C_25519, INTEGER_MOD_RING_CLAUSES] THEN
      REWRITE_TAC [p_25519] THEN CONV_TAC INT_REDUCE_CONV,
      DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC [← GSYM curve25519_group, GROUP_POW,
              GENERATOR_IN_GROUP_CARRIER_CURVE25519] THEN
    REWRITE_TAC [MONTGOMERY_NONSINGULAR_CURVE25519, ← GSYM curve25519] THEN
    REWRITE_TAC [p_25519, A_25519, INTEGER_MOD_RING_CLAUSES,
                 IN_INTEGER_MOD_RING_CARRIER] THEN
    REWRITE_TAC [← GSYM INT_OF_NUM_CLAUSES] THEN CONV_TAC INT_REDUCE_CONV THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [CURVE25519_GROUP] THEN
    CONV_TAC (LAND_CONV ECGROUP_POW_CONV) THEN REWRITE_TAC []))

  -- @@RETURN BEGIN
  return { rfcx25519, RFCX25519_PUREX25519, RFCX25519_BASE_NONZERO }
  -- @@RETURN END

end HolEC.X25519
