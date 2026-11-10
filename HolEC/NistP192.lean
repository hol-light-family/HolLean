/- ========================================================================= -/
/- The NIST-recommended elliptic curve P-192, aka secp192r1.               -/
/- ========================================================================= -/
/- File: HolEC/NistP192.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/nistp192.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/weierstrass.ml, EC/excluderoots.ml, EC/computegroup.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.NistP192 fills them).

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
import HolEC.ExcludeRoots
import HolEC.ComputeGroup

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolEC.NistP192

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ARITH CARD_BOUND_WEIERSTRASS_CURVE CARD_INTEGER_MOD_RING COPRIME_2
   CYCLIC_GROUP_ALT CYCLIC_IMP_ABELIAN_GROUP FIELD_INTEGER_MOD_RING
   FINITE_INTEGER_MOD_RING FINITE_WEIERSTRASS_CURVE FORALL_OPTION_THM
   FORALL_PAIR_THM GROUP_ADHOC_ORDER_UNIQUE_LEMMA GROUP_ELEMENT_ORDER_PRIME
   GROUP_ELEMENT_ORDER_UNIQUE_PRIME HAS_SIZE IMP_CONJ_ALT IN
   INTEGER_MOD_RING_CHAR INTEGER_MOD_RING_CLAUSES INT_DIVIDES_LE INT_REM_EQ
   INT_REM_LT INT_REM_ZERO IN_ELIM_THM IN_INTEGER_MOD_RING_CARRIER LET_TRANS
   PAIR_EQ SUBGROUP_GENERATED_ELEMENT_ORDER WEIERSTRASS_GROUP num_coprime
   option_DISTINCT option_INJ weierstrass_add weierstrass_curve weierstrass_neg
   weierstrass_nonsingular : thm)
  deriving Inhabited

/-- What nistp192.ml uses from Session besides theorems. -/
structure NistP192Deps where
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
/- The NIST curve parameters, copied from the NIST FIPS 186-4 document       -/
/- (https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.186-4.pdf), primality   -/
/- of the field characteristic and group order, a sanity check on c, and the -/
/- curve group.  (nistp192.ml)                                               -/
/- ------------------------------------------------------------------------- -/

structure NistP192Defs where
  -- @@FIELDS
  p_192 : thm
  n_192 : thm
  SEED_192 : thm
  c_192 : thm
  b_192 : thm
  G_192 : thm
  P_192 : thm
  PRIME_P192 : thm
  PRIME_N192 : thm
  SANITY_CHECK_192 : thm
  p192_group : thm
  P192_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupNistP192Defs [HolBase] (D : NistP192Deps) :
    ExceptT String IO NistP192Defs := do
  -- @@SCOPE BEGIN
  let { INT_REDUCE_CONV, NUM_REDUCE_CONV, PRIME_RULE, add_curve, add_curveadd,
        add_curveneg, add_ecgroup, define, new_definition, .. } := D
  let { ARITH, FIELD_INTEGER_MOD_RING, INTEGER_MOD_RING_CHAR, INTEGER_MOD_RING_CLAUSES,
        INT_REM_EQ, IN_ELIM_THM, WEIERSTRASS_GROUP, weierstrass_add, weierstrass_curve,
        weierstrass_neg, weierstrass_nonsingular, .. } := D.core1
  -- @@SCOPE END

  add_curve weierstrass_curve
  add_curveneg weierstrass_neg
  add_curveadd weierstrass_add

  let p_192 ← new_definition r"p_192 = 6277101735386680763835789423207666416083908700390324961279"
  let n_192 ← new_definition r"n_192 = 6277101735386680763835789423176059013767194773182842284081"
  let SEED_192 ← new_definition r"SEED_192 = 0x3045ae6fc8422f64ed579528d38120eae12196d5"
  let c_192 ← new_definition r"c_192 = 0x3099d2bbbfcb2538542dcd5fb078b6ef5f3d6fe2c745de65"
  let b_192 ← new_definition r"b_192 = 0x64210519e59c80e70fa7e9ab72243049feb8deecc146b9b1"
  let G_192 ← new_definition r"G_192 = SOME(&0x188da80eb03090f67cbf20eb43a18800f4ff0afd82ff1012:int,&0x07192b95ffc8da78631011ed6b24cdd573f977a11e794811:int)"

  /- Primality of the field characteristic and group order. -/

  let P_192 ← prove
   r"p_192 = 2 EXP 192 - 2 EXP 64 - 1"
   (← do
    pure (REWRITE_TAC [p_192] THEN CONV_TAC NUM_REDUCE_CONV))

  -- `time prove (goal, tac)`: the tactic is built before `time` runs
  let PRIME_P192 ← do
    let tac ← do
      pure (REWRITE_TAC [p_192] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (fun t => (PRIME_RULE
       ["2", "3", "5", "7", "11", "17", "19", "23", "29", "31", "37", "41",
        "43", "47", "59", "61", "101", "103", "151", "163", "191", "229",
        "283", "607", "619", "631", "907", "2477", "54251", "149309", "275729",
        "379787", "723127", "8413201", "11393611", "252396031", "455827231987",
        "108341181769254293", "5933177618131140283",
        "288626509448065367648032903"] t).run))
    ExceptT.mk (HolCore.Lib.time (fun (_ : Unit) =>
     (prove r"prime p_192" tac).run) ())

  let PRIME_N192 ← do
    let tac ← do
      pure (REWRITE_TAC [n_192] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (fun t => (PRIME_RULE
       ["2", "3", "5", "7", "11", "13", "17", "23", "29", "31", "43", "47",
        "59", "61", "71", "73", "103", "199", "239", "331", "439", "547",
        "569", "881", "1031", "1693", "1889", "2063", "2389", "4127", "6829",
        "51419", "53197", "54623", "60449", "15716741", "46245989", "51920273",
        "103840547", "7244839476697597", "7532705587894727",
        "9564682313913860059195669", "3433859179316188682119986911"] t).run))
    ExceptT.mk (HolCore.Lib.time (fun (_ : Unit) =>
     (prove r"prime n_192" tac).run) ())

  /- Basic sanity check on the (otherwise unused) c parameter. -/

  let SANITY_CHECK_192 ← prove
   r"(&b_192 pow 2 * &c_192:int == -- &27) (mod &p_192)"
   (← do
    pure (REWRITE_TAC [G_192, p_192, b_192, c_192] THEN
    REWRITE_TAC [← GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV))

  /- Definition of the curve group and proof of its key properties. -/

  let p192_group ← define
   r"p192_group =
   weierstrass_group
    (integer_mod_ring p_192,
     ring_neg (integer_mod_ring p_192) (&3),
     &b_192)"

  let P192_GROUP ← prove
   r"group_carrier p192_group =
     weierstrass_curve
      (integer_mod_ring p_192,ring_neg (integer_mod_ring p_192) (&3),&b_192) /\
   group_id p192_group =
     NONE /\
   group_inv p192_group =
     weierstrass_neg
      (integer_mod_ring p_192,ring_neg (integer_mod_ring p_192) (&3),&b_192) /\
   group_mul p192_group =
     weierstrass_add
      (integer_mod_ring p_192,ring_neg (integer_mod_ring p_192) (&3),&b_192)"
   (← do
    pure (REWRITE_TAC [p192_group] THEN
    MATCH_MP_TAC WEIERSTRASS_GROUP THEN
    REWRITE_TAC [FIELD_INTEGER_MOD_RING, INTEGER_MOD_RING_CHAR, PRIME_P192] THEN
    REWRITE_TAC [p_192, b_192, weierstrass_nonsingular] THEN
    SIMP_TAC [INTEGER_MOD_RING_CLAUSES, ARITH, IN_ELIM_THM] THEN
    CONV_TAC INT_REDUCE_CONV))

  add_ecgroup [p_192, b_192] P192_GROUP

  -- @@RETURN BEGIN
  return { p_192, n_192, SEED_192, c_192, b_192, G_192, P_192, PRIME_P192, PRIME_N192,
           SANITY_CHECK_192, p192_group, P192_GROUP }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- No 2-torsion, the generator and its order, and the group's order and      -/
/- structure.  (nistp192.ml)                                                 -/
/- ------------------------------------------------------------------------- -/

structure NistP192Group where
  -- @@FIELDS
  NO_ROOTS_P192 : thm
  GENERATOR_IN_GROUP_CARRIER_192 : thm
  GROUP_ELEMENT_ORDER_G192 : thm
  FINITE_GROUP_CARRIER_P192 : thm
  SIZE_P192_GROUP : thm
  P192_GROUP_ORDER : thm
  P192_GROUP_ELEMENT_ORDER : thm
  GENERATED_P192_GROUP : thm
  CYCLIC_P192_GROUP : thm
  ABELIAN_P192_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupNistP192Group [HolBase] (D : NistP192Deps) (BNistP192Defs : NistP192Defs) :
    ExceptT String IO NistP192Group := do
  -- @@SCOPE BEGIN
  let { ASM_INT_ARITH_TAC, ECGROUP_CARRIER_CONV, ECGROUP_POW_CONV,
        EXCLUDE_MODULAR_CUBIC_ROOTS_TAC, INTEGER_RULE, INT_ARITH, INT_REDUCE_CONV,
        INT_REM_DOWN_CONV, MESON_TAC, NUM_REDUCE_CONV, .. } := D
  let { ARITH, CARD_BOUND_WEIERSTRASS_CURVE, CARD_INTEGER_MOD_RING, COPRIME_2,
        CYCLIC_GROUP_ALT, CYCLIC_IMP_ABELIAN_GROUP, FIELD_INTEGER_MOD_RING,
        FINITE_INTEGER_MOD_RING, FINITE_WEIERSTRASS_CURVE, FORALL_OPTION_THM,
        FORALL_PAIR_THM, GROUP_ADHOC_ORDER_UNIQUE_LEMMA, GROUP_ELEMENT_ORDER_PRIME,
        GROUP_ELEMENT_ORDER_UNIQUE_PRIME, HAS_SIZE, IMP_CONJ_ALT, IN,
        INTEGER_MOD_RING_CLAUSES, INT_DIVIDES_LE, INT_REM_EQ, INT_REM_LT, INT_REM_ZERO,
        IN_INTEGER_MOD_RING_CARRIER, LET_TRANS, PAIR_EQ,
        SUBGROUP_GENERATED_ELEMENT_ORDER, num_coprime, option_DISTINCT, option_INJ,
        weierstrass_curve, weierstrass_neg, .. } := D.core1
  let { G_192, P192_GROUP, PRIME_N192, PRIME_P192, b_192, n_192, p_192, .. } := BNistP192Defs
  -- @@SCOPE END

  let NO_ROOTS_P192 ← prove
   r"!x:int. ~((x pow 3 - &3 * x + &b_192 == &0) (mod &p_192))"
   (← do
    pure (← EXCLUDE_MODULAR_CUBIC_ROOTS_TAC PRIME_P192 [p_192, b_192]))

  let GENERATOR_IN_GROUP_CARRIER_192 ← prove
   r"G_192 IN group_carrier p192_group"
   (← do
    pure (REWRITE_TAC [G_192] THEN CONV_TAC ECGROUP_CARRIER_CONV))

  let GROUP_ELEMENT_ORDER_G192 ← prove
   r"group_element_order p192_group G_192 = n_192"
   (← do
    pure (SIMP_TAC [GROUP_ELEMENT_ORDER_UNIQUE_PRIME, GENERATOR_IN_GROUP_CARRIER_192,
                    PRIME_N192] THEN
    REWRITE_TAC [G_192, ← liftExcept (el 1 (CONJUNCTS P192_GROUP)), option_DISTINCT] THEN
    REWRITE_TAC [n_192] THEN CONV_TAC (LAND_CONV ECGROUP_POW_CONV) THEN
    REFL_TAC))

  let FINITE_GROUP_CARRIER_P192 ← prove
   r"FINITE(group_carrier p192_group)"
   (← do
    pure (REWRITE_TAC [P192_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
    REWRITE_TAC [FINITE_INTEGER_MOD_RING, FIELD_INTEGER_MOD_RING, PRIME_P192] THEN
    REWRITE_TAC [p_192] THEN CONV_TAC NUM_REDUCE_CONV))

  let SIZE_P192_GROUP ← prove
   r"group_carrier p192_group HAS_SIZE n_192"
   (← do
    -- right to left: the INTEGER_RULEs, then the INT_ARITHs, from the end
    let i4 ← INTEGER_RULE
     (← q r"p divides (a * b:int) ==> coprime(a,p) ==> p divides b")
    let i3 ← INTEGER_RULE
     (← q r"(--y:int == y) (mod p) <=> p divides (&2 * y)")
    let a2 ← INT_ARITH
     (← q r"--y rem p = y ==> y rem p = y ==> (--y rem p = y rem p)")
    let a1 ← INT_ARITH (← q r"y - &3 * x + b:int = y + (-- &3) * x + b")
    pure (MATCH_MP_TAC GROUP_ADHOC_ORDER_UNIQUE_LEMMA THEN
    EXISTS_TAC (← q r"G_192:(int#int)option") THEN
    REWRITE_TAC [GENERATOR_IN_GROUP_CARRIER_192, GROUP_ELEMENT_ORDER_G192,
                 FINITE_GROUP_CARRIER_P192] THEN
    REWRITE_TAC [P192_GROUP] THEN CONJ_TAC THENL
     [wPart lhand (fun t => do lhand (← rand t)) CARD_BOUND_WEIERSTRASS_CURVE THEN
      REWRITE_TAC [FINITE_INTEGER_MOD_RING, FIELD_INTEGER_MOD_RING] THEN
      REWRITE_TAC [PRIME_P192] THEN ANTS_TAC THENL
       [REWRITE_TAC [p_192] THEN CONV_TAC NUM_REDUCE_CONV,
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] LET_TRANS)] THEN
      SIMP_TAC [CARD_INTEGER_MOD_RING, p_192, ARITH] THEN
      REWRITE_TAC [n_192] THEN CONV_TAC NUM_REDUCE_CONV,
      REWRITE_TAC [FORALL_OPTION_THM, IN, FORALL_PAIR_THM] THEN
      REWRITE_TAC [weierstrass_curve, weierstrass_neg, option_DISTINCT] THEN
      MAP_EVERY X_GEN_TAC [← q r"x:int", ← q r"y:int"] THEN REWRITE_TAC [option_INJ] THEN
      REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER, INTEGER_MOD_RING_CLAUSES] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC [p_192, PAIR_EQ] THEN
      CONV_TAC INT_REDUCE_CONV] THEN
    ASM_CASES_TAC (← q r"y:int = &0") THENL
     [ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV THEN
      DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
      CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC (← SPEC (← q r"x:int") NO_ROOTS_P192) THEN
      REWRITE_TAC [a1] THEN
      REWRITE_TAC [← GSYM INT_REM_EQ, p_192, INT_REM_ZERO],
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o MATCH_MP a2) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC [INT_REM_LT], ALL_TAC] THEN
      REWRITE_TAC [INT_REM_EQ, i3] THEN
      DISCH_THEN (MP_TAC o MATCH_MP i4) THEN
      REWRITE_TAC [← GSYM num_coprime, ARITH, COPRIME_2] THEN
      DISCH_THEN (MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]))

  let P192_GROUP_ORDER ← prove
   r"CARD(group_carrier p192_group) = n_192"
   (← do
    pure (REWRITE_TAC [← REWRITE_RULE [HAS_SIZE] SIZE_P192_GROUP]))

  let P192_GROUP_ELEMENT_ORDER ← prove
   r"!P. P IN group_carrier p192_group
       ==> group_element_order p192_group P =
           if P = group_id p192_group then 1 else n_192"
   (← do
    pure (MESON_TAC [SIZE_P192_GROUP, HAS_SIZE, GROUP_ELEMENT_ORDER_PRIME, PRIME_N192]))

  let GENERATED_P192_GROUP ← prove
   r"subgroup_generated p192_group {G_192} = p192_group"
   (← do
    pure (SIMP_TAC [SUBGROUP_GENERATED_ELEMENT_ORDER,
                    GENERATOR_IN_GROUP_CARRIER_192,
                    FINITE_GROUP_CARRIER_P192] THEN
    REWRITE_TAC [GROUP_ELEMENT_ORDER_G192,
                 ← REWRITE_RULE [HAS_SIZE] SIZE_P192_GROUP]))

  let CYCLIC_P192_GROUP ← prove
   r"cyclic_group p192_group"
   (← do
    pure (MESON_TAC [CYCLIC_GROUP_ALT, GENERATED_P192_GROUP]))

  let ABELIAN_P192_GROUP ← prove
   r"abelian_group p192_group"
   (← do
    pure (MESON_TAC [CYCLIC_P192_GROUP, CYCLIC_IMP_ABELIAN_GROUP]))

  -- @@RETURN BEGIN
  return { NO_ROOTS_P192, GENERATOR_IN_GROUP_CARRIER_192, GROUP_ELEMENT_ORDER_G192,
           FINITE_GROUP_CARRIER_P192, SIZE_P192_GROUP, P192_GROUP_ORDER,
           P192_GROUP_ELEMENT_ORDER, GENERATED_P192_GROUP, CYCLIC_P192_GROUP,
           ABELIAN_P192_GROUP }
  -- @@RETURN END

end HolEC.NistP192
