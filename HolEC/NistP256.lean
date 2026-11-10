/- ========================================================================= -/
/- The NIST-recommended elliptic curve P-256, aka secp256r1.               -/
/- ========================================================================= -/
/- File: HolEC/NistP256.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/nistp256.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/weierstrass.ml, EC/excluderoots.ml, EC/computegroup.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.NistP256 fills them).

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

namespace HolEC.NistP256

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

/-- What nistp256.ml uses from Session besides theorems. -/
structure NistP256Deps where
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
/- curve group.  (nistp256.ml 1-101)                                         -/
/- ------------------------------------------------------------------------- -/

structure NistP256Defs where
  -- @@FIELDS
  p_256 : thm
  n_256 : thm
  SEED_256 : thm
  c_256 : thm
  b_256 : thm
  G_256 : thm
  nistp256 : thm
  P_256 : thm
  PRIME_P256 : thm
  PRIME_N256 : thm
  SANITY_CHECK_256 : thm
  p256_group : thm
  P256_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupNistP256Defs [HolBase] (D : NistP256Deps) :
    ExceptT String IO NistP256Defs := do
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

  let p_256 ← new_definition r"p_256 = 115792089210356248762697446949407573530086143415290314195533631308867097853951"
  let n_256 ← new_definition r"n_256 = 115792089210356248762697446949407573529996955224135760342422259061068512044369"
  let SEED_256 ← new_definition r"SEED_256 = 0xc49d360886e704936a6678e1139d26b7819f7e90"
  let c_256 ← new_definition r"c_256 = 0x7efba1662985be9403cb055c75d4f7e0ce8d84a9c5114abcaf3177680104fa0d"
  let b_256 ← new_definition r"b_256 = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b"
  let G_256 ← new_definition r"G_256 = SOME(&0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296:int,&0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5:int)"

  let nistp256 ← define
   r"nistp256 =
    (integer_mod_ring p_256,
     ring_neg (integer_mod_ring p_256) (&3),
     &b_256:int)"

  /- Primality of the field characteristic and group order. -/

  let P_256 ← prove
   r"p_256 = 2 EXP 256 - 2 EXP 224 + 2 EXP 192 + 2 EXP 96 - 1"
   (← do
    pure (REWRITE_TAC [p_256] THEN CONV_TAC NUM_REDUCE_CONV))

  -- `time prove (goal, tac)`: the tactic is built before `time` runs
  let PRIME_P256 ← do
    let tac ← do
      pure (REWRITE_TAC [p_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (fun t => (PRIME_RULE
       ["2", "3", "5", "7", "11", "13", "17", "23", "43", "53", "107", "157",
        "173", "181", "197", "241", "257", "313", "641", "661", "727", "757",
        "919", "1087", "1531", "2411", "3677", "3769", "4349", "17449", "18169",
        "65537", "78283", "490463", "704251", "6700417", "204061199",
        "34282281433", "66417393611", "11290956913871", "46076956964474543",
        "774023187263532362759620327192479577272145303",
        "835945042244614951780389953367877943453916927241"] t).run))
    ExceptT.mk (HolCore.Lib.time (fun (_ : Unit) =>
     (prove r"prime p_256" tac).run) ())

  let PRIME_N256 ← do
    let tac ← do
      pure (REWRITE_TAC [n_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (fun t => (PRIME_RULE
       ["2", "3", "5", "7", "11", "13", "17", "19", "29", "31", "37", "41", "43",
        "71", "97", "127", "131", "151", "229", "263", "311", "337", "373", "727",
        "1201", "1297", "1511", "3023", "3407", "9547", "16879", "17449", "38189",
        "104471", "126241", "155317", "3969899", "9350987", "187019741",
        "191039911", "311245691", "622491383", "1002328039319",
        "208150935158385979", "2624747550333869278416773953"] t).run))
    ExceptT.mk (HolCore.Lib.time (fun (_ : Unit) =>
     (prove r"prime n_256" tac).run) ())

  /- Basic sanity check on the (otherwise unused) c parameter. -/

  let SANITY_CHECK_256 ← prove
   r"(&b_256 pow 2 * &c_256:int == -- &27) (mod &p_256)"
   (← do
    pure (REWRITE_TAC [G_256, p_256, b_256, c_256] THEN
    REWRITE_TAC [← GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV))

  /- Definition of the curve group and proof of its key properties. -/

  let p256_group ← define
   r"p256_group =
   weierstrass_group
    (integer_mod_ring p_256,
     ring_neg (integer_mod_ring p_256) (&3),
     &b_256)"

  let P256_GROUP ← prove
   r"group_carrier p256_group =
     weierstrass_curve
      (integer_mod_ring p_256,ring_neg (integer_mod_ring p_256) (&3),&b_256) /\
   group_id p256_group =
     NONE /\
   group_inv p256_group =
     weierstrass_neg
      (integer_mod_ring p_256,ring_neg (integer_mod_ring p_256) (&3),&b_256) /\
   group_mul p256_group =
     weierstrass_add
      (integer_mod_ring p_256,ring_neg (integer_mod_ring p_256) (&3),&b_256)"
   (← do
    pure (REWRITE_TAC [p256_group] THEN
    MATCH_MP_TAC WEIERSTRASS_GROUP THEN
    REWRITE_TAC [FIELD_INTEGER_MOD_RING, INTEGER_MOD_RING_CHAR, PRIME_P256] THEN
    REWRITE_TAC [p_256, b_256, weierstrass_nonsingular] THEN
    SIMP_TAC [INTEGER_MOD_RING_CLAUSES, ARITH, IN_ELIM_THM] THEN
    CONV_TAC INT_REDUCE_CONV))

  add_ecgroup [p_256, b_256] P256_GROUP

  -- @@RETURN BEGIN
  return { p_256, n_256, SEED_256, c_256, b_256, G_256, nistp256, P_256, PRIME_P256,
           PRIME_N256, SANITY_CHECK_256, p256_group, P256_GROUP }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- No 2-torsion, the generator and its order, and the group's order and      -/
/- structure.  (nistp256.ml 102-186)                                         -/
/- ------------------------------------------------------------------------- -/

structure NistP256Group where
  -- @@FIELDS
  NO_ROOTS_P256 : thm
  GENERATOR_IN_GROUP_CARRIER_256 : thm
  GROUP_ELEMENT_ORDER_G256 : thm
  FINITE_GROUP_CARRIER_P256 : thm
  SIZE_P256_GROUP : thm
  P256_GROUP_ORDER : thm
  P256_GROUP_ELEMENT_ORDER : thm
  GENERATED_P256_GROUP : thm
  CYCLIC_P256_GROUP : thm
  ABELIAN_P256_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupNistP256Group [HolBase] (D : NistP256Deps) (BNistP256Defs : NistP256Defs) :
    ExceptT String IO NistP256Group := do
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
  let { G_256, P256_GROUP, PRIME_N256, PRIME_P256, b_256, n_256, p_256, .. } := BNistP256Defs
  -- @@SCOPE END

  let NO_ROOTS_P256 ← prove
   r"!x:int. ~((x pow 3 - &3 * x + &b_256 == &0) (mod &p_256))"
   (← do
    pure (← EXCLUDE_MODULAR_CUBIC_ROOTS_TAC PRIME_P256 [p_256, b_256]))

  let GENERATOR_IN_GROUP_CARRIER_256 ← prove
   r"G_256 IN group_carrier p256_group"
   (← do
    pure (REWRITE_TAC [G_256] THEN CONV_TAC ECGROUP_CARRIER_CONV))

  let GROUP_ELEMENT_ORDER_G256 ← prove
   r"group_element_order p256_group G_256 = n_256"
   (← do
    pure (SIMP_TAC [GROUP_ELEMENT_ORDER_UNIQUE_PRIME, GENERATOR_IN_GROUP_CARRIER_256,
                    PRIME_N256] THEN
    REWRITE_TAC [G_256, ← liftExcept (el 1 (CONJUNCTS P256_GROUP)), option_DISTINCT] THEN
    REWRITE_TAC [n_256] THEN CONV_TAC (LAND_CONV ECGROUP_POW_CONV) THEN
    REFL_TAC))

  let FINITE_GROUP_CARRIER_P256 ← prove
   r"FINITE(group_carrier p256_group)"
   (← do
    pure (REWRITE_TAC [P256_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
    REWRITE_TAC [FINITE_INTEGER_MOD_RING, FIELD_INTEGER_MOD_RING, PRIME_P256] THEN
    REWRITE_TAC [p_256] THEN CONV_TAC NUM_REDUCE_CONV))

  let SIZE_P256_GROUP ← prove
   r"group_carrier p256_group HAS_SIZE n_256"
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
    EXISTS_TAC (← q r"G_256:(int#int)option") THEN
    REWRITE_TAC [GENERATOR_IN_GROUP_CARRIER_256, GROUP_ELEMENT_ORDER_G256,
                 FINITE_GROUP_CARRIER_P256] THEN
    REWRITE_TAC [P256_GROUP] THEN CONJ_TAC THENL
     [wPart lhand (fun t => do lhand (← rand t)) CARD_BOUND_WEIERSTRASS_CURVE THEN
      REWRITE_TAC [FINITE_INTEGER_MOD_RING, FIELD_INTEGER_MOD_RING] THEN
      REWRITE_TAC [PRIME_P256] THEN ANTS_TAC THENL
       [REWRITE_TAC [p_256] THEN CONV_TAC NUM_REDUCE_CONV,
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] LET_TRANS)] THEN
      SIMP_TAC [CARD_INTEGER_MOD_RING, p_256, ARITH] THEN
      REWRITE_TAC [n_256] THEN CONV_TAC NUM_REDUCE_CONV,
      REWRITE_TAC [FORALL_OPTION_THM, IN, FORALL_PAIR_THM] THEN
      REWRITE_TAC [weierstrass_curve, weierstrass_neg, option_DISTINCT] THEN
      MAP_EVERY X_GEN_TAC [← q r"x:int", ← q r"y:int"] THEN REWRITE_TAC [option_INJ] THEN
      REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER, INTEGER_MOD_RING_CLAUSES] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC [p_256, PAIR_EQ] THEN
      CONV_TAC INT_REDUCE_CONV] THEN
    ASM_CASES_TAC (← q r"y:int = &0") THENL
     [ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV THEN
      DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
      CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC (← SPEC (← q r"x:int") NO_ROOTS_P256) THEN
      REWRITE_TAC [a1] THEN
      REWRITE_TAC [← GSYM INT_REM_EQ, p_256, INT_REM_ZERO],
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o MATCH_MP a2) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC [INT_REM_LT], ALL_TAC] THEN
      REWRITE_TAC [INT_REM_EQ, i3] THEN
      DISCH_THEN (MP_TAC o MATCH_MP i4) THEN
      REWRITE_TAC [← GSYM num_coprime, ARITH, COPRIME_2] THEN
      DISCH_THEN (MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]))

  let P256_GROUP_ORDER ← prove
   r"CARD(group_carrier p256_group) = n_256"
   (← do
    pure (REWRITE_TAC [← REWRITE_RULE [HAS_SIZE] SIZE_P256_GROUP]))

  let P256_GROUP_ELEMENT_ORDER ← prove
   r"!P. P IN group_carrier p256_group
       ==> group_element_order p256_group P =
           if P = group_id p256_group then 1 else n_256"
   (← do
    pure (MESON_TAC [SIZE_P256_GROUP, HAS_SIZE, GROUP_ELEMENT_ORDER_PRIME, PRIME_N256]))

  let GENERATED_P256_GROUP ← prove
   r"subgroup_generated p256_group {G_256} = p256_group"
   (← do
    pure (SIMP_TAC [SUBGROUP_GENERATED_ELEMENT_ORDER,
                    GENERATOR_IN_GROUP_CARRIER_256,
                    FINITE_GROUP_CARRIER_P256] THEN
    REWRITE_TAC [GROUP_ELEMENT_ORDER_G256,
                 ← REWRITE_RULE [HAS_SIZE] SIZE_P256_GROUP]))

  let CYCLIC_P256_GROUP ← prove
   r"cyclic_group p256_group"
   (← do
    pure (MESON_TAC [CYCLIC_GROUP_ALT, GENERATED_P256_GROUP]))

  let ABELIAN_P256_GROUP ← prove
   r"abelian_group p256_group"
   (← do
    pure (MESON_TAC [CYCLIC_P256_GROUP, CYCLIC_IMP_ABELIAN_GROUP]))

  -- @@RETURN BEGIN
  return { NO_ROOTS_P256, GENERATOR_IN_GROUP_CARRIER_256, GROUP_ELEMENT_ORDER_G256,
           FINITE_GROUP_CARRIER_P256, SIZE_P256_GROUP, P256_GROUP_ORDER,
           P256_GROUP_ELEMENT_ORDER, GENERATED_P256_GROUP, CYCLIC_P256_GROUP,
           ABELIAN_P256_GROUP }
  -- @@RETURN END

end HolEC.NistP256
