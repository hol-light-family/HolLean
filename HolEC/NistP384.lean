/- ========================================================================= -/
/- The NIST-recommended elliptic curve P-384, aka secp384r1.               -/
/- ========================================================================= -/
/- File: HolEC/NistP384.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/nistp384.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/weierstrass.ml, EC/excluderoots.ml, EC/computegroup.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.NistP384 fills them).

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

namespace HolEC.NistP384

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

/-- What nistp384.ml uses from Session besides theorems. -/
structure NistP384Deps where
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
/- curve group.  (nistp384.ml)                                               -/
/- ------------------------------------------------------------------------- -/

structure NistP384Defs where
  -- @@FIELDS
  p_384 : thm
  n_384 : thm
  SEED_384 : thm
  c_384 : thm
  b_384 : thm
  G_384 : thm
  nistp384 : thm
  P_384 : thm
  PRIME_P384 : thm
  PRIME_N384 : thm
  SANITY_CHECK_384 : thm
  p384_group : thm
  P384_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupNistP384Defs [HolBase] (D : NistP384Deps) :
    ExceptT String IO NistP384Defs := do
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

  let p_384 ← new_definition r"p_384 = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319"
  let n_384 ← new_definition r"n_384 = 39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643"
  let SEED_384 ← new_definition r"SEED_384 = 0xa335926aa319a27a1d00896a6773a4827acdac73"
  let c_384 ← new_definition r"c_384 = 0x79d1e655f868f02fff48dcdee14151ddb80643c1406d0ca10dfe6fc52009540a495e8042ea5f744f6e184667cc722483"
  let b_384 ← new_definition r"b_384 = 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef"
  let G_384 ← new_definition r"G_384 = SOME(&0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7:int,&0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f:int)"

  let nistp384 ← define
   r"nistp384 =
    (integer_mod_ring p_384,
     ring_neg (integer_mod_ring p_384) (&3),
     &b_384:int)"

  /- Primality of the field characteristic and group order. -/

  let P_384 ← prove
   r"p_384 = 2 EXP 384 - 2 EXP 128 - 2 EXP 96 + 2 EXP 32 - 1"
   (← do
    pure (REWRITE_TAC [p_384] THEN CONV_TAC NUM_REDUCE_CONV))

  -- `time prove (goal, tac)`: the tactic is built before `time` runs
  let PRIME_P384 ← do
    let tac ← do
      pure (REWRITE_TAC [p_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (fun t => (PRIME_RULE
       ["2", "3", "5", "7", "11", "13", "17", "19", "23", "29", "41", "43",
        "47", "59", "61", "67", "73", "79", "97", "131", "139", "157", "181",
        "211", "233", "263", "271", "293", "599", "661", "881", "937", "1033",
        "1373", "1579", "2213", "3253", "3517", "6317", "8389", "21407",
        "38557", "312289", "336757", "363557", "568151", "6051631",
        "105957871", "246608641", "513928823", "532247449", "2862218959",
        "53448597593", "807145746439", "44925942675193", "1357291859799823621",
        "529709925838459440593", "35581458644053887931343",
        "23964610537191310276190549303", "862725979338887169942859774909",
        "20705423504133292078628634597817",
        "413244619895455989650825325680172591660047",
        "12397338596863679689524759770405177749801411",
        "19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097"] t).run))
    ExceptT.mk (HolCore.Lib.time (fun (_ : Unit) =>
     (prove r"prime p_384" tac).run) ())

  let PRIME_N384 ← do
    let tac ← do
      pure (REWRITE_TAC [n_384] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (fun t => (PRIME_RULE
       ["2", "3", "5", "7", "11", "13", "17", "19", "23", "29", "31", "37",
        "41", "43", "47", "53", "59", "73", "79", "89", "97", "107", "113",
        "149", "151", "163", "173", "179", "181", "233", "251", "311", "347",
        "421", "491", "653", "659", "881", "1087", "1117", "1553", "3739",
        "4349", "8699", "16979", "34429", "37447", "64901", "248431", "330563",
        "455737", "1276987", "8463023", "9863677", "154950581", "272109983",
        "290064143", "228572385721", "1436833069313", "23314383343543",
        "37344768852931", "55942463741690639", "426632512014427833817",
        "120699720968197491947347", "1124679999981664229965379347",
        "1495199339761412565498084319", "17942392077136950785977011829",
        "1059392654943455286185473617842338478315215895509773412096307",
        "3055465788140352002733946906144561090641249606160407884365391979704929268480326390471"] t).run))
    ExceptT.mk (HolCore.Lib.time (fun (_ : Unit) =>
     (prove r"prime n_384" tac).run) ())

  /- Basic sanity check on the (otherwise unused) c parameter. -/

  let SANITY_CHECK_384 ← prove
   r"(&b_384 pow 2 * &c_384:int == -- &27) (mod &p_384)"
   (← do
    pure (REWRITE_TAC [G_384, p_384, b_384, c_384] THEN
    REWRITE_TAC [← GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV))

  /- Definition of the curve group and proof of its key properties. -/

  let p384_group ← define
   r"p384_group =
   weierstrass_group
    (integer_mod_ring p_384,
     ring_neg (integer_mod_ring p_384) (&3),
     &b_384)"

  let P384_GROUP ← prove
   r"group_carrier p384_group =
     weierstrass_curve
      (integer_mod_ring p_384,ring_neg (integer_mod_ring p_384) (&3),&b_384) /\
   group_id p384_group =
     NONE /\
   group_inv p384_group =
     weierstrass_neg
      (integer_mod_ring p_384,ring_neg (integer_mod_ring p_384) (&3),&b_384) /\
   group_mul p384_group =
     weierstrass_add
      (integer_mod_ring p_384,ring_neg (integer_mod_ring p_384) (&3),&b_384)"
   (← do
    pure (REWRITE_TAC [p384_group] THEN
    MATCH_MP_TAC WEIERSTRASS_GROUP THEN
    REWRITE_TAC [FIELD_INTEGER_MOD_RING, INTEGER_MOD_RING_CHAR, PRIME_P384] THEN
    REWRITE_TAC [p_384, b_384, weierstrass_nonsingular] THEN
    SIMP_TAC [INTEGER_MOD_RING_CLAUSES, ARITH, IN_ELIM_THM] THEN
    CONV_TAC INT_REDUCE_CONV))

  add_ecgroup [p_384, b_384] P384_GROUP

  -- @@RETURN BEGIN
  return { p_384, n_384, SEED_384, c_384, b_384, G_384, nistp384, P_384, PRIME_P384,
           PRIME_N384, SANITY_CHECK_384, p384_group, P384_GROUP }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- No 2-torsion, the generator and its order, and the group's order and      -/
/- structure.  (nistp384.ml)                                                 -/
/- ------------------------------------------------------------------------- -/

structure NistP384Group where
  -- @@FIELDS
  NO_ROOTS_P384 : thm
  GENERATOR_IN_GROUP_CARRIER_384 : thm
  GROUP_ELEMENT_ORDER_G384 : thm
  FINITE_GROUP_CARRIER_P384 : thm
  SIZE_P384_GROUP : thm
  P384_GROUP_ORDER : thm
  P384_GROUP_ELEMENT_ORDER : thm
  GENERATED_P384_GROUP : thm
  CYCLIC_P384_GROUP : thm
  ABELIAN_P384_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupNistP384Group [HolBase] (D : NistP384Deps) (BNistP384Defs : NistP384Defs) :
    ExceptT String IO NistP384Group := do
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
  let { G_384, P384_GROUP, PRIME_N384, PRIME_P384, b_384, n_384, p_384, .. } := BNistP384Defs
  -- @@SCOPE END

  let NO_ROOTS_P384 ← prove
   r"!x:int. ~((x pow 3 - &3 * x + &b_384 == &0) (mod &p_384))"
   (← do
    pure (← EXCLUDE_MODULAR_CUBIC_ROOTS_TAC PRIME_P384 [p_384, b_384]))

  let GENERATOR_IN_GROUP_CARRIER_384 ← prove
   r"G_384 IN group_carrier p384_group"
   (← do
    pure (REWRITE_TAC [G_384] THEN CONV_TAC ECGROUP_CARRIER_CONV))

  let GROUP_ELEMENT_ORDER_G384 ← prove
   r"group_element_order p384_group G_384 = n_384"
   (← do
    pure (SIMP_TAC [GROUP_ELEMENT_ORDER_UNIQUE_PRIME, GENERATOR_IN_GROUP_CARRIER_384,
                    PRIME_N384] THEN
    REWRITE_TAC [G_384, ← liftExcept (el 1 (CONJUNCTS P384_GROUP)), option_DISTINCT] THEN
    REWRITE_TAC [n_384] THEN CONV_TAC (LAND_CONV ECGROUP_POW_CONV) THEN
    REFL_TAC))

  let FINITE_GROUP_CARRIER_P384 ← prove
   r"FINITE(group_carrier p384_group)"
   (← do
    pure (REWRITE_TAC [P384_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
    REWRITE_TAC [FINITE_INTEGER_MOD_RING, FIELD_INTEGER_MOD_RING, PRIME_P384] THEN
    REWRITE_TAC [p_384] THEN CONV_TAC NUM_REDUCE_CONV))

  let SIZE_P384_GROUP ← prove
   r"group_carrier p384_group HAS_SIZE n_384"
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
    EXISTS_TAC (← q r"G_384:(int#int)option") THEN
    REWRITE_TAC [GENERATOR_IN_GROUP_CARRIER_384, GROUP_ELEMENT_ORDER_G384,
                 FINITE_GROUP_CARRIER_P384] THEN
    REWRITE_TAC [P384_GROUP] THEN CONJ_TAC THENL
     [wPart lhand (fun t => do lhand (← rand t)) CARD_BOUND_WEIERSTRASS_CURVE THEN
      REWRITE_TAC [FINITE_INTEGER_MOD_RING, FIELD_INTEGER_MOD_RING] THEN
      REWRITE_TAC [PRIME_P384] THEN ANTS_TAC THENL
       [REWRITE_TAC [p_384] THEN CONV_TAC NUM_REDUCE_CONV,
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] LET_TRANS)] THEN
      SIMP_TAC [CARD_INTEGER_MOD_RING, p_384, ARITH] THEN
      REWRITE_TAC [n_384] THEN CONV_TAC NUM_REDUCE_CONV,
      REWRITE_TAC [FORALL_OPTION_THM, IN, FORALL_PAIR_THM] THEN
      REWRITE_TAC [weierstrass_curve, weierstrass_neg, option_DISTINCT] THEN
      MAP_EVERY X_GEN_TAC [← q r"x:int", ← q r"y:int"] THEN REWRITE_TAC [option_INJ] THEN
      REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER, INTEGER_MOD_RING_CLAUSES] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC [p_384, PAIR_EQ] THEN
      CONV_TAC INT_REDUCE_CONV] THEN
    ASM_CASES_TAC (← q r"y:int = &0") THENL
     [ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV THEN
      DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
      CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC (← SPEC (← q r"x:int") NO_ROOTS_P384) THEN
      REWRITE_TAC [a1] THEN
      REWRITE_TAC [← GSYM INT_REM_EQ, p_384, INT_REM_ZERO],
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o MATCH_MP a2) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC [INT_REM_LT], ALL_TAC] THEN
      REWRITE_TAC [INT_REM_EQ, i3] THEN
      DISCH_THEN (MP_TAC o MATCH_MP i4) THEN
      REWRITE_TAC [← GSYM num_coprime, ARITH, COPRIME_2] THEN
      DISCH_THEN (MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]))

  let P384_GROUP_ORDER ← prove
   r"CARD(group_carrier p384_group) = n_384"
   (← do
    pure (REWRITE_TAC [← REWRITE_RULE [HAS_SIZE] SIZE_P384_GROUP]))

  let P384_GROUP_ELEMENT_ORDER ← prove
   r"!P. P IN group_carrier p384_group
       ==> group_element_order p384_group P =
           if P = group_id p384_group then 1 else n_384"
   (← do
    pure (MESON_TAC [SIZE_P384_GROUP, HAS_SIZE, GROUP_ELEMENT_ORDER_PRIME, PRIME_N384]))

  let GENERATED_P384_GROUP ← prove
   r"subgroup_generated p384_group {G_384} = p384_group"
   (← do
    pure (SIMP_TAC [SUBGROUP_GENERATED_ELEMENT_ORDER,
                    GENERATOR_IN_GROUP_CARRIER_384,
                    FINITE_GROUP_CARRIER_P384] THEN
    REWRITE_TAC [GROUP_ELEMENT_ORDER_G384,
                 ← REWRITE_RULE [HAS_SIZE] SIZE_P384_GROUP]))

  let CYCLIC_P384_GROUP ← prove
   r"cyclic_group p384_group"
   (← do
    pure (MESON_TAC [CYCLIC_GROUP_ALT, GENERATED_P384_GROUP]))

  let ABELIAN_P384_GROUP ← prove
   r"abelian_group p384_group"
   (← do
    pure (MESON_TAC [CYCLIC_P384_GROUP, CYCLIC_IMP_ABELIAN_GROUP]))

  -- @@RETURN BEGIN
  return { NO_ROOTS_P384, GENERATOR_IN_GROUP_CARRIER_384, GROUP_ELEMENT_ORDER_G384,
           FINITE_GROUP_CARRIER_P384, SIZE_P384_GROUP, P384_GROUP_ORDER,
           P384_GROUP_ELEMENT_ORDER, GENERATED_P384_GROUP, CYCLIC_P384_GROUP,
           ABELIAN_P384_GROUP }
  -- @@RETURN END

end HolEC.NistP384
