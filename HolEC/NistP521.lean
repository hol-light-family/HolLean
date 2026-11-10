/- ========================================================================= -/
/- The NIST-recommended elliptic curve P-521, aka secp521r1.               -/
/- ========================================================================= -/
/- File: HolEC/NistP521.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/nistp521.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/weierstrass.ml, EC/excluderoots.ml, EC/computegroup.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.NistP521 fills them).

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

namespace HolEC.NistP521

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

/-- What nistp521.ml uses from Session besides theorems. -/
structure NistP521Deps where
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
/- curve group.  (nistp521.ml)                                               -/
/- ------------------------------------------------------------------------- -/

structure NistP521Defs where
  -- @@FIELDS
  p_521 : thm
  n_521 : thm
  SEED_521 : thm
  c_521 : thm
  b_521 : thm
  G_521 : thm
  nistp521 : thm
  P_521 : thm
  PRIME_P521 : thm
  PRIME_N521 : thm
  SANITY_CHECK_521 : thm
  p521_group : thm
  P521_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupNistP521Defs [HolBase] (D : NistP521Deps) :
    ExceptT String IO NistP521Defs := do
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

  let p_521 ← new_definition r"p_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151"
  let n_521 ← new_definition r"n_521 = 6864797660130609714981900799081393217269435300143305409394463459185543183397655394245057746333217197532963996371363321113864768612440380340372808892707005449"
  let SEED_521 ← new_definition r"SEED_521 = 0xd09e8800291cb85396cc6717393284aaa0da64ba"
  let c_521 ← new_definition r"c_521 = 0x0b48bfa5f420a34949539d2bdfc264eeeeb077688e44fbf0ad8f6d0edb37bd6b533281000518e19f1b9ffbe0fe9ed8a3c2200b8f875e523868c70c1e5bf55bad637"
  let b_521 ← new_definition r"b_521 = 0x051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef109e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd46b503f00"
  let G_521 ← new_definition r"G_521 = SOME(&0xc6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31c2e5bd66:int,&0x11839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be94769fd16650:int)"

  let nistp521 ← define
   r"nistp521 =
   (integer_mod_ring p_521,
     ring_neg (integer_mod_ring p_521) (&3),
     &b_521:int)"

  /- Primality of the field characteristic and group order. -/

  let P_521 ← prove
   r"p_521 = 2 EXP 521 - 1"
   (← do
    pure (REWRITE_TAC [p_521] THEN CONV_TAC NUM_REDUCE_CONV))

  -- `time prove (goal, tac)`: the tactic is built before `time` runs
  let PRIME_P521 ← do
    let tac ← do
      pure (REWRITE_TAC [p_521] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (fun t => (PRIME_RULE
       ["2", "3", "5", "7", "11", "13", "17", "19", "23", "29", "31", "37",
        "41", "43", "53", "59", "61", "79", "89", "103", "109", "113", "131",
        "151", "157", "173", "179", "223", "227", "257", "277", "317", "347",
        "397", "521", "683", "1051", "1237", "1381", "1433", "1613", "1663",
        "2437", "2731", "3191", "8191", "23609", "28793", "42641", "49481",
        "51481", "61681", "409891", "858001", "2995763", "5746001", "7623851",
        "8620289", "9211861", "34110701", "308761441", "2400573761",
        "2534364967", "24098228377", "65427463921", "674750394557",
        "108140989558681", "145295143558111", "361725589517273017",
        "173308343918874810521923841"] t).run))
    ExceptT.mk (HolCore.Lib.time (fun (_ : Unit) =>
     (prove r"prime p_521" tac).run) ())

  let PRIME_N521 ← do
    let tac ← do
      pure (REWRITE_TAC [n_521] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (fun t => (PRIME_RULE
       ["2", "3", "5", "7", "11", "13", "17", "19", "23", "29", "31", "37",
        "41", "47", "53", "59", "61", "71", "73", "79", "97", "109", "113",
        "127", "131", "157", "181", "191", "193", "227", "229", "233", "241",
        "257", "263", "277", "281", "311", "421", "547", "593", "641", "659",
        "811", "877", "1187", "1283", "1543", "5449", "6043", "9227", "10861",
        "14461", "15601", "17293", "17467", "20341", "65677", "92581",
        "133279", "161969", "370471", "495527", "777241", "6937379", "8196883",
        "10577321", "10924559", "19353437", "186406729", "1458105463",
        "101785224689", "43800962361397", "60018716061994831",
        "88599952463812275001", "3473195323567808068309",
        "4239602065187190872179", "1647781915921980690468599",
        "144471089338257942164514676806340723",
        "7427946019382605513260578233234962521",
        "15994076126984618329123851002118749004583184815459808099",
        "3636410625392624440351547907325502812950802686368714273274221490761556277859337865760708490235892541081304511",
        "3615194794881930010216942559103847593050265703173292383701371712350878926821661243755933835426896058418509759880171943"] t).run))
    ExceptT.mk (HolCore.Lib.time (fun (_ : Unit) =>
     (prove r"prime n_521" tac).run) ())

  /- Basic sanity check on the (otherwise unused) c parameter. -/

  let SANITY_CHECK_521 ← prove
   r"(&b_521 pow 2 * &c_521:int == -- &27) (mod &p_521)"
   (← do
    pure (REWRITE_TAC [G_521, p_521, b_521, c_521] THEN
    REWRITE_TAC [← GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV))

  /- Definition of the curve group and proof of its key properties. -/

  let p521_group ← define
   r"p521_group =
   weierstrass_group
    (integer_mod_ring p_521,
     ring_neg (integer_mod_ring p_521) (&3),
     &b_521)"

  let P521_GROUP ← prove
   r"group_carrier p521_group =
     weierstrass_curve
      (integer_mod_ring p_521,ring_neg (integer_mod_ring p_521) (&3),&b_521) /\
   group_id p521_group =
     NONE /\
   group_inv p521_group =
     weierstrass_neg
      (integer_mod_ring p_521,ring_neg (integer_mod_ring p_521) (&3),&b_521) /\
   group_mul p521_group =
     weierstrass_add
      (integer_mod_ring p_521,ring_neg (integer_mod_ring p_521) (&3),&b_521)"
   (← do
    pure (REWRITE_TAC [p521_group] THEN
    MATCH_MP_TAC WEIERSTRASS_GROUP THEN
    REWRITE_TAC [FIELD_INTEGER_MOD_RING, INTEGER_MOD_RING_CHAR, PRIME_P521] THEN
    REWRITE_TAC [p_521, b_521, weierstrass_nonsingular] THEN
    SIMP_TAC [INTEGER_MOD_RING_CLAUSES, ARITH, IN_ELIM_THM] THEN
    CONV_TAC INT_REDUCE_CONV))

  add_ecgroup [p_521, b_521] P521_GROUP

  -- @@RETURN BEGIN
  return { p_521, n_521, SEED_521, c_521, b_521, G_521, nistp521, P_521, PRIME_P521,
           PRIME_N521, SANITY_CHECK_521, p521_group, P521_GROUP }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- No 2-torsion, the generator and its order, and the group's order and      -/
/- structure.  (nistp521.ml)                                                 -/
/- ------------------------------------------------------------------------- -/

structure NistP521Group where
  -- @@FIELDS
  NO_ROOTS_P521 : thm
  GENERATOR_IN_GROUP_CARRIER_521 : thm
  GROUP_ELEMENT_ORDER_G521 : thm
  FINITE_GROUP_CARRIER_P521 : thm
  SIZE_P521_GROUP : thm
  P521_GROUP_ORDER : thm
  P521_GROUP_ELEMENT_ORDER : thm
  GENERATED_P521_GROUP : thm
  CYCLIC_P521_GROUP : thm
  ABELIAN_P521_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupNistP521Group [HolBase] (D : NistP521Deps) (BNistP521Defs : NistP521Defs) :
    ExceptT String IO NistP521Group := do
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
  let { G_521, P521_GROUP, PRIME_N521, PRIME_P521, b_521, n_521, p_521, .. } := BNistP521Defs
  -- @@SCOPE END

  let NO_ROOTS_P521 ← prove
   r"!x:int. ~((x pow 3 - &3 * x + &b_521 == &0) (mod &p_521))"
   (← do
    pure (← EXCLUDE_MODULAR_CUBIC_ROOTS_TAC PRIME_P521 [p_521, b_521]))

  let GENERATOR_IN_GROUP_CARRIER_521 ← prove
   r"G_521 IN group_carrier p521_group"
   (← do
    pure (REWRITE_TAC [G_521] THEN CONV_TAC ECGROUP_CARRIER_CONV))

  let GROUP_ELEMENT_ORDER_G521 ← prove
   r"group_element_order p521_group G_521 = n_521"
   (← do
    pure (SIMP_TAC [GROUP_ELEMENT_ORDER_UNIQUE_PRIME, GENERATOR_IN_GROUP_CARRIER_521,
                    PRIME_N521] THEN
    REWRITE_TAC [G_521, ← liftExcept (el 1 (CONJUNCTS P521_GROUP)), option_DISTINCT] THEN
    REWRITE_TAC [n_521] THEN CONV_TAC (LAND_CONV ECGROUP_POW_CONV) THEN
    REFL_TAC))

  let FINITE_GROUP_CARRIER_P521 ← prove
   r"FINITE(group_carrier p521_group)"
   (← do
    pure (REWRITE_TAC [P521_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
    REWRITE_TAC [FINITE_INTEGER_MOD_RING, FIELD_INTEGER_MOD_RING, PRIME_P521] THEN
    REWRITE_TAC [p_521] THEN CONV_TAC NUM_REDUCE_CONV))

  let SIZE_P521_GROUP ← prove
   r"group_carrier p521_group HAS_SIZE n_521"
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
    EXISTS_TAC (← q r"G_521:(int#int)option") THEN
    REWRITE_TAC [GENERATOR_IN_GROUP_CARRIER_521, GROUP_ELEMENT_ORDER_G521,
                 FINITE_GROUP_CARRIER_P521] THEN
    REWRITE_TAC [P521_GROUP] THEN CONJ_TAC THENL
     [wPart lhand (fun t => do lhand (← rand t)) CARD_BOUND_WEIERSTRASS_CURVE THEN
      REWRITE_TAC [FINITE_INTEGER_MOD_RING, FIELD_INTEGER_MOD_RING] THEN
      REWRITE_TAC [PRIME_P521] THEN ANTS_TAC THENL
       [REWRITE_TAC [p_521] THEN CONV_TAC NUM_REDUCE_CONV,
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] LET_TRANS)] THEN
      SIMP_TAC [CARD_INTEGER_MOD_RING, p_521, ARITH] THEN
      REWRITE_TAC [n_521] THEN CONV_TAC NUM_REDUCE_CONV,
      REWRITE_TAC [FORALL_OPTION_THM, IN, FORALL_PAIR_THM] THEN
      REWRITE_TAC [weierstrass_curve, weierstrass_neg, option_DISTINCT] THEN
      MAP_EVERY X_GEN_TAC [← q r"x:int", ← q r"y:int"] THEN REWRITE_TAC [option_INJ] THEN
      REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER, INTEGER_MOD_RING_CLAUSES] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC [p_521, PAIR_EQ] THEN
      CONV_TAC INT_REDUCE_CONV] THEN
    ASM_CASES_TAC (← q r"y:int = &0") THENL
     [ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV THEN
      DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
      CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC (← SPEC (← q r"x:int") NO_ROOTS_P521) THEN
      REWRITE_TAC [a1] THEN
      REWRITE_TAC [← GSYM INT_REM_EQ, p_521, INT_REM_ZERO],
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o MATCH_MP a2) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC [INT_REM_LT], ALL_TAC] THEN
      REWRITE_TAC [INT_REM_EQ, i3] THEN
      DISCH_THEN (MP_TAC o MATCH_MP i4) THEN
      REWRITE_TAC [← GSYM num_coprime, ARITH, COPRIME_2] THEN
      DISCH_THEN (MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]))

  let P521_GROUP_ORDER ← prove
   r"CARD(group_carrier p521_group) = n_521"
   (← do
    pure (REWRITE_TAC [← REWRITE_RULE [HAS_SIZE] SIZE_P521_GROUP]))

  let P521_GROUP_ELEMENT_ORDER ← prove
   r"!P. P IN group_carrier p521_group
       ==> group_element_order p521_group P =
           if P = group_id p521_group then 1 else n_521"
   (← do
    pure (MESON_TAC [SIZE_P521_GROUP, HAS_SIZE, GROUP_ELEMENT_ORDER_PRIME, PRIME_N521]))

  let GENERATED_P521_GROUP ← prove
   r"subgroup_generated p521_group {G_521} = p521_group"
   (← do
    pure (SIMP_TAC [SUBGROUP_GENERATED_ELEMENT_ORDER,
                    GENERATOR_IN_GROUP_CARRIER_521,
                    FINITE_GROUP_CARRIER_P521] THEN
    REWRITE_TAC [GROUP_ELEMENT_ORDER_G521,
                 ← REWRITE_RULE [HAS_SIZE] SIZE_P521_GROUP]))

  let CYCLIC_P521_GROUP ← prove
   r"cyclic_group p521_group"
   (← do
    pure (MESON_TAC [CYCLIC_GROUP_ALT, GENERATED_P521_GROUP]))

  let ABELIAN_P521_GROUP ← prove
   r"abelian_group p521_group"
   (← do
    pure (MESON_TAC [CYCLIC_P521_GROUP, CYCLIC_IMP_ABELIAN_GROUP]))

  -- @@RETURN BEGIN
  return { NO_ROOTS_P521, GENERATOR_IN_GROUP_CARRIER_521, GROUP_ELEMENT_ORDER_G521,
           FINITE_GROUP_CARRIER_P521, SIZE_P521_GROUP, P521_GROUP_ORDER,
           P521_GROUP_ELEMENT_ORDER, GENERATED_P521_GROUP, CYCLIC_P521_GROUP,
           ABELIAN_P521_GROUP }
  -- @@RETURN END

end HolEC.NistP521
