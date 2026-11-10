/- ========================================================================= -/
/- The GM/T 0003.1 SM2 elliptic curve for commercial cryptography.         -/
/- ========================================================================= -/
/- File: HolEC/CCSM2.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/ccsm2.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/weierstrass.ml, EC/excluderoots.ml, EC/computegroup.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.CCSM2 fills them).

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

namespace HolEC.CCSM2

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

/-- What ccsm2.ml uses from Session besides theorems. -/
structure CCSM2Deps where
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
/- The curve parameters, with a = -3 assumed, taken from Table 11 in         -/
/- section 5.2.9 of https://trustedcomputinggroup.org/wp-content/uploads/    -/
/- TCGAlgorithmRegistry_Rev01.15.pdf (a = -3 is not represented              -/
/- explicitly), primality of the field characteristic and group order, and   -/
/- the curve group.  (ccsm2.ml 1-98)                                         -/
/- ------------------------------------------------------------------------- -/

structure CCSM2Defs where
  -- @@FIELDS
  p_sm2 : thm
  n_sm2 : thm
  b_sm2 : thm
  g_sm2 : thm
  ccsm2 : thm
  P_SM2 : thm
  PRIME_PSM2 : thm
  PRIME_NSM2 : thm
  sm2_group : thm
  SM2_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupCCSM2Defs [HolBase] (D : CCSM2Deps) :
    ExceptT String IO CCSM2Defs := do
  -- @@SCOPE BEGIN
  let { INT_REDUCE_CONV, NUM_REDUCE_CONV, PRIME_RULE, add_curve, add_curveadd,
        add_curveneg, add_ecgroup, define, new_definition, .. } := D
  let { ARITH, FIELD_INTEGER_MOD_RING, INTEGER_MOD_RING_CHAR, INTEGER_MOD_RING_CLAUSES,
        IN_ELIM_THM, WEIERSTRASS_GROUP, weierstrass_add, weierstrass_curve,
        weierstrass_neg, weierstrass_nonsingular, .. } := D.core1
  -- @@SCOPE END

  add_curve weierstrass_curve
  add_curveneg weierstrass_neg
  add_curveadd weierstrass_add

  let p_sm2 ← new_definition r"p_sm2 = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF"
  let n_sm2 ← new_definition r"n_sm2 = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFF7203DF6B21C6052B53BBF40939D54123"
  let b_sm2 ← new_definition r"b_sm2 = 0x28E9FA9E9D9F5E344D5A9E4BCF6509A7F39789F515AB8F92DDBCBD414D940E93"
  let g_sm2 ← new_definition r"g_sm2 = SOME(&0x32C4AE2C1F1981195F9904466A39C9948FE30BBFF2660BE1715A4589334C74C7:int,&0xBC3736A2F4F6779C59BDCEE36B692153D0A9877CC62A474002DF32E52139F0A0:int)"

  let ccsm2 ← define
   r"ccsm2 =
    (integer_mod_ring p_sm2,
     ring_neg (integer_mod_ring p_sm2) (&3),
     &b_sm2:int)"

  /- Primality of the field characteristic and group order. -/

  let P_SM2 ← prove
   r"p_sm2 = 2 EXP 256 - 2 EXP 224 - 2 EXP 96 + 2 EXP 64 - 1"
   (← do
    pure (REWRITE_TAC [p_sm2] THEN CONV_TAC NUM_REDUCE_CONV))

  -- `time prove (goal, tac)`: the tactic is built before `time` runs
  let PRIME_PSM2 ← do
    let tac ← do
      pure (REWRITE_TAC [p_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (fun t => (PRIME_RULE
       ["2", "3", "5", "7", "11", "13", "17", "19", "23", "29", "31", "37",
        "43", "53", "61", "67", "71", "73", "79", "97", "101", "103", "137",
        "241", "337", "367", "571", "743", "769", "823", "1213", "1447",
        "2273", "2473", "4547", "5303", "5711", "30223", "34511", "54983",
        "71209", "179429", "363761", "3079049", "6158099", "8214737",
        "3017783777", "348253387243", "4641351449027", "417514796639753",
        "4773264379806847", "66013261729388519804782124120027",
        "115792089210356248756420345214020892766250353991924191454421193933289684991999"] t).run))
    ExceptT.mk (HolCore.Lib.time (fun (_ : Unit) =>
     (prove r"prime p_sm2" tac).run) ())

  let PRIME_NSM2 ← do
    let tac ← do
      pure (REWRITE_TAC [n_sm2] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (fun t => (PRIME_RULE
       ["2", "3", "5", "7", "11", "13", "17", "23", "29", "31", "41", "43",
        "53", "59", "61", "71", "79", "83", "89", "101", "103", "127", "179",
        "181", "233", "251", "359", "431", "719", "1013", "3037", "3049",
        "4957", "5801", "7759", "12149", "14057", "84163", "110899", "9061163",
        "10042883", "17965699", "107615843", "117774739", "1413296869",
        "2566129871", "2368433183657", "5636460199499", "101456283590983",
        "3258964060712033", "18120927127286907576013935251791662753637",
        "125197554539772723432468576818475380947471091418362477724521",
        "115792089210356248756420345214020892766061623724957744567843809356293439045923"] t).run))
    ExceptT.mk (HolCore.Lib.time (fun (_ : Unit) =>
     (prove r"prime n_sm2" tac).run) ())

  /- Definition of the curve group and proof of its key properties. -/

  let sm2_group ← define
   r"sm2_group =
   weierstrass_group
    (integer_mod_ring p_sm2,
     ring_neg (integer_mod_ring p_sm2) (&3),
     &b_sm2)"

  let SM2_GROUP ← prove
   r"group_carrier sm2_group =
     weierstrass_curve
      (integer_mod_ring p_sm2,ring_neg (integer_mod_ring p_sm2) (&3),&b_sm2) /\
   group_id sm2_group =
     NONE /\
   group_inv sm2_group =
     weierstrass_neg
      (integer_mod_ring p_sm2,ring_neg (integer_mod_ring p_sm2) (&3),&b_sm2) /\
   group_mul sm2_group =
     weierstrass_add
      (integer_mod_ring p_sm2,ring_neg (integer_mod_ring p_sm2) (&3),&b_sm2)"
   (← do
    pure (REWRITE_TAC [sm2_group] THEN
    MATCH_MP_TAC WEIERSTRASS_GROUP THEN
    REWRITE_TAC [FIELD_INTEGER_MOD_RING, INTEGER_MOD_RING_CHAR, PRIME_PSM2] THEN
    REWRITE_TAC [p_sm2, b_sm2, weierstrass_nonsingular] THEN
    SIMP_TAC [INTEGER_MOD_RING_CLAUSES, ARITH, IN_ELIM_THM] THEN
    CONV_TAC INT_REDUCE_CONV))

  add_ecgroup [p_sm2, b_sm2] SM2_GROUP

  -- @@RETURN BEGIN
  return { p_sm2, n_sm2, b_sm2, g_sm2, ccsm2, P_SM2, PRIME_PSM2, PRIME_NSM2, sm2_group,
           SM2_GROUP }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- No 2-torsion, the generator and its order, and the group's order and      -/
/- structure.  (ccsm2.ml 99-183)                                             -/
/- ------------------------------------------------------------------------- -/

structure CCSM2Group where
  -- @@FIELDS
  NO_ROOTS_SM2 : thm
  GENERATOR_IN_GROUP_CARRIER_SM2 : thm
  GROUP_ELEMENT_ORDER_SM2 : thm
  FINITE_GROUP_CARRIER_SM2 : thm
  SIZE_SM2_GROUP : thm
  SM2_GROUP_ORDER : thm
  SM2_GROUP_ELEMENT_ORDER : thm
  GENERATED_SM2_GROUP : thm
  CYCLIC_SM2_GROUP : thm
  ABELIAN_SM2_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupCCSM2Group [HolBase] (D : CCSM2Deps) (BCCSM2Defs : CCSM2Defs) :
    ExceptT String IO CCSM2Group := do
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
  let { PRIME_NSM2, PRIME_PSM2, SM2_GROUP, b_sm2, g_sm2, n_sm2, p_sm2, .. } := BCCSM2Defs
  -- @@SCOPE END

  let NO_ROOTS_SM2 ← prove
   r"!x:int. ~((x pow 3 - &3 * x + &b_sm2 == &0) (mod &p_sm2))"
   (← do
    pure (← EXCLUDE_MODULAR_CUBIC_ROOTS_TAC PRIME_PSM2 [p_sm2, b_sm2]))

  let GENERATOR_IN_GROUP_CARRIER_SM2 ← prove
   r"g_sm2 IN group_carrier sm2_group"
   (← do
    pure (REWRITE_TAC [g_sm2] THEN CONV_TAC ECGROUP_CARRIER_CONV))

  let GROUP_ELEMENT_ORDER_SM2 ← prove
   r"group_element_order sm2_group g_sm2 = n_sm2"
   (← do
    pure (SIMP_TAC [GROUP_ELEMENT_ORDER_UNIQUE_PRIME, GENERATOR_IN_GROUP_CARRIER_SM2,
                    PRIME_NSM2] THEN
    REWRITE_TAC [g_sm2, ← liftExcept (el 1 (CONJUNCTS SM2_GROUP)), option_DISTINCT] THEN
    REWRITE_TAC [n_sm2] THEN CONV_TAC (LAND_CONV ECGROUP_POW_CONV) THEN
    REFL_TAC))

  let FINITE_GROUP_CARRIER_SM2 ← prove
   r"FINITE(group_carrier sm2_group)"
   (← do
    pure (REWRITE_TAC [SM2_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
    REWRITE_TAC [FINITE_INTEGER_MOD_RING, FIELD_INTEGER_MOD_RING, PRIME_PSM2] THEN
    REWRITE_TAC [p_sm2] THEN CONV_TAC NUM_REDUCE_CONV))

  let SIZE_SM2_GROUP ← prove
   r"group_carrier sm2_group HAS_SIZE n_sm2"
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
    EXISTS_TAC (← q r"g_sm2:(int#int)option") THEN
    REWRITE_TAC [GENERATOR_IN_GROUP_CARRIER_SM2, GROUP_ELEMENT_ORDER_SM2,
                 FINITE_GROUP_CARRIER_SM2] THEN
    REWRITE_TAC [SM2_GROUP] THEN CONJ_TAC THENL
     [wPart lhand (fun t => do lhand (← rand t)) CARD_BOUND_WEIERSTRASS_CURVE THEN
      REWRITE_TAC [FINITE_INTEGER_MOD_RING, FIELD_INTEGER_MOD_RING] THEN
      REWRITE_TAC [PRIME_PSM2] THEN ANTS_TAC THENL
       [REWRITE_TAC [p_sm2] THEN CONV_TAC NUM_REDUCE_CONV,
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] LET_TRANS)] THEN
      SIMP_TAC [CARD_INTEGER_MOD_RING, p_sm2, ARITH] THEN
      REWRITE_TAC [n_sm2] THEN CONV_TAC NUM_REDUCE_CONV,
      REWRITE_TAC [FORALL_OPTION_THM, IN, FORALL_PAIR_THM] THEN
      REWRITE_TAC [weierstrass_curve, weierstrass_neg, option_DISTINCT] THEN
      MAP_EVERY X_GEN_TAC [← q r"x:int", ← q r"y:int"] THEN REWRITE_TAC [option_INJ] THEN
      REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER, INTEGER_MOD_RING_CLAUSES] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC [p_sm2, PAIR_EQ] THEN
      CONV_TAC INT_REDUCE_CONV] THEN
    ASM_CASES_TAC (← q r"y:int = &0") THENL
     [ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV THEN
      DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
      CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC (← SPEC (← q r"x:int") NO_ROOTS_SM2) THEN
      REWRITE_TAC [a1] THEN
      REWRITE_TAC [← GSYM INT_REM_EQ, p_sm2, INT_REM_ZERO],
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o MATCH_MP a2) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC [INT_REM_LT], ALL_TAC] THEN
      REWRITE_TAC [INT_REM_EQ, i3] THEN
      DISCH_THEN (MP_TAC o MATCH_MP i4) THEN
      REWRITE_TAC [← GSYM num_coprime, ARITH, COPRIME_2] THEN
      DISCH_THEN (MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]))

  let SM2_GROUP_ORDER ← prove
   r"CARD(group_carrier sm2_group) = n_sm2"
   (← do
    pure (REWRITE_TAC [← REWRITE_RULE [HAS_SIZE] SIZE_SM2_GROUP]))

  let SM2_GROUP_ELEMENT_ORDER ← prove
   r"!P. P IN group_carrier sm2_group
       ==> group_element_order sm2_group P =
           if P = group_id sm2_group then 1 else n_sm2"
   (← do
    pure (MESON_TAC [SIZE_SM2_GROUP, HAS_SIZE, GROUP_ELEMENT_ORDER_PRIME, PRIME_NSM2]))

  let GENERATED_SM2_GROUP ← prove
   r"subgroup_generated sm2_group {g_sm2} = sm2_group"
   (← do
    pure (SIMP_TAC [SUBGROUP_GENERATED_ELEMENT_ORDER,
                    GENERATOR_IN_GROUP_CARRIER_SM2,
                    FINITE_GROUP_CARRIER_SM2] THEN
    REWRITE_TAC [GROUP_ELEMENT_ORDER_SM2,
                 ← REWRITE_RULE [HAS_SIZE] SIZE_SM2_GROUP]))

  let CYCLIC_SM2_GROUP ← prove
   r"cyclic_group sm2_group"
   (← do
    pure (MESON_TAC [CYCLIC_GROUP_ALT, GENERATED_SM2_GROUP]))

  let ABELIAN_SM2_GROUP ← prove
   r"abelian_group sm2_group"
   (← do
    pure (MESON_TAC [CYCLIC_SM2_GROUP, CYCLIC_IMP_ABELIAN_GROUP]))

  -- @@RETURN BEGIN
  return { NO_ROOTS_SM2, GENERATOR_IN_GROUP_CARRIER_SM2, GROUP_ELEMENT_ORDER_SM2,
           FINITE_GROUP_CARRIER_SM2, SIZE_SM2_GROUP, SM2_GROUP_ORDER,
           SM2_GROUP_ELEMENT_ORDER, GENERATED_SM2_GROUP, CYCLIC_SM2_GROUP,
           ABELIAN_SM2_GROUP }
  -- @@RETURN END

end HolEC.CCSM2
