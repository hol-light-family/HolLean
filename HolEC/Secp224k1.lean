/- ========================================================================= -/
/- The SECG-recommended elliptic curve secp224k1.                          -/
/- ========================================================================= -/
/- File: HolEC/Secp224k1.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/secp224k1.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/weierstrass.ml, EC/excluderoots.ml, EC/computegroup.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.Secp224k1 fills them).

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

namespace HolEC.Secp224k1

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ARITH CARD_BOUND_WEIERSTRASS_CURVE CARD_INTEGER_MOD_RING COPRIME_2
   CYCLIC_GROUP_ALT CYCLIC_IMP_ABELIAN_GROUP FIELD_INTEGER_MOD_RING
   FINITE_INTEGER_MOD_RING FINITE_WEIERSTRASS_CURVE FORALL_OPTION_THM
   FORALL_PAIR_THM GROUP_ADHOC_ORDER_UNIQUE_LEMMA GROUP_ELEMENT_ORDER_PRIME
   GROUP_ELEMENT_ORDER_UNIQUE_PRIME HAS_SIZE IMP_CONJ_ALT IN
   INTEGER_MOD_RING_CHAR INTEGER_MOD_RING_CLAUSES INT_ADD_LID INT_DIVIDES_LE
   INT_MUL_LZERO INT_REM_EQ INT_REM_LT INT_REM_ZERO IN_ELIM_THM
   IN_INTEGER_MOD_RING_CARRIER LET_TRANS PAIR_EQ
   SUBGROUP_GENERATED_ELEMENT_ORDER WEIERSTRASS_GROUP num_coprime
   option_DISTINCT option_INJ weierstrass_add weierstrass_curve weierstrass_neg
   weierstrass_nonsingular : thm)
  deriving Inhabited

/-- What secp224k1.ml uses from Session besides theorems. -/
structure Secp224k1Deps where
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
/- The SECG curve parameters, copied from the SEC 2 document                 -/
/- (https://www.secg.org/sec2-v2.pdf), primality of the field                -/
/- characteristic and group order, and the curve group.  (secp224k1.ml)      -/
/- ------------------------------------------------------------------------- -/

structure Secp224k1Defs where
  -- @@FIELDS
  p_224k1 : thm
  n_224k1 : thm
  G_224K1 : thm
  P_224K1 : thm
  P_224K1_ALT : thm
  PRIME_P224K1 : thm
  PRIME_N224K1 : thm
  p224k1_group : thm
  P224K1_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupSecp224k1Defs [HolBase] (D : Secp224k1Deps) :
    ExceptT String IO Secp224k1Defs := do
  -- @@SCOPE BEGIN
  let { INT_REDUCE_CONV, NUM_REDUCE_CONV, PRIME_RULE, add_curve, add_curveadd,
        add_curveneg, add_ecgroup, define, .. } := D
  let { ARITH, FIELD_INTEGER_MOD_RING, INTEGER_MOD_RING_CHAR, INTEGER_MOD_RING_CLAUSES,
        IN_ELIM_THM, WEIERSTRASS_GROUP, weierstrass_add, weierstrass_curve,
        weierstrass_neg, weierstrass_nonsingular, .. } := D.core1
  -- @@SCOPE END

  add_curve weierstrass_curve
  add_curveneg weierstrass_neg
  add_curveadd weierstrass_add

  let p_224k1 ← define r"p_224k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFE56D"
  let n_224k1 ← define r"n_224k1 = 0x010000000000000000000000000001DCE8D2EC6184CAF0A971769FB1F7"
  let G_224K1 ← define r"G_224K1 = SOME(&0xA1455B334DF099DF30FC28A169A467E9E47075A90F7E650EB6B7A45C:int,&0x7E089FED7FBA344282CAFBD6F7E319F7C0B0BD59E2CA4BDB556D61A5:int)"

  /- Primality of the field characteristic and group order. -/

  let P_224K1 ← prove
   r"p_224k1 = 2 EXP 224 - 2 EXP 32 - 6803"
   (← do
    pure (REWRITE_TAC [p_224k1] THEN CONV_TAC NUM_REDUCE_CONV))

  let P_224K1_ALT ← prove
   r"p_224k1 =
   2 EXP 224 - 2 EXP 32 - 2 EXP 12 -
   2 EXP 11 - 2 EXP 9 - 2 EXP 7 - 2 EXP 4 - 2 - 1"
   (← do
    pure (REWRITE_TAC [p_224k1] THEN CONV_TAC NUM_REDUCE_CONV))

  -- `time prove (goal, tac)`: the tactic is built before `time` runs
  let PRIME_P224K1 ← do
    let tac ← do
      pure (REWRITE_TAC [p_224k1] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (fun t => (PRIME_RULE
       ["2", "3", "5", "7", "11", "13", "19", "23", "29", "37", "41", "47",
        "59", "79", "83", "89", "101", "113", "131", "163", "167", "227",
        "419", "821", "1163", "1471", "1601", "1777", "3001", "3137", "10663",
        "10903", "14983", "17293", "21347", "43613", "48847", "82837",
        "7599533", "42252061", "17042913689", "34085827379",
        "156976040219402488243", "31670999344427766303479",
        "30974237358850355444802463",
        "9743875111334057846550285755748171501325144788037"] t).run))
    ExceptT.mk (HolCore.Lib.time (fun (_ : Unit) =>
     (prove r"prime p_224k1" tac).run) ())

  let PRIME_N224K1 ← do
    let tac ← do
      pure (REWRITE_TAC [n_224k1] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (fun t => (PRIME_RULE
       ["2", "3", "5", "7", "11", "13", "17", "19", "23", "31", "41", "61",
        "73", "151", "163", "191", "193", "239", "311", "353", "367", "479",
        "1013", "1511", "2027", "3023", "3067", "9199", "9923", "17573",
        "34231", "59539", "120047", "252913", "478453", "2218883", "2396171",
        "4167731", "4437767", "10083949", "12019933", "21244693", "33341849",
        "6058046233", "24281921209346341", "58597812472881879287",
        "2514514399252200308862687893991356095647329471",
        "4493324444525106632444502514503273391085054513853345758165826444713"] t).run))
    ExceptT.mk (HolCore.Lib.time (fun (_ : Unit) =>
     (prove r"prime n_224k1" tac).run) ())

  /- Definition of the curve group and proof of its key properties. -/

  let p224k1_group ← define
   r"p224k1_group = weierstrass_group(integer_mod_ring p_224k1,&0,&5)"

  let P224K1_GROUP ← prove
   r"group_carrier p224k1_group =
     weierstrass_curve(integer_mod_ring p_224k1,&0,&5) /\
   group_id p224k1_group =
     NONE /\
   group_inv p224k1_group =
     weierstrass_neg(integer_mod_ring p_224k1,&0,&5) /\
   group_mul p224k1_group =
     weierstrass_add(integer_mod_ring p_224k1,&0,&5)"
   (← do
    pure (REWRITE_TAC [p224k1_group] THEN
    MATCH_MP_TAC WEIERSTRASS_GROUP THEN
    REWRITE_TAC [FIELD_INTEGER_MOD_RING, INTEGER_MOD_RING_CHAR, PRIME_P224K1] THEN
    REWRITE_TAC [p_224k1, weierstrass_nonsingular] THEN
    SIMP_TAC [INTEGER_MOD_RING_CLAUSES, ARITH, IN_ELIM_THM] THEN
    CONV_TAC INT_REDUCE_CONV))

  add_ecgroup [p_224k1] P224K1_GROUP

  -- @@RETURN BEGIN
  return { p_224k1, n_224k1, G_224K1, P_224K1, P_224K1_ALT, PRIME_P224K1, PRIME_N224K1,
           p224k1_group, P224K1_GROUP }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- No 2-torsion, the generator and its order, the group's order and          -/
/- structure.  (secp224k1.ml)                                                -/
/- ------------------------------------------------------------------------- -/

structure Secp224k1Group where
  -- @@FIELDS
  NO_ROOTS_224K1 : thm
  GENERATOR_IN_GROUP_CARRIER_224K1 : thm
  GROUP_ELEMENT_ORDER_G224K1 : thm
  FINITE_GROUP_CARRIER_P224K1 : thm
  SIZE_P224K1_GROUP : thm
  P224K1_GROUP_ORDER : thm
  P224K1_GROUP_ELEMENT_ORDER : thm
  GENERATED_P224K1_GROUP : thm
  CYCLIC_P224K1_GROUP : thm
  ABELIAN_P224K1_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupSecp224k1Group [HolBase] (D : Secp224k1Deps) (BSecp224k1Defs : Secp224k1Defs) :
    ExceptT String IO Secp224k1Group := do
  -- @@SCOPE BEGIN
  let { ASM_INT_ARITH_TAC, ECGROUP_CARRIER_CONV, ECGROUP_POW_CONV,
        EXCLUDE_MODULAR_CUBIC_ROOTS_TAC, INTEGER_RULE, INT_ARITH, INT_REDUCE_CONV,
        INT_REM_DOWN_CONV, MESON_TAC, NUM_REDUCE_CONV, .. } := D
  let { ARITH, CARD_BOUND_WEIERSTRASS_CURVE, CARD_INTEGER_MOD_RING, COPRIME_2,
        CYCLIC_GROUP_ALT, CYCLIC_IMP_ABELIAN_GROUP, FIELD_INTEGER_MOD_RING,
        FINITE_INTEGER_MOD_RING, FINITE_WEIERSTRASS_CURVE, FORALL_OPTION_THM,
        FORALL_PAIR_THM, GROUP_ADHOC_ORDER_UNIQUE_LEMMA, GROUP_ELEMENT_ORDER_PRIME,
        GROUP_ELEMENT_ORDER_UNIQUE_PRIME, HAS_SIZE, IMP_CONJ_ALT, IN,
        INTEGER_MOD_RING_CLAUSES, INT_ADD_LID, INT_DIVIDES_LE, INT_MUL_LZERO,
        INT_REM_EQ, INT_REM_LT, INT_REM_ZERO, IN_INTEGER_MOD_RING_CARRIER, LET_TRANS,
        PAIR_EQ, SUBGROUP_GENERATED_ELEMENT_ORDER, num_coprime, option_DISTINCT,
        option_INJ, weierstrass_curve, weierstrass_neg, .. } := D.core1
  let { G_224K1, P224K1_GROUP, PRIME_N224K1, PRIME_P224K1, n_224k1, p_224k1, .. } := BSecp224k1Defs
  -- @@SCOPE END

  let NO_ROOTS_224K1 ← prove
   r"!x:int. ~((x pow 3 + &5 == &0) (mod &p_224k1))"
   (← do
    pure (← EXCLUDE_MODULAR_CUBIC_ROOTS_TAC PRIME_P224K1 [p_224k1]))

  let GENERATOR_IN_GROUP_CARRIER_224K1 ← prove
   r"G_224K1 IN group_carrier p224k1_group"
   (← do
    pure (REWRITE_TAC [G_224K1] THEN CONV_TAC ECGROUP_CARRIER_CONV))

  let GROUP_ELEMENT_ORDER_G224K1 ← prove
   r"group_element_order p224k1_group G_224K1 = n_224k1"
   (← do
    pure (SIMP_TAC [GROUP_ELEMENT_ORDER_UNIQUE_PRIME,
                    GENERATOR_IN_GROUP_CARRIER_224K1, PRIME_N224K1] THEN
    REWRITE_TAC [G_224K1, ← liftExcept (el 1 (CONJUNCTS P224K1_GROUP)),
                 option_DISTINCT] THEN
    REWRITE_TAC [n_224k1] THEN CONV_TAC (LAND_CONV ECGROUP_POW_CONV) THEN
    REFL_TAC))

  let FINITE_GROUP_CARRIER_P224K1 ← prove
   r"FINITE(group_carrier p224k1_group)"
   (← do
    pure (REWRITE_TAC [P224K1_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
    REWRITE_TAC [FINITE_INTEGER_MOD_RING,
                 FIELD_INTEGER_MOD_RING, PRIME_P224K1] THEN
    REWRITE_TAC [p_224k1] THEN CONV_TAC NUM_REDUCE_CONV))

  let SIZE_P224K1_GROUP ← prove
   r"group_carrier p224k1_group HAS_SIZE n_224k1"
   (← do
    -- right to left: the INTEGER_RULEs, then the INT_ARITH
    let i3 ← INTEGER_RULE
     (← q r"p divides (a * b:int) ==> coprime(a,p) ==> p divides b")
    let i2 ← INTEGER_RULE
     (← q r"(--y:int == y) (mod p) <=> p divides (&2 * y)")
    let a1 ← INT_ARITH
     (← q r"--y rem p = y ==> y rem p = y ==> (--y rem p = y rem p)")
    pure (MATCH_MP_TAC GROUP_ADHOC_ORDER_UNIQUE_LEMMA THEN
    EXISTS_TAC (← q r"G_224K1:(int#int)option") THEN
    REWRITE_TAC [GENERATOR_IN_GROUP_CARRIER_224K1,
                 GROUP_ELEMENT_ORDER_G224K1,
                 FINITE_GROUP_CARRIER_P224K1] THEN
    REWRITE_TAC [P224K1_GROUP] THEN CONJ_TAC THENL
     [wPart lhand (fun t => do lhand (← rand t)) CARD_BOUND_WEIERSTRASS_CURVE THEN
      REWRITE_TAC [FINITE_INTEGER_MOD_RING, FIELD_INTEGER_MOD_RING] THEN
      REWRITE_TAC [PRIME_P224K1] THEN ANTS_TAC THENL
       [REWRITE_TAC [p_224k1] THEN CONV_TAC NUM_REDUCE_CONV,
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] LET_TRANS)] THEN
      SIMP_TAC [CARD_INTEGER_MOD_RING, p_224k1, ARITH] THEN
      REWRITE_TAC [n_224k1] THEN CONV_TAC NUM_REDUCE_CONV,
      REWRITE_TAC [FORALL_OPTION_THM, IN, FORALL_PAIR_THM] THEN
      REWRITE_TAC [weierstrass_curve, weierstrass_neg, option_DISTINCT] THEN
      MAP_EVERY X_GEN_TAC [← q r"x:int", ← q r"y:int"] THEN REWRITE_TAC [option_INJ] THEN
      REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER, INTEGER_MOD_RING_CLAUSES] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC [p_224k1, PAIR_EQ] THEN
      CONV_TAC INT_REDUCE_CONV] THEN
    ASM_CASES_TAC (← q r"y:int = &0") THENL
     [ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV THEN
      DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
      CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC (← SPEC (← q r"x:int") NO_ROOTS_224K1) THEN
      REWRITE_TAC [INT_MUL_LZERO, INT_ADD_LID] THEN
      REWRITE_TAC [← GSYM INT_REM_EQ, p_224k1, INT_REM_ZERO],
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o MATCH_MP a1) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC [INT_REM_LT], ALL_TAC] THEN
      REWRITE_TAC [INT_REM_EQ, i2] THEN
      DISCH_THEN (MP_TAC o MATCH_MP i3) THEN
      REWRITE_TAC [← GSYM num_coprime, ARITH, COPRIME_2] THEN
      DISCH_THEN (MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]))

  let P224K1_GROUP_ORDER ← prove
   r"CARD(group_carrier p224k1_group) = n_224k1"
   (← do
    pure (REWRITE_TAC [← REWRITE_RULE [HAS_SIZE] SIZE_P224K1_GROUP]))

  let P224K1_GROUP_ELEMENT_ORDER ← prove
   r"!P. P IN group_carrier p224k1_group
       ==> group_element_order p224k1_group P =
           if P = group_id p224k1_group then 1 else n_224k1"
   (← do
    pure (MESON_TAC [SIZE_P224K1_GROUP, HAS_SIZE, GROUP_ELEMENT_ORDER_PRIME,
                     PRIME_N224K1]))

  let GENERATED_P224K1_GROUP ← prove
   r"subgroup_generated p224k1_group {G_224K1} = p224k1_group"
   (← do
    pure (SIMP_TAC [SUBGROUP_GENERATED_ELEMENT_ORDER,
                    GENERATOR_IN_GROUP_CARRIER_224K1,
                    FINITE_GROUP_CARRIER_P224K1] THEN
    REWRITE_TAC [GROUP_ELEMENT_ORDER_G224K1,
                 ← REWRITE_RULE [HAS_SIZE] SIZE_P224K1_GROUP]))

  let CYCLIC_P224K1_GROUP ← prove
   r"cyclic_group p224k1_group"
   (← do
    pure (MESON_TAC [CYCLIC_GROUP_ALT, GENERATED_P224K1_GROUP]))

  let ABELIAN_P224K1_GROUP ← prove
   r"abelian_group p224k1_group"
   (← do
    pure (MESON_TAC [CYCLIC_P224K1_GROUP, CYCLIC_IMP_ABELIAN_GROUP]))

  -- @@RETURN BEGIN
  return { NO_ROOTS_224K1, GENERATOR_IN_GROUP_CARRIER_224K1, GROUP_ELEMENT_ORDER_G224K1,
           FINITE_GROUP_CARRIER_P224K1, SIZE_P224K1_GROUP, P224K1_GROUP_ORDER,
           P224K1_GROUP_ELEMENT_ORDER, GENERATED_P224K1_GROUP, CYCLIC_P224K1_GROUP,
           ABELIAN_P224K1_GROUP }
  -- @@RETURN END

end HolEC.Secp224k1
