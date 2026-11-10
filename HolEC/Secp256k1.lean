/- ========================================================================= -/
/- The SECG-recommended elliptic curve secp256k1.                          -/
/- ========================================================================= -/
/- File: HolEC/Secp256k1.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/secp256k1.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/weierstrass.ml, EC/excluderoots.ml, EC/computegroup.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.Secp256k1 fills them).

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

namespace HolEC.Secp256k1

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ABELIAN_GROUP_HOMOMORPHISM_POWERING ARITH CARD_BOUND_WEIERSTRASS_CURVE
   CARD_INTEGER_MOD_RING COPRIME_2 CYCLIC_GROUP_ALT CYCLIC_IMP_ABELIAN_GROUP
   ETA_AX FIELD_INTEGER_MOD_RING FINITE_INTEGER_MOD_RING
   FINITE_WEIERSTRASS_CURVE FORALL_OPTION_THM FORALL_PAIR_THM FORALL_UNWIND_THM2
   GROUP_ADHOC_ORDER_UNIQUE_LEMMA GROUP_ELEMENT_ORDER_PRIME
   GROUP_ELEMENT_ORDER_UNIQUE_PRIME GROUP_ENDOMORPHISM_TRIPLEX
   GROUP_HOMOMORPHISMS_EQ_ON_GENERATORS HAS_SIZE IMP_CONJ_ALT IN
   INTEGER_MOD_RING INTEGER_MOD_RING_CHAR INTEGER_MOD_RING_CLAUSES
   INTEGER_MOD_RING_OF_NUM INTEGER_MOD_RING_POW INT_ADD_LID INT_DIVIDES_LE
   INT_MUL_LZERO INT_REM_EQ INT_REM_LT INT_REM_ZERO IN_ELIM_THM IN_INSERT
   IN_INTEGER_MOD_RING_CARRIER IN_SING LET_TRANS PAIR_EQ
   SUBGROUP_GENERATED_ELEMENT_ORDER WEIERSTRASS_GROUP group_endomorphism
   num_coprime option_DISTINCT option_INJ weierstrass_add weierstrass_curve
   weierstrass_neg weierstrass_nonsingular weierstrass_triplex : thm)
  deriving Inhabited

/-- What secp256k1.ml uses from Session besides theorems. -/
structure Secp256k1Deps where
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
/- (https://www.secg.org/sec2-v2.pdf), the parameters beta and lambda for an -/
/- endomorphism, primality of the field characteristic and group order, and  -/
/- the curve group.  (secp256k1.ml 1-102)                                    -/
/- ------------------------------------------------------------------------- -/

structure Secp256k1Defs where
  -- @@FIELDS
  p_256k1 : thm
  n_256k1 : thm
  G_256K1 : thm
  secp256k1 : thm
  p256k1_beta : thm
  p256k1_lambda : thm
  P_256K1 : thm
  P_256K1_ALT : thm
  PRIME_P256K1 : thm
  PRIME_N256K1 : thm
  p256k1_group : thm
  P256K1_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupSecp256k1Defs [HolBase] (D : Secp256k1Deps) :
    ExceptT String IO Secp256k1Defs := do
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

  let p_256k1 ← define r"p_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"
  let n_256k1 ← define r"n_256k1 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"
  let G_256K1 ← define r"G_256K1 = SOME(&0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798:int,&0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8:int)"

  let secp256k1 ← define
   r"secp256k1 = (integer_mod_ring p_256k1,&0:int,&7:int)"

  /- Also parameters beta and lambda for an endomorphism. -/

  let p256k1_beta ← define r"p256k1_beta = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee"
  let p256k1_lambda ← define r"p256k1_lambda = 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72"

  /- Primality of the field characteristic and group order. -/

  let P_256K1 ← prove
   r"p_256k1 = 2 EXP 256 - 2 EXP 32 - 977"
   (← do
    pure (REWRITE_TAC [p_256k1] THEN CONV_TAC NUM_REDUCE_CONV))

  let P_256K1_ALT ← prove
   r"p_256k1 =
   2 EXP 256 - 2 EXP 32 - 2 EXP 9 - 2 EXP 8 - 2 EXP 7 - 2 EXP 6 - 2 EXP 4 - 1"
   (← do
    pure (REWRITE_TAC [p_256k1] THEN CONV_TAC NUM_REDUCE_CONV))

  -- `time prove (goal, tac)`: the tactic is built before `time` runs
  let PRIME_P256K1 ← do
    let tac ← do
      pure (REWRITE_TAC [p_256k1] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (fun t => (PRIME_RULE
       ["2", "3", "5", "7", "11", "13", "17", "19", "29", "31", "41", "53", "67",
        "83", "97", "101", "103", "131", "239", "271", "419", "443", "887", "971",
        "1373", "1627", "2621", "2657", "4423", "5323", "7723", "13441", "20113",
        "24809", "41201", "96557", "1206781", "7240687", "13331831", "107590001",
        "173378833005251801", "22149492674086928081353",
        "132896956044521568488119", "255515944373312847190720520512484175977",
        "205115282021455665897114700593932402728804164701536103180137503955397371"] t).run))
    ExceptT.mk (HolCore.Lib.time (fun (_ : Unit) =>
     (prove r"prime p_256k1" tac).run) ())

  let PRIME_N256K1 ← do
    let tac ← do
      pure (REWRITE_TAC [n_256k1] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (fun t => (PRIME_RULE
       ["2", "3", "5", "7", "11", "13", "17", "19", "23", "29", "37", "41", "59",
        "67", "73", "97", "109", "113", "149", "199", "293", "461", "631", "797",
        "1409", "1871", "2011", "2731", "2861", "4051", "9349", "16699", "28181",
        "85831", "120233", "305873", "1627771", "4681609", "44706919",
        "545358713", "297159362677", "107361793816595537",
        "174723607534414371449", "29047611873442575647497758179",
        "341948486974166000522343609283189"] t).run))
    ExceptT.mk (HolCore.Lib.time (fun (_ : Unit) =>
     (prove r"prime n_256k1" tac).run) ())

  /- Definition of the curve group and proof of its key properties. -/

  let p256k1_group ← define
   r"p256k1_group = weierstrass_group(integer_mod_ring p_256k1,&0,&7)"

  let P256K1_GROUP ← prove
   r"group_carrier p256k1_group =
     weierstrass_curve(integer_mod_ring p_256k1,&0,&7) /\
   group_id p256k1_group =
     NONE /\
   group_inv p256k1_group =
     weierstrass_neg(integer_mod_ring p_256k1,&0,&7) /\
   group_mul p256k1_group =
     weierstrass_add(integer_mod_ring p_256k1,&0,&7)"
   (← do
    pure (REWRITE_TAC [p256k1_group] THEN
    MATCH_MP_TAC WEIERSTRASS_GROUP THEN
    REWRITE_TAC [FIELD_INTEGER_MOD_RING, INTEGER_MOD_RING_CHAR, PRIME_P256K1] THEN
    REWRITE_TAC [p_256k1, weierstrass_nonsingular] THEN
    SIMP_TAC [INTEGER_MOD_RING_CLAUSES, ARITH, IN_ELIM_THM] THEN
    CONV_TAC INT_REDUCE_CONV))

  add_ecgroup [p_256k1] P256K1_GROUP

  -- @@RETURN BEGIN
  return { p_256k1, n_256k1, G_256K1, secp256k1, p256k1_beta, p256k1_lambda, P_256K1,
           P_256K1_ALT, PRIME_P256K1, PRIME_N256K1, p256k1_group, P256K1_GROUP }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- No 2-torsion, the generator and its order, the group's order and          -/
/- structure, and the easily computable endomorphism.                        -/
/- (secp256k1.ml 103-213)                                                    -/
/- ------------------------------------------------------------------------- -/

structure Secp256k1Group where
  -- @@FIELDS
  NO_ROOTS_256K1 : thm
  GENERATOR_IN_GROUP_CARRIER_256K1 : thm
  GROUP_ELEMENT_ORDER_G256K1 : thm
  FINITE_GROUP_CARRIER_P256K1 : thm
  SIZE_P256K1_GROUP : thm
  P256K1_GROUP_ORDER : thm
  P256K1_GROUP_ELEMENT_ORDER : thm
  GENERATED_P256K1_GROUP : thm
  CYCLIC_P256K1_GROUP : thm
  ABELIAN_P256K1_GROUP : thm
  GROUP_ENDOMORPHISM_TRIPLEX_BETA : thm
  P256K1_TRIPLEX_BETA : thm
  deriving Inhabited

@[nospecialize]
def setupSecp256k1Group [HolBase] (D : Secp256k1Deps) (BSecp256k1Defs : Secp256k1Defs) :
    ExceptT String IO Secp256k1Group := do
  -- @@SCOPE BEGIN
  let { ASM_INT_ARITH_TAC, ECGROUP_CARRIER_CONV, ECGROUP_POW_CONV,
        EXCLUDE_MODULAR_CUBIC_ROOTS_TAC, INTEGER_RULE, INT_ARITH, INT_REDUCE_CONV,
        INT_REM_DOWN_CONV, MESON_TAC, NUM_REDUCE_CONV, .. } := D
  let { ABELIAN_GROUP_HOMOMORPHISM_POWERING, ARITH, CARD_BOUND_WEIERSTRASS_CURVE,
        CARD_INTEGER_MOD_RING, COPRIME_2, CYCLIC_GROUP_ALT, CYCLIC_IMP_ABELIAN_GROUP,
        ETA_AX, FIELD_INTEGER_MOD_RING, FINITE_INTEGER_MOD_RING,
        FINITE_WEIERSTRASS_CURVE, FORALL_OPTION_THM, FORALL_PAIR_THM,
        FORALL_UNWIND_THM2, GROUP_ADHOC_ORDER_UNIQUE_LEMMA, GROUP_ELEMENT_ORDER_PRIME,
        GROUP_ELEMENT_ORDER_UNIQUE_PRIME, GROUP_ENDOMORPHISM_TRIPLEX,
        GROUP_HOMOMORPHISMS_EQ_ON_GENERATORS, HAS_SIZE, IMP_CONJ_ALT, IN,
        INTEGER_MOD_RING, INTEGER_MOD_RING_CHAR, INTEGER_MOD_RING_CLAUSES,
        INTEGER_MOD_RING_OF_NUM, INTEGER_MOD_RING_POW, INT_ADD_LID, INT_DIVIDES_LE,
        INT_MUL_LZERO, INT_REM_EQ, INT_REM_LT, INT_REM_ZERO, IN_ELIM_THM, IN_INSERT,
        IN_INTEGER_MOD_RING_CARRIER, IN_SING, LET_TRANS, PAIR_EQ,
        SUBGROUP_GENERATED_ELEMENT_ORDER, group_endomorphism, num_coprime,
        option_DISTINCT, option_INJ, weierstrass_curve, weierstrass_neg,
        weierstrass_nonsingular, weierstrass_triplex, .. } := D.core1
  let { G_256K1, P256K1_GROUP, PRIME_N256K1, PRIME_P256K1, n_256k1, p256k1_beta,
        p256k1_group, p256k1_lambda, p_256k1, .. } := BSecp256k1Defs
  -- @@SCOPE END

  let NO_ROOTS_256K1 ← prove
   r"!x:int. ~((x pow 3 + &7 == &0) (mod &p_256k1))"
   (← do
    pure (← EXCLUDE_MODULAR_CUBIC_ROOTS_TAC PRIME_P256K1 [p_256k1]))

  let GENERATOR_IN_GROUP_CARRIER_256K1 ← prove
   r"G_256K1 IN group_carrier p256k1_group"
   (← do
    pure (REWRITE_TAC [G_256K1] THEN CONV_TAC ECGROUP_CARRIER_CONV))

  let GROUP_ELEMENT_ORDER_G256K1 ← prove
   r"group_element_order p256k1_group G_256K1 = n_256k1"
   (← do
    pure (SIMP_TAC [GROUP_ELEMENT_ORDER_UNIQUE_PRIME,
                    GENERATOR_IN_GROUP_CARRIER_256K1, PRIME_N256K1] THEN
    REWRITE_TAC [G_256K1, ← liftExcept (el 1 (CONJUNCTS P256K1_GROUP)),
                 option_DISTINCT] THEN
    REWRITE_TAC [n_256k1] THEN CONV_TAC (LAND_CONV ECGROUP_POW_CONV) THEN
    REFL_TAC))

  let FINITE_GROUP_CARRIER_P256K1 ← prove
   r"FINITE(group_carrier p256k1_group)"
   (← do
    pure (REWRITE_TAC [P256K1_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
    REWRITE_TAC [FINITE_INTEGER_MOD_RING,
                 FIELD_INTEGER_MOD_RING, PRIME_P256K1] THEN
    REWRITE_TAC [p_256k1] THEN CONV_TAC NUM_REDUCE_CONV))

  let SIZE_P256K1_GROUP ← prove
   r"group_carrier p256k1_group HAS_SIZE n_256k1"
   (← do
    -- right to left: the INTEGER_RULEs, then the INT_ARITH
    let i3 ← INTEGER_RULE
     (← q r"p divides (a * b:int) ==> coprime(a,p) ==> p divides b")
    let i2 ← INTEGER_RULE
     (← q r"(--y:int == y) (mod p) <=> p divides (&2 * y)")
    let a1 ← INT_ARITH
     (← q r"--y rem p = y ==> y rem p = y ==> (--y rem p = y rem p)")
    pure (MATCH_MP_TAC GROUP_ADHOC_ORDER_UNIQUE_LEMMA THEN
    EXISTS_TAC (← q r"G_256K1:(int#int)option") THEN
    REWRITE_TAC [GENERATOR_IN_GROUP_CARRIER_256K1,
                 GROUP_ELEMENT_ORDER_G256K1,
                 FINITE_GROUP_CARRIER_P256K1] THEN
    REWRITE_TAC [P256K1_GROUP] THEN CONJ_TAC THENL
     [wPart lhand (fun t => do lhand (← rand t)) CARD_BOUND_WEIERSTRASS_CURVE THEN
      REWRITE_TAC [FINITE_INTEGER_MOD_RING, FIELD_INTEGER_MOD_RING] THEN
      REWRITE_TAC [PRIME_P256K1] THEN ANTS_TAC THENL
       [REWRITE_TAC [p_256k1] THEN CONV_TAC NUM_REDUCE_CONV,
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] LET_TRANS)] THEN
      SIMP_TAC [CARD_INTEGER_MOD_RING, p_256k1, ARITH] THEN
      REWRITE_TAC [n_256k1] THEN CONV_TAC NUM_REDUCE_CONV,
      REWRITE_TAC [FORALL_OPTION_THM, IN, FORALL_PAIR_THM] THEN
      REWRITE_TAC [weierstrass_curve, weierstrass_neg, option_DISTINCT] THEN
      MAP_EVERY X_GEN_TAC [← q r"x:int", ← q r"y:int"] THEN REWRITE_TAC [option_INJ] THEN
      REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER, INTEGER_MOD_RING_CLAUSES] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC [p_256k1, PAIR_EQ] THEN
      CONV_TAC INT_REDUCE_CONV] THEN
    ASM_CASES_TAC (← q r"y:int = &0") THENL
     [ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV THEN
      DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
      CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC (← SPEC (← q r"x:int") NO_ROOTS_256K1) THEN
      REWRITE_TAC [INT_MUL_LZERO, INT_ADD_LID] THEN
      REWRITE_TAC [← GSYM INT_REM_EQ, p_256k1, INT_REM_ZERO],
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o MATCH_MP a1) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC [INT_REM_LT], ALL_TAC] THEN
      REWRITE_TAC [INT_REM_EQ, i2] THEN
      DISCH_THEN (MP_TAC o MATCH_MP i3) THEN
      REWRITE_TAC [← GSYM num_coprime, ARITH, COPRIME_2] THEN
      DISCH_THEN (MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]))

  let P256K1_GROUP_ORDER ← prove
   r"CARD(group_carrier p256k1_group) = n_256k1"
   (← do
    pure (REWRITE_TAC [← REWRITE_RULE [HAS_SIZE] SIZE_P256K1_GROUP]))

  let P256K1_GROUP_ELEMENT_ORDER ← prove
   r"!P. P IN group_carrier p256k1_group
       ==> group_element_order p256k1_group P =
           if P = group_id p256k1_group then 1 else n_256k1"
   (← do
    pure (MESON_TAC [SIZE_P256K1_GROUP, HAS_SIZE, GROUP_ELEMENT_ORDER_PRIME,
                     PRIME_N256K1]))

  let GENERATED_P256K1_GROUP ← prove
   r"subgroup_generated p256k1_group {G_256K1} = p256k1_group"
   (← do
    pure (SIMP_TAC [SUBGROUP_GENERATED_ELEMENT_ORDER,
                    GENERATOR_IN_GROUP_CARRIER_256K1,
                    FINITE_GROUP_CARRIER_P256K1] THEN
    REWRITE_TAC [GROUP_ELEMENT_ORDER_G256K1,
                 ← REWRITE_RULE [HAS_SIZE] SIZE_P256K1_GROUP]))

  let CYCLIC_P256K1_GROUP ← prove
   r"cyclic_group p256k1_group"
   (← do
    pure (MESON_TAC [CYCLIC_GROUP_ALT, GENERATED_P256K1_GROUP]))

  let ABELIAN_P256K1_GROUP ← prove
   r"abelian_group p256k1_group"
   (← do
    pure (MESON_TAC [CYCLIC_P256K1_GROUP, CYCLIC_IMP_ABELIAN_GROUP]))

  /- Easily computable endomorphism of secp256k1 curve. -/

  let GROUP_ENDOMORPHISM_TRIPLEX_BETA ← prove
   r"group_endomorphism p256k1_group
        (weierstrass_triplex (integer_mod_ring p_256k1) (&p256k1_beta))"
   (← do
    pure (REWRITE_TAC [p256k1_group] THEN MATCH_MP_TAC GROUP_ENDOMORPHISM_TRIPLEX THEN
    SIMP_TAC [INTEGER_MOD_RING, INTEGER_MOD_RING_CHAR, INTEGER_MOD_RING_POW,
              p_256k1, IN_INSERT, FIELD_INTEGER_MOD_RING, ARITH, p256k1_beta,
              IN_ELIM_THM, weierstrass_nonsingular, INTEGER_MOD_RING_OF_NUM] THEN
    REWRITE_TAC [← REWRITE_RULE [p_256k1] PRIME_P256K1] THEN
    CONV_TAC INT_REDUCE_CONV))

  let P256K1_TRIPLEX_BETA ← prove
   r"!x. x IN group_carrier p256k1_group
       ==> weierstrass_triplex (integer_mod_ring p_256k1) (&p256k1_beta) x =
           group_pow p256k1_group x p256k1_lambda"
   (← do
    pure (GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o ONCE_DEPTH_CONV)
     [← GSYM GENERATED_P256K1_GROUP] THEN
    MATCH_MP_TAC  GROUP_HOMOMORPHISMS_EQ_ON_GENERATORS THEN
    EXISTS_TAC (← q r"p256k1_group") THEN
    SIMP_TAC [ABELIAN_GROUP_HOMOMORPHISM_POWERING, ABELIAN_P256K1_GROUP] THEN
    REWRITE_TAC [← GSYM group_endomorphism] THEN
    REWRITE_TAC [GROUP_ENDOMORPHISM_TRIPLEX_BETA, ETA_AX] THEN
    REWRITE_TAC [IMP_CONJ_ALT, IN_SING, FORALL_UNWIND_THM2] THEN
    DISCH_TAC THEN
    SIMP_TAC [weierstrass_triplex, p256k1_beta, p256k1_lambda, G_256K1] THEN
    CONV_TAC (RAND_CONV ECGROUP_POW_CONV) THEN
    REWRITE_TAC [option_INJ, PAIR_EQ] THEN
    REWRITE_TAC [INTEGER_MOD_RING, p_256k1] THEN CONV_TAC INT_REDUCE_CONV))

  -- @@RETURN BEGIN
  return { NO_ROOTS_256K1, GENERATOR_IN_GROUP_CARRIER_256K1, GROUP_ELEMENT_ORDER_G256K1,
           FINITE_GROUP_CARRIER_P256K1, SIZE_P256K1_GROUP, P256K1_GROUP_ORDER,
           P256K1_GROUP_ELEMENT_ORDER, GENERATED_P256K1_GROUP, CYCLIC_P256K1_GROUP,
           ABELIAN_P256K1_GROUP, GROUP_ENDOMORPHISM_TRIPLEX_BETA, P256K1_TRIPLEX_BETA }
  -- @@RETURN END

end HolEC.Secp256k1
