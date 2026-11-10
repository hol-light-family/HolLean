/- ========================================================================= -/
/- The NIST-recommended elliptic curve P-224, aka secp224r1.               -/
/- ========================================================================= -/
/- File: HolEC/NistP224.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/nistp224.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/weierstrass.ml, EC/excluderoots.ml, EC/computegroup.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.NistP224 fills them).

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

namespace HolEC.NistP224

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

/-- What nistp224.ml uses from Session besides theorems. -/
structure NistP224Deps where
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
/- curve group.  (nistp224.ml)                                               -/
/- ------------------------------------------------------------------------- -/

structure NistP224Defs where
  -- @@FIELDS
  p_224 : thm
  n_224 : thm
  SEED_224 : thm
  c_224 : thm
  b_224 : thm
  G_224 : thm
  P_224 : thm
  PRIME_P224 : thm
  PRIME_N224 : thm
  SANITY_CHECK_224 : thm
  p224_group : thm
  P224_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupNistP224Defs [HolBase] (D : NistP224Deps) :
    ExceptT String IO NistP224Defs := do
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

  let p_224 ← new_definition r"p_224 = 26959946667150639794667015087019630673557916260026308143510066298881"
  let n_224 ← new_definition r"n_224 = 26959946667150639794667015087019625940457807714424391721682722368061"
  let SEED_224 ← new_definition r"SEED_224 = 0xbd71344799d5c7fcdc45b59fa3b9ab8f6a948bc5"
  let c_224 ← new_definition r"c_224 = 0x5b056c7e11dd68f40469ee7f3c7a7d74f7d121116506d031218291fb"
  let b_224 ← new_definition r"b_224 = 0xb4050a850c04b3abf54132565044b0b7d7bfd8ba270b39432355ffb4"
  let G_224 ← new_definition r"G_224 = SOME(&0xb70e0cbd6bb4bf7f321390b94a03c1d356c21122343280d6115c1d21:int,&0xbd376388b5f723fb4c22dfe6cd4375a05a07476444d5819985007e34:int)"

  /- Primality of the field characteristic and group order. -/

  let P_224 ← prove
   r"p_224 = 2 EXP 224 - 2 EXP 96 + 1"
   (← do
    pure (REWRITE_TAC [p_224] THEN CONV_TAC NUM_REDUCE_CONV))

  -- `time prove (goal, tac)`: the tactic is built before `time` runs
  let PRIME_P224 ← do
    let tac ← do
      pure (REWRITE_TAC [p_224] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (fun t => (PRIME_RULE
       ["2", "3", "5", "7", "11", "17", "23", "31", "43", "47", "173", "257",
        "347", "373", "641", "727", "16657", "17449", "65537", "166571",
        "274177", "2998279", "6700417", "67280421310721"] t).run))
    ExceptT.mk (HolCore.Lib.time (fun (_ : Unit) =>
     (prove r"prime p_224" tac).run) ())

  let PRIME_N224 ← do
    let tac ← do
      pure (REWRITE_TAC [n_224] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (fun t => (PRIME_RULE
       ["2", "3", "5", "7", "11", "13", "17", "23", "29", "31", "37", "41",
        "43", "47", "61", "67", "89", "101", "127", "139", "173", "239", "269",
        "347", "349", "509", "631", "659", "1303", "1319", "2089", "2153",
        "2707", "3433", "10909", "20599", "30859", "85999", "87739", "145091",
        "166823", "11105363", "13928737", "821796863", "432621809776543",
        "136401162692544977256234449", "34646440928557194402992574983797",
        "375503554633724504423937478103159147573209",
        "50520606258875818707470860153287666700917696099933389351507"] t).run))
    ExceptT.mk (HolCore.Lib.time (fun (_ : Unit) =>
     (prove r"prime n_224" tac).run) ())

  /- Basic sanity check on the (otherwise unused) c parameter. -/

  let SANITY_CHECK_224 ← prove
   r"(&b_224 pow 2 * &c_224:int == -- &27) (mod &p_224)"
   (← do
    pure (REWRITE_TAC [G_224, p_224, b_224, c_224] THEN
    REWRITE_TAC [← GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV))

  /- Definition of the curve group and proof of its key properties. -/

  let p224_group ← define
   r"p224_group =
   weierstrass_group
    (integer_mod_ring p_224,
     ring_neg (integer_mod_ring p_224) (&3),
     &b_224)"

  let P224_GROUP ← prove
   r"group_carrier p224_group =
     weierstrass_curve
      (integer_mod_ring p_224,ring_neg (integer_mod_ring p_224) (&3),&b_224) /\
   group_id p224_group =
     NONE /\
   group_inv p224_group =
     weierstrass_neg
      (integer_mod_ring p_224,ring_neg (integer_mod_ring p_224) (&3),&b_224) /\
   group_mul p224_group =
     weierstrass_add
      (integer_mod_ring p_224,ring_neg (integer_mod_ring p_224) (&3),&b_224)"
   (← do
    pure (REWRITE_TAC [p224_group] THEN
    MATCH_MP_TAC WEIERSTRASS_GROUP THEN
    REWRITE_TAC [FIELD_INTEGER_MOD_RING, INTEGER_MOD_RING_CHAR, PRIME_P224] THEN
    REWRITE_TAC [p_224, b_224, weierstrass_nonsingular] THEN
    SIMP_TAC [INTEGER_MOD_RING_CLAUSES, ARITH, IN_ELIM_THM] THEN
    CONV_TAC INT_REDUCE_CONV))

  add_ecgroup [p_224, b_224] P224_GROUP

  -- @@RETURN BEGIN
  return { p_224, n_224, SEED_224, c_224, b_224, G_224, P_224, PRIME_P224, PRIME_N224,
           SANITY_CHECK_224, p224_group, P224_GROUP }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- No 2-torsion, the generator and its order, and the group's order and      -/
/- structure.  (nistp224.ml)                                                 -/
/- ------------------------------------------------------------------------- -/

structure NistP224Group where
  -- @@FIELDS
  NO_ROOTS_P224 : thm
  GENERATOR_IN_GROUP_CARRIER_224 : thm
  GROUP_ELEMENT_ORDER_G224 : thm
  FINITE_GROUP_CARRIER_P224 : thm
  SIZE_P224_GROUP : thm
  P256_GROUP_ORDER : thm
  P224_GROUP_ELEMENT_ORDER : thm
  GENERATED_P224_GROUP : thm
  CYCLIC_P224_GROUP : thm
  ABELIAN_P224_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupNistP224Group [HolBase] (D : NistP224Deps) (BNistP224Defs : NistP224Defs) :
    ExceptT String IO NistP224Group := do
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
  let { G_224, P224_GROUP, PRIME_N224, PRIME_P224, b_224, n_224, p_224, .. } := BNistP224Defs
  -- @@SCOPE END

  let NO_ROOTS_P224 ← prove
   r"!x:int. ~((x pow 3 - &3 * x + &b_224 == &0) (mod &p_224))"
   (← do
    pure (← EXCLUDE_MODULAR_CUBIC_ROOTS_TAC PRIME_P224 [p_224, b_224]))

  let GENERATOR_IN_GROUP_CARRIER_224 ← prove
   r"G_224 IN group_carrier p224_group"
   (← do
    pure (REWRITE_TAC [G_224] THEN CONV_TAC ECGROUP_CARRIER_CONV))

  let GROUP_ELEMENT_ORDER_G224 ← prove
   r"group_element_order p224_group G_224 = n_224"
   (← do
    pure (SIMP_TAC [GROUP_ELEMENT_ORDER_UNIQUE_PRIME, GENERATOR_IN_GROUP_CARRIER_224,
                    PRIME_N224] THEN
    REWRITE_TAC [G_224, ← liftExcept (el 1 (CONJUNCTS P224_GROUP)), option_DISTINCT] THEN
    REWRITE_TAC [n_224] THEN CONV_TAC (LAND_CONV ECGROUP_POW_CONV) THEN
    REFL_TAC))

  let FINITE_GROUP_CARRIER_P224 ← prove
   r"FINITE(group_carrier p224_group)"
   (← do
    pure (REWRITE_TAC [P224_GROUP] THEN MATCH_MP_TAC FINITE_WEIERSTRASS_CURVE THEN
    REWRITE_TAC [FINITE_INTEGER_MOD_RING, FIELD_INTEGER_MOD_RING, PRIME_P224] THEN
    REWRITE_TAC [p_224] THEN CONV_TAC NUM_REDUCE_CONV))

  let SIZE_P224_GROUP ← prove
   r"group_carrier p224_group HAS_SIZE n_224"
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
    EXISTS_TAC (← q r"G_224:(int#int)option") THEN
    REWRITE_TAC [GENERATOR_IN_GROUP_CARRIER_224, GROUP_ELEMENT_ORDER_G224,
                 FINITE_GROUP_CARRIER_P224] THEN
    REWRITE_TAC [P224_GROUP] THEN CONJ_TAC THENL
     [wPart lhand (fun t => do lhand (← rand t)) CARD_BOUND_WEIERSTRASS_CURVE THEN
      REWRITE_TAC [FINITE_INTEGER_MOD_RING, FIELD_INTEGER_MOD_RING] THEN
      REWRITE_TAC [PRIME_P224] THEN ANTS_TAC THENL
       [REWRITE_TAC [p_224] THEN CONV_TAC NUM_REDUCE_CONV,
        MATCH_MP_TAC (← REWRITE_RULE [IMP_CONJ_ALT] LET_TRANS)] THEN
      SIMP_TAC [CARD_INTEGER_MOD_RING, p_224, ARITH] THEN
      REWRITE_TAC [n_224] THEN CONV_TAC NUM_REDUCE_CONV,
      REWRITE_TAC [FORALL_OPTION_THM, IN, FORALL_PAIR_THM] THEN
      REWRITE_TAC [weierstrass_curve, weierstrass_neg, option_DISTINCT] THEN
      MAP_EVERY X_GEN_TAC [← q r"x:int", ← q r"y:int"] THEN REWRITE_TAC [option_INJ] THEN
      REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER, INTEGER_MOD_RING_CLAUSES] THEN
      CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC [p_224, PAIR_EQ] THEN
      CONV_TAC INT_REDUCE_CONV] THEN
    ASM_CASES_TAC (← q r"y:int = &0") THENL
     [ASM_REWRITE_TAC [] THEN CONV_TAC INT_REDUCE_CONV THEN
      DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o SYM)) THEN
      CONV_TAC INT_REM_DOWN_CONV THEN MP_TAC (← SPEC (← q r"x:int") NO_ROOTS_P224) THEN
      REWRITE_TAC [a1] THEN
      REWRITE_TAC [← GSYM INT_REM_EQ, p_224, INT_REM_ZERO],
      STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o MATCH_MP a2) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC [INT_REM_LT], ALL_TAC] THEN
      REWRITE_TAC [INT_REM_EQ, i3] THEN
      DISCH_THEN (MP_TAC o MATCH_MP i4) THEN
      REWRITE_TAC [← GSYM num_coprime, ARITH, COPRIME_2] THEN
      DISCH_THEN (MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC]))

  let P256_GROUP_ORDER ← prove
   r"CARD(group_carrier p224_group) = n_224"
   (← do
    pure (REWRITE_TAC [← REWRITE_RULE [HAS_SIZE] SIZE_P224_GROUP]))

  let P224_GROUP_ELEMENT_ORDER ← prove
   r"!P. P IN group_carrier p224_group
       ==> group_element_order p224_group P =
           if P = group_id p224_group then 1 else n_224"
   (← do
    pure (MESON_TAC [SIZE_P224_GROUP, HAS_SIZE, GROUP_ELEMENT_ORDER_PRIME, PRIME_N224]))

  let GENERATED_P224_GROUP ← prove
   r"subgroup_generated p224_group {G_224} = p224_group"
   (← do
    pure (SIMP_TAC [SUBGROUP_GENERATED_ELEMENT_ORDER,
                    GENERATOR_IN_GROUP_CARRIER_224,
                    FINITE_GROUP_CARRIER_P224] THEN
    REWRITE_TAC [GROUP_ELEMENT_ORDER_G224,
                 ← REWRITE_RULE [HAS_SIZE] SIZE_P224_GROUP]))

  let CYCLIC_P224_GROUP ← prove
   r"cyclic_group p224_group"
   (← do
    pure (MESON_TAC [CYCLIC_GROUP_ALT, GENERATED_P224_GROUP]))

  let ABELIAN_P224_GROUP ← prove
   r"abelian_group p224_group"
   (← do
    pure (MESON_TAC [CYCLIC_P224_GROUP, CYCLIC_IMP_ABELIAN_GROUP]))

  -- @@RETURN BEGIN
  return { NO_ROOTS_P224, GENERATOR_IN_GROUP_CARRIER_224, GROUP_ELEMENT_ORDER_G224,
           FINITE_GROUP_CARRIER_P224, SIZE_P224_GROUP, P256_GROUP_ORDER,
           P224_GROUP_ELEMENT_ORDER, GENERATED_P224_GROUP, CYCLIC_P224_GROUP,
           ABELIAN_P224_GROUP }
  -- @@RETURN END

end HolEC.NistP224
