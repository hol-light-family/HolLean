/- ========================================================================= -/
/- curve25519, in its plain Montgomery form.                               -/
/- ========================================================================= -/
/- File: HolEC/Curve25519.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/curve25519.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/montgomery.ml, EC/excluderoots.ml, EC/computegroup.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.Curve25519 fills them).

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

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolEC.Curve25519

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ARITH ARITH_EQ CARD_BOUND_MONTGOMERY_CURVE CARD_EQ_0 CARD_INTEGER_MOD_RING
   CONG CYCLIC_GROUP_ALT CYCLIC_IMP_ABELIAN_GROUP EULER_CRITERION
   FIELD_INTEGER_MOD_RING FINITE_INTEGER_MOD_RING FINITE_MONTGOMERY_CURVE
   GROUP_CARRIER_NONEMPTY GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER
   GROUP_ELEMENT_ORDER_MUL_EQ GROUP_ELEMENT_ORDER_UNIQUE_ALT
   GROUP_ELEMENT_ORDER_UNIQUE_PRIME HAS_SIZE IMP_CONJ_ALT INTEGER_MOD_RING
   INTEGER_MOD_RING_CHAR INTEGER_MOD_RING_CLAUSES INTEGER_MOD_RING_ROOT_EXISTS
   INT_OF_NUM_CLAUSES IN_ELIM_THM IN_INTEGER_MOD_RING_CARRIER
   LEFT_IMP_EXISTS_THM LE_MULT_RCANCEL MONTGOMERY_GROUP MULT_CLAUSES
   SUBGROUP_GENERATED_ELEMENT_ORDER divides montgomery_add montgomery_curve
   montgomery_neg montgomery_nonsingular montgomery_strongly_nonsingular
   option_DISTINCT : thm)
  deriving Inhabited

/-- What curve25519.ml uses from Session besides theorems. -/
structure Curve25519Deps where
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
/- Parameters for curve25519. Here  n_25519 is the large prime factor of the -/
/- group order, the full group order being 8 * n_25519. Likewise C_25519 is  -/
/- the generator of the prime order subgroup and CC_25519 is a generator for -/
/- the full group.  Then primality of the field characteristic and           -/
/- (sub)group order, strong nonsingularity, and the curve group.             -/
/- (curve25519.ml 1-116)                                                     -/
/- ------------------------------------------------------------------------- -/

structure Curve25519Defs where
  -- @@FIELDS
  p_25519 : thm
  n_25519 : thm
  A_25519 : thm
  B_25519 : thm
  C_25519 : thm
  CC_25519 : thm
  curve25519 : thm
  P_25519 : thm
  N_25519 : thm
  PRIME_P25519 : thm
  PRIME_N25519 : thm
  MONTGOMERY_STRONGLY_NONSINGULAR_CURVE25519 : thm
  MONTGOMERY_NONSINGULAR_CURVE25519 : thm
  curve25519_group : thm
  CURVE25519_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupCurve25519Defs [HolBase] (D : Curve25519Deps) :
    ExceptT String IO Curve25519Defs := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, DIVIDES_CONV, EXP_MOD_CONV, INTEGER_MOD_RING_RED_CONV,
        INT_REDUCE_CONV, INT_RED_CONV, NUM_DIV_CONV, NUM_REDUCE_CONV, NUM_SUB_CONV,
        PRIME_RULE, add_curve, add_curveadd, add_curveneg, add_ecgroup, define, .. } := D
  let { ARITH, CONG, EULER_CRITERION, FIELD_INTEGER_MOD_RING, INTEGER_MOD_RING_CHAR,
        INTEGER_MOD_RING_CLAUSES, INTEGER_MOD_RING_ROOT_EXISTS, INT_OF_NUM_CLAUSES,
        IN_ELIM_THM, IN_INTEGER_MOD_RING_CARRIER, MONTGOMERY_GROUP, montgomery_add,
        montgomery_curve, montgomery_neg, montgomery_nonsingular,
        montgomery_strongly_nonsingular, .. } := D.core1
  -- @@SCOPE END

  add_curve montgomery_curve
  add_curveneg montgomery_neg
  add_curveadd montgomery_add

  let p_25519 ← define r"p_25519 = 57896044618658097711785492504343953926634992332820282019728792003956564819949"
  let n_25519 ← define r"n_25519 = 7237005577332262213973186563042994240857116359379907606001950938285454250989"
  let A_25519 ← define r"A_25519 = 486662"
  let B_25519 ← define r"B_25519 = 1"
  let C_25519 ← define r"C_25519 = SOME(&0x09:int,&0x20ae19a1b8a086b4e01edd2c7748d14c923d4d7e6d7c61b229e9c5a27eced3d9:int)"
  let CC_25519 ← define r"CC_25519 = SOME(&6911272784993971428141625084124731891523734454433518466500745240824540625972:int,&35197529511187359173101698576797651179158701633820552795916138355302448607023:int)"

  let curve25519 ← define
   r"curve25519 = (integer_mod_ring p_25519,&A_25519:int,&1:int)"

  /- Primality of the field characteristic and (sub)group order. -/

  let P_25519 ← prove
   r"p_25519 = 2 EXP 255 - 19"
   (← do
    pure (REWRITE_TAC [p_25519] THEN ARITH_TAC))

  let N_25519 ← prove
   r"n_25519 = 2 EXP 252 + 27742317777372353535851937790883648493"
   (← do
    pure (REWRITE_TAC [n_25519] THEN ARITH_TAC))

  let PRIME_P25519 ← prove
   r"prime p_25519"
   (← do
    pure (REWRITE_TAC [p_25519] THEN CONV_TAC (fun t => (PRIME_RULE
     ["2", "3", "5", "7", "11", "13", "17", "19", "23", "29", "31", "37", "41",
      "43", "47", "53", "59", "83", "97", "103", "107", "127", "131", "173",
      "223", "239", "353", "419", "479", "487", "991", "1723", "2437", "3727",
      "4153", "9463", "32573", "37853", "57467", "65147", "75707", "132049",
      "430751", "569003", "1923133", "8574133", "2773320623", "72106336199",
      "1919519569386763", "31757755568855353",
      "75445702479781427272750846543864801",
      "74058212732561358302231226437062788676166966415465897661863160754340907",
      "57896044618658097711785492504343953926634992332820282019728792003956564819949"] t).run)))

  let PRIME_N25519 ← prove
   r"prime n_25519"
   (← do
    pure (REWRITE_TAC [n_25519] THEN CONV_TAC (fun t => (PRIME_RULE
     ["2", "3", "5", "7", "11", "13", "17", "19", "23", "41", "43", "47", "67",
      "73", "79", "113", "269", "307", "1361", "1723", "2551", "2851", "2939",
      "3797", "5879", "17231", "22111", "30703", "34123", "41081", "82163",
      "132667", "137849", "409477", "531581", "1224481", "14741173", "58964693",
      "292386187", "213441916511", "1257559732178653", "4434155615661930479",
      "3044861653679985063343", "172054593956031949258510691",
      "198211423230930754013084525763697",
      "19757330305831588566944191468367130476339",
      "276602624281642239937218680557139826668747",
      "7237005577332262213973186563042994240857116359379907606001950938285454250989"] t).run)))

  /- Strong nonsingularity. -/

  let MONTGOMERY_STRONGLY_NONSINGULAR_CURVE25519 ← prove
   r"montgomery_strongly_nonsingular curve25519"
   (← do
    pure (REWRITE_TAC [montgomery_strongly_nonsingular, curve25519] THEN
    REWRITE_TAC [A_25519, p_25519] THEN
    CONV_TAC (DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
    REWRITE_TAC [INTEGER_MOD_RING_ROOT_EXISTS] THEN
    REWRITE_TAC [INT_OF_NUM_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC [EULER_CRITERION, ← REWRITE_RULE [p_25519] PRIME_P25519] THEN
    CONV_TAC (DEPTH_CONV
     (NUM_SUB_CONV ORELSEC NUM_DIV_CONV ORELSEC DIVIDES_CONV)) THEN
    REWRITE_TAC [CONG] THEN CONV_TAC (ONCE_DEPTH_CONV EXP_MOD_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV))

  let MONTGOMERY_NONSINGULAR_CURVE25519 ← prove
   r"montgomery_nonsingular curve25519"
   (← do
    pure (REWRITE_TAC [montgomery_nonsingular, curve25519, p_25519] THEN
    REWRITE_TAC [A_25519, p_25519, IN_INTEGER_MOD_RING_CARRIER] THEN
    CONV_TAC (DEPTH_CONV
     (INTEGER_MOD_RING_RED_CONV ORELSEC INT_RED_CONV))))

  /- Definition of the curve group and proof of its key properties. -/

  let curve25519_group ← define
   r"curve25519_group =
    montgomery_group(integer_mod_ring p_25519,&A_25519,&1)"

  let CURVE25519_GROUP ← prove
   r"group_carrier curve25519_group =
     montgomery_curve(integer_mod_ring p_25519,&A_25519,&1) /\
   group_id curve25519_group =
     NONE /\
   group_inv curve25519_group =
     montgomery_neg(integer_mod_ring p_25519,&A_25519,&1) /\
   group_mul curve25519_group =
     montgomery_add(integer_mod_ring p_25519,&A_25519,&1)"
   (← do
    pure (REWRITE_TAC [curve25519_group] THEN MATCH_MP_TAC MONTGOMERY_GROUP THEN
    REWRITE_TAC [FIELD_INTEGER_MOD_RING, INTEGER_MOD_RING_CHAR, PRIME_P25519] THEN
    REWRITE_TAC [A_25519, B_25519, p_25519, montgomery_nonsingular] THEN
    SIMP_TAC [INTEGER_MOD_RING_CLAUSES, ARITH, IN_ELIM_THM] THEN
    CONV_TAC INT_REDUCE_CONV))

  add_ecgroup [A_25519, B_25519, p_25519] CURVE25519_GROUP

  -- @@RETURN BEGIN
  return { p_25519, n_25519, A_25519, B_25519, C_25519, CC_25519, curve25519, P_25519,
           N_25519, PRIME_P25519, PRIME_N25519,
           MONTGOMERY_STRONGLY_NONSINGULAR_CURVE25519, MONTGOMERY_NONSINGULAR_CURVE25519,
           curve25519_group, CURVE25519_GROUP }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- The generators and their orders, and the group's order and structure.     -/
/- (curve25519.ml 117-216)                                                   -/
/- ------------------------------------------------------------------------- -/

structure Curve25519Group where
  -- @@FIELDS
  FINITE_GROUP_CARRIER_CURVE25519 : thm
  GENERATOR_IN_GROUP_CARRIER_CURVE25519 : thm
  GROUP_ELEMENT_ORDER_CURVE25519_C25519 : thm
  FULLGENERATOR_IN_GROUP_CARRIER_CURVE25519 : thm
  GROUP_ELEMENT_ORDER_CURVE25519_CC25519 : thm
  SIZE_CURVE25519_GROUP : thm
  GENERATED_CURVE25519_GROUP : thm
  CYCLIC_CURVE25519_GROUP : thm
  ABELIAN_CURVE25519_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupCurve25519Group [HolBase] (D : Curve25519Deps) (BCurve25519Defs : Curve25519Defs) :
    ExceptT String IO Curve25519Group := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, COPRIME_CONV, ECGROUP_CARRIER_CONV, ECGROUP_MUL_CONV,
        ECGROUP_POW_CONV, EXPAND_CASES_CONV, MESON_TAC, NUM_REDUCE_CONV, TAUT, .. } := D
  let { ARITH, ARITH_EQ, CARD_BOUND_MONTGOMERY_CURVE, CARD_EQ_0, CARD_INTEGER_MOD_RING,
        CYCLIC_GROUP_ALT, CYCLIC_IMP_ABELIAN_GROUP, FIELD_INTEGER_MOD_RING,
        FINITE_INTEGER_MOD_RING, FINITE_MONTGOMERY_CURVE, GROUP_CARRIER_NONEMPTY,
        GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER, GROUP_ELEMENT_ORDER_MUL_EQ,
        GROUP_ELEMENT_ORDER_UNIQUE_ALT, GROUP_ELEMENT_ORDER_UNIQUE_PRIME, HAS_SIZE,
        IMP_CONJ_ALT, INTEGER_MOD_RING, INT_OF_NUM_CLAUSES,
        IN_INTEGER_MOD_RING_CARRIER, LEFT_IMP_EXISTS_THM, LE_MULT_RCANCEL,
        MULT_CLAUSES, SUBGROUP_GENERATED_ELEMENT_ORDER, divides, option_DISTINCT, .. } := D.core1
  let { A_25519, CC_25519, CURVE25519_GROUP, C_25519, PRIME_N25519, PRIME_P25519,
        n_25519, p_25519, .. } := BCurve25519Defs
  -- @@SCOPE END

  let FINITE_GROUP_CARRIER_CURVE25519 ← prove
   r"FINITE(group_carrier curve25519_group)"
   (← do
    pure (REWRITE_TAC [CURVE25519_GROUP] THEN MATCH_MP_TAC FINITE_MONTGOMERY_CURVE THEN
    REWRITE_TAC [FINITE_INTEGER_MOD_RING,
                 FIELD_INTEGER_MOD_RING, PRIME_P25519] THEN
    REWRITE_TAC [p_25519] THEN CONV_TAC NUM_REDUCE_CONV))

  let GENERATOR_IN_GROUP_CARRIER_CURVE25519 ← prove
   r"C_25519 IN group_carrier curve25519_group"
   (← do
    pure (REWRITE_TAC [C_25519] THEN CONV_TAC ECGROUP_CARRIER_CONV))

  let GROUP_ELEMENT_ORDER_CURVE25519_C25519 ← prove
   r"group_element_order curve25519_group C_25519 = n_25519"
   (← do
    pure (SIMP_TAC [GROUP_ELEMENT_ORDER_UNIQUE_PRIME,
                    GENERATOR_IN_GROUP_CARRIER_CURVE25519, PRIME_N25519] THEN
    REWRITE_TAC [C_25519, ← liftExcept (el 1 (CONJUNCTS CURVE25519_GROUP)),
                 option_DISTINCT] THEN
    REWRITE_TAC [n_25519] THEN CONV_TAC (LAND_CONV ECGROUP_POW_CONV) THEN
    REFL_TAC))

  let FULLGENERATOR_IN_GROUP_CARRIER_CURVE25519 ← prove
   r"CC_25519 IN group_carrier curve25519_group"
   (← do
    pure (REWRITE_TAC [CC_25519] THEN CONV_TAC ECGROUP_CARRIER_CONV))

  let GROUP_ELEMENT_ORDER_CURVE25519_CC25519 ← prove
   r"group_element_order curve25519_group CC_25519 = 8 * n_25519"
   (← do
    let t1 ← TAUT (← q r"p /\ (p ==> q) ==> p /\ q")
    pure (ABBREV_TAC
     (← q r"h = SOME
     (&39382357235489614581723060781553021112529911719440698176882885853963445705823,
      &10506421237558716435988711236408671798265365380393424752549290025458740468278)
    :(int#int)option") THEN
    SUBGOAL_THEN
     (← q r"h IN group_carrier curve25519_group /\
      group_element_order curve25519_group h = 8")
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "h" THEN
      MATCH_MP_TAC t1 THEN CONJ_TAC THENL
       [CONV_TAC ECGROUP_CARRIER_CONV,
        SIMP_TAC [GROUP_ELEMENT_ORDER_UNIQUE_ALT, ARITH]] THEN
      DISCH_TAC THEN REWRITE_TAC [CURVE25519_GROUP] THEN CONJ_TAC THENL
       [CONV_TAC (LAND_CONV ECGROUP_POW_CONV) THEN REFL_TAC, ALL_TAC] THEN
      REWRITE_TAC [IMP_CONJ_ALT] THEN CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
      CONV_TAC (RAND_CONV (LAND_CONV ECGROUP_POW_CONV)) THEN
      REWRITE_TAC [option_DISTINCT],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"CC_25519 = group_mul curve25519_group h C_25519") SUBST1_TAC THENL
     [EXPAND_TAC "h" THEN REWRITE_TAC [C_25519, CC_25519] THEN
      CONV_TAC (RAND_CONV ECGROUP_MUL_CONV) THEN REFL_TAC,
      ALL_TAC] THEN
    wPart lhand (fun t => do lhand (← rand t)) GROUP_ELEMENT_ORDER_MUL_EQ THEN
    ASM_REWRITE_TAC [GROUP_ELEMENT_ORDER_CURVE25519_C25519] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC [GENERATOR_IN_GROUP_CARRIER_CURVE25519] THEN CONJ_TAC THENL
     [EXPAND_TAC "h" THEN REWRITE_TAC [C_25519] THEN
      CONV_TAC (BINOP_CONV ECGROUP_MUL_CONV) THEN REFL_TAC,
      REWRITE_TAC [n_25519] THEN CONV_TAC COPRIME_CONV]))

  let SIZE_CURVE25519_GROUP ← prove
   r"group_carrier curve25519_group HAS_SIZE (8 * n_25519)"
   (← do
    -- right to left: the second ARITH_RULE, then the first
    let a2 ← ARITH_RULE
     (← q r"s < 16 * n /\ 2 * n <= d * n ==> s = (8 * n) * d ==> x = 8 * n")
    let a1 ← ARITH_RULE (← q r"d = 0 \/ d = 1 \/ 2 <= d")
    pure (REWRITE_TAC [HAS_SIZE, FINITE_GROUP_CARRIER_CURVE25519] THEN
    MP_TAC (← ISPECL [← q r"curve25519_group", ← q r"CC_25519"]
      GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER) THEN
    REWRITE_TAC [FINITE_GROUP_CARRIER_CURVE25519,
                 FULLGENERATOR_IN_GROUP_CARRIER_CURVE25519] THEN
    REWRITE_TAC [divides, LEFT_IMP_EXISTS_THM,
                  GROUP_ELEMENT_ORDER_CURVE25519_CC25519] THEN
    X_GEN_TAC (← q r"d:num") THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     a1 THEN
    ASM_SIMP_TAC [CARD_EQ_0, FINITE_GROUP_CARRIER_CURVE25519,
                  MULT_CLAUSES, GROUP_CARRIER_NONEMPTY] THEN
    MATCH_MP_TAC a2 THEN
    REWRITE_TAC [LE_MULT_RCANCEL, n_25519, ARITH_EQ] THEN
    ASM_REWRITE_TAC [← GSYM n_25519, CURVE25519_GROUP] THEN
    wPart lhand (fun t => do lhand (← rand t)) CARD_BOUND_MONTGOMERY_CURVE THEN
    REWRITE_TAC [FIELD_INTEGER_MOD_RING, PRIME_P25519] THEN
    SIMP_TAC [FINITE_INTEGER_MOD_RING, CARD_INTEGER_MOD_RING,
              IN_INTEGER_MOD_RING_CARRIER, n_25519, p_25519,
              INTEGER_MOD_RING, A_25519, INT_OF_NUM_CLAUSES, ARITH_EQ] THEN
    ARITH_TAC))

  let GENERATED_CURVE25519_GROUP ← prove
   r"subgroup_generated curve25519_group {CC_25519} = curve25519_group"
   (← do
    pure (SIMP_TAC [SUBGROUP_GENERATED_ELEMENT_ORDER,
                    FULLGENERATOR_IN_GROUP_CARRIER_CURVE25519,
                    FINITE_GROUP_CARRIER_CURVE25519] THEN
    REWRITE_TAC [GROUP_ELEMENT_ORDER_CURVE25519_CC25519,
                 ← REWRITE_RULE [HAS_SIZE] SIZE_CURVE25519_GROUP]))

  let CYCLIC_CURVE25519_GROUP ← prove
   r"cyclic_group curve25519_group"
   (← do
    pure (MESON_TAC [CYCLIC_GROUP_ALT, GENERATED_CURVE25519_GROUP]))

  let ABELIAN_CURVE25519_GROUP ← prove
   r"abelian_group curve25519_group"
   (← do
    pure (MESON_TAC [CYCLIC_CURVE25519_GROUP, CYCLIC_IMP_ABELIAN_GROUP]))

  -- @@RETURN BEGIN
  return { FINITE_GROUP_CARRIER_CURVE25519, GENERATOR_IN_GROUP_CARRIER_CURVE25519,
           GROUP_ELEMENT_ORDER_CURVE25519_C25519,
           FULLGENERATOR_IN_GROUP_CARRIER_CURVE25519,
           GROUP_ELEMENT_ORDER_CURVE25519_CC25519, SIZE_CURVE25519_GROUP,
           GENERATED_CURVE25519_GROUP, CYCLIC_CURVE25519_GROUP, ABELIAN_CURVE25519_GROUP }
  -- @@RETURN END

end HolEC.Curve25519
