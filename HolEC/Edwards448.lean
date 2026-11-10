/- ========================================================================= -/
/- The Edwards curve commonly known as Goldilocks, edwards448.             -/
/- ========================================================================= -/
/- File: HolEC/Edwards448.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/edwards448.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/edwards.ml, EC/excluderoots.ml, EC/computegroup.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.Edwards448 fills them).

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
import HolEC.Edwards
import HolEC.ExcludeRoots
import HolEC.ComputeGroup

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolEC.Edwards448

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (ARITH_EQ CARD_BOUND_EDWARDS_CURVE CARD_CLAUSES CARD_EQ_0
   CARD_INTEGER_MOD_RING CARD_SUBSET CARRIER_SUBGROUP_GENERATED_SUBGROUP CONG
   CYCLIC_GROUP_ALT CYCLIC_IMP_ABELIAN_GROUP DIVIDES_PRIMEPOW EDWARDS_GROUP
   EDWARDS_GROUP_ELEMENT_ORDER_EQ_2 EDWARDS_GROUP_ELEMENT_ORDER_EQ_4
   EDWARDS_GROUP_ELEMENT_ORDER_EQ_8_EQUIV EULER_CRITERION EXTENSION
   FIELD_INTEGER_MOD_RING FINITE_EDWARDS_CURVE FINITE_EMPTY FINITE_INSERT
   FINITE_INTEGER_MOD_RING FINITE_SUBGROUP_GENERATED FORALL_PAIR_THM
   GROUP_CARRIER_NONEMPTY GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER
   GROUP_ELEMENT_ORDER_EQ_1 GROUP_ELEMENT_ORDER_MUL_EQ
   GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED GROUP_ELEMENT_ORDER_UNIQUE_PRIME
   GROUP_ID HAS_SIZE IMP_CONJ IN INTEGER_MOD_RING INTEGER_MOD_RING_CHAR
   INTEGER_MOD_RING_CLAUSES INTEGER_MOD_RING_ROOT_EXISTS INT_FORALL_ABS
   INT_MUL_ASSOC INT_OF_NUM_CLAUSES INT_OF_NUM_EQ INT_POW2_ABS INT_REM_EQ
   IN_ELIM_THM IN_INSERT IN_INTEGER_MOD_RING_CARRIER IN_SING LEFT_IMP_EXISTS_THM
   LE_TRANS MULT_CLAUSES NOT_EXISTS_THM NOT_IMP NOT_IN_EMPTY PAIR_EQ PRIME_2
   SUBGROUP_GENERATED_ELEMENT_ORDER SUBGROUP_OF_IMP_SUBSET SUBSET SYLOW_THEOREM
   divides edwards_0 edwards_add edwards_curve edwards_neg edwards_nonsingular
   num_congruent : thm)
  deriving Inhabited

/-- What edwards448.ml uses from Session besides theorems. -/
structure Edwards448Deps where
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
/- Parameters for the edwards448 curve, based on the original Mike Hamburg   -/
/- paper "Ed448-Goldilocks" (https://eprint.iacr.org/2015/625.pdf).          -/
/- Here  n_448 is the large prime factor of the group order, the full        -/
/- group order being 4 * n_448. Likewise E_448 is the generator of the       -/
/- prime order subgroup and EE_448 is a generator for the full group.        -/
/- We use e_448 instead of a_448 as the name, to reserve the latter for any  -/
/- Weierstrass variants we might also add.  Then some other equally usable   -/
/- basepoints, primality of the field characteristic and (sub)group order,   -/
/- and the curve group.  (edwards448.ml 1-127)                               -/
/- ------------------------------------------------------------------------- -/

structure Edwards448Defs where
  -- @@FIELDS
  p_448 : thm
  n_448 : thm
  e_448 : thm
  d_448 : thm
  E_448 : thm
  EE_448 : thm
  F_448 : thm
  H_448 : thm
  P_448 : thm
  N_448 : thm
  PRIME_P448 : thm
  PRIME_N448 : thm
  edwards448_group : thm
  EDWARDS_NONSINGULAR_448 : thm
  EDWARDS448_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupEdwards448Defs [HolBase] (D : Edwards448Deps) :
    ExceptT String IO Edwards448Defs := do
  -- @@SCOPE BEGIN
  let { ARITH_TAC, DIVIDES_CONV, EXP_MOD_CONV, INT_REDUCE_CONV, NUM_DIV_CONV,
        NUM_REDUCE_CONV, NUM_SUB_CONV, PRIME_RULE, add_curve, add_curveadd,
        add_curveneg, add_curvezero, add_ecgroup, define, .. } := D
  let { CONG, EDWARDS_GROUP, EULER_CRITERION, FIELD_INTEGER_MOD_RING, INTEGER_MOD_RING,
        INTEGER_MOD_RING_ROOT_EXISTS, INT_OF_NUM_EQ, IN_INTEGER_MOD_RING_CARRIER,
        edwards_0, edwards_add, edwards_curve, edwards_neg, edwards_nonsingular, .. } := D.core1
  -- @@SCOPE END

  add_curve edwards_curve
  add_curvezero edwards_0
  add_curveneg edwards_neg
  add_curveadd edwards_add

  let p_448 ← define r"p_448 = 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439"
  let n_448 ← define r"n_448 = 181709681073901722637330951972001133588410340171829515070372549795146003961539585716195755291692375963310293709091662304773755859649779"
  let e_448 ← define r"e_448 = 1"
  let d_448 ← define r"d_448 = 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018326358"
  let E_448 ← define r"E_448 = (&0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa955555555555555555555555555555555555555555555555555555555:int, &0xae05e9634ad7048db359d6205086c2b0036ed7a035884dd7b7e36d728ad8c4b80d6565833a2a3098bbbcb2bed1cda06bdaeafbcdea9386ed:int)"
  let EE_448 ← define r"EE_448 = (&494088759867433727674302672526735089350544552303727723746126484473087719117037293890093462157703888342865036477787453078312060500281069:int,&242279574765202296849774602629334844784547120229106020093830066393555416020021691321995239242950195063812052916896239502005235079621290:int)"

  /- Some other equally usable basepoints.

      - E_448 above is in the (revised version of) the original paper
        https://eprint.iacr.org/2015/625.pdf

      - F_448 is the one standardized here:
        https://www.rfc-editor.org/rfc/rfc7748
        https://datatracker.ietf.org/doc/html/
           draft-ietf-lwig-curve-representations-23

      - H_448 is the one given in Hamburg's own
        http://ed448goldilocks.sourceforge.net/spec/ -/

  let F_448 ← define r"F_448 = (&0x4f1970c66bed0ded221d15a622bf36da9e146570470f1767ea6de324a3d3a46412ae1af72ab66511433b80e18b00938e2626a82bc70cc05e:int,&0x693f46716eb6bc248876203756c9c7624bea73736ca3984087789c1e05a0c2d73ad3ff1ce67c39c4fdbd132c4ed7c8ad9808795bf230fa14:int)"

  let H_448 ← define r"H_448 = (&117812161263436946737282484343310064665180535357016373416879082147939404277809514858788439644911793978499419995990477371552926308078495:int,&19:int)"

  /- Primality of the field characteristic and (sub)group order. -/

  let P_448 ← prove
   r"p_448 = 2 EXP 448 - 2 EXP 224 - 1"
   (← do
    pure (REWRITE_TAC [p_448] THEN ARITH_TAC))

  let N_448 ← prove
   r"n_448 = 2 EXP 446 - 0x8335dc163bb124b65129c96fde933d8d723a70aadc873d6d54a7bb0d"
   (← do
    pure (REWRITE_TAC [n_448] THEN ARITH_TAC))

  let PRIME_P448 ← prove
   r"prime p_448"
   (← do
    pure (REWRITE_TAC [p_448] THEN CONV_TAC (fun t => (PRIME_RULE
     ["2", "3", "5", "7", "11", "13", "17", "19", "23", "29", "31", "37", "41",
      "43", "59", "61", "67", "109", "137", "149", "151", "197", "223", "229",
      "271", "443", "463", "593", "613", "641", "727", "1481", "1549", "1979",
      "2437", "2531", "2683", "2963", "6197", "9749", "17449", "18287", "47497",
      "116989", "189989", "196687", "217003", "379979", "411743", "1466449",
      "1609403", "2916841", "6700417", "36753053", "1255525949", "1335912079",
      "1764234391", "3402277943", "32061889897", "25136521679249",
      "97859369123353", "34741861125639557", "36131535570665139281",
      "1469495262398780123809", "167773885276849215533569",
      "596242599987116128415063", "37414057161322375957408148834323969"] t).run)))

  let PRIME_N448 ← prove
   r"prime n_448"
   (← do
    pure (REWRITE_TAC [n_448] THEN CONV_TAC (fun t => (PRIME_RULE
     ["2", "3", "5", "7", "11", "13", "17", "19", "23", "31", "41", "43", "53",
      "61", "67", "71", "79", "83", "89", "97", "101", "113", "137", "167",
      "173", "179", "193", "197", "311", "337", "347", "373", "431", "691",
      "821", "991", "1609", "1933", "2239", "3217", "3449", "4051", "6577",
      "14221", "16657", "34483", "41389", "51473", "64817", "74551", "142211",
      "227393", "766223", "816763", "894613", "3009341", "3578453", "4847597",
      "7156907", "9801157", "15643211", "35796097", "47840521", "671065561",
      "765448337", "8464734851", "342682509629", "95024118539459",
      "760192948315673", "2746144996771313789",
      "163131120638915058577002756917", "929098197455246849020086750707",
      "6730519843040614479184435237013", "3591893631361984318311655378233263",
      "392279121964710096549298451519713063",
      "547972593843380542316719287015009101629889568888367769396279985548530313239"] t).run)))

  /- Definition of the curve group and proof of its key properties. -/

  let edwards448_group ← define
   r"edwards448_group =
    edwards_group(integer_mod_ring p_448,&e_448,&d_448)"

  let EDWARDS_NONSINGULAR_448 ← prove
   r"edwards_nonsingular (integer_mod_ring p_448,&e_448,&d_448)"
   (← do
    pure (REWRITE_TAC [edwards_nonsingular, INTEGER_MOD_RING_ROOT_EXISTS] THEN
    SIMP_TAC [INTEGER_MOD_RING, INT_OF_NUM_EQ, e_448, d_448, p_448] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC [EULER_CRITERION, ← REWRITE_RULE [p_448] PRIME_P448] THEN
    CONV_TAC (DEPTH_CONV
     (NUM_SUB_CONV ORELSEC NUM_DIV_CONV ORELSEC DIVIDES_CONV)) THEN
    REWRITE_TAC [CONG] THEN CONV_TAC (ONCE_DEPTH_CONV EXP_MOD_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV))

  let EDWARDS448_GROUP ← prove
   r"group_carrier edwards448_group =
     edwards_curve(integer_mod_ring p_448,&e_448,&d_448) /\
   group_id edwards448_group =
     edwards_0(integer_mod_ring p_448,&e_448,&d_448) /\
   group_inv edwards448_group =
     edwards_neg(integer_mod_ring p_448,&e_448,&d_448) /\
   group_mul edwards448_group =
     edwards_add(integer_mod_ring p_448,&e_448,&d_448)"
   (← do
    pure (REWRITE_TAC [edwards448_group] THEN MATCH_MP_TAC EDWARDS_GROUP THEN
    REWRITE_TAC [EDWARDS_NONSINGULAR_448] THEN
    REWRITE_TAC [FIELD_INTEGER_MOD_RING, PRIME_P448] THEN
    REWRITE_TAC [e_448, d_448, p_448] THEN
    REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER] THEN CONV_TAC INT_REDUCE_CONV))

  add_ecgroup [e_448, d_448, p_448] EDWARDS448_GROUP

  -- @@RETURN BEGIN
  return { p_448, n_448, e_448, d_448, E_448, EE_448, F_448, H_448, P_448, N_448,
           PRIME_P448, PRIME_N448, edwards448_group, EDWARDS_NONSINGULAR_448,
           EDWARDS448_GROUP }
  -- @@RETURN END



/- ------------------------------------------------------------------------- -/
/- The generators and their orders, the elements of orders 1, 2, 4 and 8,    -/
/- and the group's order and structure.  (edwards448.ml 128-383)             -/
/- ------------------------------------------------------------------------- -/

structure Edwards448Group where
  -- @@FIELDS
  FINITE_GROUP_CARRIER_EDWARDS448 : thm
  GENERATOR_IN_GROUP_CARRIER_EDWARDS448 : thm
  GROUP_ELEMENT_ORDER_EDWARDS448_E448 : thm
  GENERATOR_IN_GROUP_CARRIER_F448 : thm
  GROUP_ELEMENT_ORDER_EDWARDS448_F448 : thm
  GENERATOR_IN_GROUP_CARRIER_H448 : thm
  GROUP_ELEMENT_ORDER_EDWARDS448_H448 : thm
  EDWARDS448_ORDER_1 : thm
  EDWARDS448_ORDER_2 : thm
  EDWARDS448_ORDER_4 : thm
  EDWARDS448_ORDER_8 : thm
  FULLGENERATOR_IN_GROUP_CARRIER_EDWARDS448 : thm
  GROUP_ELEMENT_ORDER_EDWARDS448_EE448 : thm
  SIZE_EDWARDS448_GROUP : thm
  GENERATED_EDWARDS448_GROUP : thm
  CYCLIC_EDWARDS448_GROUP : thm
  ABELIAN_EDWARDS448_GROUP : thm
  deriving Inhabited

@[nospecialize]
def setupEdwards448Group [HolBase] (D : Edwards448Deps) (BEdwards448Defs : Edwards448Defs) :
    ExceptT String IO Edwards448Group := do
  -- @@SCOPE BEGIN
  let { ARITH_RULE, ARITH_TAC, ASM_ARITH_TAC, COPRIME_CONV, DIVIDES_CONV,
        ECGROUP_CARRIER_CONV, ECGROUP_MUL_CONV, ECGROUP_POW_CONV, EXPAND_CASES_CONV,
        EXP_MOD_CONV, INTEGER_MOD_RING_RED_CONV, INTEGER_RULE, INT_REDUCE_CONV,
        INT_RED_CONV, INT_REM_DOWN_CONV, MESON, MESON_TAC, NUM_DIV_CONV,
        NUM_REDUCE_CONV, NUM_SUB_CONV, SET_RULE, SET_TAC, TAUT, .. } := D
  let { ARITH_EQ, CARD_BOUND_EDWARDS_CURVE, CARD_CLAUSES, CARD_EQ_0,
        CARD_INTEGER_MOD_RING, CARD_SUBSET, CARRIER_SUBGROUP_GENERATED_SUBGROUP, CONG,
        CYCLIC_GROUP_ALT, CYCLIC_IMP_ABELIAN_GROUP, DIVIDES_PRIMEPOW,
        EDWARDS_GROUP_ELEMENT_ORDER_EQ_2, EDWARDS_GROUP_ELEMENT_ORDER_EQ_4,
        EDWARDS_GROUP_ELEMENT_ORDER_EQ_8_EQUIV, EULER_CRITERION, EXTENSION,
        FIELD_INTEGER_MOD_RING, FINITE_EDWARDS_CURVE, FINITE_EMPTY, FINITE_INSERT,
        FINITE_INTEGER_MOD_RING, FINITE_SUBGROUP_GENERATED, FORALL_PAIR_THM,
        GROUP_CARRIER_NONEMPTY, GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER,
        GROUP_ELEMENT_ORDER_EQ_1, GROUP_ELEMENT_ORDER_MUL_EQ,
        GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED, GROUP_ELEMENT_ORDER_UNIQUE_PRIME,
        GROUP_ID, HAS_SIZE, IMP_CONJ, IN, INTEGER_MOD_RING, INTEGER_MOD_RING_CHAR,
        INTEGER_MOD_RING_CLAUSES, INT_FORALL_ABS, INT_MUL_ASSOC, INT_OF_NUM_CLAUSES,
        INT_OF_NUM_EQ, INT_POW2_ABS, INT_REM_EQ, IN_ELIM_THM, IN_INSERT,
        IN_INTEGER_MOD_RING_CARRIER, IN_SING, LEFT_IMP_EXISTS_THM, LE_TRANS,
        MULT_CLAUSES, NOT_EXISTS_THM, NOT_IMP, NOT_IN_EMPTY, PAIR_EQ, PRIME_2,
        SUBGROUP_GENERATED_ELEMENT_ORDER, SUBGROUP_OF_IMP_SUBSET, SUBSET,
        SYLOW_THEOREM, divides, edwards_0, edwards_curve, num_congruent, .. } := D.core1
  let { EDWARDS448_GROUP, EDWARDS_NONSINGULAR_448, EE_448, E_448, F_448, H_448,
        PRIME_N448, PRIME_P448, d_448, e_448, edwards448_group, n_448, p_448, .. } := BEdwards448Defs
  -- @@SCOPE END

  let FINITE_GROUP_CARRIER_EDWARDS448 ← prove
   r"FINITE(group_carrier edwards448_group)"
   (← do
    pure (REWRITE_TAC [EDWARDS448_GROUP] THEN MATCH_MP_TAC FINITE_EDWARDS_CURVE THEN
    REWRITE_TAC [FINITE_INTEGER_MOD_RING,
                 FIELD_INTEGER_MOD_RING, PRIME_P448] THEN
    REWRITE_TAC [p_448] THEN CONV_TAC NUM_REDUCE_CONV))

  let GENERATOR_IN_GROUP_CARRIER_EDWARDS448 ← prove
   r"E_448 IN group_carrier edwards448_group"
   (← do
    pure (REWRITE_TAC [E_448] THEN CONV_TAC ECGROUP_CARRIER_CONV))

  let GROUP_ELEMENT_ORDER_EDWARDS448_E448 ← prove
   r"group_element_order edwards448_group E_448 = n_448"
   (← do
    pure (SIMP_TAC [GROUP_ELEMENT_ORDER_UNIQUE_PRIME,
                    GENERATOR_IN_GROUP_CARRIER_EDWARDS448, PRIME_N448] THEN
    REWRITE_TAC [E_448, ← liftExcept (el 1 (CONJUNCTS EDWARDS448_GROUP))] THEN
    REWRITE_TAC [edwards_0, PAIR_EQ, INTEGER_MOD_RING] THEN
    REWRITE_TAC [n_448, p_448] THEN CONV_TAC INT_REDUCE_CONV THEN
    CONV_TAC (LAND_CONV ECGROUP_POW_CONV) THEN REFL_TAC))

  let GENERATOR_IN_GROUP_CARRIER_F448 ← prove
   r"F_448 IN group_carrier edwards448_group"
   (← do
    pure (REWRITE_TAC [F_448] THEN CONV_TAC ECGROUP_CARRIER_CONV))

  let GROUP_ELEMENT_ORDER_EDWARDS448_F448 ← prove
   r"group_element_order edwards448_group F_448 = n_448"
   (← do
    pure (SIMP_TAC [GROUP_ELEMENT_ORDER_UNIQUE_PRIME,
                    GENERATOR_IN_GROUP_CARRIER_F448, PRIME_N448] THEN
    REWRITE_TAC [F_448, ← liftExcept (el 1 (CONJUNCTS EDWARDS448_GROUP))] THEN
    REWRITE_TAC [edwards_0, PAIR_EQ, INTEGER_MOD_RING] THEN
    REWRITE_TAC [n_448, p_448] THEN CONV_TAC INT_REDUCE_CONV THEN
    CONV_TAC (LAND_CONV ECGROUP_POW_CONV) THEN REFL_TAC))

  let GENERATOR_IN_GROUP_CARRIER_H448 ← prove
   r"H_448 IN group_carrier edwards448_group"
   (← do
    pure (REWRITE_TAC [H_448] THEN CONV_TAC ECGROUP_CARRIER_CONV))

  let GROUP_ELEMENT_ORDER_EDWARDS448_H448 ← prove
   r"group_element_order edwards448_group H_448 = n_448"
   (← do
    pure (SIMP_TAC [GROUP_ELEMENT_ORDER_UNIQUE_PRIME,
                    GENERATOR_IN_GROUP_CARRIER_H448, PRIME_N448] THEN
    REWRITE_TAC [H_448, ← liftExcept (el 1 (CONJUNCTS EDWARDS448_GROUP))] THEN
    REWRITE_TAC [edwards_0, PAIR_EQ, INTEGER_MOD_RING] THEN
    REWRITE_TAC [n_448, p_448] THEN CONV_TAC INT_REDUCE_CONV THEN
    CONV_TAC (LAND_CONV ECGROUP_POW_CONV) THEN REFL_TAC))

  let EDWARDS448_ORDER_1 ← prove
   r"{p | p IN group_carrier edwards448_group /\
        group_element_order edwards448_group p = 1} = {(&0,&1)}"
   (← do
    let m1 ← MESON []
     (← q r"!a'. a' IN G /\ (x IN G ==> (P x <=> x = a')) /\ a' = a
           ==> (x IN G /\ P x <=> x = a)")
    pure (REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_ELIM_THM, IN_SING] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:int", ← q r"y:int"] THEN
    MATCH_MP_TAC m1 THEN
    EXISTS_TAC (← q r"group_id edwards448_group") THEN
    REWRITE_TAC [GROUP_ELEMENT_ORDER_EQ_1, GROUP_ID] THEN
    REWRITE_TAC [EDWARDS448_GROUP, edwards_0, INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC [p_448, PAIR_EQ] THEN CONV_TAC INT_REDUCE_CONV))

  let EDWARDS448_ORDER_2 ← prove
   r"{p | p IN group_carrier edwards448_group /\
        group_element_order edwards448_group p = 2} = {(&0,&p_448 - &1)}"
   (← do
    let m1 ← MESON []
     (← q r"a IN G /\ (x IN G ==> (P x <=> x = a))
      ==> (x IN G /\ P x <=> x = a)")
    pure (REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_ELIM_THM, IN_SING] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:int", ← q r"y:int"] THEN
    MATCH_MP_TAC m1 THEN
    CONJ_TAC THENL
     [REWRITE_TAC [EDWARDS448_GROUP, IN] THEN REWRITE_TAC [edwards_curve] THEN
      REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER, p_448, d_448] THEN
      CONV_TAC (DEPTH_CONV (INTEGER_MOD_RING_RED_CONV ORELSEC INT_RED_CONV)),
      DISCH_TAC] THEN
    REWRITE_TAC [edwards448_group] THEN
    wPart lhand (fun t => do lhand (← rand t)) EDWARDS_GROUP_ELEMENT_ORDER_EQ_2 THEN
    ANTS_TAC THENL
     [REWRITE_TAC [EDWARDS_NONSINGULAR_448] THEN
      REWRITE_TAC [FIELD_INTEGER_MOD_RING, PRIME_P448] THEN
      ASM_REWRITE_TAC [← GSYM edwards448_group, INTEGER_MOD_RING_CHAR] THEN
      REWRITE_TAC [e_448, d_448, p_448, ← GSYM INT_OF_NUM_EQ] THEN
      REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER] THEN CONV_TAC INT_REDUCE_CONV,
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN REWRITE_TAC [PAIR_EQ, p_448] THEN
    CONV_TAC (DEPTH_CONV (INTEGER_MOD_RING_RED_CONV ORELSEC INT_RED_CONV))))

  let EDWARDS448_ORDER_4 ← prove
   r"{p | p IN group_carrier edwards448_group /\
        group_element_order edwards448_group p = 4} =
   {(&1,&0), (&p_448 - &1,&0)}"
   (← do
    let m1 ← MESON []
     (← q r"(a IN G /\ b IN G) /\ (x IN G ==> (P x <=> x = a \/ x = b))
      ==> (x IN G /\ P x <=> x = a \/ x = b)")
    pure (REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_ELIM_THM] THEN
    REWRITE_TAC [IN_INSERT, NOT_IN_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:int", ← q r"y:int"] THEN
    MATCH_MP_TAC m1 THEN
    CONJ_TAC THENL
     [REWRITE_TAC [EDWARDS448_GROUP, IN] THEN REWRITE_TAC [edwards_curve] THEN
      REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER, p_448, d_448, e_448] THEN
      CONV_TAC (DEPTH_CONV (INTEGER_MOD_RING_RED_CONV ORELSEC INT_RED_CONV)),
      DISCH_TAC] THEN
    REWRITE_TAC [edwards448_group] THEN
    MP_TAC (← ISPECL
     [← q r"integer_mod_ring p_448", ← q r"&e_448:int", ← q r"&d_448:int", ← q r"&1:int",
      ← q r"(x,y):int#int"]
     EDWARDS_GROUP_ELEMENT_ORDER_EQ_4) THEN
    ANTS_TAC THENL
     [REWRITE_TAC [EDWARDS_NONSINGULAR_448] THEN
      REWRITE_TAC [FIELD_INTEGER_MOD_RING, PRIME_P448] THEN
      ASM_REWRITE_TAC [← GSYM edwards448_group, INTEGER_MOD_RING_CHAR] THEN
      REWRITE_TAC [e_448, d_448, p_448, ← GSYM INT_OF_NUM_EQ] THEN
      REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER] THEN
      CONV_TAC (DEPTH_CONV (INTEGER_MOD_RING_RED_CONV ORELSEC INT_RED_CONV)),
      DISCH_THEN SUBST1_TAC] THEN
    BINOP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [PAIR_EQ, p_448] THEN
    CONV_TAC (DEPTH_CONV (INTEGER_MOD_RING_RED_CONV ORELSEC INT_RED_CONV))))

  let EDWARDS448_ORDER_8 ← prove
   r"{p | p IN group_carrier edwards448_group /\
        group_element_order edwards448_group p = 8} = {}"
   (← do
    -- right to left: the INTEGER_RULE, then the TAUT
    let i1 ← INTEGER_RULE
     (← q r"(&4 * z:int == (&1 + d * z) pow 2) (mod p)
      ==> ((d pow 2 * z + (d - &2)) pow 2 == &4 * (p + &1 - d)) (mod p)")
    let t1 ← TAUT (← q r"~(p /\ q) <=> p ==> ~q")
    pure (REWRITE_TAC [EXTENSION, FORALL_PAIR_THM, IN_ELIM_THM, NOT_IN_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [← q r"x:int", ← q r"y:int"] THEN
    REWRITE_TAC [t1] THEN DISCH_TAC THEN
    REWRITE_TAC [edwards448_group] THEN
    wPart rand (fun t => do lhand (← rand t)) EDWARDS_GROUP_ELEMENT_ORDER_EQ_8_EQUIV THEN
    ANTS_TAC THENL
     [REWRITE_TAC [EDWARDS_NONSINGULAR_448] THEN
      REWRITE_TAC [FIELD_INTEGER_MOD_RING, PRIME_P448] THEN
      ASM_REWRITE_TAC [← GSYM edwards448_group, INTEGER_MOD_RING_CHAR] THEN
      REWRITE_TAC [e_448, d_448, p_448, ← GSYM INT_OF_NUM_EQ] THEN
      REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER] THEN CONV_TAC INT_REDUCE_CONV,
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC [INTEGER_MOD_RING_CLAUSES] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    DISCH_THEN (MP_TAC o CONJUNCT2) THEN REWRITE_TAC [INT_REM_EQ] THEN
    ABBREV_TAC (← q r"z:int = x pow 4") THEN
    REWRITE_TAC [e_448, d_448, INT_MUL_ASSOC] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC [← GSYM d_448] THEN DISCH_THEN (MP_TAC o MATCH_MP i1) THEN
    REWRITE_TAC [] THEN ONCE_REWRITE_TAC [← GSYM INT_POW2_ABS] THEN
    SPEC_TAC (← q r"&d_448 pow 2 * z + &d_448 - &2:int", ← q r"w:int") THEN
    REWRITE_TAC [← GSYM INT_FORALL_ABS] THEN
    REWRITE_TAC [← GSYM NOT_EXISTS_THM] THEN
    REWRITE_TAC [p_448, d_448] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC [INT_OF_NUM_CLAUSES, ← GSYM num_congruent] THEN
    SIMP_TAC [EULER_CRITERION, ← REWRITE_RULE [p_448] PRIME_P448] THEN
    CONV_TAC (DEPTH_CONV
     (NUM_SUB_CONV ORELSEC NUM_DIV_CONV ORELSEC DIVIDES_CONV)) THEN
    REWRITE_TAC [CONG] THEN CONV_TAC (ONCE_DEPTH_CONV EXP_MOD_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV))

  let FULLGENERATOR_IN_GROUP_CARRIER_EDWARDS448 ← prove
   r"EE_448 IN group_carrier edwards448_group"
   (← do
    pure (REWRITE_TAC [EE_448] THEN CONV_TAC ECGROUP_CARRIER_CONV))

  let GROUP_ELEMENT_ORDER_EDWARDS448_EE448 ← prove
   r"group_element_order edwards448_group EE_448 = 4 * n_448"
   (← do
    let s1 ← SET_RULE (← q r"h IN s /\ P h <=> h IN {x | x IN s /\ P x}")
    pure (ABBREV_TAC (← q r"h = (&1,&0):int#int") THEN
    SUBGOAL_THEN
     (← q r"h IN group_carrier edwards448_group /\
      group_element_order edwards448_group h = 4")
    STRIP_ASSUME_TAC THENL
     [ONCE_REWRITE_TAC [s1] THEN
      EXPAND_TAC "h" THEN REWRITE_TAC [EDWARDS448_ORDER_4, IN_INSERT],
      ALL_TAC] THEN
    SUBGOAL_THEN (← q r"EE_448 = group_mul edwards448_group h E_448") SUBST1_TAC THENL
     [EXPAND_TAC "h" THEN REWRITE_TAC [E_448, EE_448] THEN
      CONV_TAC (RAND_CONV ECGROUP_MUL_CONV) THEN REFL_TAC,
      ALL_TAC] THEN
    wPart lhand (fun t => do lhand (← rand t)) GROUP_ELEMENT_ORDER_MUL_EQ THEN
    ASM_REWRITE_TAC [GROUP_ELEMENT_ORDER_EDWARDS448_E448] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC [GENERATOR_IN_GROUP_CARRIER_EDWARDS448] THEN CONJ_TAC THENL
     [EXPAND_TAC "h" THEN REWRITE_TAC [E_448] THEN
      CONV_TAC (BINOP_CONV ECGROUP_MUL_CONV) THEN REFL_TAC,
      REWRITE_TAC [n_448] THEN CONV_TAC COPRIME_CONV]))

  let SIZE_EDWARDS448_GROUP ← prove
   r"group_carrier edwards448_group HAS_SIZE (4 * n_448)"
   (← do
    -- right to left: the second branch's ARITH_RULE, then in the first
    -- branch the SET_RULE, the ARITH_RULE, `NUM_REDUCE_CONV `2 EXP 3``
    -- and the first ARITH_RULE
    let a356 ← ARITH_RULE
     (← q r"n * 3 <= n * d /\ s < 3 * n ==> s = n * d ==> u:num = v")
    let s348 ← SET_RULE
     (← q r"x IN group_carrier G /\
       {y | y IN group_carrier G /\ group_element_order G y = n} SUBSET s
       ==> group_element_order G x = n ==> x IN s")
    let a345 ← ARITH_RULE (← q r"i <= 3 <=> i < 4")
    let c344 ← ExceptT.mk (NUM_REDUCE_CONV (← q r"2 EXP 3"))
    let a323 ← ARITH_RULE
     (← q r"~(s = 8 * n) ==> s = (4 * n) * 2 ==> u:num = v")
    pure (REWRITE_TAC [HAS_SIZE, FINITE_GROUP_CARRIER_EDWARDS448] THEN
    MP_TAC (← ISPECL [← q r"edwards448_group", ← q r"EE_448"]
      GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER) THEN
    REWRITE_TAC [FINITE_GROUP_CARRIER_EDWARDS448,
                 FULLGENERATOR_IN_GROUP_CARRIER_EDWARDS448] THEN
    REWRITE_TAC [divides, LEFT_IMP_EXISTS_THM,
                 GROUP_ELEMENT_ORDER_EDWARDS448_EE448] THEN
    X_GEN_TAC (← q r"d:num") THEN
    ASM_CASES_TAC (← q r"d = 0") THEN
    ASM_SIMP_TAC [CARD_EQ_0, MULT_CLAUSES, GROUP_CARRIER_NONEMPTY,
                  FINITE_GROUP_CARRIER_EDWARDS448] THEN
    ASM_CASES_TAC (← q r"d = 1") THEN ASM_REWRITE_TAC [MULT_CLAUSES] THEN
    ASM_CASES_TAC (← q r"d = 2") THEN ASM_REWRITE_TAC [] THENL
     [MATCH_MP_TAC a323 THEN
      DISCH_TAC THEN
      MP_TAC (← ISPECL [← q r"edwards448_group", ← q r"2", ← q r"3"] SYLOW_THEOREM) THEN
      ASM_REWRITE_TAC [FINITE_GROUP_CARRIER_EDWARDS448, PRIME_2, NOT_IMP] THEN
      REWRITE_TAC [n_448] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC (LAND_CONV DIVIDES_CONV) THEN REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN (← q r"h:int#int->bool") STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN (← q r"CARD(h:int#int->bool) <= 4") MP_TAC THENL
       [ALL_TAC, ASM_REWRITE_TAC [] THEN ARITH_TAC] THEN
      TRANS_TAC LE_TRANS
       (← q r"CARD{(&0:int,&1:int), (&0,&p_448 - &1), (&1,&0), (&p_448 - &1,&0)}") THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC [FINITE_INSERT, FINITE_EMPTY],
        SIMP_TAC [CARD_CLAUSES, FINITE_INSERT, FINITE_EMPTY] THEN ARITH_TAC] THEN
      REWRITE_TAC [SUBSET] THEN X_GEN_TAC (← q r"p:int#int") THEN DISCH_TAC THEN
      MP_TAC (← ISPECL [← q r"subgroup_generated edwards448_group h", ← q r"p:int#int"]
        GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER) THEN
      ASM_SIMP_TAC [FINITE_SUBGROUP_GENERATED, FINITE_GROUP_CARRIER_EDWARDS448,
                    CARRIER_SUBGROUP_GENERATED_SUBGROUP] THEN
      REWRITE_TAC [GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED] THEN
      SIMP_TAC [← GSYM c344, DIVIDES_PRIMEPOW, PRIME_2] THEN
      REWRITE_TAC [a345, LEFT_IMP_EXISTS_THM] THEN
      REWRITE_TAC [IMP_CONJ] THEN
      CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC s348 THEN
      REWRITE_TAC [EDWARDS448_ORDER_1, EDWARDS448_ORDER_2,
                   EDWARDS448_ORDER_4, EDWARDS448_ORDER_8] THEN
      FIRST_X_ASSUM (MP_TAC o MATCH_MP SUBGROUP_OF_IMP_SUBSET) THEN
      ASM SET_TAC [],
      MATCH_MP_TAC a356 THEN
      REWRITE_TAC [n_448] THEN CONJ_TAC THENL [ASM_ARITH_TAC, ALL_TAC] THEN
      ASM_REWRITE_TAC [← GSYM n_448, EDWARDS448_GROUP] THEN
      wPart lhand (fun t => do lhand (← rand t)) CARD_BOUND_EDWARDS_CURVE THEN
      REWRITE_TAC [EDWARDS_NONSINGULAR_448] THEN
      REWRITE_TAC [FIELD_INTEGER_MOD_RING, PRIME_P448] THEN
       SIMP_TAC [FINITE_INTEGER_MOD_RING, CARD_INTEGER_MOD_RING,
               IN_INTEGER_MOD_RING_CARRIER, n_448, p_448, d_448,
               INTEGER_MOD_RING, e_448, INT_OF_NUM_CLAUSES, ARITH_EQ] THEN
      ARITH_TAC]))

  let GENERATED_EDWARDS448_GROUP ← prove
   r"subgroup_generated edwards448_group {EE_448} = edwards448_group"
   (← do
    pure (SIMP_TAC [SUBGROUP_GENERATED_ELEMENT_ORDER,
                    FULLGENERATOR_IN_GROUP_CARRIER_EDWARDS448,
                    FINITE_GROUP_CARRIER_EDWARDS448] THEN
    REWRITE_TAC [GROUP_ELEMENT_ORDER_EDWARDS448_EE448,
                 ← REWRITE_RULE [HAS_SIZE] SIZE_EDWARDS448_GROUP]))

  let CYCLIC_EDWARDS448_GROUP ← prove
   r"cyclic_group edwards448_group"
   (← do
    pure (MESON_TAC [CYCLIC_GROUP_ALT, GENERATED_EDWARDS448_GROUP]))

  let ABELIAN_EDWARDS448_GROUP ← prove
   r"abelian_group edwards448_group"
   (← do
    pure (MESON_TAC [CYCLIC_EDWARDS448_GROUP, CYCLIC_IMP_ABELIAN_GROUP]))

  -- @@RETURN BEGIN
  return { FINITE_GROUP_CARRIER_EDWARDS448, GENERATOR_IN_GROUP_CARRIER_EDWARDS448,
           GROUP_ELEMENT_ORDER_EDWARDS448_E448, GENERATOR_IN_GROUP_CARRIER_F448,
           GROUP_ELEMENT_ORDER_EDWARDS448_F448, GENERATOR_IN_GROUP_CARRIER_H448,
           GROUP_ELEMENT_ORDER_EDWARDS448_H448, EDWARDS448_ORDER_1, EDWARDS448_ORDER_2,
           EDWARDS448_ORDER_4, EDWARDS448_ORDER_8,
           FULLGENERATOR_IN_GROUP_CARRIER_EDWARDS448,
           GROUP_ELEMENT_ORDER_EDWARDS448_EE448, SIZE_EDWARDS448_GROUP,
           GENERATED_EDWARDS448_GROUP, CYCLIC_EDWARDS448_GROUP, ABELIAN_EDWARDS448_GROUP }
  -- @@RETURN END

end HolEC.Edwards448
