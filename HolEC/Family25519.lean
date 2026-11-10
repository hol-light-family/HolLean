/- ========================================================================= -/
/- The three forms of curve25519 related via isomorphisms.                 -/
/- ========================================================================= -/
/- File: HolEC/Family25519.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/family25519.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/iter.ml, Library/prime.ml, Library/pocklington.ml, Library/integer.ml, Library/isum.ml, Library/binomial.ml, Library/products.ml, Library/multiplicative.ml, Library/primitive.ml, Library/frag.ml, Library/wo.ml, Library/card.ml, Library/grouptheory.ml, Library/ringtheory.ml, EC/misc.ml, EC/edwards.ml, EC/montgomery.ml, EC/edmont.ml, EC/weierstrass.ml, EC/montwe.ml, EC/excluderoots.ml, EC/computegroup.ml, EC/edwards25519.ml, EC/curve25519.ml, EC/wei25519.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.Family25519 fills them).

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
import HolEC.Montgomery
import HolEC.Edmont
import HolEC.Weierstrass
import HolEC.Montwe
import HolEC.ExcludeRoots
import HolEC.ComputeGroup
import HolEC.Edwards25519
import HolEC.Curve25519
import HolEC.Wei25519

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolEC.Family25519

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (A_25519 CC_25519 C_25519 EDWARDS_NONSINGULAR_25519 EE_25519 E_25519
   FIELD_INTEGER_MOD_RING GG_25519 GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP
   GROUP_ISOMORPHISMS_IMP_ISOMORPHISM
   GROUP_ISOMORPHISMS_MONTGOMERY_WEIERSTRASS_GROUP G_25519 INTEGER_MOD_RING
   INTEGER_MOD_RING_CHAR INTEGER_MOD_RING_CLAUSES INT_OF_NUM_EQ
   IN_INTEGER_MOD_RING_CARRIER ISOMORPHIC_GROUP_SYM PAIR_EQ PRIME_P25519 a_25519
   b_25519 curve25519_group d_25519 e_25519 edwards25519_group
   edwards_of_montgomery isomorphic_group mcurve_of_ecurve
   montgomery_nonsingular montgomery_of_edwards montgomery_of_weierstrass
   p_25519 wcurve_of_mcurve wei25519_group weierstrass_of_montgomery : thm)
  deriving Inhabited

/-- What family25519.ml uses from Session besides theorems. -/
structure Family25519Deps where
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
/- The three forms of curve25519 related via isomorphisms: the extra scaling -/
/- factor (in terms of the other parameters c_25519 = sqrt(-(A_25519+2)/     -/
/- B_25519), see https://datatracker.ietf.org/doc/html/                      -/
/- draft-ietf-lwig-curve-representations-23), the mappings between Edwards   -/
/- and Montgomery forms, and those between Montgomery and Weierstrass forms. -/
/- (family25519.ml 1-180)                                                    -/
/- ------------------------------------------------------------------------- -/

structure Family25519Maps where
  -- @@FIELDS
  c_25519 : thm
  curve25519_of_edwards25519 : thm
  edwards25519_of_curve25519 : thm
  MCURVE_OF_ECURVE_25519 : thm
  GROUP_ISOMORPHISMS_EDWARDS25519_CURVE25519 : thm
  ISOMORPHIC_GROUPS_EDWARDS25519_CURVE25519 : thm
  ISOMORPHIC_GROUPS_CURVE25519_EDWARDS25519 : thm
  CURVE25519_OF_EDWARDS25519_E25519 : thm
  CURVE25519_OF_EDWARDS25519_EE25519 : thm
  EDWARDS25519_OF_CURVE25519_C25519 : thm
  EDWARDS25519_OF_CURVE25519_CC25519 : thm
  wei25519_of_curve25519 : thm
  curve25519_of_wei25519 : thm
  WCURVE_OF_MCURVE_25519 : thm
  GROUP_ISOMORPHISMS_CURVE25519_WEI25519 : thm
  ISOMORPHIC_GROUPS_CURVE25519_WEI25519 : thm
  ISOMORPHIC_GROUPS_WEI25519_CURVE25519 : thm
  WEI25519_OF_CURVE25519_C25519 : thm
  WEI25519_OF_CURVE25519_CC25519 : thm
  CURVE25519_OF_WEI25519_G25519 : thm
  CURVE25519_OF_WEI25519_GG25519 : thm
  deriving Inhabited

@[nospecialize]
def setupFamily25519Maps [HolBase] (D : Family25519Deps) :
    ExceptT String IO Family25519Maps := do
  -- @@SCOPE BEGIN
  let { INTEGER_MOD_RING_RED_CONV, INT_REDUCE_CONV, MESON_TAC, define, .. } := D
  let { A_25519, CC_25519, C_25519, EDWARDS_NONSINGULAR_25519, EE_25519, E_25519,
        FIELD_INTEGER_MOD_RING, GG_25519, GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP,
        GROUP_ISOMORPHISMS_IMP_ISOMORPHISM,
        GROUP_ISOMORPHISMS_MONTGOMERY_WEIERSTRASS_GROUP, G_25519, INTEGER_MOD_RING,
        INTEGER_MOD_RING_CHAR, INTEGER_MOD_RING_CLAUSES, INT_OF_NUM_EQ,
        IN_INTEGER_MOD_RING_CARRIER, ISOMORPHIC_GROUP_SYM, PAIR_EQ, PRIME_P25519,
        a_25519, b_25519, curve25519_group, d_25519, e_25519, edwards25519_group,
        edwards_of_montgomery, isomorphic_group, mcurve_of_ecurve,
        montgomery_nonsingular, montgomery_of_edwards, montgomery_of_weierstrass,
        p_25519, wcurve_of_mcurve, wei25519_group, weierstrass_of_montgomery, .. } := D.core1
  -- @@SCOPE END

  /- Extra scaling factor. -/

  let c_25519 ← define r"c_25519 = 51042569399160536130206135233146329284152202253034631822681833788666877215207"

  /- Mappings between Edwards and Montgomery forms. -/

  let curve25519_of_edwards25519 ← define
   r"curve25519_of_edwards25519 =
        montgomery_of_edwards (integer_mod_ring p_25519) (&c_25519)"

  let edwards25519_of_curve25519 ← define
   r"edwards25519_of_curve25519 =
        edwards_of_montgomery (integer_mod_ring p_25519) (&c_25519)"

  let MCURVE_OF_ECURVE_25519 ← prove
   r"mcurve_of_ecurve (integer_mod_ring p_25519,&e_25519,&d_25519) (&c_25519) =
   (integer_mod_ring p_25519,&A_25519,&1)"
   (← do
    pure (REWRITE_TAC [mcurve_of_ecurve, PAIR_EQ] THEN
    REWRITE_TAC [p_25519, A_25519, e_25519, d_25519, c_25519] THEN
    CONV_TAC (DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN REWRITE_TAC []))

  let GROUP_ISOMORPHISMS_EDWARDS25519_CURVE25519 ← prove
   r"group_isomorphisms
      (edwards25519_group,curve25519_group)
      (curve25519_of_edwards25519,edwards25519_of_curve25519)"
   (← do
    pure (MP_TAC (← ISPECL
     [← q r"integer_mod_ring p_25519", ← q r"&e_25519:int", ← q r"&d_25519:int",
      ← q r"&c_25519:int"]
     GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP) THEN
    REWRITE_TAC [← GSYM curve25519_of_edwards25519, ← GSYM edwards25519_of_curve25519,
                 ← GSYM curve25519_group, ← GSYM edwards25519_group,
                 MCURVE_OF_ECURVE_25519] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [EDWARDS_NONSINGULAR_25519] THEN
    REWRITE_TAC [FIELD_INTEGER_MOD_RING, PRIME_P25519] THEN
    REWRITE_TAC [INTEGER_MOD_RING_CHAR, ← GSYM INT_OF_NUM_EQ] THEN
    REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER, INTEGER_MOD_RING] THEN
    REWRITE_TAC [p_25519, e_25519, d_25519, c_25519] THEN
    CONV_TAC INT_REDUCE_CONV))

  let ISOMORPHIC_GROUPS_EDWARDS25519_CURVE25519 ← prove
   r"edwards25519_group isomorphic_group curve25519_group"
   (← do
    pure (MP_TAC GROUP_ISOMORPHISMS_EDWARDS25519_CURVE25519 THEN
    MESON_TAC [isomorphic_group, GROUP_ISOMORPHISMS_IMP_ISOMORPHISM]))

  let ISOMORPHIC_GROUPS_CURVE25519_EDWARDS25519 ← prove
   r"curve25519_group isomorphic_group edwards25519_group"
   (← do
    pure (ONCE_REWRITE_TAC [ISOMORPHIC_GROUP_SYM] THEN
    REWRITE_TAC [ISOMORPHIC_GROUPS_EDWARDS25519_CURVE25519]))

  let CURVE25519_OF_EDWARDS25519_E25519 ← prove
   r"curve25519_of_edwards25519 E_25519 = C_25519"
   (← do
    pure (REWRITE_TAC [curve25519_of_edwards25519, montgomery_of_edwards,
      C_25519, E_25519, PAIR_EQ, p_25519, e_25519, d_25519, c_25519] THEN
    CONV_TAC (DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
    CONV_TAC INT_REDUCE_CONV))

  let CURVE25519_OF_EDWARDS25519_EE25519 ← prove
   r"curve25519_of_edwards25519 EE_25519 = CC_25519"
   (← do
    pure (REWRITE_TAC [curve25519_of_edwards25519, montgomery_of_edwards,
      CC_25519, EE_25519, PAIR_EQ, p_25519, e_25519, d_25519, c_25519] THEN
    CONV_TAC (DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
    CONV_TAC INT_REDUCE_CONV))

  let EDWARDS25519_OF_CURVE25519_C25519 ← prove
   r"edwards25519_of_curve25519 C_25519 = E_25519"
   (← do
    pure (REWRITE_TAC [edwards25519_of_curve25519, edwards_of_montgomery,
       C_25519, E_25519, PAIR_EQ, p_25519, e_25519, d_25519, c_25519] THEN
    CONV_TAC (DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
    CONV_TAC INT_REDUCE_CONV))

  let EDWARDS25519_OF_CURVE25519_CC25519 ← prove
   r"edwards25519_of_curve25519 CC_25519 = EE_25519"
   (← do
    pure (REWRITE_TAC [edwards25519_of_curve25519, edwards_of_montgomery,
      CC_25519, EE_25519, PAIR_EQ, p_25519, e_25519, d_25519, c_25519] THEN
    CONV_TAC (DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
    CONV_TAC INT_REDUCE_CONV))

  /- Mappings between Montgomery and Weierstrass forms. -/

  let wei25519_of_curve25519 ← define
   r"wei25519_of_curve25519 =
        weierstrass_of_montgomery (integer_mod_ring p_25519,&A_25519,&1)"

  let curve25519_of_wei25519 ← define
   r"curve25519_of_wei25519 =
        montgomery_of_weierstrass (integer_mod_ring p_25519,&A_25519,&1)"

  let WCURVE_OF_MCURVE_25519 ← prove
   r"wcurve_of_mcurve(integer_mod_ring p_25519,&A_25519,&1) =
   (integer_mod_ring p_25519,&a_25519,&b_25519)"
   (← do
    pure (REWRITE_TAC [wcurve_of_mcurve, p_25519, PAIR_EQ,
                 a_25519, b_25519, A_25519] THEN
    CONV_TAC (DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
    REWRITE_TAC []))

  let GROUP_ISOMORPHISMS_CURVE25519_WEI25519 ← prove
   r"group_isomorphisms
      (curve25519_group,wei25519_group)
      (wei25519_of_curve25519,curve25519_of_wei25519)"
   (← do
    pure (MP_TAC (← ISPECL
     [← q r"integer_mod_ring p_25519", ← q r"&A_25519:int", ← q r"&1:int"]
     GROUP_ISOMORPHISMS_MONTGOMERY_WEIERSTRASS_GROUP) THEN
    REWRITE_TAC [← GSYM wei25519_of_curve25519, ← GSYM curve25519_of_wei25519,
                 ← GSYM wei25519_group, ← GSYM curve25519_group,
                 WCURVE_OF_MCURVE_25519] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC [montgomery_nonsingular] THEN
    REWRITE_TAC [FIELD_INTEGER_MOD_RING, PRIME_P25519] THEN
    REWRITE_TAC [INTEGER_MOD_RING_CHAR, ← GSYM INT_OF_NUM_EQ] THEN
    REWRITE_TAC [IN_INTEGER_MOD_RING_CARRIER, INTEGER_MOD_RING_CLAUSES] THEN
    REWRITE_TAC [p_25519, A_25519] THEN CONV_TAC INT_REDUCE_CONV))

  let ISOMORPHIC_GROUPS_CURVE25519_WEI25519 ← prove
   r"curve25519_group isomorphic_group wei25519_group"
   (← do
    pure (MP_TAC GROUP_ISOMORPHISMS_CURVE25519_WEI25519 THEN
    MESON_TAC [isomorphic_group, GROUP_ISOMORPHISMS_IMP_ISOMORPHISM]))

  let ISOMORPHIC_GROUPS_WEI25519_CURVE25519 ← prove
   r"wei25519_group isomorphic_group curve25519_group"
   (← do
    pure (ONCE_REWRITE_TAC [ISOMORPHIC_GROUP_SYM] THEN
    REWRITE_TAC [ISOMORPHIC_GROUPS_CURVE25519_WEI25519]))

  let WEI25519_OF_CURVE25519_C25519 ← prove
   r"wei25519_of_curve25519 C_25519 = G_25519"
   (← do
    pure (REWRITE_TAC [wei25519_of_curve25519, weierstrass_of_montgomery,
       C_25519, G_25519, PAIR_EQ, p_25519, A_25519] THEN
    CONV_TAC (DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
    CONV_TAC INT_REDUCE_CONV))

  let WEI25519_OF_CURVE25519_CC25519 ← prove
   r"wei25519_of_curve25519 CC_25519 = GG_25519"
   (← do
    pure (REWRITE_TAC [wei25519_of_curve25519, weierstrass_of_montgomery,
       CC_25519, GG_25519, PAIR_EQ, p_25519, A_25519] THEN
    CONV_TAC (DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
    CONV_TAC INT_REDUCE_CONV))

  let CURVE25519_OF_WEI25519_G25519 ← prove
   r"curve25519_of_wei25519 G_25519 = C_25519"
   (← do
    pure (REWRITE_TAC [curve25519_of_wei25519, montgomery_of_weierstrass,
       C_25519, G_25519, PAIR_EQ, p_25519, A_25519] THEN
    CONV_TAC (DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
    CONV_TAC INT_REDUCE_CONV))

  let CURVE25519_OF_WEI25519_GG25519 ← prove
   r"curve25519_of_wei25519 GG_25519 = CC_25519"
   (← do
    pure (REWRITE_TAC [curve25519_of_wei25519, montgomery_of_weierstrass,
       CC_25519, GG_25519, PAIR_EQ, p_25519, A_25519] THEN
    CONV_TAC (DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THEN
    CONV_TAC INT_REDUCE_CONV))

  -- @@RETURN BEGIN
  return { c_25519, curve25519_of_edwards25519, edwards25519_of_curve25519,
           MCURVE_OF_ECURVE_25519, GROUP_ISOMORPHISMS_EDWARDS25519_CURVE25519,
           ISOMORPHIC_GROUPS_EDWARDS25519_CURVE25519,
           ISOMORPHIC_GROUPS_CURVE25519_EDWARDS25519, CURVE25519_OF_EDWARDS25519_E25519,
           CURVE25519_OF_EDWARDS25519_EE25519, EDWARDS25519_OF_CURVE25519_C25519,
           EDWARDS25519_OF_CURVE25519_CC25519, wei25519_of_curve25519,
           curve25519_of_wei25519, WCURVE_OF_MCURVE_25519,
           GROUP_ISOMORPHISMS_CURVE25519_WEI25519, ISOMORPHIC_GROUPS_CURVE25519_WEI25519,
           ISOMORPHIC_GROUPS_WEI25519_CURVE25519, WEI25519_OF_CURVE25519_C25519,
           WEI25519_OF_CURVE25519_CC25519, CURVE25519_OF_WEI25519_G25519,
           CURVE25519_OF_WEI25519_GG25519 }
  -- @@RETURN END

end HolEC.Family25519
