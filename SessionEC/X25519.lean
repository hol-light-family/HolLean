/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/x25519.ml                                     . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/X25519.lean

  The session half of the x25519.ml translation: it supplies HolEC.X25519's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/x25519.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.X25519
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Integer
import SessionLibrary.Isum
import SessionLibrary.Binomial
import SessionLibrary.Products
import SessionLibrary.Multiplicative
import SessionLibrary.Primitive
import SessionLibrary.Frag
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.GroupTheory
import SessionLibrary.RingTheory
import SessionEC.Misc
import SessionEC.Montgomery
import SessionEC.ExcludeRoots
import SessionEC.ComputeGroup
import SessionEC.Curve25519
import SessionEC.XZProjective

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionEC.X25519

/-- The core theorems x25519.ml uses. -/
def core1 : HolEC.X25519.CoreThms1 where
  ADD_CLAUSES := Session.ADD_CLAUSES
  AND_FORALL_THM := Session.AND_FORALL_THM
  ARITH_EQ := Session.ARITH_EQ
  ARITH_LE := Session.ARITH_LE
  ARITH_LT := Session.ARITH_LT
  A_25519 := SessionEC.Curve25519.«A_25519»
  COND_SWAP := Session.COND_SWAP
  CONG := Session.CONG
  CONG_SQUARE_1_PRIME_POWER := SessionLibrary.Pocklington.«CONG_SQUARE_1_PRIME_POWER»
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  COPRIME_SYM := SessionLibrary.Prime.«COPRIME_SYM»
  CURVE25519_GROUP := SessionEC.Curve25519.«CURVE25519_GROUP»
  C_25519 := SessionEC.Curve25519.«C_25519»
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_MOD := Session.DIVIDES_MOD
  DIVIDES_ONE := Session.DIVIDES_ONE
  EQ_IMP := Session.EQ_IMP
  EULER_CRITERION := SessionLibrary.Primitive.«EULER_CRITERION»
  EVEN := Session.EVEN
  EXISTS_OPTION_THM := Session.EXISTS_OPTION_THM
  EXISTS_OR_THM := Session.EXISTS_OR_THM
  EXISTS_PAIR_THM := Session.EXISTS_PAIR_THM
  EXP_1 := Session.EXP_1
  EXP_2 := Session.EXP_2
  EXP_EXP := Session.EXP_EXP
  FERMAT_LITTLE_PRIME := SessionLibrary.Pocklington.«FERMAT_LITTLE_PRIME»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_INTEGER_MOD_RING := SessionLibrary.RingTheory.«FIELD_INTEGER_MOD_RING»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FORALL_INT_CASES := Session.FORALL_INT_CASES
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_OPTION_THM := Session.FORALL_OPTION_THM
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  GENERATOR_IN_GROUP_CARRIER_CURVE25519 := SessionEC.Curve25519.«GENERATOR_IN_GROUP_CARRIER_CURVE25519»
  GROUP_ELEMENT_ORDER_CURVE25519_C25519 := SessionEC.Curve25519.«GROUP_ELEMENT_ORDER_CURVE25519_C25519»
  GROUP_POW := SessionLibrary.GroupTheory.«GROUP_POW»
  GROUP_POW_1 := SessionLibrary.GroupTheory.«GROUP_POW_1»
  GROUP_POW_EQ_ID := SessionLibrary.GroupTheory.«GROUP_POW_EQ_ID»
  GROUP_POW_ID := SessionLibrary.GroupTheory.«GROUP_POW_ID»
  GROUP_POW_MUL := SessionLibrary.GroupTheory.«GROUP_POW_MUL»
  IMP_CONJ := Session.IMP_CONJ
  IN := Session.IN
  INTEGER_MOD_RING_CHAR := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CHAR»
  INTEGER_MOD_RING_CLAUSES := SessionLibrary.RingTheory.«INTEGER_MOD_RING_CLAUSES»
  INTEGER_MOD_RING_ROOT_EXISTS := SessionEC.Misc.«INTEGER_MOD_RING_ROOT_EXISTS»
  INTEGRAL_DOMAIN_CHAR := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_CHAR»
  INT_CONG := SessionLibrary.Integer.«INT_CONG»
  INT_CONG_LMUL := SessionLibrary.Integer.«INT_CONG_LMUL»
  INT_CONG_REFL := SessionLibrary.Integer.«INT_CONG_REFL»
  INT_CONG_RREM := Session.INT_CONG_RREM
  INT_CONG_TRANS := SessionLibrary.Integer.«INT_CONG_TRANS»
  INT_LT_REM_EQ := Session.INT_LT_REM_EQ
  INT_OF_NUM_CLAUSES := Session.INT_OF_NUM_CLAUSES
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_OF_NUM_REM := Session.INT_OF_NUM_REM
  INT_POS := Session.INT_POS
  INT_REM_EQ := Session.INT_REM_EQ
  INT_REM_EQ_0 := Session.INT_REM_EQ_0
  INT_REM_POS_EQ := Session.INT_REM_POS_EQ
  INT_REM_REM := Session.INT_REM_REM
  INVERSE_MOD_LMUL_EQ := SessionLibrary.Pocklington.«INVERSE_MOD_LMUL_EQ»
  INVERSE_MOD_RMUL_EQ := SessionLibrary.Pocklington.«INVERSE_MOD_RMUL_EQ»
  IN_CROSS := Session.IN_CROSS
  IN_INTEGER_MOD_RING_CARRIER := SessionLibrary.RingTheory.«IN_INTEGER_MOD_RING_CARRIER»
  MOD_0 := Session.MOD_0
  MOD_LT := Session.MOD_LT
  MOD_LT_EQ_LT := Session.MOD_LT_EQ_LT
  MOD_MOD_EXP_MIN := Session.MOD_MOD_EXP_MIN
  MOD_MULT_ADD := Session.MOD_MULT_ADD
  MOD_MULT_MOD2 := Session.MOD_MULT_MOD2
  MONTGOMERY_GROUP := SessionEC.Montgomery.«MONTGOMERY_GROUP»
  MONTGOMERY_NONSINGULAR_CURVE25519 := SessionEC.Curve25519.«MONTGOMERY_NONSINGULAR_CURVE25519»
  MONTGOMERY_XMAP_EQ_0 := SessionEC.XZProjective.«MONTGOMERY_XMAP_EQ_0»
  MONTGOMERY_XZDIFFADD_GROUP := SessionEC.XZProjective.«MONTGOMERY_XZDIFFADD_GROUP»
  MONTGOMERY_XZDOUBLE_GROUP := SessionEC.XZProjective.«MONTGOMERY_XZDOUBLE_GROUP»
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EXP := Session.MULT_EXP
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_IMP := Session.NOT_IMP
  PAIR_EQ := Session.PAIR_EQ
  PRIME_1 := SessionLibrary.Prime.«PRIME_1»
  PRIME_COPRIME_EQ := SessionLibrary.Prime.«PRIME_COPRIME_EQ»
  PRIME_DIVEXP_EQ := SessionLibrary.Prime.«PRIME_DIVEXP_EQ»
  PRIME_DIVPROD_EQ := SessionLibrary.Prime.«PRIME_DIVPROD_EQ»
  PRIME_P25519 := SessionEC.Curve25519.«PRIME_P25519»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_CHAR_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_CHAR_MONOMORPHIC_IMAGE»
  RING_DIV := SessionLibrary.RingTheory.«RING_DIV»
  RING_DIV_1 := SessionLibrary.RingTheory.«RING_DIV_1»
  RING_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM»
  RING_LINV_UNIQUE := SessionLibrary.RingTheory.«RING_LINV_UNIQUE»
  RING_MONOMORPHISM_ALT := SessionLibrary.RingTheory.«RING_MONOMORPHISM_ALT»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_NEG_0 := SessionLibrary.RingTheory.«RING_NEG_0»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INT_CLAUSES := SessionLibrary.RingTheory.«RING_OF_INT_CLAUSES»
  RING_OF_INT_EQ := SessionLibrary.RingTheory.«RING_OF_INT_EQ»
  RING_OF_INT_EQ_0 := SessionLibrary.RingTheory.«RING_OF_INT_EQ_0»
  RING_OF_INT_NEG := SessionLibrary.RingTheory.«RING_OF_INT_NEG»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_INT_REM := SessionLibrary.RingTheory.«RING_OF_INT_REM»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_0 := SessionLibrary.RingTheory.«RING_OF_NUM_0»
  RING_OF_NUM_1 := SessionLibrary.RingTheory.«RING_OF_NUM_1»
  RING_OF_NUM_EQ := SessionLibrary.RingTheory.«RING_OF_NUM_EQ»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_OF_NUM_MOD := SessionLibrary.RingTheory.«RING_OF_NUM_MOD»
  RING_OF_NUM_MUL := SessionLibrary.RingTheory.«RING_OF_NUM_MUL»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_2 := SessionLibrary.RingTheory.«RING_POW_2»
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SUBSET := Session.SUBSET
  SUB_0 := Session.SUB_0
  curve25519 := SessionEC.Curve25519.«curve25519»
  curve25519_group := SessionEC.Curve25519.«curve25519_group»
  field := SessionLibrary.RingTheory.«field»
  group_pow := SessionLibrary.GroupTheory.«group_pow»
  montgomery_add := SessionEC.Montgomery.«montgomery_add»
  montgomery_curve := SessionEC.Montgomery.«montgomery_curve»
  montgomery_nonsingular := SessionEC.Montgomery.«montgomery_nonsingular»
  montgomery_xmap := SessionEC.XZProjective.«montgomery_xmap»
  montgomery_xz := SessionEC.XZProjective.«montgomery_xz»
  montgomery_xzdiffadd := SessionEC.XZProjective.«montgomery_xzdiffadd»
  montgomery_xzdouble := SessionEC.XZProjective.«montgomery_xzdouble»
  n_25519 := SessionEC.Curve25519.«n_25519»
  num_WF := Session.num_WF
  num_congruent := Session.num_congruent
  num_divides := Session.num_divides
  p_25519 := SessionEC.Curve25519.«p_25519»
  ring_0 := SessionLibrary.RingTheory.«ring_0»
  ring_1 := SessionLibrary.RingTheory.«ring_1»
  ring_add := SessionLibrary.RingTheory.«ring_add»
  ring_carrier := SessionLibrary.RingTheory.«ring_carrier»
  ring_div := SessionLibrary.RingTheory.«ring_div»
  ring_mul := SessionLibrary.RingTheory.«ring_mul»
  ring_neg := SessionLibrary.RingTheory.«ring_neg»
  ring_of_num := SessionLibrary.RingTheory.«ring_of_num»
  ring_tybij := SessionLibrary.RingTheory.«ring_tybij»

/-- What x25519.ml uses from Session. -/
def deps : HolEC.X25519.X25519Deps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  METIS_TAC := Session.METIS_TAC
  ASM_METIS_TAC := Session.ASM_METIS_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  TAUT t := ExceptT.mk (Session.TAUT t)
  INDUCT_TAC := Session.INDUCT_TAC
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)
  INT_ARITH_TAC := Session.INT_ARITH_TAC
  ASM_INT_ARITH_TAC := Session.ASM_INT_ARITH_TAC
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  INTEGER_TAC := Session.INTEGER_TAC
  NUMBER_RULE := Session.NUMBER_RULE
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  INT_REDUCE_CONV := Session.INT_REDUCE_CONV
  INT_RED_CONV := Session.INT_RED_CONV
  INT_REM_DOWN_CONV := Session.INT_REM_DOWN_CONV
  HAS_SIZE_CONV := Session.HAS_SIZE_CONV
  let_CONV := Session.let_CONV
  num_CONV := Session.num_CONV
  mk_numeral := Session.mk_numeral
  PRIME_CONV t := ExceptT.mk (SessionLibrary.Pocklington.PRIME_CONV t)
  PRIME_RULE := SessionLibrary.Pocklington.PRIME_RULE
  RING_RULE t := ExceptT.mk (SessionLibrary.RingTheory.RING_RULE t)
  INTEGRAL_DOMAIN_RULE t := ExceptT.mk (SessionLibrary.RingTheory.INTEGRAL_DOMAIN_RULE t)
  FIELD_TAC := SessionLibrary.RingTheory.FIELD_TAC
  RING_CARRIER_TAC := SessionLibrary.RingTheory.RING_CARRIER_TAC
  RING_TAC := SessionLibrary.RingTheory.RING_TAC
  RING_PULL_DIV_TAC := SessionLibrary.RingTheory.RING_PULL_DIV_TAC
  LET_TAC := Session.LET_TAC
  GROUP_RULE t := ExceptT.mk (SessionLibrary.GroupTheory.GROUP_RULE t)
  basic_ss := Session.basic_ss
  INTEGER_MOD_RING_RED_CONV := SessionLibrary.RingTheory.INTEGER_MOD_RING_RED_CONV
  NUM_SUB_CONV := Session.NUM_SUB_CONV
  NUM_EQ_CONV := Session.NUM_EQ_CONV
  NUM_DIV_CONV := Session.NUM_DIV_CONV
  EXP_MOD_CONV := Session.EXP_MOD_CONV
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  DIVIDES_CONV := SessionLibrary.Prime.DIVIDES_CONV
  COPRIME_CONV := SessionLibrary.Prime.COPRIME_CONV
  NOT_RING_CHAR_DIVIDES_TAC := SessionEC.Misc.NOT_RING_CHAR_DIVIDES_TAC
  EXCLUDE_MODULAR_CUBIC_ROOTS_TAC := SessionEC.ExcludeRoots.EXCLUDE_MODULAR_CUBIC_ROOTS_TAC
  add_curve := SessionEC.ComputeGroup.add_curve
  add_curvezero := SessionEC.ComputeGroup.add_curvezero
  add_curveneg := SessionEC.ComputeGroup.add_curveneg
  add_curveadd := SessionEC.ComputeGroup.add_curveadd
  add_ecgroup := SessionEC.ComputeGroup.add_ecgroup
  ECGROUP_CARRIER_CONV := SessionEC.ComputeGroup.ECGROUP_CARRIER_CONV
  ECGROUP_ID_CONV := SessionEC.ComputeGroup.ECGROUP_ID_CONV
  ECGROUP_INV_CONV := SessionEC.ComputeGroup.ECGROUP_INV_CONV
  ECGROUP_MUL_CONV := SessionEC.ComputeGroup.ECGROUP_MUL_CONV
  ECGROUP_POW_CONV := SessionEC.ComputeGroup.ECGROUP_POW_CONV
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in x25519.ml order. -/
initialize BX25519Curve : HolEC.X25519.X25519Curve ←
  ioB "setupX25519Curve" (HolEC.X25519.setupX25519Curve deps).run
initialize BX25519Quadratic : HolEC.X25519.X25519Quadratic ←
  ioB "setupX25519Quadratic" (HolEC.X25519.setupX25519Quadratic deps).run
initialize BX25519Pure : HolEC.X25519.X25519Pure ←
  ioB "setupX25519Pure" (HolEC.X25519.setupX25519Pure deps BX25519Curve BX25519Quadratic).run
initialize BX25519Rfc : HolEC.X25519.X25519Rfc ←
  ioB "setupX25519Rfc" (HolEC.X25519.setupX25519Rfc deps BX25519Curve BX25519Pure).run

-- X25519Curve
def curve25519x : thm := BX25519Curve.curve25519x
def curve25519x_curve25519 : thm := BX25519Curve.curve25519x_curve25519
def MONTGOMERY_NONSINGULAR_CURVE25519X_GEN : thm := BX25519Curve.MONTGOMERY_NONSINGULAR_CURVE25519X_GEN
def MONTGOMERY_NONSINGULAR_CURVE25519X : thm := BX25519Curve.MONTGOMERY_NONSINGULAR_CURVE25519X
def SPECIALLY_NONSINGULAR_CURVE25519X : thm := BX25519Curve.SPECIALLY_NONSINGULAR_CURVE25519X
def curve25519x_group : thm := BX25519Curve.curve25519x_group
def CURVE25519X_CURVE25519_GROUP : thm := BX25519Curve.CURVE25519X_CURVE25519_GROUP
def CURVE25519X_GROUP_GEN : thm := BX25519Curve.CURVE25519X_GROUP_GEN
def CURVE25519X_GROUP : thm := BX25519Curve.CURVE25519X_GROUP
def GROUP_POW_CURVE25519X_TORSION : thm := BX25519Curve.GROUP_POW_CURVE25519X_TORSION

-- X25519Quadratic
def quadratic_extension : thm := BX25519Quadratic.quadratic_extension
def QUADRATIC_EXTENSION : thm := BX25519Quadratic.QUADRATIC_EXTENSION
def RING_HOMOMORPHISM_INTO_QUADRATIC_EXTENSION : thm := BX25519Quadratic.RING_HOMOMORPHISM_INTO_QUADRATIC_EXTENSION
def RING_MONOMORPHISM_INTO_QUADRATIC_EXTENSION : thm := BX25519Quadratic.RING_MONOMORPHISM_INTO_QUADRATIC_EXTENSION
def RING_OF_NUM_QUADRATIC_EXTENSION : thm := BX25519Quadratic.RING_OF_NUM_QUADRATIC_EXTENSION
def RING_OF_INT_QUADRATIC_EXTENSION : thm := BX25519Quadratic.RING_OF_INT_QUADRATIC_EXTENSION
def RING_CHAR_QUADRATIC_EXTENSION : thm := BX25519Quadratic.RING_CHAR_QUADRATIC_EXTENSION
def FIELD_QUADRATIC_EXTENSION : thm := BX25519Quadratic.FIELD_QUADRATIC_EXTENSION
def sqintmod_field : thm := BX25519Quadratic.sqintmod_field
def FIELD_SQINTMOD_FIELD : thm := BX25519Quadratic.FIELD_SQINTMOD_FIELD
def RING_CHAR_SQINTMOD_FIELD : thm := BX25519Quadratic.RING_CHAR_SQINTMOD_FIELD
def SQUARE_ROOTS_SQINTMOD_FIELD : thm := BX25519Quadratic.SQUARE_ROOTS_SQINTMOD_FIELD

-- X25519Pure
def x25519_ladderstep : thm := BX25519Pure.x25519_ladderstep
def x25519_ladder : thm := BX25519Pure.x25519_ladder
def purex25519_def : thm := BX25519Pure.purex25519_def
def PUREX25519_LADDER : thm := BX25519Pure.PUREX25519_LADDER
def PUREX25519_BOUND : thm := BX25519Pure.PUREX25519_BOUND
def PUREX25519 : thm := BX25519Pure.PUREX25519
def PUREX25519_UNIQUE : thm := BX25519Pure.PUREX25519_UNIQUE
def purex25519 : thm := BX25519Pure.purex25519
def PUREX25519_MOD : thm := BX25519Pure.PUREX25519_MOD
def PUREX25519_UNIQUE_IMP : thm := BX25519Pure.PUREX25519_UNIQUE_IMP

-- X25519Rfc
def rfcx25519 : thm := BX25519Rfc.rfcx25519
def RFCX25519_PUREX25519 : thm := BX25519Rfc.RFCX25519_PUREX25519
def RFCX25519_BASE_NONZERO : thm := BX25519Rfc.RFCX25519_BASE_NONZERO

/-- `needs "EC/x25519.ml"`: already done by importing this module. -/
def ensureX25519 : IO Unit := pure ()

end SessionEC.X25519
