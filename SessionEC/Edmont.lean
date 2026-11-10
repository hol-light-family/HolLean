/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/edmont.ml                                     . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/Edmont.lean

  The session half of the edmont.ml translation: it supplies HolEC.Edmont's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/edmont.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.Edmont
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
import SessionEC.Edwards
import SessionEC.Montgomery

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionEC.Edmont

/-- The core theorems edmont.ml uses. -/
def core1 : HolEC.Edmont.CoreThms1 where
  ABELIAN_EDWARDS_GROUP := SessionEC.Edwards.«ABELIAN_EDWARDS_GROUP»
  ABELIAN_MONTGOMERY_GROUP := SessionEC.Montgomery.«ABELIAN_MONTGOMERY_GROUP»
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  EDWARDS_GROUP := SessionEC.Edwards.«EDWARDS_GROUP»
  EDWARDS_NONSINGULAR_DENOMINATORS := SessionEC.Edwards.«EDWARDS_NONSINGULAR_DENOMINATORS»
  FIELD_CHAR_NOT2 := SessionEC.Misc.«FIELD_CHAR_NOT2»
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_INV_EQ_0 := SessionLibrary.RingTheory.«FIELD_INV_EQ_0»
  FIELD_MUL_EQ_0 := SessionLibrary.RingTheory.«FIELD_MUL_EQ_0»
  FIELD_POW_EQ_0 := SessionLibrary.RingTheory.«FIELD_POW_EQ_0»
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_OPTION_THM := Session.FORALL_OPTION_THM
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  GROUP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM»
  GROUP_INV := SessionLibrary.GroupTheory.«GROUP_INV»
  GROUP_ISOMORPHISMS := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISMS»
  GROUP_ISOMORPHISMS_IMP_ISOMORPHISM := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISMS_IMP_ISOMORPHISM»
  GROUP_ISOMORPHISMS_SYM := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISMS_SYM»
  GROUP_LID_EQ := SessionLibrary.GroupTheory.«GROUP_LID_EQ»
  GROUP_MUL := SessionLibrary.GroupTheory.«GROUP_MUL»
  GROUP_MUL_ASSOC := SessionLibrary.GroupTheory.«GROUP_MUL_ASSOC»
  GROUP_MUL_LCANCEL := SessionLibrary.GroupTheory.«GROUP_MUL_LCANCEL»
  GROUP_MUL_LID := SessionLibrary.GroupTheory.«GROUP_MUL_LID»
  GROUP_MUL_RID := SessionLibrary.GroupTheory.«GROUP_MUL_RID»
  GROUP_RINV_EQ := SessionLibrary.GroupTheory.«GROUP_RINV_EQ»
  IMP_CONJ := Session.IMP_CONJ
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  IMP_IMP := Session.IMP_IMP
  IN := Session.IN
  ISOMORPHIC_GROUP_SYM := SessionLibrary.GroupTheory.«ISOMORPHIC_GROUP_SYM»
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  MONTGOMERY_GROUP := SessionEC.Montgomery.«MONTGOMERY_GROUP»
  MONTGOMERY_STRONGLY_NONSINGULAR := SessionEC.Montgomery.«MONTGOMERY_STRONGLY_NONSINGULAR»
  MONTGOMERY_STRONGLY_NONSINGULAR_IMP_NONSINGULAR := SessionEC.Montgomery.«MONTGOMERY_STRONGLY_NONSINGULAR_IMP_NONSINGULAR»
  PAIR_EQ := Session.PAIR_EQ
  PRIME_2 := SessionLibrary.Prime.«PRIME_2»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_ADD_LZERO := SessionLibrary.RingTheory.«RING_ADD_LZERO»
  RING_ADD_RZERO := SessionLibrary.RingTheory.«RING_ADD_RZERO»
  RING_CHAR_DIVIDES_PRIME := SessionLibrary.RingTheory.«RING_CHAR_DIVIDES_PRIME»
  RING_CLAUSES := SessionLibrary.RingTheory.«RING_CLAUSES»
  RING_DIV_1 := SessionLibrary.RingTheory.«RING_DIV_1»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_INV_MUL := SessionLibrary.RingTheory.«RING_INV_MUL»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LNEG := SessionLibrary.RingTheory.«RING_MUL_LNEG»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RNEG := SessionLibrary.RingTheory.«RING_MUL_RNEG»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_NEG := SessionLibrary.RingTheory.«RING_NEG»
  RING_NEG_EQ := SessionLibrary.RingTheory.«RING_NEG_EQ»
  RING_NEG_EQ_0 := SessionLibrary.RingTheory.«RING_NEG_EQ_0»
  RING_NEG_NEG := SessionLibrary.RingTheory.«RING_NEG_NEG»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_2 := SessionLibrary.RingTheory.«RING_POW_2»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_RZERO := SessionLibrary.RingTheory.«RING_SUB_RZERO»
  SUBSET := Session.SUBSET
  abelian_group := SessionLibrary.GroupTheory.«abelian_group»
  edwards_0 := SessionEC.Edwards.«edwards_0»
  edwards_add := SessionEC.Edwards.«edwards_add»
  edwards_curve := SessionEC.Edwards.«edwards_curve»
  edwards_neg := SessionEC.Edwards.«edwards_neg»
  edwards_nonsingular := SessionEC.Edwards.«edwards_nonsingular»
  isomorphic_group := SessionLibrary.GroupTheory.«isomorphic_group»
  montgomery_add := SessionEC.Montgomery.«montgomery_add»
  montgomery_curve := SessionEC.Montgomery.«montgomery_curve»
  montgomery_neg := SessionEC.Montgomery.«montgomery_neg»
  montgomery_nonsingular := SessionEC.Montgomery.«montgomery_nonsingular»
  montgomery_strongly_nonsingular := SessionEC.Montgomery.«montgomery_strongly_nonsingular»
  option_DISTINCT := Session.indTypesBoot.option_DISTINCT
  option_INJ := Session.indTypesBoot.option_INJ
  ring_div := SessionLibrary.RingTheory.«ring_div»

/-- What edmont.ml uses from Session. -/
def deps : HolEC.Edmont.EdmontDeps where
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
  NOT_RING_CHAR_DIVIDES_TAC := SessionEC.Misc.NOT_RING_CHAR_DIVIDES_TAC
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in edmont.ml order. -/
initialize BEdmontDefs : HolEC.Edmont.EdmontDefs ←
  ioB "setupEdmontDefs" (HolEC.Edmont.setupEdmontDefs deps).run
initialize BEdmontMaps : HolEC.Edmont.EdmontMaps ←
  ioB "setupEdmontMaps" (HolEC.Edmont.setupEdmontMaps deps BEdmontDefs).run
initialize BEdmontIso : HolEC.Edmont.EdmontIso ←
  ioB "setupEdmontIso" (HolEC.Edmont.setupEdmontIso deps BEdmontDefs BEdmontMaps).run
initialize BEdmontIsoCor : HolEC.Edmont.EdmontIsoCor ←
  ioB "setupEdmontIsoCor" (HolEC.Edmont.setupEdmontIsoCor deps BEdmontDefs BEdmontIso).run

-- EdmontDefs
def mcurve_of_ecurve : thm := BEdmontDefs.mcurve_of_ecurve
def montgomery_of_edwards : thm := BEdmontDefs.montgomery_of_edwards
def ecurve_of_mcurve : thm := BEdmontDefs.ecurve_of_mcurve
def edwards_of_montgomery : thm := BEdmontDefs.edwards_of_montgomery
def ECURVE_OF_MCURVE_OF_ECURVE : thm := BEdmontDefs.ECURVE_OF_MCURVE_OF_ECURVE
def MCURVE_OF_ECURVE_OF_MCURVE : thm := BEdmontDefs.MCURVE_OF_ECURVE_OF_MCURVE
def MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR_EQ : thm := BEdmontDefs.MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR_EQ
def MCURVE_OF_ECURVE_NONSINGULAR_EQ : thm := BEdmontDefs.MCURVE_OF_ECURVE_NONSINGULAR_EQ
def MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR : thm := BEdmontDefs.MCURVE_OF_ECURVE_STRONGLY_NONSINGULAR
def MCURVE_OF_ECURVE_NONSINGULAR : thm := BEdmontDefs.MCURVE_OF_ECURVE_NONSINGULAR

-- EdmontMaps
def MONTGOMERY_OF_EDWARDS : thm := BEdmontMaps.MONTGOMERY_OF_EDWARDS
def EDWARDS_OF_MONTGOMERY_OF_EDWARDS : thm := BEdmontMaps.EDWARDS_OF_MONTGOMERY_OF_EDWARDS
def EDWARDS_OF_MONTGOMERY : thm := BEdmontMaps.EDWARDS_OF_MONTGOMERY
def MONTGOMERY_OF_EDWARDS_OF_MONTGOMERY : thm := BEdmontMaps.MONTGOMERY_OF_EDWARDS_OF_MONTGOMERY

-- EdmontIso
def MONTGOMERY_OF_EDWARDS_NEG : thm := BEdmontIso.MONTGOMERY_OF_EDWARDS_NEG
def GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP : thm := BEdmontIso.GROUP_ISOMORPHISMS_EDWARDS_MONTGOMERY_GROUP

-- EdmontIsoCor
def MONTGOMERY_OF_EDWARDS_ADD : thm := BEdmontIsoCor.MONTGOMERY_OF_EDWARDS_ADD
def GROUP_ISOMORPHISMS_MONTGOMERY_EDWARDS_GROUP : thm := BEdmontIsoCor.GROUP_ISOMORPHISMS_MONTGOMERY_EDWARDS_GROUP
def ISOMORPHIC_EDWARDS_MONTGOMERY_GROUP : thm := BEdmontIsoCor.ISOMORPHIC_EDWARDS_MONTGOMERY_GROUP
def ISOMORPHIC_MONTGOMERY_EDWARDS_GROUP : thm := BEdmontIsoCor.ISOMORPHIC_MONTGOMERY_EDWARDS_GROUP

/-- `needs "EC/edmont.ml"`: already done by importing this module. -/
def ensureEdmont : IO Unit := pure ()

end SessionEC.Edmont
