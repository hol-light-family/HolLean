/- ---------------------------------------------------------------------- -/
/- Session wiring for EC/computegroup.ml                               . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionEC/ComputeGroup.lean

  The session half of the computegroup.ml translation: it supplies HolEC.ComputeGroup's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "EC/computegroup.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolEC.ComputeGroup
import SessionLibrary.Frag
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.Prime
import SessionLibrary.GroupTheory
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Pocklington
import SessionLibrary.RingTheory

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionEC.ComputeGroup

/-- The core theorems computegroup.ml uses. -/
def core1 : HolEC.ComputeGroup.CoreThms1 where
  BIT0 := Session.BIT0
  COND_CLAUSES := Session.COND_CLAUSES
  GROUP_POW_2 := SessionLibrary.GroupTheory.«GROUP_POW_2»
  GROUP_POW_POW := SessionLibrary.GroupTheory.«GROUP_POW_POW»
  IN := Session.IN
  IN_INTEGER_MOD_RING_CARRIER := SessionLibrary.RingTheory.«IN_INTEGER_MOD_RING_CARRIER»
  MULT_2 := Session.MULT_2
  NUMERAL := Session.NUMERAL
  group_pow := SessionLibrary.GroupTheory.«group_pow»

/-- What computegroup.ml uses from Session. -/
def deps : HolEC.ComputeGroup.ComputeGroupDeps where
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
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in computegroup.ml order. -/
initialize BComputeGroupConvs : HolEC.ComputeGroup.ComputeGroupConvs ←
  ioB "setupComputeGroupConvs" (HolEC.ComputeGroup.setupComputeGroupConvs deps).run

-- ComputeGroupConvs
def curve_clauses : Option (IO.Ref (List thm)) := BComputeGroupConvs.curve_clauses
def curvezero_clauses : Option (IO.Ref (List thm)) := BComputeGroupConvs.curvezero_clauses
def curveneg_clauses : Option (IO.Ref (List thm)) := BComputeGroupConvs.curveneg_clauses
def curveadd_clauses : Option (IO.Ref (List thm)) := BComputeGroupConvs.curveadd_clauses
def ecgroup_carriers : Option (IO.Ref (List thm)) := BComputeGroupConvs.ecgroup_carriers
def ecgroup_ids : Option (IO.Ref (List thm)) := BComputeGroupConvs.ecgroup_ids
def ecgroup_invs : Option (IO.Ref (List thm)) := BComputeGroupConvs.ecgroup_invs
def ecgroup_muls : Option (IO.Ref (List thm)) := BComputeGroupConvs.ecgroup_muls
def add_curve : thm → IO Unit := BComputeGroupConvs.add_curve
def add_curvezero : thm → IO Unit := BComputeGroupConvs.add_curvezero
def add_curveneg : thm → IO Unit := BComputeGroupConvs.add_curveneg
def add_curveadd : thm → IO Unit := BComputeGroupConvs.add_curveadd
def add_ecgroup : List thm → thm → ExceptT String IO Unit := BComputeGroupConvs.add_ecgroup
def ECGROUP_CARRIER_CONV : HolCore.Equal.ioconv := BComputeGroupConvs.ECGROUP_CARRIER_CONV
def ECGROUP_ID_CONV : HolCore.Equal.ioconv := BComputeGroupConvs.ECGROUP_ID_CONV
def ECGROUP_INV_CONV : HolCore.Equal.ioconv := BComputeGroupConvs.ECGROUP_INV_CONV
def ECGROUP_MUL_CONV : HolCore.Equal.ioconv := BComputeGroupConvs.ECGROUP_MUL_CONV
def ECGROUP_POW_CONV : HolCore.Equal.ioconv := BComputeGroupConvs.ECGROUP_POW_CONV

/-- `needs "EC/computegroup.ml"`: already done by importing this module. -/
def ensureComputeGroup : IO Unit := pure ()

end SessionEC.ComputeGroup
