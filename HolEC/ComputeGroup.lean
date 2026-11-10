/- ========================================================================= -/
/- Explicit computations of group operations from extensible clauses.      -/
/- ========================================================================= -/
/- File: HolEC/ComputeGroup.lean

  Lean4 translation by Chris Walton 2026

  A translation of HOL Light's `EC/computegroup.ml` (078839e), by hand, in file order,
  in the style of HolLibrary/Galois.lean (see there and HolMath/Base.lean for
  the conventions).  Its `needs` closure is Library/frag.ml, Library/wo.ml, Library/card.ml, Library/prime.ml, Library/grouptheory.ml, Library/binomial.ml, Library/iter.ml, Library/pocklington.ml, Library/ringtheory.ml; the theorems it uses from
  them and from the core library are supplied via the CoreThms structures
  (SessionEC.ComputeGroup fills them).

  EVALUATION ORDER.  OCaml evaluates function arguments, tuples and list
  literals right to left, so in a proof the rules nearer the end are
  evaluated first.  Where one proof applies two or more rules that print or
  use counters (MESON, ARITH_RULE, INT_ARITH, TAUT, SET_RULE, ...) they are
  bound first, in OCaml's order.
-/

import HolLibrary.Frag
import HolLibrary.Wo
import HolLibrary.Card
import HolLibrary.Prime
import HolLibrary.GroupTheory
import HolLibrary.Binomial
import HolLibrary.Iter
import HolLibrary.Pocklington
import HolLibrary.RingTheory

open HolCore HolCore.Lib HolCore.Basics
open HolCore.Kernel hiding ASSUME INST TRANS MK_COMB EQ_MP
open HolCore.Equal (ioconv lhs lhand rhs)
open HolCore.Tactics (tactic thm_tactic thm_tactical goal goalstate justification)
open HolLight HolLight.Syntax

namespace HolEC.ComputeGroup

/-- Theorems used from the core library and the parent Library files. -/
structure CoreThms1 where
  (BIT0 COND_CLAUSES GROUP_POW_2 GROUP_POW_POW IN IN_INTEGER_MOD_RING_CARRIER
   MULT_2 NUMERAL group_pow : thm)
  deriving Inhabited

/-- What computegroup.ml uses from Session besides theorems. -/
structure ComputeGroupDeps where
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

/-- The local `conv` of computegroup.ml's ECGROUP_POW_CONV (lines 89-103):
    `group_pow G x n` for a numeral `n`, by halving `n` when it is even and
    peeling off one factor when it is odd. -/
partial def ecgroupPowConv [HolBase] (num_CONV num_half_CONV conv_0 conv_1
    ECGROUP_MUL_CONV ECGROUP_CARRIER_CONV : ioconv)
    (conv_2 : term → ExceptT String IO thm) : ioconv := fun tm => ExceptT.run do
  let conv := ecgroupPowConv num_CONV num_half_CONV conv_0 conv_1 ECGROUP_MUL_CONV
    ECGROUP_CARRIER_CONV conv_2
  match tm with
  | .Comb (.Comb (.Comb (.Const "group_pow" _) _) _) ntm =>
    let n ← liftExcept (dest_numeral ntm)
    if n = 0 then ExceptT.mk (conv_0 tm)
    else if n.num % 2 = 1 then
      ExceptT.mk ((RAND_CONV num_CONV THENC conv_1 THENC
                   RAND_CONV conv THENC ECGROUP_MUL_CONV) tm)
    else
      let th1 ← ExceptT.mk (RAND_CONV num_half_CONV tm)
      let th2 ← conv_2 (← liftExcept (rand (concl th1)))
      let th3 ← MP th2
       (← EQT_ELIM (← ExceptT.mk (ECGROUP_CARRIER_CONV (← liftExcept (lhand (concl th2))))))
      let th4 ← TRANS th1 th3
      CONV_RULE (RAND_CONV (LAND_CONV ECGROUP_MUL_CONV THENC conv)) th4
  | _ => throw "ECGROUP_POW_CONV"



/- ------------------------------------------------------------------------- -/
/- Explicit computations of group operations from extensible clauses: the    -/
/- stores of clauses, the functions that augment them (for curve types and   -/
/- for specific curves), and the conversions.  (computegroup.ml 1-104;       -/
/- the recursion of ECGROUP_POW_CONV is `ecgroupPowConv` above.)             -/
/- ------------------------------------------------------------------------- -/

structure ComputeGroupConvs where
  -- @@FIELDS
  curve_clauses : Option (IO.Ref (List thm))
  curvezero_clauses : Option (IO.Ref (List thm))
  curveneg_clauses : Option (IO.Ref (List thm))
  curveadd_clauses : Option (IO.Ref (List thm))
  ecgroup_carriers : Option (IO.Ref (List thm))
  ecgroup_ids : Option (IO.Ref (List thm))
  ecgroup_invs : Option (IO.Ref (List thm))
  ecgroup_muls : Option (IO.Ref (List thm))
  add_curve : thm → IO Unit
  add_curvezero : thm → IO Unit
  add_curveneg : thm → IO Unit
  add_curveadd : thm → IO Unit
  add_ecgroup : List thm → thm → ExceptT String IO Unit
  ECGROUP_CARRIER_CONV : ioconv
  ECGROUP_ID_CONV : ioconv
  ECGROUP_INV_CONV : ioconv
  ECGROUP_MUL_CONV : ioconv
  ECGROUP_POW_CONV : ioconv
  deriving Inhabited

@[nospecialize]
def setupComputeGroupConvs [HolBase] (D : ComputeGroupDeps) :
    ExceptT String IO ComputeGroupConvs := do
  -- @@SCOPE BEGIN
  let { INTEGER_MOD_RING_RED_CONV, INT_RED_CONV, let_CONV, num_CONV, .. } := D
  let { BIT0, COND_CLAUSES, GROUP_POW_2, GROUP_POW_POW, IN,
        IN_INTEGER_MOD_RING_CARRIER, MULT_2, NUMERAL, group_pow, .. } := D.core1
  -- @@SCOPE END

  -- `let curve_clauses = ref [] and .. and ecgroup_muls = ref []`: created
  -- once, when this (cached) setup runs at load, and closed over by the
  -- functions below.  Exported as `some ref`: a structure with an `IO.Ref`
  -- field cannot derive `Inhabited` computably, so the fields are `Option`s.
  let loc_curve_clauses : IO.Ref (List thm) ← IO.mkRef []
  let loc_curvezero_clauses : IO.Ref (List thm) ← IO.mkRef []
  let loc_curveneg_clauses : IO.Ref (List thm) ← IO.mkRef []
  let loc_curveadd_clauses : IO.Ref (List thm) ← IO.mkRef []
  let loc_ecgroup_carriers : IO.Ref (List thm) ← IO.mkRef []
  let loc_ecgroup_ids : IO.Ref (List thm) ← IO.mkRef []
  let loc_ecgroup_invs : IO.Ref (List thm) ← IO.mkRef []
  let loc_ecgroup_muls : IO.Ref (List thm) ← IO.mkRef []
  let curve_clauses : Option (IO.Ref (List thm)) ← pure (some loc_curve_clauses)
  let curvezero_clauses : Option (IO.Ref (List thm)) ← pure (some loc_curvezero_clauses)
  let curveneg_clauses : Option (IO.Ref (List thm)) ← pure (some loc_curveneg_clauses)
  let curveadd_clauses : Option (IO.Ref (List thm)) ← pure (some loc_curveadd_clauses)
  let ecgroup_carriers : Option (IO.Ref (List thm)) ← pure (some loc_ecgroup_carriers)
  let ecgroup_ids : Option (IO.Ref (List thm)) ← pure (some loc_ecgroup_ids)
  let ecgroup_invs : Option (IO.Ref (List thm)) ← pure (some loc_ecgroup_invs)
  let ecgroup_muls : Option (IO.Ref (List thm)) ← pure (some loc_ecgroup_muls)

  /- Augment store of clauses, both curve types and actual specific curves. -/

  let add_curve : thm → IO Unit ← pure (fun th =>
    loc_curve_clauses.modify (insert th))
  let add_curvezero : thm → IO Unit ← pure (fun th =>
    loc_curvezero_clauses.modify (insert th))
  let add_curveneg : thm → IO Unit ← pure (fun th =>
    loc_curveneg_clauses.modify (insert th))
  let add_curveadd : thm → IO Unit ← pure (fun th =>
    loc_curveadd_clauses.modify (insert th))

  let add_ecgroup : List thm → thm → ExceptT String IO Unit ← pure (fun defs th => do
    match CONJUNCTS (← PURE_REWRITE_RULE defs th) with
    | [cth, ith, nth, ath] =>
      loc_ecgroup_carriers.modify (insert cth)
      loc_ecgroup_ids.modify (insert ith)
      loc_ecgroup_invs.modify (insert nth)
      loc_ecgroup_muls.modify (insert ath)
    | _ => throw "Match_failure")

  /- The actual conversions. -/

  let ECGROUP_CARRIER_CONV : ioconv ← pure (fun tm => do
    (GEN_REWRITE_CONV RAND_CONV (← loc_ecgroup_carriers.get) THENC
     GEN_REWRITE_CONV I [IN] THENC
     GEN_REWRITE_CONV I (← loc_curve_clauses.get) THENC
     REWRITE_CONV [IN_INTEGER_MOD_RING_CARRIER] THENC
     DEPTH_CONV (INTEGER_MOD_RING_RED_CONV ORELSEC INT_RED_CONV)) tm)

  let ECGROUP_ID_CONV : ioconv ← pure (fun tm => do
    (GEN_REWRITE_CONV I (← loc_ecgroup_ids.get) THENC
     TRY_CONV (GEN_REWRITE_CONV I (← loc_curvezero_clauses.get) THENC
               DEPTH_CONV INTEGER_MOD_RING_RED_CONV)) tm)

  let ECGROUP_INV_CONV : ioconv ← pure (fun tm => do
    (GEN_REWRITE_CONV RATOR_CONV (← loc_ecgroup_invs.get) THENC
     GEN_REWRITE_CONV I (← loc_curveneg_clauses.get) THENC
     DEPTH_CONV INTEGER_MOD_RING_RED_CONV) tm)

  let ECGROUP_MUL_CONV : ioconv ← do
    let pconv :=
      RATOR_CONV (LAND_CONV
       (DEPTH_CONV (INTEGER_MOD_RING_RED_CONV ORELSEC INT_RED_CONV))) THENC
      GEN_REWRITE_CONV I [COND_CLAUSES]
    let condconv : ioconv := fun tm =>
      match tm with
      | .Comb (.Comb (.Comb (.Const "COND" _) _) _) _ => pconv tm
      | _ => pure (failwith "condconv")
    let bodyconv :=
      REPEATC condconv THENC
      REPEATC (HolMath.Pair.SUBLET_CONV (DEPTH_CONV INTEGER_MOD_RING_RED_CONV) THENC
               let_CONV) THENC
      DEPTH_CONV INTEGER_MOD_RING_RED_CONV
    pure (fun tm => do
     (GEN_REWRITE_CONV (RATOR_CONV o RATOR_CONV) (← loc_ecgroup_muls.get) THENC
      GEN_REWRITE_CONV I (← loc_curveadd_clauses.get) THENC bodyconv) tm)

  -- `let pth = .. and dth = .. in`, left to right
  let ECGROUP_POW_CONV : ioconv ← do
    let pth ← prove
     r"!G x m n.
          x IN group_carrier G
          ==> group_pow G x (2 * n) = group_pow G (group_mul G x x) n"
     (← do
      pure (SIMP_TAC [← GSYM GROUP_POW_2, GROUP_POW_POW]))
    let dth ← prove
     r"NUMERAL(BIT0 n) = 2 * NUMERAL n"
     (← do
      pure (REWRITE_TAC [MULT_2] THEN REWRITE_TAC [BIT0] THEN
      REWRITE_TAC [NUMERAL]))
    let num_half_CONV := GEN_REWRITE_CONV I [dth]
    -- `let conv_0 tm = .. and conv_1 = .. and conv_2 = .. in`
    let gp1 ← CONJUNCT1 group_pow
    let conv_0 : ioconv := fun tm =>
     (GEN_REWRITE_CONV I [gp1] THENC
      ECGROUP_ID_CONV) tm
    let conv_1 := GEN_REWRITE_CONV I [← CONJUNCT2 group_pow]
    let conv_2 := PART_MATCH (fun t => do lhand (← rand t)) pth
    pure (ecgroupPowConv num_CONV num_half_CONV conv_0 conv_1 ECGROUP_MUL_CONV
      ECGROUP_CARRIER_CONV conv_2)

  -- @@RETURN BEGIN
  return { curve_clauses, curvezero_clauses, curveneg_clauses, curveadd_clauses,
           ecgroup_carriers, ecgroup_ids, ecgroup_invs, ecgroup_muls, add_curve,
           add_curvezero, add_curveneg, add_curveadd, add_ecgroup, ECGROUP_CARRIER_CONV,
           ECGROUP_ID_CONV, ECGROUP_INV_CONV, ECGROUP_MUL_CONV, ECGROUP_POW_CONV }
  -- @@RETURN END

end HolEC.ComputeGroup
