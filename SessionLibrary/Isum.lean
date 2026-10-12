/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/isum.ml.                                    -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Isum.lean

  The `unsafe` half of the isum.ml translation: it supplies
  HolLibrary.Isum's dependencies from Session, builds the single bundle, and
  exports every name under its HOL Light name.  `ensureIsum` is
  `needs "Library/isum.ml"`.

  NOTE.  isum.ml's `INT_OF_REAL_THM` is exported under its HOL Light name,
  which SHADOWS core int.ml's `Session.INT_OF_REAL_THM`; callers qualify the
  clash as `SessionLibrary.Isum.INT_OF_REAL_THM`.

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Isum.lean by tools/isumdiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.Isum

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Isum

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems isum.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.Isum.CoreThms1 where
  BETA_THM := Session.BETA_THM
  CARD_EQ_SUM := Session.CARD_EQ_SUM
  ETA_AX := Session.ETA_AX
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  IMP_CONJ := Session.IMP_CONJ
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_NUMSEG := Session.IN_NUMSEG
  ITERATE_CLAUSES := Session.ITERATE_CLAUSES
  ITERATE_CLOSED := Session.ITERATE_CLOSED
  ITERATE_CLOSED_NONEMPTY := Session.ITERATE_CLOSED_NONEMPTY
  ITERATE_EXPAND_CASES := Session.ITERATE_EXPAND_CASES
  ITERATE_ITERATE_PRODUCT := Session.ITERATE_ITERATE_PRODUCT
  ITERATE_RELATED := Session.ITERATE_RELATED
  ITERATE_RELATED_NONEMPTY := Session.ITERATE_RELATED_NONEMPTY
  ITERATE_SUPPORT := Session.ITERATE_SUPPORT
  ITERATE_UNIV := Session.ITERATE_UNIV
  MONOIDAL_INT_ADD := Session.MONOIDAL_INT_ADD
  MONOIDAL_REAL_ADD := Session.MONOIDAL_REAL_ADD
  NEUTRAL_INT_ADD := Session.NEUTRAL_INT_ADD
  NEUTRAL_REAL_ADD := Session.NEUTRAL_REAL_ADD
  REAL_OF_NUM_SUM := Session.REAL_OF_NUM_SUM
  REAL_OF_NUM_SUM_NUMSEG := Session.REAL_OF_NUM_SUM_NUMSEG
  REAL_SUB_POW := Session.REAL_SUB_POW
  REAL_SUB_POW_L1 := Session.REAL_SUB_POW_L1
  REAL_SUB_POW_R1 := Session.REAL_SUB_POW_R1
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  SUM_0 := Session.SUM_0
  SUM_ABS := Session.SUM_ABS
  SUM_ABS_BOUND := Session.SUM_ABS_BOUND
  SUM_ABS_LE := Session.SUM_ABS_LE
  SUM_ABS_NUMSEG := Session.SUM_ABS_NUMSEG
  SUM_ADD := Session.SUM_ADD
  SUM_ADD_NUMSEG := Session.SUM_ADD_NUMSEG
  SUM_ADD_SPLIT := Session.SUM_ADD_SPLIT
  SUM_BIJECTION := Session.SUM_BIJECTION
  SUM_BOUND := Session.SUM_BOUND
  SUM_BOUND_LT := Session.SUM_BOUND_LT
  SUM_BOUND_LT_ALL := Session.SUM_BOUND_LT_ALL
  SUM_CASES := Session.SUM_CASES
  SUM_CLAUSES_LEFT := Session.SUM_CLAUSES_LEFT
  SUM_CLAUSES_NUMSEG := Session.SUM_CLAUSES_NUMSEG
/-- The core theorems isum.ml uses. -/
unsafe def core2 (_ : Unit) : HolLibrary.Isum.CoreThms2 where
  SUM_CLAUSES_RIGHT := Session.SUM_CLAUSES_RIGHT
  SUM_COMBINE_L := Session.SUM_COMBINE_L
  SUM_COMBINE_R := Session.SUM_COMBINE_R
  SUM_CONST := Session.SUM_CONST
  SUM_CONST_NUMSEG := Session.SUM_CONST_NUMSEG
  SUM_DELETE := Session.SUM_DELETE
  SUM_DELETE_CASES := Session.SUM_DELETE_CASES
  SUM_DELTA := Session.SUM_DELTA
  SUM_DIFF := Session.SUM_DIFF
  SUM_DIFFS := Session.SUM_DIFFS
  SUM_EQ := Session.SUM_EQ
  SUM_EQ_0 := Session.SUM_EQ_0
  SUM_EQ_0_NUMSEG := Session.SUM_EQ_0_NUMSEG
  SUM_EQ_GENERAL := Session.SUM_EQ_GENERAL
  SUM_EQ_GENERAL_INVERSES := Session.SUM_EQ_GENERAL_INVERSES
  SUM_EQ_NUMSEG := Session.SUM_EQ_NUMSEG
  SUM_EQ_SUPERSET := Session.SUM_EQ_SUPERSET
  SUM_GROUP := Session.SUM_GROUP
  SUM_IMAGE := Session.SUM_IMAGE
  SUM_IMAGE_GEN := Session.SUM_IMAGE_GEN
  SUM_IMAGE_LE := Session.SUM_IMAGE_LE
  SUM_IMAGE_NONZERO := Session.SUM_IMAGE_NONZERO
  SUM_INCL_EXCL := Session.SUM_INCL_EXCL
  SUM_INJECTION := Session.SUM_INJECTION
  SUM_LE := Session.SUM_LE
  SUM_LE_INCLUDED := Session.SUM_LE_INCLUDED
  SUM_LE_NUMSEG := Session.SUM_LE_NUMSEG
  SUM_LMUL := Session.SUM_LMUL
  SUM_LT := Session.SUM_LT
  SUM_LT_ALL := Session.SUM_LT_ALL
  SUM_MULTICOUNT := Session.SUM_MULTICOUNT
  SUM_MULTICOUNT_GEN := Session.SUM_MULTICOUNT_GEN
  SUM_NEG := Session.SUM_NEG
  SUM_OFFSET := Session.SUM_OFFSET
  SUM_OFFSET_0 := Session.SUM_OFFSET_0
  SUM_PARTIAL_PRE := Session.SUM_PARTIAL_PRE
  SUM_PARTIAL_SUC := Session.SUM_PARTIAL_SUC
  SUM_POS_BOUND := Session.SUM_POS_BOUND
  SUM_POS_EQ_0 := Session.SUM_POS_EQ_0
  SUM_POS_EQ_0_NUMSEG := Session.SUM_POS_EQ_0_NUMSEG
  SUM_POS_LE := Session.SUM_POS_LE
  SUM_POS_LE_NUMSEG := Session.SUM_POS_LE_NUMSEG
/-- The core theorems isum.ml uses. -/
unsafe def core3 (_ : Unit) : HolLibrary.Isum.CoreThms3 where
  SUM_RESTRICT := Session.SUM_RESTRICT
  SUM_RESTRICT_SET := Session.SUM_RESTRICT_SET
  SUM_RMUL := Session.SUM_RMUL
  SUM_SING := Session.SUM_SING
  SUM_SING_NUMSEG := Session.SUM_SING_NUMSEG
  SUM_SUB := Session.SUM_SUB
  SUM_SUBSET := Session.SUM_SUBSET
  SUM_SUBSET_SIMPLE := Session.SUM_SUBSET_SIMPLE
  SUM_SUB_NUMSEG := Session.SUM_SUB_NUMSEG
  SUM_SUM_RESTRICT := Session.SUM_SUM_RESTRICT
  SUM_SUPERSET := Session.SUM_SUPERSET
  SUM_SWAP := Session.SUM_SWAP
  SUM_SWAP_NUMSEG := Session.SUM_SWAP_NUMSEG
  SUM_TRIV_NUMSEG := Session.SUM_TRIV_NUMSEG
  SUM_UNION := Session.SUM_UNION
  SUM_UNIONS_NONZERO := Session.SUM_UNIONS_NONZERO
  SUM_UNION_EQ := Session.SUM_UNION_EQ
  SUM_UNION_LZERO := Session.SUM_UNION_LZERO
  SUM_UNION_NONZERO := Session.SUM_UNION_NONZERO
  SUM_UNION_RZERO := Session.SUM_UNION_RZERO
  SUM_ZERO_EXISTS := Session.SUM_ZERO_EXISTS
  admissible := Session.admissible_DEF
  int_abs_th := Session.int_abs_th
  int_add_th := Session.int_add_th
  int_eq := Session.int_eq
  int_ge := Session.int_ge
  int_gt := Session.int_gt
  int_le := Session.int_le
  int_lt := Session.int_lt
  int_max_th := Session.int_max_th
  int_min_th := Session.int_min_th
  int_mul_th := Session.int_mul_th
  int_neg_th := Session.int_neg_th
  int_of_num_th := Session.int_of_num_th
  int_pow_th := Session.int_pow_th
  int_sub_th := Session.int_sub_th
  isum := Session.isum
  o_DEF := Session.o_DEF
  sum := Session.sum
  support := Session.support-- @@CORE END

/-- What isum.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Isum.IsumDeps where
  extend_basic_congs := Session.extend_basic_congs
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  MESON_TAC := Session.MESON_TAC
  NUM_LT_CONV := Session.NUM_LT_CONV
  NUM_LE_CONV := Session.NUM_LE_CONV
  NUM_ADD_CONV := Session.NUM_ADD_CONV
  core1 := core1 ()
  core2 := core2 ()
  core3 := core3 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`, and MATCH_CONV's basic conversions, which HOL
    Light adds loading ind_types.ml). -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.Isum: {name}"

/- The single bundle. -/

-- @@BUNDLES BEGIN
initialize theIsum : IO.Ref (Option HolLibrary.Isum.Isum) ← IO.mkRef none
unsafe def BIsum : HolLibrary.Isum.Isum :=
  cached theIsum "setupIsum" fun _ => do
    (HolLibrary.Isum.setupIsum (deps ())).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Isum
unsafe def ISUM_SUPPORT : thm := BIsum.ISUM_SUPPORT
unsafe def int_isum : thm := BIsum.int_isum
unsafe def INT_OF_REAL_THM := BIsum.INT_OF_REAL_THM
unsafe def CARD_EQ_ISUM : thm := BIsum.CARD_EQ_ISUM
unsafe def INT_SUB_POW : thm := BIsum.INT_SUB_POW
unsafe def ISUM_0 : thm := BIsum.ISUM_0
unsafe def ISUM_ABS : thm := BIsum.ISUM_ABS
unsafe def ISUM_ABS_BOUND : thm := BIsum.ISUM_ABS_BOUND
unsafe def ISUM_ABS_LE : thm := BIsum.ISUM_ABS_LE
unsafe def ISUM_ABS_NUMSEG : thm := BIsum.ISUM_ABS_NUMSEG
unsafe def ISUM_ADD : thm := BIsum.ISUM_ADD
unsafe def ISUM_ADD_NUMSEG : thm := BIsum.ISUM_ADD_NUMSEG
unsafe def ISUM_ADD_SPLIT : thm := BIsum.ISUM_ADD_SPLIT
unsafe def ISUM_BIJECTION : thm := BIsum.ISUM_BIJECTION
unsafe def ISUM_BOUND : thm := BIsum.ISUM_BOUND
unsafe def ISUM_BOUND_LT : thm := BIsum.ISUM_BOUND_LT
unsafe def ISUM_BOUND_LT_ALL : thm := BIsum.ISUM_BOUND_LT_ALL
unsafe def ISUM_CASES : thm := BIsum.ISUM_CASES
unsafe def ISUM_CLAUSES_LEFT : thm := BIsum.ISUM_CLAUSES_LEFT
unsafe def ISUM_CLAUSES_NUMSEG : thm := BIsum.ISUM_CLAUSES_NUMSEG
unsafe def ISUM_CLAUSES_RIGHT : thm := BIsum.ISUM_CLAUSES_RIGHT
unsafe def ISUM_COMBINE_L : thm := BIsum.ISUM_COMBINE_L
unsafe def ISUM_COMBINE_R : thm := BIsum.ISUM_COMBINE_R
unsafe def ISUM_CONST : thm := BIsum.ISUM_CONST
unsafe def ISUM_CONST_NUMSEG : thm := BIsum.ISUM_CONST_NUMSEG
unsafe def ISUM_DELETE : thm := BIsum.ISUM_DELETE
unsafe def ISUM_DELETE_CASES : thm := BIsum.ISUM_DELETE_CASES
unsafe def ISUM_DELTA : thm := BIsum.ISUM_DELTA
unsafe def ISUM_DIFF : thm := BIsum.ISUM_DIFF
unsafe def ISUM_DIFFS : thm := BIsum.ISUM_DIFFS
unsafe def ISUM_EQ : thm := BIsum.ISUM_EQ
unsafe def ISUM_EQ_0 : thm := BIsum.ISUM_EQ_0
unsafe def ISUM_EQ_0_NUMSEG : thm := BIsum.ISUM_EQ_0_NUMSEG
unsafe def ISUM_EQ_GENERAL : thm := BIsum.ISUM_EQ_GENERAL
unsafe def ISUM_EQ_GENERAL_INVERSES : thm := BIsum.ISUM_EQ_GENERAL_INVERSES
unsafe def ISUM_EQ_NUMSEG : thm := BIsum.ISUM_EQ_NUMSEG
unsafe def ISUM_EQ_SUPERSET : thm := BIsum.ISUM_EQ_SUPERSET
unsafe def ISUM_GROUP : thm := BIsum.ISUM_GROUP
unsafe def ISUM_IMAGE : thm := BIsum.ISUM_IMAGE
unsafe def ISUM_IMAGE_GEN : thm := BIsum.ISUM_IMAGE_GEN
unsafe def ISUM_IMAGE_LE : thm := BIsum.ISUM_IMAGE_LE
unsafe def ISUM_IMAGE_NONZERO : thm := BIsum.ISUM_IMAGE_NONZERO
unsafe def ISUM_INCL_EXCL : thm := BIsum.ISUM_INCL_EXCL
unsafe def ISUM_INJECTION : thm := BIsum.ISUM_INJECTION
unsafe def ISUM_LE : thm := BIsum.ISUM_LE
unsafe def ISUM_LE_INCLUDED : thm := BIsum.ISUM_LE_INCLUDED
unsafe def ISUM_LE_NUMSEG : thm := BIsum.ISUM_LE_NUMSEG
unsafe def ISUM_LMUL : thm := BIsum.ISUM_LMUL
unsafe def ISUM_LT : thm := BIsum.ISUM_LT
unsafe def ISUM_LT_ALL : thm := BIsum.ISUM_LT_ALL
unsafe def ISUM_MULTICOUNT : thm := BIsum.ISUM_MULTICOUNT
unsafe def ISUM_MULTICOUNT_GEN : thm := BIsum.ISUM_MULTICOUNT_GEN
unsafe def ISUM_NEG : thm := BIsum.ISUM_NEG
unsafe def ISUM_OFFSET : thm := BIsum.ISUM_OFFSET
unsafe def ISUM_OFFSET_0 : thm := BIsum.ISUM_OFFSET_0
unsafe def ISUM_PARTIAL_PRE : thm := BIsum.ISUM_PARTIAL_PRE
unsafe def ISUM_PARTIAL_SUC : thm := BIsum.ISUM_PARTIAL_SUC
unsafe def ISUM_POS_BOUND : thm := BIsum.ISUM_POS_BOUND
unsafe def ISUM_POS_EQ_0 : thm := BIsum.ISUM_POS_EQ_0
unsafe def ISUM_POS_EQ_0_NUMSEG : thm := BIsum.ISUM_POS_EQ_0_NUMSEG
unsafe def ISUM_POS_LE : thm := BIsum.ISUM_POS_LE
unsafe def ISUM_POS_LE_NUMSEG : thm := BIsum.ISUM_POS_LE_NUMSEG
unsafe def ISUM_RESTRICT : thm := BIsum.ISUM_RESTRICT
unsafe def ISUM_RESTRICT_SET : thm := BIsum.ISUM_RESTRICT_SET
unsafe def ISUM_RMUL : thm := BIsum.ISUM_RMUL
unsafe def ISUM_SING : thm := BIsum.ISUM_SING
unsafe def ISUM_SING_NUMSEG : thm := BIsum.ISUM_SING_NUMSEG
unsafe def ISUM_SUB : thm := BIsum.ISUM_SUB
unsafe def ISUM_SUBSET : thm := BIsum.ISUM_SUBSET
unsafe def ISUM_SUBSET_SIMPLE : thm := BIsum.ISUM_SUBSET_SIMPLE
unsafe def ISUM_SUB_NUMSEG : thm := BIsum.ISUM_SUB_NUMSEG
unsafe def ISUM_ISUM_RESTRICT : thm := BIsum.ISUM_ISUM_RESTRICT
unsafe def ISUM_SUPERSET : thm := BIsum.ISUM_SUPERSET
unsafe def ISUM_SWAP : thm := BIsum.ISUM_SWAP
unsafe def ISUM_SWAP_NUMSEG : thm := BIsum.ISUM_SWAP_NUMSEG
unsafe def ISUM_TRIV_NUMSEG : thm := BIsum.ISUM_TRIV_NUMSEG
unsafe def ISUM_UNION : thm := BIsum.ISUM_UNION
unsafe def ISUM_UNIONS_NONZERO : thm := BIsum.ISUM_UNIONS_NONZERO
unsafe def ISUM_UNION_EQ : thm := BIsum.ISUM_UNION_EQ
unsafe def ISUM_UNION_LZERO : thm := BIsum.ISUM_UNION_LZERO
unsafe def ISUM_UNION_NONZERO : thm := BIsum.ISUM_UNION_NONZERO
unsafe def ISUM_UNION_RZERO : thm := BIsum.ISUM_UNION_RZERO
unsafe def ISUM_ZERO_EXISTS : thm := BIsum.ISUM_ZERO_EXISTS
unsafe def REAL_OF_NUM_ISUM : thm := BIsum.REAL_OF_NUM_ISUM
unsafe def REAL_OF_NUM_ISUM_NUMSEG : thm := BIsum.REAL_OF_NUM_ISUM_NUMSEG
unsafe def ISUM_ISUM_PRODUCT : thm := BIsum.ISUM_ISUM_PRODUCT
unsafe def ADMISSIBLE_ISUM : thm := BIsum.ADMISSIBLE_ISUM
unsafe def INT_SUB_POW_L1 : thm := BIsum.INT_SUB_POW_L1
unsafe def INT_SUB_POW_R1 : thm := BIsum.INT_SUB_POW_R1
unsafe def ISUM_UNIV : thm := BIsum.ISUM_UNIV
unsafe def ISUM_CLOSED : thm := BIsum.ISUM_CLOSED
unsafe def ISUM_RELATED : thm := BIsum.ISUM_RELATED
unsafe def ISUM_CLOSED_NONEMPTY : thm := BIsum.ISUM_CLOSED_NONEMPTY
unsafe def ISUM_RELATED_NONEMPTY : thm := BIsum.ISUM_RELATED_NONEMPTY
unsafe def EXPAND_ISUM_CONV : HolCore.Equal.ioconv := fun t => BIsum.EXPAND_ISUM_CONV t



-- @@EXPORTS END

/-- `needs "Library/isum.ml"`: build the bundle. -/
unsafe def ensureIsum : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BIsum.ISUM_SUPPORT  -- @@ENSURE END
  pure ()

end SessionLibrary.Isum
