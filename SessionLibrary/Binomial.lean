/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/binomial.ml.                                -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Binomial.lean

  The `unsafe` half of the binomial.ml translation: it supplies
  HolLibrary.Binomial's dependencies from Session, builds the bundle once,
  and exports every name under its HOL Light name.  `ensureBinomial` is
  `needs "Library/binomial.ml"`.

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Binomial.lean by tools/binomialdiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.Binomial

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Binomial

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems binomial.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.Binomial.CoreThms1 where
  ADD1 := Session.ADD1
  ADD_0 := Session.ADD_0
  ADD_AC := Session.ADD_AC
  ADD_ASSOC := Session.ADD_ASSOC
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD := Session.ADD
  ADD_SUB := Session.ADD_SUB
  ADD_SUB2 := Session.ADD_SUB2
  ADD_SUC := Session.ADD_SUC
  ADD_SYM := Session.ADD_SYM
  ARITH := Session.ARITH
  ARITH_SUC := Session.ARITH_SUC
  CARD_CLAUSES := Session.CARD_CLAUSES
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DISJOINT := Session.DISJOINT
  DIVIDES_LE := Session.DIVIDES_LE
  DIV_UNIQ := Session.DIV_UNIQ
  EQ_ADD_RCANCEL := Session.EQ_ADD_RCANCEL
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EXP := Session.EXP
  EXTENSION := Session.EXTENSION
  FACT := Session.FACT
  FACT_LT := Session.FACT_LT
  FACT_NZ := Session.FACT_NZ
  FINITE_HAS_SIZE := Session.FINITE_HAS_SIZE
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_0 := Session.HAS_SIZE_0
  HAS_SIZE_CLAUSES := Session.HAS_SIZE_CLAUSES
  HAS_SIZE_IMAGE_INJ := Session.HAS_SIZE_IMAGE_INJ
  HAS_SIZE_SUC := Session.HAS_SIZE_SUC
  HAS_SIZE_UNION := Session.HAS_SIZE_UNION
  IN_ELIM_PAIR_THM := Session.IN_ELIM_PAIR_THM
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INTER := Session.IN_INTER
  IN_NUMSEG := Session.IN_NUMSEG
  IN_SING := Session.IN_SING
/-- The core theorems binomial.ml uses. -/
unsafe def core2 (_ : Unit) : HolLibrary.Binomial.CoreThms2 where
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_0 := Session.LE_0
  LE_EXISTS := Session.LE_EXISTS
  LE_REFL := Session.LE_REFL
  LE_SUC := Session.LE_SUC
  LT := Session.LT
  LT_0 := Session.LT_0
  LT_MULT := Session.LT_MULT
  LT_NZ := Session.LT_NZ
  LT_REFL := Session.LT_REFL
  LT_SUC := Session.LT_SUC
  MULT_AC := Session.MULT_AC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_SYM := Session.MULT_SYM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LE := Session.NOT_LE
  NOT_LT := Session.NOT_LT
  NOT_SUC := Session.NOT_SUC
  NSUM_ADD_NUMSEG := Session.NSUM_ADD_NUMSEG
  NSUM_CLAUSES_LEFT := Session.NSUM_CLAUSES_LEFT
  NSUM_CLAUSES_NUMSEG := Session.NSUM_CLAUSES_NUMSEG
  NSUM_LMUL := Session.NSUM_LMUL
  NSUM_OFFSET := Session.NSUM_OFFSET
  NSUM_SING_NUMSEG := Session.NSUM_SING_NUMSEG
  ONE := Session.ONE
  PAIR_EQ := Session.PAIR_EQ
  POWERSET_CLAUSES := Session.POWERSET_CLAUSES
  PRIME_COPRIME_EQ_NONDIVISIBLE := Session.PRIME_COPRIME_EQ_NONDIVISIBLE
  REAL_ADD_RDISTRIB := Session.REAL_ADD_RDISTRIB
  REAL_ADD_RID := Session.REAL_ADD_RID
  REAL_EQ_RDIV_EQ := Session.REAL_EQ_RDIV_EQ
  REAL_LT_MUL := Session.REAL_LT_MUL
  REAL_MUL_AC := Session.REAL_MUL_AC
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_LZERO := Session.REAL_MUL_LZERO
  REAL_MUL_RZERO := Session.REAL_MUL_RZERO
  REAL_OF_NUM_ADD := Session.REAL_OF_NUM_ADD
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_LE := Session.REAL_OF_NUM_LE
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_OF_NUM_MUL := Session.REAL_OF_NUM_MUL
  REAL_OF_NUM_SUB := Session.REAL_OF_NUM_SUB
/-- The core theorems binomial.ml uses. -/
unsafe def core3 (_ : Unit) : HolLibrary.Binomial.CoreThms3 where
  RIGHT_ADD_DISTRIB := Session.RIGHT_ADD_DISTRIB
  SUBSET_EMPTY := Session.SUBSET_EMPTY
  SUB_0 := Session.SUB_0
  SUB_EQ_0 := Session.SUB_EQ_0
  SUB_REFL := Session.SUB_REFL
  SUB_SUC := Session.SUB_SUC
  SUC_INJ := Session.SUC_INJ
  SUC_SUB1 := Session.SUC_SUB1
  SUM_ADD_NUMSEG := Session.SUM_ADD_NUMSEG
  SUM_CLAUSES_LEFT := Session.SUM_CLAUSES_LEFT
  SUM_CLAUSES_NUMSEG := Session.SUM_CLAUSES_NUMSEG
  SUM_EQ_GENERAL_INVERSES := Session.SUM_EQ_GENERAL_INVERSES
  SUM_LMUL := Session.SUM_LMUL
  SUM_OFFSET := Session.SUM_OFFSET
  SUM_RMUL := Session.SUM_RMUL
  SUM_SING_NUMSEG := Session.SUM_SING_NUMSEG
  SUM_SUM_PRODUCT := Session.SUM_SUM_PRODUCT
  real_pow := Session.real_pow-- @@CORE END

/-- What binomial.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Binomial.BinomialDeps where
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  mk_numeral := Session.mk_numeral
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  MESON_TAC := Session.MESON_TAC
  NUMBER_RULE t := ExceptT.mk (Session.NUMBER_RULE t)
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH3 t)
  REAL_FIELD t := ExceptT.mk (Session.REAL_FIELD t)
  REAL_RING t := ExceptT.mk (Session.REAL_RING t)
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  HAS_SIZE_CONV := Session.HAS_SIZE_CONV
  num_CONV := Session.num_CONV
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  NUM_RING := Session.NUM_RING
  NUM_LE_CONV := Session.NUM_LE_CONV
  NUM_LT_CONV := Session.NUM_LT_CONV
  NUM_SUB_CONV := Session.NUM_SUB_CONV
  NUM_SUC_CONV := Session.NUM_SUC_CONV
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
  | .ok d => d | _ => panic! s!"SessionLibrary.Binomial: {name}"

/- The bundle, in binomial.ml order. -/

-- @@BUNDLES BEGIN
initialize theBinomial : IO.Ref (Option HolLibrary.Binomial.Binomial) ← IO.mkRef none
unsafe def BBinomial : HolLibrary.Binomial.Binomial :=
  cached theBinomial "setupBinomial" fun _ => do
    (HolLibrary.Binomial.setupBinomial (deps ())).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Binomial
unsafe def binom : thm := BBinomial.binom
unsafe def BINOM_0 : thm := BBinomial.BINOM_0
unsafe def BINOM_LT : thm := BBinomial.BINOM_LT
unsafe def BINOM_REFL : thm := BBinomial.BINOM_REFL
unsafe def BINOM_1 : thm := BBinomial.BINOM_1
unsafe def BINOM_FACT : thm := BBinomial.BINOM_FACT
unsafe def BINOM_EQ_0 : thm := BBinomial.BINOM_EQ_0
unsafe def BINOM_PENULT : thm := BBinomial.BINOM_PENULT
unsafe def BINOM_GE_TOP : thm := BBinomial.BINOM_GE_TOP
unsafe def BINOM_TOP_STEP : thm := BBinomial.BINOM_TOP_STEP
unsafe def BINOM_BOTTOM_STEP : thm := BBinomial.BINOM_BOTTOM_STEP
unsafe def HAS_SIZE_RESTRICTED_POWERSET : thm := BBinomial.HAS_SIZE_RESTRICTED_POWERSET
unsafe def CARD_RESTRICTED_POWERSET : thm := BBinomial.CARD_RESTRICTED_POWERSET
unsafe def BINOMIAL_THEOREM : thm := BBinomial.BINOMIAL_THEOREM
unsafe def REAL_BINOMIAL_THEOREM : thm := BBinomial.REAL_BINOMIAL_THEOREM
unsafe def BINOM_TOP_STEP_REAL : thm := BBinomial.BINOM_TOP_STEP_REAL
unsafe def BINOM_BOTTOM_STEP_REAL : thm := BBinomial.BINOM_BOTTOM_STEP_REAL
unsafe def REAL_OF_NUM_BINOM : thm := BBinomial.REAL_OF_NUM_BINOM
unsafe def BINOM_BOTH_STEP_REAL : thm := BBinomial.BINOM_BOTH_STEP_REAL
unsafe def BINOM_BOTH_STEP : thm := BBinomial.BINOM_BOTH_STEP
unsafe def BINOM_BOTH_STEP_DOWN : thm := BBinomial.BINOM_BOTH_STEP_DOWN
unsafe def BINOM : thm := BBinomial.BINOM
unsafe def DIVIDES_GCD_BINOM : thm := BBinomial.DIVIDES_GCD_BINOM
unsafe def DIVIDES_COPRIME_BINOM : thm := BBinomial.DIVIDES_COPRIME_BINOM
unsafe def DIVIDES_PRIME_BINOM : thm := BBinomial.DIVIDES_PRIME_BINOM
unsafe def BINOM_SYM : thm := BBinomial.BINOM_SYM
unsafe def BINOM_MUL_SHIFT : thm := BBinomial.BINOM_MUL_SHIFT
unsafe def APPELL_SEQUENCE : thm := BBinomial.APPELL_SEQUENCE
unsafe def NUM_BINOM_CONV : term → IO (Except String thm) := fun t => (BBinomial.NUM_BINOM_CONV t).run



-- @@EXPORTS END

/-- `needs "Library/binomial.ml"`: build every bundle, in file order. -/
unsafe def ensureBinomial : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BBinomial.binom  -- @@ENSURE END
  pure ()

end SessionLibrary.Binomial
