/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/binomial.ml.                                -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Binomial.lean

  The session half of the binomial.ml translation: it supplies
  HolLibrary.Binomial's dependencies from Session and exports every name
  under its HOL Light name.  Importing this module is
  `needs "Library/binomial.ml"`: the bundle is built by `initialize` when the
  module is loaded.
-/

import Session
import HolLibrary.Binomial

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Binomial

/-- The core theorems binomial.ml uses. -/
def core1 : HolLibrary.Binomial.CoreThms1 where
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
def core2 : HolLibrary.Binomial.CoreThms2 where
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
def core3 : HolLibrary.Binomial.CoreThms3 where
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
  real_pow := Session.real_pow

/-- What binomial.ml uses from Session. -/
def deps : HolLibrary.Binomial.BinomialDeps where
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
  core1 := core1
  core2 := core2
  core3 := core3

/-- binomial.ml, run when this module is loaded. -/
initialize BBinomial : HolLibrary.Binomial.Binomial ← do
  match ← (HolLibrary.Binomial.setupBinomial deps).run with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"setupBinomial failed: {e}")

-- Binomial
def binom : thm := BBinomial.binom
def BINOM_0 : thm := BBinomial.BINOM_0
def BINOM_LT : thm := BBinomial.BINOM_LT
def BINOM_REFL : thm := BBinomial.BINOM_REFL
def BINOM_1 : thm := BBinomial.BINOM_1
def BINOM_FACT : thm := BBinomial.BINOM_FACT
def BINOM_EQ_0 : thm := BBinomial.BINOM_EQ_0
def BINOM_PENULT : thm := BBinomial.BINOM_PENULT
def BINOM_GE_TOP : thm := BBinomial.BINOM_GE_TOP
def BINOM_TOP_STEP : thm := BBinomial.BINOM_TOP_STEP
def BINOM_BOTTOM_STEP : thm := BBinomial.BINOM_BOTTOM_STEP
def HAS_SIZE_RESTRICTED_POWERSET : thm := BBinomial.HAS_SIZE_RESTRICTED_POWERSET
def CARD_RESTRICTED_POWERSET : thm := BBinomial.CARD_RESTRICTED_POWERSET
def BINOMIAL_THEOREM : thm := BBinomial.BINOMIAL_THEOREM
def REAL_BINOMIAL_THEOREM : thm := BBinomial.REAL_BINOMIAL_THEOREM
def BINOM_TOP_STEP_REAL : thm := BBinomial.BINOM_TOP_STEP_REAL
def BINOM_BOTTOM_STEP_REAL : thm := BBinomial.BINOM_BOTTOM_STEP_REAL
def REAL_OF_NUM_BINOM : thm := BBinomial.REAL_OF_NUM_BINOM
def BINOM_BOTH_STEP_REAL : thm := BBinomial.BINOM_BOTH_STEP_REAL
def BINOM_BOTH_STEP : thm := BBinomial.BINOM_BOTH_STEP
def BINOM_BOTH_STEP_DOWN : thm := BBinomial.BINOM_BOTH_STEP_DOWN
def BINOM : thm := BBinomial.BINOM
def DIVIDES_GCD_BINOM : thm := BBinomial.DIVIDES_GCD_BINOM
def DIVIDES_COPRIME_BINOM : thm := BBinomial.DIVIDES_COPRIME_BINOM
def DIVIDES_PRIME_BINOM : thm := BBinomial.DIVIDES_PRIME_BINOM
def BINOM_SYM : thm := BBinomial.BINOM_SYM
def BINOM_MUL_SHIFT : thm := BBinomial.BINOM_MUL_SHIFT
def APPELL_SEQUENCE : thm := BBinomial.APPELL_SEQUENCE
def NUM_BINOM_CONV : term → IO (Except String thm) := fun t => (BBinomial.NUM_BINOM_CONV t).run

/-- `needs "Library/binomial.ml"`: already done by importing this module. -/
def ensureBinomial : IO Unit := pure ()

end SessionLibrary.Binomial
