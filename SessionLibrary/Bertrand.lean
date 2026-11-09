/- ---------------------------------------------------------------------- -/
/- Session wiring for 100/bertrand.ml.                                    -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Bertrand.lean

  The session half of the bertrand.ml translation: it supplies
  HolLibrary.Bertrand's dependencies from Session, SessionLibrary.Prime,
  SessionLibrary.Binomial and SessionLibrary.Products, and exports every
  name under its HOL Light name.  Importing this module is
  `needs "100/bertrand.ml"`; its `needs` are the imports of those modules.
  The bundles are built by `initialize` when the module is loaded.
-/

import Session
import HolLibrary.Bertrand
import SessionLibrary.Prime
import SessionLibrary.Binomial
import SessionLibrary.Products

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Bertrand

/-- The core theorems bertrand.ml uses. -/
def core1 : HolLibrary.Bertrand.CoreThms1 where
  ADD1 := Session.ADD1
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_EQ_0 := Session.ADD_EQ_0
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  BINOMIAL_THEOREM := SessionLibrary.Binomial.«BINOMIAL_THEOREM»
  BINOM_EQ_0 := SessionLibrary.Binomial.«BINOM_EQ_0»
  BINOM_FACT := SessionLibrary.Binomial.«BINOM_FACT»
  BINOM_SYM := SessionLibrary.Binomial.«BINOM_SYM»
  CARD_NUMSEG_1 := Session.CARD_NUMSEG_1
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CARD_SING := Session.CARD_SING
  CARD_SUBSET := Session.CARD_SUBSET
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  COPRIME_NPRODUCT := SessionLibrary.Prime.«COPRIME_NPRODUCT»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DISJOINT := Session.DISJOINT
  DISTINCT_PRIME_COPRIME := SessionLibrary.Prime.«DISTINCT_PRIME_COPRIME»
  DIVIDES_1 := SessionLibrary.Prime.«DIVIDES_1»
  DIVIDES_FACT_PRIME := SessionLibrary.Prime.«DIVIDES_FACT_PRIME»
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_MOD := Session.DIVIDES_MOD
  DIVIDES_MUL := SessionLibrary.Prime.«DIVIDES_MUL»
  DIVISION := Session.DIVISION
  DIV_EQ_0 := Session.DIV_EQ_0
  DIV_UNIQ := Session.DIV_UNIQ
  EQ_IMP_LE := Session.EQ_IMP_LE
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EVEN_OR_ODD := Session.EVEN_OR_ODD
  EXISTS_OR_THM := Session.EXISTS_OR_THM
  EXP := Session.EXP
  EXP_1 := Session.EXP_1
  EXP_2 := Session.EXP_2
  EXP_ADD := Session.EXP_ADD
  EXP_EQ_0 := Session.EXP_EQ_0
  EXP_EQ_1 := Session.EXP_EQ_1
  EXP_EXP := Session.EXP_EXP
  EXP_MONO_LE_IMP := Session.EXP_MONO_LE_IMP
  EXP_ONE := Session.EXP_ONE
  EXTENSION := Session.EXTENSION
  FACT := Session.FACT
  FACT_NZ := Session.FACT_NZ
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_EXP_LE := SessionLibrary.Prime.«FINITE_EXP_LE»
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_NUMSEG_LE := Session.FINITE_NUMSEG_LE
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  IMP_CONJ := Session.IMP_CONJ
  INDEX_FACT_ALT := SessionLibrary.Prime.«INDEX_FACT_ALT»
  INDEX_MUL := SessionLibrary.Prime.«INDEX_MUL»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_INSERT := Session.IN_INSERT
  IN_INTER := Session.IN_INTER
  IN_NUMSEG := Session.IN_NUMSEG
  IN_SING := Session.IN_SING
  IN_UNION := Session.IN_UNION
  LET_TRANS := Session.LET_TRANS
  LE_CASES := Session.LE_CASES
  LE_EXP := Session.LE_EXP
  LE_MULT2 := Session.LE_MULT2
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_MULT_RCANCEL := Session.LE_MULT_RCANCEL
  LE_RDIV_EQ := Session.LE_RDIV_EQ
  LE_REFL := Session.LE_REFL
  LE_TRANS := Session.LE_TRANS
  LTE_TRANS := Session.LTE_TRANS
  LT_EXP := Session.LT_EXP
  LT_POW2_REFL := Session.LT_POW2_REFL
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_ASSOC := Session.MULT_ASSOC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_EXP := Session.MULT_EXP
  NOT_EVEN := Session.NOT_EVEN
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LE := Session.NOT_LE
  NOT_LT := Session.NOT_LT
  NPRODUCT_CLAUSES := Session.NPRODUCT_CLAUSES
  NPRODUCT_CONST := SessionLibrary.Products.«NPRODUCT_CONST»
  NPRODUCT_LE := SessionLibrary.Products.«NPRODUCT_LE»
  NPRODUCT_MUL := SessionLibrary.Products.«NPRODUCT_MUL»
  NPRODUCT_RESTRICT_SET := SessionLibrary.Products.«NPRODUCT_RESTRICT_SET»
  NPRODUCT_SING := SessionLibrary.Products.«NPRODUCT_SING»
  NPRODUCT_SUPERSET := SessionLibrary.Products.«NPRODUCT_SUPERSET»
  NPRODUCT_UNION := SessionLibrary.Products.«NPRODUCT_UNION»
  NSUM_ADD := Session.NSUM_ADD
  NSUM_CLAUSES := Session.NSUM_CLAUSES
  NSUM_CONST := Session.NSUM_CONST
  NSUM_LE := Session.NSUM_LE
  NSUM_LMUL := Session.NSUM_LMUL
  NSUM_SING := Session.NSUM_SING
  NSUM_SUBSET_SIMPLE := Session.NSUM_SUBSET_SIMPLE
  NSUM_SUPERSET := Session.NSUM_SUPERSET
  ODD_EXISTS := Session.ODD_EXISTS
  PRIME_2 := SessionLibrary.Prime.«PRIME_2»
  PRIME_DIVPROD_EQ := SessionLibrary.Prime.«PRIME_DIVPROD_EQ»
  PRIME_FACTORIZATION_ALT := SessionLibrary.Prime.«PRIME_FACTORIZATION_ALT»
  PRIME_GE_2 := SessionLibrary.Prime.«PRIME_GE_2»
  PRIME_ODD := SessionLibrary.Prime.«PRIME_ODD»
  RDIV_LT_EQ := Session.RDIV_LT_EQ
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_OR_DISTRIB := Session.RIGHT_OR_DISTRIB
  SUBSET := Session.SUBSET
  UNWIND_THM2 := Session.UNWIND_THM2
  binom := SessionLibrary.Binomial.«binom»
  divides := Session.divides
  num_WF := Session.num_WF
  num_WOP := Session.num_WOP
  prime := Session.prime

/-- What bertrand.ml uses from Session. -/
def deps : HolLibrary.Bertrand.BertrandDeps where
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  SET_TAC := Session.SET_TAC
  TAUT t := ExceptT.mk (Session.TAUT t)
  INDUCT_TAC := Session.INDUCT_TAC
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  NUM_RING := Session.NUM_RING
  NUMBER_RULE := Session.NUMBER_RULE
  prioritize_num := do
    match ← HolCore.Kernel.mk_type "num" [] with
    | .ok ty => Session.prioritize_overload ty
    | .error e => throw (IO.userError e)
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in bertrand.ml order. -/
initialize BCentralBinomial : HolLibrary.Bertrand.CentralBinomial ←
  ioB "setupCentralBinomial" (HolLibrary.Bertrand.setupCentralBinomial deps).run
initialize BPrimorial : HolLibrary.Bertrand.Primorial ←
  ioB "setupPrimorial" (HolLibrary.Bertrand.setupPrimorial deps BCentralBinomial).run
initialize BIndexBinom : HolLibrary.Bertrand.IndexBinom ←
  ioB "setupIndexBinom" (HolLibrary.Bertrand.setupIndexBinom deps).run
initialize BBertrandPostulate : HolLibrary.Bertrand.BertrandPostulate ←
  ioB "setupBertrandPostulate" (HolLibrary.Bertrand.setupBertrandPostulate deps BCentralBinomial BPrimorial BIndexBinom).run

-- CentralBinomial
def BINOM_CENTRAL_STEP : thm := BCentralBinomial.BINOM_CENTRAL_STEP
def BINOM_CENTRAL_LOWER : thm := BCentralBinomial.BINOM_CENTRAL_LOWER
def BINOM_ODD_UPPER : thm := BCentralBinomial.BINOM_ODD_UPPER

-- Primorial
def PRIME_DIVIDES_BINOM_ODD : thm := BPrimorial.PRIME_DIVIDES_BINOM_ODD
def NPRODUCT_PRIMES_DIVIDES : thm := BPrimorial.NPRODUCT_PRIMES_DIVIDES
def FINITE_PRIMES_LE : thm := BPrimorial.FINITE_PRIMES_LE
def PRIMORIAL_LE_4_EXP : thm := BPrimorial.PRIMORIAL_LE_4_EXP

-- IndexBinom
def DIV_DOUBLE_LE : thm := BIndexBinom.DIV_DOUBLE_LE
def INDEX_BINOM_CENTRAL : thm := BIndexBinom.INDEX_BINOM_CENTRAL
def INDEX_BINOM_CENTRAL_CARD : thm := BIndexBinom.INDEX_BINOM_CENTRAL_CARD
def INDEX_BINOM_CENTRAL_LE : thm := BIndexBinom.INDEX_BINOM_CENTRAL_LE
def INDEX_BINOM_CENTRAL_SQRT : thm := BIndexBinom.INDEX_BINOM_CENTRAL_SQRT
def PRIMEPOW_INDICES_SING : thm := BIndexBinom.PRIMEPOW_INDICES_SING
def INDEX_BINOM_CENTRAL_ZERO : thm := BIndexBinom.INDEX_BINOM_CENTRAL_ZERO

-- BertrandPostulate
def BINOM_CENTRAL_UPPER : thm := BBertrandPostulate.BINOM_CENTRAL_UPPER
def EXP_4_BRACKET : thm := BBertrandPostulate.EXP_4_BRACKET
def BERTRAND_THRESHOLD : thm := BBertrandPostulate.BERTRAND_THRESHOLD
def BERTRAND_LARGE : thm := BBertrandPostulate.BERTRAND_LARGE
def PRIME_TRIAL_DIVISION : thm := BBertrandPostulate.PRIME_TRIAL_DIVISION
def BERTRAND : thm := BBertrandPostulate.BERTRAND

/-- `needs "100/bertrand.ml"`: already done by importing this module. -/
def ensureBertrand : IO Unit := pure ()

end SessionLibrary.Bertrand
