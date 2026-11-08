/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/prime.ml.                                   -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Prime.lean

  The session half of the prime.ml translation: it supplies
  HolLibrary.Prime's dependencies from Session and exports every theorem by
  name.  Importing this module is `needs "Library/prime.ml"`: each theorem
  bundle is built by `initialize` when the module is loaded, in file order.
-/

import Session
import HolLibrary.Prime

open HolCore HolCore.Kernel
open Session

namespace SessionLibrary.Prime

/-- The core theorems prime.ml uses, A-L. -/
def core1 : HolLibrary.Prime.CoreThms1 where
  ADD1 := Session.ADD1
  ADD_AC := Session.ADD_AC
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_EQ_0 := Session.ADD_EQ_0
  ADD_SYM := Session.ADD_SYM
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_NUMSEG_1 := Session.CARD_NUMSEG_1
  COND_CLAUSES := Session.COND_CLAUSES
  COND_ID := Session.COND_ID
  COND_RAND := Session.COND_RAND
  COND_RATOR := Session.COND_RATOR
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONJ_SYM := Session.CONJ_SYM
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  COPRIME_RMOD := Session.COPRIME_RMOD
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DISJ_ACI := Session.DISJ_ACI
  DISJ_SYM := Session.DISJ_SYM
  DIVIDES_ANTISYM := Session.DIVIDES_ANTISYM
  DIVIDES_DIV_MULT := Session.DIVIDES_DIV_MULT
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_LE_IMP := Session.DIVIDES_LE_IMP
  DIVIDES_LE_STRONG := Session.DIVIDES_LE_STRONG
  DIVIDES_MOD := Session.DIVIDES_MOD
  DIVIDES_ONE := Session.DIVIDES_ONE
  DIV_1 := Session.DIV_1
  DIV_EQ_0 := Session.DIV_EQ_0
  DIV_EQ_SELF := Session.DIV_EQ_SELF
  DIV_LE := Session.DIV_LE
  DIV_MULT := Session.DIV_MULT
  DIV_MULT2 := Session.DIV_MULT2
  DIV_UNIQ := Session.DIV_UNIQ
  DIV_ZERO := Session.DIV_ZERO
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EQ_ADD_RCANCEL := Session.EQ_ADD_RCANCEL
  EQ_ADD_RCANCEL_0 := Session.EQ_ADD_RCANCEL_0
  EQ_IMP := Session.EQ_IMP
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EQ_SYM_EQ := Session.EQ_SYM_EQ
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EVEN_EXISTS := Session.EVEN_EXISTS
  EXISTS_INT_CASES := Session.EXISTS_INT_CASES
  EXISTS_IN_INSERT := Session.EXISTS_IN_INSERT
  EXISTS_REFL := Session.EXISTS_REFL
  EXP := Session.EXP
  EXP_1 := Session.EXP_1
  EXP_2 := Session.EXP_2
  EXP_ADD := Session.EXP_ADD
  EXP_EQ_0 := Session.EXP_EQ_0
  EXP_EQ_1 := Session.EXP_EQ_1
  EXP_EXP := Session.EXP_EXP
  EXP_MONO_EQ := Session.EXP_MONO_EQ
  EXP_MONO_LE := Session.EXP_MONO_LE
  EXP_MONO_LE_IMP := Session.EXP_MONO_LE_IMP
  EXP_ONE := Session.EXP_ONE
  EXP_ZERO := Session.EXP_ZERO
  EXTENSION := Session.EXTENSION
  FACT := Session.FACT
  FACT_LT := Session.FACT_LT
  FACT_NZ := Session.FACT_NZ
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_NUMSEG_LE := Session.FINITE_NUMSEG_LE
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_AND_THM := Session.FORALL_AND_THM
  FORALL_INT_CASES := Session.FORALL_INT_CASES
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  FUN_EQ_THM := Session.FUN_EQ_THM
  GCD := Session.GCD
  GT := Session.GT
  IMP_CONJ := Session.IMP_CONJ
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  INFINITE := Session.INFINITE
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_CONG_NUM_EXISTS := Session.INT_CONG_NUM_EXISTS
  INT_MUL_LNEG := Session.INT_MUL_LNEG
  INT_MUL_RNEG := Session.INT_MUL_RNEG
  INT_NEG_NEG := Session.INT_NEG_NEG
  INT_OF_NUM_ADD := Session.INT_OF_NUM_ADD
  INT_OF_NUM_CLAUSES := Session.INT_OF_NUM_CLAUSES
  INT_OF_NUM_DIV := Session.INT_OF_NUM_DIV
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_POW := Session.INT_OF_NUM_POW
  INT_OF_NUM_SUB := Session.INT_OF_NUM_SUB
  INT_POW := Session.INT_POW
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_NUMSEG := Session.IN_NUMSEG
  IN_UNIV := Session.IN_UNIV
  ITERATE_CLAUSES := Session.ITERATE_CLAUSES
  ITERATE_DELTA := Session.ITERATE_DELTA
  ITERATE_EQ := Session.ITERATE_EQ
  ITERATE_EQ_NEUTRAL := Session.ITERATE_EQ_NEUTRAL
  ITERATE_EXPAND_CASES := Session.ITERATE_EXPAND_CASES
  ITERATE_OP_GEN := Session.ITERATE_OP_GEN
  ITERATE_SUPERSET := Session.ITERATE_SUPERSET
  LE := Session.LE
  LEFT_ADD_DISTRIB := Session.LEFT_ADD_DISTRIB
  LEFT_AND_EXISTS_THM := Session.LEFT_AND_EXISTS_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_0 := Session.LE_0
  LE_1 := Session.LE_1
  LE_ADD := Session.LE_ADD
  LE_ADD2 := Session.LE_ADD2
  LE_ANTISYM := Session.LE_ANTISYM
  LE_EXISTS := Session.LE_EXISTS
  LE_EXP := Session.LE_EXP
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_RDIV_EQ := Session.LE_RDIV_EQ
  LE_REFL := Session.LE_REFL
  LE_TRANS := Session.LE_TRANS
  LT := Session.LT
  LTE_TRANS := Session.LTE_TRANS
  LT_EXISTS := Session.LT_EXISTS
  LT_EXP := Session.LT_EXP
  LT_IMP_LE := Session.LT_IMP_LE
  LT_LE := Session.LT_LE
  LT_MULT_RCANCEL := Session.LT_MULT_RCANCEL
  LT_POW2_REFL := Session.LT_POW2_REFL
  LT_REFL := Session.LT_REFL

/-- The core theorems prime.ml uses, M-Z and lower case. -/
def core2 : HolLibrary.Prime.CoreThms2 where
  MAX := Session.MAX
  MOD_LT_EQ := Session.MOD_LT_EQ
  MONOIDAL_MUL := Session.MONOIDAL_MUL
  MONO_EXISTS := Session.MONO_EXISTS
  MONO_OR := Session.MONO_OR
  MULT_AC := Session.MULT_AC
  MULT_ASSOC := Session.MULT_ASSOC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_EQ_1 := Session.MULT_EQ_1
  MULT_EXP := Session.MULT_EXP
  MULT_SYM := Session.MULT_SYM
  NEUTRAL_MUL := Session.NEUTRAL_MUL
  NOT_EVEN := Session.NOT_EVEN
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LE := Session.NOT_LE
  NOT_LT := Session.NOT_LT
  NOT_SUC := Session.NOT_SUC
  NPRODUCT_CLAUSES := Session.NPRODUCT_CLAUSES
  NSUM_ADD_NUMSEG := Session.NSUM_ADD_NUMSEG
  NSUM_CLAUSES := Session.NSUM_CLAUSES
  NSUM_CLAUSES_NUMSEG := Session.NSUM_CLAUSES_NUMSEG
  NSUM_CLOSED_NONEMPTY := Session.NSUM_CLOSED_NONEMPTY
  NSUM_CONST := Session.NSUM_CONST
  NSUM_EQ := Session.NSUM_EQ
  NSUM_EQ_NUMSEG := Session.NSUM_EQ_NUMSEG
  NSUM_IMAGE := Session.NSUM_IMAGE
  NSUM_RESTRICT_SET := Session.NSUM_RESTRICT_SET
  NSUM_SUPERSET := Session.NSUM_SUPERSET
  NSUM_SWAP := Session.NSUM_SWAP
  NUM_GCD := Session.NUM_GCD
  NUM_LCM := Session.NUM_LCM
  ODD_EXISTS := Session.ODD_EXISTS
  ONE_OR_PRIME_DIVIDES_OR_COPRIME := Session.ONE_OR_PRIME_DIVIDES_OR_COPRIME
  PRIME_COPRIME_EQ_NONDIVISIBLE := Session.PRIME_COPRIME_EQ_NONDIVISIBLE
  RIGHT_ADD_DISTRIB := Session.RIGHT_ADD_DISTRIB
  RIGHT_AND_EXISTS_THM := Session.RIGHT_AND_EXISTS_THM
  RIGHT_EXISTS_AND_THM := Session.RIGHT_EXISTS_AND_THM
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_SUB_DISTRIB := Session.RIGHT_SUB_DISTRIB
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SUBSET := Session.SUBSET
  SUBSET_REFL := Session.SUBSET_REFL
  SUB_0 := Session.SUB_0
  SUB_ADD := Session.SUB_ADD
  SUB_EQ_0 := Session.SUB_EQ_0
  SWAP_EXISTS_THM := Session.SWAP_EXISTS_THM
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  UNWIND_THM2 := Session.UNWIND_THM2
  ZERO_ONE_OR_PRIME := Session.ZERO_ONE_OR_PRIME
  coprime := Session.coprime
  divides := Session.divides
  int_divides := Session.int_divides
  int_lcm := Session.int_lcm
  monoidal := Session.monoidal
  neutral := Session.neutral
  nproduct := Session.nproduct
  num_CASES := Session.num_CASES
  num_FINITE := Session.num_FINITE
  num_MAX := Session.num_MAX
  num_WF := Session.num_WF
  num_divides := Session.num_divides
  numseg := Session.numseg
  o_DEF := Session.o_DEF
  prime := Session.prime
  support := Session.support

/-- prime.ml's dependencies, from Session. -/
def deps : HolLibrary.Prime.PrimeDeps where
  new_definition s := do
    let t ← ExceptT.mk (HolCore.Parser.parse_term s)
    ExceptT.mk (Session.new_definition t)
  ARITH_RULE t := ExceptT.mk (ARITH_RULE t)
  ARITH_TAC := ARITH_TAC
  ASM_ARITH_TAC := ASM_ARITH_TAC
  ASM_MESON_TAC := ASM_MESON_TAC
  INDUCT_TAC := INDUCT_TAC
  INTEGER_RULE t := ExceptT.mk (INTEGER_RULE t)
  INTEGER_TAC := INTEGER_TAC
  INT_ARITH t := ExceptT.mk (INT_ARITH t)
  MESON ths t := ExceptT.mk (MESON ths t)
  MESON_TAC := MESON_TAC
  NUMBER_RULE t := ExceptT.mk (NUMBER_RULE t)
  NUMBER_TAC := NUMBER_TAC
  NUM_RING t := ExceptT.mk (NUM_RING t)
  SET_RULE t := ExceptT.mk (SET_RULE t)
  SET_TAC := SET_TAC
  CONTRAPOS_CONV t := pure (CONTRAPOS_CONV t)
  EXPAND_CASES_CONV := EXPAND_CASES_CONV
  NUM_DIV_CONV := NUM_DIV_CONV
  NUM_EQ_CONV := NUM_EQ_CONV
  NUM_MOD_CONV := NUM_MOD_CONV
  NUM_MULT_CONV := NUM_MULT_CONV
  NUM_REDUCE_CONV := NUM_REDUCE_CONV
  mk_numeral := mk_numeral
  core1 := core1
  core2 := core2

/-- prime.ml runs after the whole of hol.ml, then `prioritize_num()`
    (prime.ml 5).  Run when this module is loaded, before the first bundle. -/
initialize primePrelude : Unit ← do
  match ← (HolMath.Int.prioritize_num Session.prioritize_overload).run with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"prioritize_num failed: {e}")

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in prime.ml order. -/
initialize BDivides : HolLibrary.Prime.Divides ←
  ioB "setupDivides" (HolLibrary.Prime.setupDivides deps).run
initialize BGcd : HolLibrary.Prime.Gcd ←
  ioB "setupGcd" (HolLibrary.Prime.setupGcd deps BDivides).run
initialize BCoprime : HolLibrary.Prime.Coprime ←
  ioB "setupCoprime" (HolLibrary.Prime.setupCoprime deps BDivides BGcd).run
initialize BPrimes : HolLibrary.Prime.Primes ←
  ioB "setupPrimes" (HolLibrary.Prime.setupPrimes deps BDivides BGcd BCoprime).run
initialize BChinese : HolLibrary.Prime.Chinese ←
  ioB "setupChinese" (HolLibrary.Prime.setupChinese deps BGcd BCoprime).run
initialize BIndex : HolLibrary.Prime.Index ←
  ioB "setupIndex" (HolLibrary.Prime.setupIndex deps BDivides BGcd BCoprime BPrimes).run
initialize BLcm : HolLibrary.Prime.Lcm ←
  ioB "setupLcm" (HolLibrary.Prime.setupLcm deps BDivides BGcd BCoprime BPrimes BIndex).run
initialize BIterated : HolLibrary.Prime.Iterated ←
  ioB "setupIterated" (HolLibrary.Prime.setupIterated deps BDivides BGcd BPrimes BLcm).run
initialize BInduct : HolLibrary.Prime.Induct ←
  ioB "setupInduct" (HolLibrary.Prime.setupInduct deps BCoprime BPrimes).run
initialize BConvs : HolLibrary.Prime.Convs ←
  ioB "setupConvs" (HolLibrary.Prime.setupConvs deps BDivides BGcd).run

/- The theorems, by name. -/
-- Divides
def DIVIDES_0                    : thm := BDivides.DIVIDES_0
def DIVIDES_ZERO                 : thm := BDivides.DIVIDES_ZERO
def DIVIDES_1                    : thm := BDivides.DIVIDES_1
def DIVIDES_REFL                 : thm := BDivides.DIVIDES_REFL
def DIVIDES_TRANS                : thm := BDivides.DIVIDES_TRANS
def DIVIDES_ADD                  : thm := BDivides.DIVIDES_ADD
def DIVIDES_SUB_EQ               : thm := BDivides.DIVIDES_SUB_EQ
def DIVIDES_SUB                  : thm := BDivides.DIVIDES_SUB
def DIVIDES_SUB_1                : thm := BDivides.DIVIDES_SUB_1
def DIVIDES_LMUL                 : thm := BDivides.DIVIDES_LMUL
def DIVIDES_RMUL                 : thm := BDivides.DIVIDES_RMUL
def DIVIDES_ADD_REVR             : thm := BDivides.DIVIDES_ADD_REVR
def DIVIDES_ADD_REVL             : thm := BDivides.DIVIDES_ADD_REVL
def DIVIDES_MUL_L                : thm := BDivides.DIVIDES_MUL_L
def DIVIDES_MUL_R                : thm := BDivides.DIVIDES_MUL_R
def DIVIDES_LMUL2                : thm := BDivides.DIVIDES_LMUL2
def DIVIDES_RMUL2                : thm := BDivides.DIVIDES_RMUL2
def DIVIDES_CMUL2                : thm := BDivides.DIVIDES_CMUL2
def DIVIDES_LMUL2_EQ             : thm := BDivides.DIVIDES_LMUL2_EQ
def DIVIDES_RMUL2_EQ             : thm := BDivides.DIVIDES_RMUL2_EQ
def DIVIDES_EQ_ZERO              : thm := BDivides.DIVIDES_EQ_ZERO
def DIVIDES_CASES                : thm := BDivides.DIVIDES_CASES
def DIVIDES_DIV_NOT              : thm := BDivides.DIVIDES_DIV_NOT
def DIVIDES_MUL2                 : thm := BDivides.DIVIDES_MUL2
def DIVIDES_EXP                  : thm := BDivides.DIVIDES_EXP
def DIVIDES_EXP2                 : thm := BDivides.DIVIDES_EXP2
def DIVIDES_EXP_LE_IMP           : thm := BDivides.DIVIDES_EXP_LE_IMP
def DIVIDES_EXP_LE               : thm := BDivides.DIVIDES_EXP_LE
def DIVIDES_TRIVIAL_UPPERBOUND   : thm := BDivides.DIVIDES_TRIVIAL_UPPERBOUND
def DIVIDES_FACT                 : thm := BDivides.DIVIDES_FACT
def DIVIDES_2                    : thm := BDivides.DIVIDES_2
def DIVIDES_REXP_SUC             : thm := BDivides.DIVIDES_REXP_SUC
def DIVIDES_REXP                 : thm := BDivides.DIVIDES_REXP
def FINITE_DIVISORS              : thm := BDivides.FINITE_DIVISORS
def FINITE_SPECIAL_DIVISORS      : thm := BDivides.FINITE_SPECIAL_DIVISORS
def DIVISORS_EQ                  : thm := BDivides.DIVISORS_EQ
def MULTIPLES_EQ                 : thm := BDivides.MULTIPLES_EQ
def DIVIDES_NSUM                 : thm := BDivides.DIVIDES_NSUM

-- Gcd
def DIVIDES_GCD                  : thm := BGcd.DIVIDES_GCD
def GCD_0                        : thm := BGcd.GCD_0
def GCD_ZERO                     : thm := BGcd.GCD_ZERO
def GCD_REFL                     : thm := BGcd.GCD_REFL
def GCD_1                        : thm := BGcd.GCD_1
def GCD_MULTIPLE                 : thm := BGcd.GCD_MULTIPLE
def GCD_ADD                      : thm := BGcd.GCD_ADD
def GCD_SUB                      : thm := BGcd.GCD_SUB
def DIVIDES_GCD_LEFT             : thm := BGcd.DIVIDES_GCD_LEFT
def DIVIDES_GCD_RIGHT            : thm := BGcd.DIVIDES_GCD_RIGHT
def GCD_COPRIME_LMUL             : thm := BGcd.GCD_COPRIME_LMUL
def GCD_COPRIME_RMUL             : thm := BGcd.GCD_COPRIME_RMUL
def DIVIDES_LMUL_GCD             : thm := BGcd.DIVIDES_LMUL_GCD
def DIVIDES_RMUL_GCD             : thm := BGcd.DIVIDES_RMUL_GCD
def GCD_MUL_COPRIME              : thm := BGcd.GCD_MUL_COPRIME
def GCD_SYM                      : thm := BGcd.GCD_SYM
def GCD_ASSOC                    : thm := BGcd.GCD_ASSOC
def GCD_LMUL                     : thm := BGcd.GCD_LMUL
def GCD_RMUL                     : thm := BGcd.GCD_RMUL
def GCD_BEZOUT_SUM               : thm := BGcd.GCD_BEZOUT_SUM
def GCD_COPRIME_DIVIDES_LMUL     : thm := BGcd.GCD_COPRIME_DIVIDES_LMUL
def GCD_COPRIME_DIVIDES_RMUL     : thm := BGcd.GCD_COPRIME_DIVIDES_RMUL
def GCD_UNIQUE                   : thm := BGcd.GCD_UNIQUE
def GCD_EQ                       : thm := BGcd.GCD_EQ
def BEZOUT_GCD_STRONG            : thm := BGcd.BEZOUT_GCD_STRONG
def BEZOUT_ADD_STRONG            : thm := BGcd.BEZOUT_ADD_STRONG
def BEZOUT_GCD                   : thm := BGcd.BEZOUT_GCD
def BEZOUT_ADD                   : thm := BGcd.BEZOUT_ADD
def BEZOUT                       : thm := BGcd.BEZOUT
def GCD_BEZOUT                   : thm := BGcd.GCD_BEZOUT
def GCD_LE                       : thm := BGcd.GCD_LE
def GCD_LE_MIN_EQ                : thm := BGcd.GCD_LE_MIN_EQ
def GCD_LE_MIN                   : thm := BGcd.GCD_LE_MIN
def GCD_LE_MAX                   : thm := BGcd.GCD_LE_MAX

-- Coprime
def COPRIME                      : thm := BCoprime.COPRIME
def COPRIME_GCD                  : thm := BCoprime.COPRIME_GCD
def GCD_ONE                      : thm := BCoprime.GCD_ONE
def COPRIME_SYM                  : thm := BCoprime.COPRIME_SYM
def COPRIME_BEZOUT               : thm := BCoprime.COPRIME_BEZOUT
def COPRIME_DIVPROD              : thm := BCoprime.COPRIME_DIVPROD
def COPRIME_1                    : thm := BCoprime.COPRIME_1
def GCD_COPRIME                  : thm := BCoprime.GCD_COPRIME
def GCD_COPRIME_EXISTS           : thm := BCoprime.GCD_COPRIME_EXISTS
def COPRIME_DIVPROD_IFF          : thm := BCoprime.COPRIME_DIVPROD_IFF
def CONG_MULT_LCANCEL_IFF        : thm := BCoprime.CONG_MULT_LCANCEL_IFF
def CONG_MULT_RCANCEL_IFF        : thm := BCoprime.CONG_MULT_RCANCEL_IFF
def COPRIME_0                    : thm := BCoprime.COPRIME_0
def COPRIME_MUL                  : thm := BCoprime.COPRIME_MUL
def COPRIME_LMUL2                : thm := BCoprime.COPRIME_LMUL2
def COPRIME_RMUL2                : thm := BCoprime.COPRIME_RMUL2
def COPRIME_LMUL                 : thm := BCoprime.COPRIME_LMUL
def COPRIME_RMUL                 : thm := BCoprime.COPRIME_RMUL
def COPRIME_EXP                  : thm := BCoprime.COPRIME_EXP
def COPRIME_EXP_IMP              : thm := BCoprime.COPRIME_EXP_IMP
def COPRIME_REXP                 : thm := BCoprime.COPRIME_REXP
def COPRIME_LEXP                 : thm := BCoprime.COPRIME_LEXP
def COPRIME_EXP2                 : thm := BCoprime.COPRIME_EXP2
def COPRIME_EXP2_SUC             : thm := BCoprime.COPRIME_EXP2_SUC
def COPRIME_NPRODUCT_EQ          : thm := BCoprime.COPRIME_NPRODUCT_EQ
def COPRIME_NPRODUCT             : thm := BCoprime.COPRIME_NPRODUCT
def COPRIME_DIVISORS             : thm := BCoprime.COPRIME_DIVISORS
def COPRIME_REFL                 : thm := BCoprime.COPRIME_REFL
def COPRIME_PLUS1                : thm := BCoprime.COPRIME_PLUS1
def COPRIME_MINUS1               : thm := BCoprime.COPRIME_MINUS1
def GCD_EXP                      : thm := BCoprime.GCD_EXP
def DIVIDES_EXP2_REV             : thm := BCoprime.DIVIDES_EXP2_REV
def DIVIDES_EXP2_EQ              : thm := BCoprime.DIVIDES_EXP2_EQ
def DIVIDES_MUL                  : thm := BCoprime.DIVIDES_MUL
def DIVISION_DECOMP              : thm := BCoprime.DIVISION_DECOMP

-- Primes
def PRIME_0                      : thm := BPrimes.PRIME_0
def PRIME_1                      : thm := BPrimes.PRIME_1
def PRIME_ALT                    : thm := BPrimes.PRIME_ALT
def PRIME_2                      : thm := BPrimes.PRIME_2
def PRIME_COPRIME_STRONG         : thm := BPrimes.PRIME_COPRIME_STRONG
def PRIME_COPRIME                : thm := BPrimes.PRIME_COPRIME
def PRIME_COPRIME_EQ             : thm := BPrimes.PRIME_COPRIME_EQ
def COPRIME_PRIME                : thm := BPrimes.COPRIME_PRIME
def PRIME_DIVPROD                : thm := BPrimes.PRIME_DIVPROD
def PRIME_DIVPROD_EQ             : thm := BPrimes.PRIME_DIVPROD_EQ
def PRIME_INT_DIVPROD_EQ         : thm := BPrimes.PRIME_INT_DIVPROD_EQ
def PRIME_GE_2                   : thm := BPrimes.PRIME_GE_2
def PRIME_FACTOR                 : thm := BPrimes.PRIME_FACTOR
def PRIME                        : thm := BPrimes.PRIME
def PRIME_PRIME_FACTOR           : thm := BPrimes.PRIME_PRIME_FACTOR
def PRIME_FACTOR_LT              : thm := BPrimes.PRIME_FACTOR_LT
def COPRIME_PRIME_EQ             : thm := BPrimes.COPRIME_PRIME_EQ
def GCD_PRIME_CASES              : thm := BPrimes.GCD_PRIME_CASES
def GCD_2_CASES                  : thm := BPrimes.GCD_2_CASES
def COPRIME_PRIMEPOW             : thm := BPrimes.COPRIME_PRIMEPOW
def COPRIME_BEZOUT_STRONG        : thm := BPrimes.COPRIME_BEZOUT_STRONG
def COPRIME_BEZOUT_ALT           : thm := BPrimes.COPRIME_BEZOUT_ALT
def BEZOUT_PRIME                 : thm := BPrimes.BEZOUT_PRIME
def PRIME_DIVEXP                 : thm := BPrimes.PRIME_DIVEXP
def PRIME_DIVEXP_N               : thm := BPrimes.PRIME_DIVEXP_N
def PRIME_DIVEXP_EQ              : thm := BPrimes.PRIME_DIVEXP_EQ
def COPRIME_SOS                  : thm := BPrimes.COPRIME_SOS
def PRIME_IMP_NZ                 : thm := BPrimes.PRIME_IMP_NZ
def DISTINCT_PRIME_COPRIME       : thm := BPrimes.DISTINCT_PRIME_COPRIME
def PRIME_COPRIME_LT             : thm := BPrimes.PRIME_COPRIME_LT
def DIVIDES_PRIME_PRIME          : thm := BPrimes.DIVIDES_PRIME_PRIME
def COPRIME_PRIME_PRIME          : thm := BPrimes.COPRIME_PRIME_PRIME
def DIVIDES_PRIME_EXP_LE         : thm := BPrimes.DIVIDES_PRIME_EXP_LE
def EQ_PRIME_EXP                 : thm := BPrimes.EQ_PRIME_EXP
def PRIME_ODD                    : thm := BPrimes.PRIME_ODD
def ODD_PRIME                    : thm := BPrimes.ODD_PRIME
def DIVIDES_FACT_PRIME           : thm := BPrimes.DIVIDES_FACT_PRIME
def EQ_PRIMEPOW                  : thm := BPrimes.EQ_PRIMEPOW
def COPRIME_2                    : thm := BPrimes.COPRIME_2
def DIVIDES_EXP_PLUS1            : thm := BPrimes.DIVIDES_EXP_PLUS1
def DIVIDES_EXP_MINUS1           : thm := BPrimes.DIVIDES_EXP_MINUS1
def PRIME_IRREDUCIBLE            : thm := BPrimes.PRIME_IRREDUCIBLE
def COPRIME_EXP_DIVPROD          : thm := BPrimes.COPRIME_EXP_DIVPROD
def PRIME_COPRIME_CASES          : thm := BPrimes.PRIME_COPRIME_CASES
def PRIME_DIVPROD_POW_GEN        : thm := BPrimes.PRIME_DIVPROD_POW_GEN
def PRIME_DIVPROD_POW_GEN_EQ     : thm := BPrimes.PRIME_DIVPROD_POW_GEN_EQ
def PRIME_DIVPROD_POW            : thm := BPrimes.PRIME_DIVPROD_POW
def PRIME_DIVPROD_POW_EQ         : thm := BPrimes.PRIME_DIVPROD_POW_EQ
def PRIME_FACTOR_INDUCT          : thm := BPrimes.PRIME_FACTOR_INDUCT
def COMPLETE_FACTOR_INDUCT       : thm := BPrimes.COMPLETE_FACTOR_INDUCT
def PRIME_FACTOR_PARTITION       : thm := BPrimes.PRIME_FACTOR_PARTITION
def COPRIME_PAIR_DECOMP          : thm := BPrimes.COPRIME_PAIR_DECOMP
def EXP_MULT_EXISTS              : thm := BPrimes.EXP_MULT_EXISTS
def COPRIME_POW                  : thm := BPrimes.COPRIME_POW
def PRIME_EXP                    : thm := BPrimes.PRIME_EXP
def PRIME_POWER_MULT             : thm := BPrimes.PRIME_POWER_MULT
def PRIME_POWER_EXP              : thm := BPrimes.PRIME_POWER_EXP
def DIVIDES_PRIMEPOW             : thm := BPrimes.DIVIDES_PRIMEPOW
def PRIMEPOW_DIVIDES_PROD        : thm := BPrimes.PRIMEPOW_DIVIDES_PROD
def EUCLID_BOUND                 : thm := BPrimes.EUCLID_BOUND
def EUCLID                       : thm := BPrimes.EUCLID
def PRIMES_INFINITE              : thm := BPrimes.PRIMES_INFINITE
def FACTORIZATION_INDEX          : thm := BPrimes.FACTORIZATION_INDEX
def PRIMEPOW_FACTOR              : thm := BPrimes.PRIMEPOW_FACTOR
def PRIMEPOW_DIVISORS_DIVIDES    : thm := BPrimes.PRIMEPOW_DIVISORS_DIVIDES
def PRIMEPOW_DIVISORS_EQ         : thm := BPrimes.PRIMEPOW_DIVISORS_EQ

-- Chinese
def CHINESE_REMAINDER            : thm := BChinese.CHINESE_REMAINDER

-- Index
def FINITE_EXP_LE                : thm := BIndex.FINITE_EXP_LE
def FINITE_INDICES               : thm := BIndex.FINITE_INDICES
def index_def                    : thm := BIndex.index_def
def INDEX_0                      : thm := BIndex.INDEX_0
def PRIMEPOW_DIVIDES_INDEX       : thm := BIndex.PRIMEPOW_DIVIDES_INDEX
def LE_INDEX                     : thm := BIndex.LE_INDEX
def EXP_INDEX_DIVIDES            : thm := BIndex.EXP_INDEX_DIVIDES
def INDEX_LT                     : thm := BIndex.INDEX_LT
def INDEX_1                      : thm := BIndex.INDEX_1
def INDEX_MUL                    : thm := BIndex.INDEX_MUL
def INDEX_EXP                    : thm := BIndex.INDEX_EXP
def INDEX_NPRODUCT : thm := BIndex.INDEX_NPRODUCT
def INDEX_FACT                   : thm := BIndex.INDEX_FACT
def INDEX_FACT_ALT               : thm := BIndex.INDEX_FACT_ALT
def INDEX_FACT_UNBOUNDED         : thm := BIndex.INDEX_FACT_UNBOUNDED
def PRIMEPOW_DIVIDES_FACT        : thm := BIndex.PRIMEPOW_DIVIDES_FACT
def INDEX_REFL                   : thm := BIndex.INDEX_REFL
def INDEX_EQ_0                   : thm := BIndex.INDEX_EQ_0
def INDEX_ZERO                   : thm := BIndex.INDEX_ZERO
def INDEX_POW                    : thm := BIndex.INDEX_POW
def INDEX_PRIME                  : thm := BIndex.INDEX_PRIME
def INDEX_TRIVIAL_BOUND          : thm := BIndex.INDEX_TRIVIAL_BOUND
def INDEX_DECOMPOSITION          : thm := BIndex.INDEX_DECOMPOSITION
def INDEX_DECOMPOSITION_PRIME    : thm := BIndex.INDEX_DECOMPOSITION_PRIME
def INDEX_DECOMPOSITION_LE       : thm := BIndex.INDEX_DECOMPOSITION_LE
def INDEX_DECOMPOSITION_UNIQUE   : thm := BIndex.INDEX_DECOMPOSITION_UNIQUE
def INDEX_UNIQUE                 : thm := BIndex.INDEX_UNIQUE
def INDEX_UNIQUE_EQ              : thm := BIndex.INDEX_UNIQUE_EQ
def INDEX_UNIQUE_ALT             : thm := BIndex.INDEX_UNIQUE_ALT
def INDEX_ADD_MIN                : thm := BIndex.INDEX_ADD_MIN
def INDEX_SUB_MIN                : thm := BIndex.INDEX_SUB_MIN
def INDEX_ADD                    : thm := BIndex.INDEX_ADD
def INDEX_MULT_BASE              : thm := BIndex.INDEX_MULT_BASE
def INDEX_MULT_EXP               : thm := BIndex.INDEX_MULT_EXP
def INDEX_MULT_ADD               : thm := BIndex.INDEX_MULT_ADD
def INDEX_NSUM_LE                : thm := BIndex.INDEX_NSUM_LE
def DIVIDES_INDEX                : thm := BIndex.DIVIDES_INDEX
def EQ_INDEX                     : thm := BIndex.EQ_INDEX
def COPRIME_INDEX                : thm := BIndex.COPRIME_INDEX
def INDEX_GCD                    : thm := BIndex.INDEX_GCD
def FORALL_PRIME_INDEX           : thm := BIndex.FORALL_PRIME_INDEX
def INDEX_FACT_PRIME_MULT        : thm := BIndex.INDEX_FACT_PRIME_MULT
def PRIME_FACTORIZATION_INDEX    : thm := BIndex.PRIME_FACTORIZATION_INDEX
def PRIME_POWER_EXISTS           : thm := BIndex.PRIME_POWER_EXISTS
def PRIME_POWER_EXISTS_ALT       : thm := BIndex.PRIME_POWER_EXISTS_ALT
def PRIME_FACTORIZATION_ALT      : thm := BIndex.PRIME_FACTORIZATION_ALT
def PRIME_FACTORIZATION          : thm := BIndex.PRIME_FACTORIZATION

-- Lcm
def lcm                          : thm := BLcm.lcm
def LCM_DIVIDES                  : thm := BLcm.LCM_DIVIDES
def LCM                          : thm := BLcm.LCM
def LCM_DIVIDES_MUL              : thm := BLcm.LCM_DIVIDES_MUL
def DIVIDES_LCM                  : thm := BLcm.DIVIDES_LCM
def LCM_0                        : thm := BLcm.LCM_0
def LCM_1                        : thm := BLcm.LCM_1
def LCM_SYM                      : thm := BLcm.LCM_SYM
def DIVIDES_LCM_GCD              : thm := BLcm.DIVIDES_LCM_GCD
def PRIMEPOW_DIVIDES_LCM         : thm := BLcm.PRIMEPOW_DIVIDES_LCM
def PRIME_DIVIDES_LCM            : thm := BLcm.PRIME_DIVIDES_LCM
def LCM_ZERO                     : thm := BLcm.LCM_ZERO
def INDEX_LCM                    : thm := BLcm.INDEX_LCM
def LCM_ASSOC                    : thm := BLcm.LCM_ASSOC
def LCM_REFL                     : thm := BLcm.LCM_REFL
def LCM_MULTIPLE                 : thm := BLcm.LCM_MULTIPLE
def LCM_GCD_DISTRIB              : thm := BLcm.LCM_GCD_DISTRIB
def GCD_LCM_DISTRIB              : thm := BLcm.GCD_LCM_DISTRIB
def LCM_UNIQUE                   : thm := BLcm.LCM_UNIQUE
def LCM_EQ                       : thm := BLcm.LCM_EQ
def LCM_EQ_1                     : thm := BLcm.LCM_EQ_1
def DIVIDES_LCM_LEFT             : thm := BLcm.DIVIDES_LCM_LEFT
def DIVIDES_LCM_RIGHT            : thm := BLcm.DIVIDES_LCM_RIGHT
def MULT_LCM_GCD                 : thm := BLcm.MULT_LCM_GCD
def MULT_GCD_LCM                 : thm := BLcm.MULT_GCD_LCM
def LCM_LMUL                     : thm := BLcm.LCM_LMUL
def LCM_RMUL                     : thm := BLcm.LCM_RMUL
def LCM_EXP                      : thm := BLcm.LCM_EXP
def LCM_COPRIME_DECOMP           : thm := BLcm.LCM_COPRIME_DECOMP
def LE_LCM                       : thm := BLcm.LE_LCM
def LCM_LE_MULT                  : thm := BLcm.LCM_LE_MULT
def LCM_EQ_MULT                  : thm := BLcm.LCM_EQ_MULT
def MAX_LE_LCM_EQ                : thm := BLcm.MAX_LE_LCM_EQ
def MAX_LE_LCM                   : thm := BLcm.MAX_LE_LCM

-- Iterated
def NEUTRAL_GCD                  : thm := BIterated.NEUTRAL_GCD
def MONOIDAL_GCD                 : thm := BIterated.MONOIDAL_GCD
def NEUTRAL_LCM                  : thm := BIterated.NEUTRAL_LCM
def MONOIDAL_LCM                 : thm := BIterated.MONOIDAL_LCM
def ITERATE_GCD_DIVIDES          : thm := BIterated.ITERATE_GCD_DIVIDES
def ITERATE_GCD_DIVIDES_EQ       : thm := BIterated.ITERATE_GCD_DIVIDES_EQ
def DIVIDES_ITERATE_GCD          : thm := BIterated.DIVIDES_ITERATE_GCD
def DIVIDES_ITERATE_GCD_GEN      : thm := BIterated.DIVIDES_ITERATE_GCD_GEN
def DIVIDES_ITERATE_LCM          : thm := BIterated.DIVIDES_ITERATE_LCM
def DIVIDES_ITERATE_LCM_GEN      : thm := BIterated.DIVIDES_ITERATE_LCM_GEN
def ITERATE_LCM_DIVIDES          : thm := BIterated.ITERATE_LCM_DIVIDES
def ITERATE_LCM_DIVIDES_GEN      : thm := BIterated.ITERATE_LCM_DIVIDES_GEN
def PRIMEPOW_DIVIDES_ITERATE_LCM : thm := BIterated.PRIMEPOW_DIVIDES_ITERATE_LCM
def PRIMEPOW_DIVIDES_ITERATE_LCM_GEN : thm := BIterated.PRIMEPOW_DIVIDES_ITERATE_LCM_GEN
def PRIME_DIVIDES_ITERATE_LCM_GEN : thm := BIterated.PRIME_DIVIDES_ITERATE_LCM_GEN
def PRIME_DIVIDES_ITERATE_LCM    : thm := BIterated.PRIME_DIVIDES_ITERATE_LCM
def ITERATE_LCM_EQ_0_GEN         : thm := BIterated.ITERATE_LCM_EQ_0_GEN
def ITERATE_LCM_EQ_0             : thm := BIterated.ITERATE_LCM_EQ_0
def ITERATE_LCM_EQ_1_GEN         : thm := BIterated.ITERATE_LCM_EQ_1_GEN
def ITERATE_LCM_EQ_1             : thm := BIterated.ITERATE_LCM_EQ_1
def ITERATE_GCD_EQ_0_GEN         : thm := BIterated.ITERATE_GCD_EQ_0_GEN
def ITERATE_GCD_EQ_0             : thm := BIterated.ITERATE_GCD_EQ_0

-- Induct
def INDUCT_COPRIME               : thm := BInduct.INDUCT_COPRIME
def INDUCT_COPRIME_STRONG        : thm := BInduct.INDUCT_COPRIME_STRONG
def INDUCT_COPRIME_ALT           : thm := BInduct.INDUCT_COPRIME_ALT

/- The conversions (prime.ml 2358-2472). -/
/-- `DIVIDES_CONV` (prime.ml 2361). -/
def DIVIDES_CONV : HolCore.Equal.ioconv := fun tm => HolLibrary.Prime.DIVIDES_CONV (deps) BConvs tm
/-- `COPRIME_CONV` (prime.ml 2381). -/
def COPRIME_CONV : HolCore.Equal.ioconv := fun tm => HolLibrary.Prime.COPRIME_CONV (deps) BConvs tm
/-- `GCD_CONV` (prime.ml 2429). -/
def GCD_CONV : HolCore.Equal.ioconv := fun tm => HolLibrary.Prime.GCD_CONV (deps) BConvs tm
/-- `LCM_CONV` (prime.ml 2467), built once at load.  A conversion, so it is
    kept in a one-field structure: an `initialize` of function type is never
    run in compiled code (see `WfQqconvBox`, SessionMath/Wf.lean). -/
structure LcmConvBox where
  conv : HolCore.Equal.ioconv

instance : Inhabited LcmConvBox := ⟨⟨fun _ => pure (.error "LCM_CONV")⟩⟩

initialize lcmConvBox : LcmConvBox ←
  return ⟨← ioB "LCM_CONV" (HolLibrary.Prime.LCM_CONV deps BConvs BLcm.lcm).run⟩
def LCM_CONV : HolCore.Equal.ioconv := lcmConvBox.conv

/-- `needs "Library/prime.ml"`: already done by importing this module. -/
def ensurePrime : IO Unit := pure ()

end SessionLibrary.Prime
