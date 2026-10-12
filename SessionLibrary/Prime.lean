/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/prime.ml.                                   -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Prime.lean

  The `unsafe` half of the prime.ml translation, as Session.lean is for
  HolMath: it supplies HolLibrary.Prime's dependencies from Session, builds
  each theorem bundle on first use (in file order), and exports every
  theorem by name.  `ensurePrime` is `needs "Library/prime.ml"`.
-/

import Session
import HolLibrary.Prime

open HolCore HolCore.Kernel
open Session

namespace SessionLibrary.Prime

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨sessionB, sessionC, sessionT⟩

/-- The core theorems prime.ml uses, A-L. -/
unsafe def core1 (_ : Unit) : HolLibrary.Prime.CoreThms1 where
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
unsafe def core2 (_ : Unit) : HolLibrary.Prime.CoreThms2 where
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

/-- prime.ml's dependencies, from Session.  A function, not a constant: a
    constant would be built (forcing every Session theorem it names) when
    first referenced, before hol.ml's library has been loaded in order. -/
unsafe def deps (_ : Unit) : HolLibrary.Prime.PrimeDeps where
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
  core1 := core1 ()
  core2 := core2 ()

/-- prime.ml runs after the whole of hol.ml, then `prioritize_num()`
    (prime.ml 5).  Run once, before the first bundle. -/
initialize thePrimePrelude : IO.Ref Bool ← IO.mkRef false

unsafe def ensurePrimePrelude : IO Unit := do
  unless (← thePrimePrelude.get) do
    thePrimePrelude.set true
    Session.ensureDefine
    match ← (HolMath.Int.prioritize_num Session.prioritize_overload).run with
    | .ok () => pure ()
    | .error e => panic! s!"prioritize_num failed: {e}"

/-- Build a bundle once, after the prelude.  `setup` is a thunk: building
    its argument would force `deps`, and so every Session theorem it names,
    before hol.ml's library has been loaded in order. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      ensurePrimePrelude
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.Prime: {name}"

initialize theDivides : IO.Ref (Option HolLibrary.Prime.Divides) ← IO.mkRef none
private unsafe def BDivides : HolLibrary.Prime.Divides :=
  cached theDivides "setupDivides" fun _ => (HolLibrary.Prime.setupDivides (deps ())).run
initialize theGcd : IO.Ref (Option HolLibrary.Prime.Gcd) ← IO.mkRef none
private unsafe def BGcd : HolLibrary.Prime.Gcd :=
  cached theGcd "setupGcd" fun _ => (HolLibrary.Prime.setupGcd (deps ()) BDivides).run
initialize theCoprime : IO.Ref (Option HolLibrary.Prime.Coprime) ← IO.mkRef none
private unsafe def BCoprime : HolLibrary.Prime.Coprime :=
  cached theCoprime "setupCoprime" fun _ => (HolLibrary.Prime.setupCoprime (deps ()) BDivides BGcd).run
initialize thePrimes : IO.Ref (Option HolLibrary.Prime.Primes) ← IO.mkRef none
private unsafe def BPrimes : HolLibrary.Prime.Primes :=
  cached thePrimes "setupPrimes" fun _ => (HolLibrary.Prime.setupPrimes (deps ()) BDivides BGcd BCoprime).run
initialize theChinese : IO.Ref (Option HolLibrary.Prime.Chinese) ← IO.mkRef none
private unsafe def BChinese : HolLibrary.Prime.Chinese :=
  cached theChinese "setupChinese" fun _ => (HolLibrary.Prime.setupChinese (deps ()) BGcd BCoprime).run
initialize theIndex : IO.Ref (Option HolLibrary.Prime.Index) ← IO.mkRef none
private unsafe def BIndex : HolLibrary.Prime.Index :=
  cached theIndex "setupIndex" fun _ => (HolLibrary.Prime.setupIndex (deps ()) BDivides BGcd BCoprime BPrimes).run
initialize theLcm : IO.Ref (Option HolLibrary.Prime.Lcm) ← IO.mkRef none
private unsafe def BLcm : HolLibrary.Prime.Lcm :=
  cached theLcm "setupLcm" fun _ => (HolLibrary.Prime.setupLcm (deps ()) BDivides BGcd BCoprime BPrimes BIndex).run
initialize theIterated : IO.Ref (Option HolLibrary.Prime.Iterated) ← IO.mkRef none
private unsafe def BIterated : HolLibrary.Prime.Iterated :=
  cached theIterated "setupIterated" fun _ => (HolLibrary.Prime.setupIterated (deps ()) BDivides BGcd BPrimes BLcm).run
initialize theInduct : IO.Ref (Option HolLibrary.Prime.Induct) ← IO.mkRef none
private unsafe def BInduct : HolLibrary.Prime.Induct :=
  cached theInduct "setupInduct" fun _ => (HolLibrary.Prime.setupInduct (deps ()) BCoprime BPrimes).run
initialize theConvs : IO.Ref (Option HolLibrary.Prime.Convs) ← IO.mkRef none
private unsafe def BConvs : HolLibrary.Prime.Convs :=
  cached theConvs "setupConvs" fun _ => (HolLibrary.Prime.setupConvs (deps ()) BDivides BGcd).run

/- The theorems, by name. -/
-- Divides
unsafe def DIVIDES_0                    : thm := BDivides.DIVIDES_0
unsafe def DIVIDES_ZERO                 : thm := BDivides.DIVIDES_ZERO
unsafe def DIVIDES_1                    : thm := BDivides.DIVIDES_1
unsafe def DIVIDES_REFL                 : thm := BDivides.DIVIDES_REFL
unsafe def DIVIDES_TRANS                : thm := BDivides.DIVIDES_TRANS
unsafe def DIVIDES_ADD                  : thm := BDivides.DIVIDES_ADD
unsafe def DIVIDES_SUB_EQ               : thm := BDivides.DIVIDES_SUB_EQ
unsafe def DIVIDES_SUB                  : thm := BDivides.DIVIDES_SUB
unsafe def DIVIDES_SUB_1                : thm := BDivides.DIVIDES_SUB_1
unsafe def DIVIDES_LMUL                 : thm := BDivides.DIVIDES_LMUL
unsafe def DIVIDES_RMUL                 : thm := BDivides.DIVIDES_RMUL
unsafe def DIVIDES_ADD_REVR             : thm := BDivides.DIVIDES_ADD_REVR
unsafe def DIVIDES_ADD_REVL             : thm := BDivides.DIVIDES_ADD_REVL
unsafe def DIVIDES_MUL_L                : thm := BDivides.DIVIDES_MUL_L
unsafe def DIVIDES_MUL_R                : thm := BDivides.DIVIDES_MUL_R
unsafe def DIVIDES_LMUL2                : thm := BDivides.DIVIDES_LMUL2
unsafe def DIVIDES_RMUL2                : thm := BDivides.DIVIDES_RMUL2
unsafe def DIVIDES_CMUL2                : thm := BDivides.DIVIDES_CMUL2
unsafe def DIVIDES_LMUL2_EQ             : thm := BDivides.DIVIDES_LMUL2_EQ
unsafe def DIVIDES_RMUL2_EQ             : thm := BDivides.DIVIDES_RMUL2_EQ
unsafe def DIVIDES_EQ_ZERO              : thm := BDivides.DIVIDES_EQ_ZERO
unsafe def DIVIDES_CASES                : thm := BDivides.DIVIDES_CASES
unsafe def DIVIDES_DIV_NOT              : thm := BDivides.DIVIDES_DIV_NOT
unsafe def DIVIDES_MUL2                 : thm := BDivides.DIVIDES_MUL2
unsafe def DIVIDES_EXP                  : thm := BDivides.DIVIDES_EXP
unsafe def DIVIDES_EXP2                 : thm := BDivides.DIVIDES_EXP2
unsafe def DIVIDES_EXP_LE_IMP           : thm := BDivides.DIVIDES_EXP_LE_IMP
unsafe def DIVIDES_EXP_LE               : thm := BDivides.DIVIDES_EXP_LE
unsafe def DIVIDES_TRIVIAL_UPPERBOUND   : thm := BDivides.DIVIDES_TRIVIAL_UPPERBOUND
unsafe def DIVIDES_FACT                 : thm := BDivides.DIVIDES_FACT
unsafe def DIVIDES_2                    : thm := BDivides.DIVIDES_2
unsafe def DIVIDES_REXP_SUC             : thm := BDivides.DIVIDES_REXP_SUC
unsafe def DIVIDES_REXP                 : thm := BDivides.DIVIDES_REXP
unsafe def FINITE_DIVISORS              : thm := BDivides.FINITE_DIVISORS
unsafe def FINITE_SPECIAL_DIVISORS      : thm := BDivides.FINITE_SPECIAL_DIVISORS
unsafe def DIVISORS_EQ                  : thm := BDivides.DIVISORS_EQ
unsafe def MULTIPLES_EQ                 : thm := BDivides.MULTIPLES_EQ
unsafe def DIVIDES_NSUM                 : thm := BDivides.DIVIDES_NSUM

-- Gcd
unsafe def DIVIDES_GCD                  : thm := BGcd.DIVIDES_GCD
unsafe def GCD_0                        : thm := BGcd.GCD_0
unsafe def GCD_ZERO                     : thm := BGcd.GCD_ZERO
unsafe def GCD_REFL                     : thm := BGcd.GCD_REFL
unsafe def GCD_1                        : thm := BGcd.GCD_1
unsafe def GCD_MULTIPLE                 : thm := BGcd.GCD_MULTIPLE
unsafe def GCD_ADD                      : thm := BGcd.GCD_ADD
unsafe def GCD_SUB                      : thm := BGcd.GCD_SUB
unsafe def DIVIDES_GCD_LEFT             : thm := BGcd.DIVIDES_GCD_LEFT
unsafe def DIVIDES_GCD_RIGHT            : thm := BGcd.DIVIDES_GCD_RIGHT
unsafe def GCD_COPRIME_LMUL             : thm := BGcd.GCD_COPRIME_LMUL
unsafe def GCD_COPRIME_RMUL             : thm := BGcd.GCD_COPRIME_RMUL
unsafe def DIVIDES_LMUL_GCD             : thm := BGcd.DIVIDES_LMUL_GCD
unsafe def DIVIDES_RMUL_GCD             : thm := BGcd.DIVIDES_RMUL_GCD
unsafe def GCD_MUL_COPRIME              : thm := BGcd.GCD_MUL_COPRIME
unsafe def GCD_SYM                      : thm := BGcd.GCD_SYM
unsafe def GCD_ASSOC                    : thm := BGcd.GCD_ASSOC
unsafe def GCD_LMUL                     : thm := BGcd.GCD_LMUL
unsafe def GCD_RMUL                     : thm := BGcd.GCD_RMUL
unsafe def GCD_BEZOUT_SUM               : thm := BGcd.GCD_BEZOUT_SUM
unsafe def GCD_COPRIME_DIVIDES_LMUL     : thm := BGcd.GCD_COPRIME_DIVIDES_LMUL
unsafe def GCD_COPRIME_DIVIDES_RMUL     : thm := BGcd.GCD_COPRIME_DIVIDES_RMUL
unsafe def GCD_UNIQUE                   : thm := BGcd.GCD_UNIQUE
unsafe def GCD_EQ                       : thm := BGcd.GCD_EQ
unsafe def BEZOUT_GCD_STRONG            : thm := BGcd.BEZOUT_GCD_STRONG
unsafe def BEZOUT_ADD_STRONG            : thm := BGcd.BEZOUT_ADD_STRONG
unsafe def BEZOUT_GCD                   : thm := BGcd.BEZOUT_GCD
unsafe def BEZOUT_ADD                   : thm := BGcd.BEZOUT_ADD
unsafe def BEZOUT                       : thm := BGcd.BEZOUT
unsafe def GCD_BEZOUT                   : thm := BGcd.GCD_BEZOUT
unsafe def GCD_LE                       : thm := BGcd.GCD_LE
unsafe def GCD_LE_MIN_EQ                : thm := BGcd.GCD_LE_MIN_EQ
unsafe def GCD_LE_MIN                   : thm := BGcd.GCD_LE_MIN
unsafe def GCD_LE_MAX                   : thm := BGcd.GCD_LE_MAX

-- Coprime
unsafe def COPRIME                      : thm := BCoprime.COPRIME
unsafe def COPRIME_GCD                  : thm := BCoprime.COPRIME_GCD
unsafe def GCD_ONE                      : thm := BCoprime.GCD_ONE
unsafe def COPRIME_SYM                  : thm := BCoprime.COPRIME_SYM
unsafe def COPRIME_BEZOUT               : thm := BCoprime.COPRIME_BEZOUT
unsafe def COPRIME_DIVPROD              : thm := BCoprime.COPRIME_DIVPROD
unsafe def COPRIME_1                    : thm := BCoprime.COPRIME_1
unsafe def GCD_COPRIME                  : thm := BCoprime.GCD_COPRIME
unsafe def GCD_COPRIME_EXISTS           : thm := BCoprime.GCD_COPRIME_EXISTS
unsafe def COPRIME_DIVPROD_IFF          : thm := BCoprime.COPRIME_DIVPROD_IFF
unsafe def CONG_MULT_LCANCEL_IFF        : thm := BCoprime.CONG_MULT_LCANCEL_IFF
unsafe def CONG_MULT_RCANCEL_IFF        : thm := BCoprime.CONG_MULT_RCANCEL_IFF
unsafe def COPRIME_0                    : thm := BCoprime.COPRIME_0
unsafe def COPRIME_MUL                  : thm := BCoprime.COPRIME_MUL
unsafe def COPRIME_LMUL2                : thm := BCoprime.COPRIME_LMUL2
unsafe def COPRIME_RMUL2                : thm := BCoprime.COPRIME_RMUL2
unsafe def COPRIME_LMUL                 : thm := BCoprime.COPRIME_LMUL
unsafe def COPRIME_RMUL                 : thm := BCoprime.COPRIME_RMUL
unsafe def COPRIME_EXP                  : thm := BCoprime.COPRIME_EXP
unsafe def COPRIME_EXP_IMP              : thm := BCoprime.COPRIME_EXP_IMP
unsafe def COPRIME_REXP                 : thm := BCoprime.COPRIME_REXP
unsafe def COPRIME_LEXP                 : thm := BCoprime.COPRIME_LEXP
unsafe def COPRIME_EXP2                 : thm := BCoprime.COPRIME_EXP2
unsafe def COPRIME_EXP2_SUC             : thm := BCoprime.COPRIME_EXP2_SUC
unsafe def COPRIME_NPRODUCT_EQ          : thm := BCoprime.COPRIME_NPRODUCT_EQ
unsafe def COPRIME_NPRODUCT             : thm := BCoprime.COPRIME_NPRODUCT
unsafe def COPRIME_DIVISORS             : thm := BCoprime.COPRIME_DIVISORS
unsafe def COPRIME_REFL                 : thm := BCoprime.COPRIME_REFL
unsafe def COPRIME_PLUS1                : thm := BCoprime.COPRIME_PLUS1
unsafe def COPRIME_MINUS1               : thm := BCoprime.COPRIME_MINUS1
unsafe def GCD_EXP                      : thm := BCoprime.GCD_EXP
unsafe def DIVIDES_EXP2_REV             : thm := BCoprime.DIVIDES_EXP2_REV
unsafe def DIVIDES_EXP2_EQ              : thm := BCoprime.DIVIDES_EXP2_EQ
unsafe def DIVIDES_MUL                  : thm := BCoprime.DIVIDES_MUL
unsafe def DIVISION_DECOMP              : thm := BCoprime.DIVISION_DECOMP

-- Primes
unsafe def PRIME_0                      : thm := BPrimes.PRIME_0
unsafe def PRIME_1                      : thm := BPrimes.PRIME_1
unsafe def PRIME_ALT                    : thm := BPrimes.PRIME_ALT
unsafe def PRIME_2                      : thm := BPrimes.PRIME_2
unsafe def PRIME_COPRIME_STRONG         : thm := BPrimes.PRIME_COPRIME_STRONG
unsafe def PRIME_COPRIME                : thm := BPrimes.PRIME_COPRIME
unsafe def PRIME_COPRIME_EQ             : thm := BPrimes.PRIME_COPRIME_EQ
unsafe def COPRIME_PRIME                : thm := BPrimes.COPRIME_PRIME
unsafe def PRIME_DIVPROD                : thm := BPrimes.PRIME_DIVPROD
unsafe def PRIME_DIVPROD_EQ             : thm := BPrimes.PRIME_DIVPROD_EQ
unsafe def PRIME_INT_DIVPROD_EQ         : thm := BPrimes.PRIME_INT_DIVPROD_EQ
unsafe def PRIME_GE_2                   : thm := BPrimes.PRIME_GE_2
unsafe def PRIME_FACTOR                 : thm := BPrimes.PRIME_FACTOR
unsafe def PRIME                        : thm := BPrimes.PRIME
unsafe def PRIME_PRIME_FACTOR           : thm := BPrimes.PRIME_PRIME_FACTOR
unsafe def PRIME_FACTOR_LT              : thm := BPrimes.PRIME_FACTOR_LT
unsafe def COPRIME_PRIME_EQ             : thm := BPrimes.COPRIME_PRIME_EQ
unsafe def GCD_PRIME_CASES              : thm := BPrimes.GCD_PRIME_CASES
unsafe def GCD_2_CASES                  : thm := BPrimes.GCD_2_CASES
unsafe def COPRIME_PRIMEPOW             : thm := BPrimes.COPRIME_PRIMEPOW
unsafe def COPRIME_BEZOUT_STRONG        : thm := BPrimes.COPRIME_BEZOUT_STRONG
unsafe def COPRIME_BEZOUT_ALT           : thm := BPrimes.COPRIME_BEZOUT_ALT
unsafe def BEZOUT_PRIME                 : thm := BPrimes.BEZOUT_PRIME
unsafe def PRIME_DIVEXP                 : thm := BPrimes.PRIME_DIVEXP
unsafe def PRIME_DIVEXP_N               : thm := BPrimes.PRIME_DIVEXP_N
unsafe def PRIME_DIVEXP_EQ              : thm := BPrimes.PRIME_DIVEXP_EQ
unsafe def COPRIME_SOS                  : thm := BPrimes.COPRIME_SOS
unsafe def PRIME_IMP_NZ                 : thm := BPrimes.PRIME_IMP_NZ
unsafe def DISTINCT_PRIME_COPRIME       : thm := BPrimes.DISTINCT_PRIME_COPRIME
unsafe def PRIME_COPRIME_LT             : thm := BPrimes.PRIME_COPRIME_LT
unsafe def DIVIDES_PRIME_PRIME          : thm := BPrimes.DIVIDES_PRIME_PRIME
unsafe def COPRIME_PRIME_PRIME          : thm := BPrimes.COPRIME_PRIME_PRIME
unsafe def DIVIDES_PRIME_EXP_LE         : thm := BPrimes.DIVIDES_PRIME_EXP_LE
unsafe def EQ_PRIME_EXP                 : thm := BPrimes.EQ_PRIME_EXP
unsafe def PRIME_ODD                    : thm := BPrimes.PRIME_ODD
unsafe def ODD_PRIME                    : thm := BPrimes.ODD_PRIME
unsafe def DIVIDES_FACT_PRIME           : thm := BPrimes.DIVIDES_FACT_PRIME
unsafe def EQ_PRIMEPOW                  : thm := BPrimes.EQ_PRIMEPOW
unsafe def COPRIME_2                    : thm := BPrimes.COPRIME_2
unsafe def DIVIDES_EXP_PLUS1            : thm := BPrimes.DIVIDES_EXP_PLUS1
unsafe def DIVIDES_EXP_MINUS1           : thm := BPrimes.DIVIDES_EXP_MINUS1
unsafe def PRIME_IRREDUCIBLE            : thm := BPrimes.PRIME_IRREDUCIBLE
unsafe def COPRIME_EXP_DIVPROD          : thm := BPrimes.COPRIME_EXP_DIVPROD
unsafe def PRIME_COPRIME_CASES          : thm := BPrimes.PRIME_COPRIME_CASES
unsafe def PRIME_DIVPROD_POW_GEN        : thm := BPrimes.PRIME_DIVPROD_POW_GEN
unsafe def PRIME_DIVPROD_POW_GEN_EQ     : thm := BPrimes.PRIME_DIVPROD_POW_GEN_EQ
unsafe def PRIME_DIVPROD_POW            : thm := BPrimes.PRIME_DIVPROD_POW
unsafe def PRIME_DIVPROD_POW_EQ         : thm := BPrimes.PRIME_DIVPROD_POW_EQ
unsafe def PRIME_FACTOR_INDUCT          : thm := BPrimes.PRIME_FACTOR_INDUCT
unsafe def COMPLETE_FACTOR_INDUCT       : thm := BPrimes.COMPLETE_FACTOR_INDUCT
unsafe def PRIME_FACTOR_PARTITION       : thm := BPrimes.PRIME_FACTOR_PARTITION
unsafe def COPRIME_PAIR_DECOMP          : thm := BPrimes.COPRIME_PAIR_DECOMP
unsafe def EXP_MULT_EXISTS              : thm := BPrimes.EXP_MULT_EXISTS
unsafe def COPRIME_POW                  : thm := BPrimes.COPRIME_POW
unsafe def PRIME_EXP                    : thm := BPrimes.PRIME_EXP
unsafe def PRIME_POWER_MULT             : thm := BPrimes.PRIME_POWER_MULT
unsafe def PRIME_POWER_EXP              : thm := BPrimes.PRIME_POWER_EXP
unsafe def DIVIDES_PRIMEPOW             : thm := BPrimes.DIVIDES_PRIMEPOW
unsafe def PRIMEPOW_DIVIDES_PROD        : thm := BPrimes.PRIMEPOW_DIVIDES_PROD
unsafe def EUCLID_BOUND                 : thm := BPrimes.EUCLID_BOUND
unsafe def EUCLID                       : thm := BPrimes.EUCLID
unsafe def PRIMES_INFINITE              : thm := BPrimes.PRIMES_INFINITE
unsafe def FACTORIZATION_INDEX          : thm := BPrimes.FACTORIZATION_INDEX
unsafe def PRIMEPOW_FACTOR              : thm := BPrimes.PRIMEPOW_FACTOR
unsafe def PRIMEPOW_DIVISORS_DIVIDES    : thm := BPrimes.PRIMEPOW_DIVISORS_DIVIDES
unsafe def PRIMEPOW_DIVISORS_EQ         : thm := BPrimes.PRIMEPOW_DIVISORS_EQ

-- Chinese
unsafe def CHINESE_REMAINDER            : thm := BChinese.CHINESE_REMAINDER

-- Index
unsafe def FINITE_EXP_LE                : thm := BIndex.FINITE_EXP_LE
unsafe def FINITE_INDICES               : thm := BIndex.FINITE_INDICES
unsafe def index_def                    : thm := BIndex.index_def
unsafe def INDEX_0                      : thm := BIndex.INDEX_0
unsafe def PRIMEPOW_DIVIDES_INDEX       : thm := BIndex.PRIMEPOW_DIVIDES_INDEX
unsafe def LE_INDEX                     : thm := BIndex.LE_INDEX
unsafe def EXP_INDEX_DIVIDES            : thm := BIndex.EXP_INDEX_DIVIDES
unsafe def INDEX_LT                     : thm := BIndex.INDEX_LT
unsafe def INDEX_1                      : thm := BIndex.INDEX_1
unsafe def INDEX_MUL                    : thm := BIndex.INDEX_MUL
unsafe def INDEX_EXP                    : thm := BIndex.INDEX_EXP
unsafe def INDEX_FACT                   : thm := BIndex.INDEX_FACT
unsafe def INDEX_FACT_ALT               : thm := BIndex.INDEX_FACT_ALT
unsafe def INDEX_FACT_UNBOUNDED         : thm := BIndex.INDEX_FACT_UNBOUNDED
unsafe def PRIMEPOW_DIVIDES_FACT        : thm := BIndex.PRIMEPOW_DIVIDES_FACT
unsafe def INDEX_REFL                   : thm := BIndex.INDEX_REFL
unsafe def INDEX_EQ_0                   : thm := BIndex.INDEX_EQ_0
unsafe def INDEX_ZERO                   : thm := BIndex.INDEX_ZERO
unsafe def INDEX_POW                    : thm := BIndex.INDEX_POW
unsafe def INDEX_PRIME                  : thm := BIndex.INDEX_PRIME
unsafe def INDEX_TRIVIAL_BOUND          : thm := BIndex.INDEX_TRIVIAL_BOUND
unsafe def INDEX_DECOMPOSITION          : thm := BIndex.INDEX_DECOMPOSITION
unsafe def INDEX_DECOMPOSITION_PRIME    : thm := BIndex.INDEX_DECOMPOSITION_PRIME
unsafe def INDEX_DECOMPOSITION_LE       : thm := BIndex.INDEX_DECOMPOSITION_LE
unsafe def INDEX_DECOMPOSITION_UNIQUE   : thm := BIndex.INDEX_DECOMPOSITION_UNIQUE
unsafe def INDEX_UNIQUE                 : thm := BIndex.INDEX_UNIQUE
unsafe def INDEX_UNIQUE_EQ              : thm := BIndex.INDEX_UNIQUE_EQ
unsafe def INDEX_UNIQUE_ALT             : thm := BIndex.INDEX_UNIQUE_ALT
unsafe def INDEX_ADD_MIN                : thm := BIndex.INDEX_ADD_MIN
unsafe def INDEX_SUB_MIN                : thm := BIndex.INDEX_SUB_MIN
unsafe def INDEX_ADD                    : thm := BIndex.INDEX_ADD
unsafe def INDEX_MULT_BASE              : thm := BIndex.INDEX_MULT_BASE
unsafe def INDEX_MULT_EXP               : thm := BIndex.INDEX_MULT_EXP
unsafe def INDEX_MULT_ADD               : thm := BIndex.INDEX_MULT_ADD
unsafe def INDEX_NSUM_LE                : thm := BIndex.INDEX_NSUM_LE
unsafe def DIVIDES_INDEX                : thm := BIndex.DIVIDES_INDEX
unsafe def EQ_INDEX                     : thm := BIndex.EQ_INDEX
unsafe def COPRIME_INDEX                : thm := BIndex.COPRIME_INDEX
unsafe def INDEX_GCD                    : thm := BIndex.INDEX_GCD
unsafe def FORALL_PRIME_INDEX           : thm := BIndex.FORALL_PRIME_INDEX
unsafe def INDEX_FACT_PRIME_MULT        : thm := BIndex.INDEX_FACT_PRIME_MULT
unsafe def PRIME_FACTORIZATION_INDEX    : thm := BIndex.PRIME_FACTORIZATION_INDEX
unsafe def PRIME_POWER_EXISTS           : thm := BIndex.PRIME_POWER_EXISTS
unsafe def PRIME_POWER_EXISTS_ALT       : thm := BIndex.PRIME_POWER_EXISTS_ALT
unsafe def PRIME_FACTORIZATION_ALT      : thm := BIndex.PRIME_FACTORIZATION_ALT
unsafe def PRIME_FACTORIZATION          : thm := BIndex.PRIME_FACTORIZATION

-- Lcm
unsafe def lcm                          : thm := BLcm.lcm
unsafe def LCM_DIVIDES                  : thm := BLcm.LCM_DIVIDES
unsafe def LCM                          : thm := BLcm.LCM
unsafe def LCM_DIVIDES_MUL              : thm := BLcm.LCM_DIVIDES_MUL
unsafe def DIVIDES_LCM                  : thm := BLcm.DIVIDES_LCM
unsafe def LCM_0                        : thm := BLcm.LCM_0
unsafe def LCM_1                        : thm := BLcm.LCM_1
unsafe def LCM_SYM                      : thm := BLcm.LCM_SYM
unsafe def DIVIDES_LCM_GCD              : thm := BLcm.DIVIDES_LCM_GCD
unsafe def PRIMEPOW_DIVIDES_LCM         : thm := BLcm.PRIMEPOW_DIVIDES_LCM
unsafe def PRIME_DIVIDES_LCM            : thm := BLcm.PRIME_DIVIDES_LCM
unsafe def LCM_ZERO                     : thm := BLcm.LCM_ZERO
unsafe def INDEX_LCM                    : thm := BLcm.INDEX_LCM
unsafe def LCM_ASSOC                    : thm := BLcm.LCM_ASSOC
unsafe def LCM_REFL                     : thm := BLcm.LCM_REFL
unsafe def LCM_MULTIPLE                 : thm := BLcm.LCM_MULTIPLE
unsafe def LCM_GCD_DISTRIB              : thm := BLcm.LCM_GCD_DISTRIB
unsafe def GCD_LCM_DISTRIB              : thm := BLcm.GCD_LCM_DISTRIB
unsafe def LCM_UNIQUE                   : thm := BLcm.LCM_UNIQUE
unsafe def LCM_EQ                       : thm := BLcm.LCM_EQ
unsafe def LCM_EQ_1                     : thm := BLcm.LCM_EQ_1
unsafe def DIVIDES_LCM_LEFT             : thm := BLcm.DIVIDES_LCM_LEFT
unsafe def DIVIDES_LCM_RIGHT            : thm := BLcm.DIVIDES_LCM_RIGHT
unsafe def MULT_LCM_GCD                 : thm := BLcm.MULT_LCM_GCD
unsafe def MULT_GCD_LCM                 : thm := BLcm.MULT_GCD_LCM
unsafe def LCM_LMUL                     : thm := BLcm.LCM_LMUL
unsafe def LCM_RMUL                     : thm := BLcm.LCM_RMUL
unsafe def LCM_EXP                      : thm := BLcm.LCM_EXP
unsafe def LCM_COPRIME_DECOMP           : thm := BLcm.LCM_COPRIME_DECOMP
unsafe def LE_LCM                       : thm := BLcm.LE_LCM
unsafe def LCM_LE_MULT                  : thm := BLcm.LCM_LE_MULT
unsafe def LCM_EQ_MULT                  : thm := BLcm.LCM_EQ_MULT
unsafe def MAX_LE_LCM_EQ                : thm := BLcm.MAX_LE_LCM_EQ
unsafe def MAX_LE_LCM                   : thm := BLcm.MAX_LE_LCM

-- Iterated
unsafe def NEUTRAL_GCD                  : thm := BIterated.NEUTRAL_GCD
unsafe def MONOIDAL_GCD                 : thm := BIterated.MONOIDAL_GCD
unsafe def NEUTRAL_LCM                  : thm := BIterated.NEUTRAL_LCM
unsafe def MONOIDAL_LCM                 : thm := BIterated.MONOIDAL_LCM
unsafe def ITERATE_GCD_DIVIDES          : thm := BIterated.ITERATE_GCD_DIVIDES
unsafe def ITERATE_GCD_DIVIDES_EQ       : thm := BIterated.ITERATE_GCD_DIVIDES_EQ
unsafe def DIVIDES_ITERATE_GCD          : thm := BIterated.DIVIDES_ITERATE_GCD
unsafe def DIVIDES_ITERATE_GCD_GEN      : thm := BIterated.DIVIDES_ITERATE_GCD_GEN
unsafe def DIVIDES_ITERATE_LCM          : thm := BIterated.DIVIDES_ITERATE_LCM
unsafe def DIVIDES_ITERATE_LCM_GEN      : thm := BIterated.DIVIDES_ITERATE_LCM_GEN
unsafe def ITERATE_LCM_DIVIDES          : thm := BIterated.ITERATE_LCM_DIVIDES
unsafe def ITERATE_LCM_DIVIDES_GEN      : thm := BIterated.ITERATE_LCM_DIVIDES_GEN
unsafe def PRIMEPOW_DIVIDES_ITERATE_LCM : thm := BIterated.PRIMEPOW_DIVIDES_ITERATE_LCM
unsafe def PRIMEPOW_DIVIDES_ITERATE_LCM_GEN : thm := BIterated.PRIMEPOW_DIVIDES_ITERATE_LCM_GEN
unsafe def PRIME_DIVIDES_ITERATE_LCM_GEN : thm := BIterated.PRIME_DIVIDES_ITERATE_LCM_GEN
unsafe def PRIME_DIVIDES_ITERATE_LCM    : thm := BIterated.PRIME_DIVIDES_ITERATE_LCM
unsafe def ITERATE_LCM_EQ_0_GEN         : thm := BIterated.ITERATE_LCM_EQ_0_GEN
unsafe def ITERATE_LCM_EQ_0             : thm := BIterated.ITERATE_LCM_EQ_0
unsafe def ITERATE_LCM_EQ_1_GEN         : thm := BIterated.ITERATE_LCM_EQ_1_GEN
unsafe def ITERATE_LCM_EQ_1             : thm := BIterated.ITERATE_LCM_EQ_1
unsafe def ITERATE_GCD_EQ_0_GEN         : thm := BIterated.ITERATE_GCD_EQ_0_GEN
unsafe def ITERATE_GCD_EQ_0             : thm := BIterated.ITERATE_GCD_EQ_0

-- Induct
unsafe def INDUCT_COPRIME               : thm := BInduct.INDUCT_COPRIME
unsafe def INDUCT_COPRIME_STRONG        : thm := BInduct.INDUCT_COPRIME_STRONG
unsafe def INDUCT_COPRIME_ALT           : thm := BInduct.INDUCT_COPRIME_ALT

/- The conversions (prime.ml 2358-2472). -/
/-- `DIVIDES_CONV` (prime.ml 2361). -/
unsafe def DIVIDES_CONV : HolCore.Equal.ioconv := fun tm => HolLibrary.Prime.DIVIDES_CONV (deps ()) BConvs tm
/-- `COPRIME_CONV` (prime.ml 2381). -/
unsafe def COPRIME_CONV : HolCore.Equal.ioconv := fun tm => HolLibrary.Prime.COPRIME_CONV (deps ()) BConvs tm
/-- `GCD_CONV` (prime.ml 2429). -/
unsafe def GCD_CONV : HolCore.Equal.ioconv := fun tm => HolLibrary.Prime.GCD_CONV (deps ()) BConvs tm
/-- `LCM_CONV` (prime.ml 2467), built once. -/
initialize theLcmConv : IO.Ref (Option HolCore.Equal.ioconv) ← IO.mkRef none
private unsafe def BLcmConv : HolCore.Equal.ioconv :=
  cached theLcmConv "LCM_CONV" fun _ => (HolLibrary.Prime.LCM_CONV (deps ()) BConvs BLcm.lcm).run
unsafe def LCM_CONV : HolCore.Equal.ioconv := fun tm => BLcmConv tm

/-- `needs "Library/prime.ml"`: build every bundle, in file order. -/
unsafe def ensurePrime : IO Unit := do
  let _ ← IO.mkRef (concl BDivides.DIVIDES_0)
  let _ ← IO.mkRef (concl BGcd.DIVIDES_GCD)
  let _ ← IO.mkRef (concl BCoprime.COPRIME)
  let _ ← IO.mkRef (concl BPrimes.PRIME_0)
  let _ ← IO.mkRef (concl BChinese.CHINESE_REMAINDER)
  let _ ← IO.mkRef (concl BIndex.FINITE_EXP_LE)
  let _ ← IO.mkRef (concl BLcm.lcm)
  let _ ← IO.mkRef (concl BIterated.NEUTRAL_GCD)
  let _ ← IO.mkRef (concl BInduct.INDUCT_COPRIME)
  let _ ← IO.mkRef (concl BConvs.divides_pth_0)
  pure ()

end SessionLibrary.Prime
