/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/multiplicative.ml.                    -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Multiplicative.lean

  The `unsafe` half of the multiplicative.ml translation: it supplies HolLibrary.Multiplicative's
  dependencies from Session and SessionLibrary.Products, SessionLibrary.Iter, SessionLibrary.Prime, SessionLibrary.Pocklington, builds the bundles once, in order,
  and exports every name under its HOL Light name.  `ensureMultiplicative` is
  `needs "Library/multiplicative.ml"` (which first does `needs "Library/products.ml"`, `needs "Library/iter.ml"`, `needs "Library/prime.ml"`, `needs "Library/pocklington.ml"`).

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Multiplicative.lean by tools/multiplicativediff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.Multiplicative
import SessionLibrary.Products
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Multiplicative

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems multiplicative.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.Multiplicative.CoreThms1 where
  ARITH_EQ := Session.ARITH_EQ
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_SING := Session.CARD_SING
  CARD_UNION_EQ := Session.CARD_UNION_EQ
  COND_SWAP := Session.COND_SWAP
  COPRIME_0 := SessionLibrary.Prime.«COPRIME_0»
  COPRIME_DIVISORS := SessionLibrary.Prime.«COPRIME_DIVISORS»
  COPRIME_DIVPROD := SessionLibrary.Prime.«COPRIME_DIVPROD»
  COPRIME_PRIME := SessionLibrary.Prime.«COPRIME_PRIME»
  COPRIME_PRIME_EQ := SessionLibrary.Prime.«COPRIME_PRIME_EQ»
  COPRIME_SYM := SessionLibrary.Prime.«COPRIME_SYM»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DISJOINT := Session.DISJOINT
  DIVIDES_ANTISYM := Session.DIVIDES_ANTISYM
  DIVIDES_DIVIDES_DIV := Session.DIVIDES_DIVIDES_DIV
  DIVIDES_DIV_MULT := Session.DIVIDES_DIV_MULT
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_MUL2 := SessionLibrary.Prime.«DIVIDES_MUL2»
  DIVIDES_ONE := Session.DIVIDES_ONE
  DIVIDES_PRIMEPOW := SessionLibrary.Prime.«DIVIDES_PRIMEPOW»
  DIVIDES_PRIME_PRIME := SessionLibrary.Prime.«DIVIDES_PRIME_PRIME»
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  DIVIDES_RMUL := SessionLibrary.Prime.«DIVIDES_RMUL»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  DIVISION_DECOMP := SessionLibrary.Prime.«DIVISION_DECOMP»
  DIV_1 := Session.DIV_1
  DIV_EQ_0 := Session.DIV_EQ_0
  DIV_MULT := Session.DIV_MULT
  DIV_REFL := Session.DIV_REFL
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EQ_ADD_LCANCEL_0 := Session.EQ_ADD_LCANCEL_0
  EQ_ADD_RCANCEL_0 := Session.EQ_ADD_RCANCEL_0
  EQ_PRIMEPOW := SessionLibrary.Prime.«EQ_PRIMEPOW»
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EXISTS_PAIR_THM := Session.EXISTS_PAIR_THM
  EXISTS_UNIQUE_DEF := Session.EXISTS_UNIQUE_DEF
  EXP := Session.EXP
  EXP_1 := Session.EXP_1
  EXP_ONE := Session.EXP_ONE
  EXTENSION := Session.EXTENSION
  FINITE_DIVISORS := SessionLibrary.Prime.«FINITE_DIVISORS»
  FINITE_NUMSEG_LE := Session.FINITE_NUMSEG_LE
  FINITE_RULES := Session.FINITE_RULES
  FINITE_SPECIAL_DIVISORS := SessionLibrary.Prime.«FINITE_SPECIAL_DIVISORS»
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  GCD_1 := SessionLibrary.Prime.«GCD_1»
  GCD_SYM := SessionLibrary.Prime.«GCD_SYM»
  IMP_IMP := Session.IMP_IMP
  INDEX_EQ_0 := SessionLibrary.Prime.«INDEX_EQ_0»
  INDEX_EXP := SessionLibrary.Prime.«INDEX_EXP»
  INDEX_MUL := SessionLibrary.Prime.«INDEX_MUL»
  INDEX_REFL := SessionLibrary.Prime.«INDEX_REFL»
  INDUCT_COPRIME_STRONG := SessionLibrary.Prime.«INDUCT_COPRIME_STRONG»
  IN_ELIM_PAIR_THM := Session.IN_ELIM_PAIR_THM
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_INSERT := Session.IN_INSERT
  IN_INTER := Session.IN_INTER
  IN_SING := Session.IN_SING
  LE := Session.LE
  LE_0 := Session.LE_0
  LE_1 := Session.LE_1
  LE_EXP := Session.LE_EXP
  MONO_FORALL := Session.MONO_FORALL
  MULT_AC := Session.MULT_AC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_EQ_1 := Session.MULT_EQ_1
  MULT_EXP := Session.MULT_EXP
  MULT_SYM := Session.MULT_SYM
/-- The core theorems multiplicative.ml uses. -/
unsafe def core2 (_ : Unit) : HolLibrary.Multiplicative.CoreThms2 where
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LT := Session.NOT_LT
  NOT_SUC := Session.NOT_SUC
  NPRODUCT_CLAUSES := Session.NPRODUCT_CLAUSES
  NPRODUCT_EQ := SessionLibrary.Products.«NPRODUCT_EQ»
  NPRODUCT_SING := SessionLibrary.Products.«NPRODUCT_SING»
  NPRODUCT_UNION := SessionLibrary.Products.«NPRODUCT_UNION»
  NSUM_CLAUSES := Session.NSUM_CLAUSES
  NSUM_CONST := Session.NSUM_CONST
  NSUM_EQ_GENERAL := Session.NSUM_EQ_GENERAL
  NSUM_IMAGE := Session.NSUM_IMAGE
  NSUM_LMUL := Session.NSUM_LMUL
  NSUM_NSUM_PRODUCT := Session.NSUM_NSUM_PRODUCT
  NSUM_SING := Session.NSUM_SING
  PAIR_EQ := Session.PAIR_EQ
  PHI_0 := SessionLibrary.Pocklington.«PHI_0»
  PHI_1 := SessionLibrary.Pocklington.«PHI_1»
  PHI_MULTIPLICATIVE := SessionLibrary.Pocklington.«PHI_MULTIPLICATIVE»
  PHI_PRIMEPOW := SessionLibrary.Pocklington.«PHI_PRIMEPOW»
  PHI_PRIMEPOW_ALT := SessionLibrary.Pocklington.«PHI_PRIMEPOW_ALT»
  PRIME_0 := SessionLibrary.Prime.«PRIME_0»
  PRIME_1 := SessionLibrary.Prime.«PRIME_1»
  PRIME_DIVEXP_EQ := SessionLibrary.Prime.«PRIME_DIVEXP_EQ»
  PRIME_DIVPROD_EQ := SessionLibrary.Prime.«PRIME_DIVPROD_EQ»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_IMP_SQUAREFREE := SessionLibrary.Pocklington.«PRIME_IMP_SQUAREFREE»
  REAL_ABS_NEG := Session.REAL_ABS_NEG
  REAL_ABS_NUM := Session.REAL_ABS_NUM
  REAL_ABS_POW := Session.REAL_ABS_POW
  REAL_ADD_RID := Session.REAL_ADD_RID
  REAL_ADD_RINV := Session.REAL_ADD_RINV
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_LZERO := Session.REAL_MUL_LZERO
  REAL_MUL_RID := Session.REAL_MUL_RID
  REAL_MUL_RZERO := Session.REAL_MUL_RZERO
  REAL_MUL_SYM := Session.REAL_MUL_SYM
  REAL_POW_ADD := Session.REAL_POW_ADD
  REAL_POW_ONE := Session.REAL_POW_ONE
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  SING_GSPEC := Session.SING_GSPEC
  SQUAREFREE_0 := SessionLibrary.Pocklington.«SQUAREFREE_0»
  SQUAREFREE_1 := SessionLibrary.Pocklington.«SQUAREFREE_1»
  SQUAREFREE_EXP := SessionLibrary.Pocklington.«SQUAREFREE_EXP»
  SQUAREFREE_MUL := SessionLibrary.Pocklington.«SQUAREFREE_MUL»
  SQUAREFREE_PRIME := SessionLibrary.Pocklington.«SQUAREFREE_PRIME»
  SUBSET := Session.SUBSET
  SUC_SUB1 := Session.SUC_SUB1
  SUM_CLAUSES := Session.SUM_CLAUSES
  SUM_EQ_GENERAL := Session.SUM_EQ_GENERAL
  SUM_EQ_GENERAL_INVERSES := Session.SUM_EQ_GENERAL_INVERSES
  SUM_LMUL := Session.SUM_LMUL
  SUM_SING := Session.SUM_SING
  SUM_SUM_PRODUCT := Session.SUM_SUM_PRODUCT
  SUM_SUPERSET := Session.SUM_SUPERSET
  divides := Session.divides
  num_WF := Session.num_WF
  o_DEF := Session.o_DEF
  real_pow := Session.real_pow
/-- The core theorems multiplicative.ml uses. -/
unsafe def core3 (_ : Unit) : HolLibrary.Multiplicative.CoreThms3 where
/-- The core theorems multiplicative.ml uses. -/
unsafe def core4 (_ : Unit) : HolLibrary.Multiplicative.CoreThms4 where
-- @@CORE END

/-- What multiplicative.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Multiplicative.MultiplicativeDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  prioritize_real := Session.prioritize_real
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  NUMBER_RULE t := ExceptT.mk (Session.NUMBER_RULE t)
  NUMBER_TAC := Session.NUMBER_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC2
  INDUCT_TAC := Session.INDUCT_TAC
  GEN_BETA_CONV := Session.GEN_BETA_CONV
  REAL_RAT_REDUCE_CONV := Session.REAL_RAT_REDUCE_CONV
  core1 := core1 ()
  core2 := core2 ()
  core3 := core3 ()
  core4 := core4 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`, and MATCH_CONV's basic conversions, which HOL
    Light adds loading ind_types.ml), then products.ml, iter.ml, prime.ml, pocklington.ml, which multiplicative.ml needs. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      SessionLibrary.Products.ensureProducts
      SessionLibrary.Iter.ensureIter
      SessionLibrary.Prime.ensurePrime
      SessionLibrary.Pocklington.ensurePocklington
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.Multiplicative: {name}"

/- The bundles, in file order; each forces the one before it. -/

-- @@BUNDLES BEGIN
initialize theBasics : IO.Ref (Option HolLibrary.Multiplicative.Basics) ← IO.mkRef none
unsafe def BBasics : HolLibrary.Multiplicative.Basics :=
  cached theBasics "setupBasics" fun _ => do
    (HolLibrary.Multiplicative.setupBasics (deps ())).run

initialize theParticular : IO.Ref (Option HolLibrary.Multiplicative.Particular) ← IO.mkRef none
unsafe def BParticular : HolLibrary.Multiplicative.Particular :=
  cached theParticular "setupParticular" fun _ => do
    let _ ← IO.mkRef BBasics.multiplicative
    (HolLibrary.Multiplicative.setupParticular (deps ()) BBasics).run

initialize theReal : IO.Ref (Option HolLibrary.Multiplicative.Real) ← IO.mkRef none
unsafe def BReal : HolLibrary.Multiplicative.Real :=
  cached theReal "setupReal" fun _ => do
    let _ ← IO.mkRef BParticular.MULTIPLICATIVE_ID
    (HolLibrary.Multiplicative.setupReal (deps ())).run

initialize theMobius : IO.Ref (Option HolLibrary.Multiplicative.Mobius) ← IO.mkRef none
unsafe def BMobius : HolLibrary.Multiplicative.Mobius :=
  cached theMobius "setupMobius" fun _ => do
    let _ ← IO.mkRef BReal.real_multiplicative
    (HolLibrary.Multiplicative.setupMobius (deps ()) BReal).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Basics
unsafe def multiplicative : thm := BBasics.multiplicative
unsafe def MULTIPLICATIVE_1 : thm := BBasics.MULTIPLICATIVE_1
unsafe def MULTIPLICATIVE : thm := BBasics.MULTIPLICATIVE
unsafe def MULTIPLICATIVE_IGNOREZERO : thm := BBasics.MULTIPLICATIVE_IGNOREZERO
unsafe def MULTIPLICATIVE_EXPAND : thm := BBasics.MULTIPLICATIVE_EXPAND
unsafe def MULTIPLICATIVE_CONVOLUTION : thm := BBasics.MULTIPLICATIVE_CONVOLUTION
unsafe def MULTIPLICATIVE_CONST : thm := BBasics.MULTIPLICATIVE_CONST
unsafe def MULTIPLICATIVE_DELTA : thm := BBasics.MULTIPLICATIVE_DELTA
unsafe def MULTIPLICATIVE_DIVISORSUM : thm := BBasics.MULTIPLICATIVE_DIVISORSUM

-- Particular
unsafe def MULTIPLICATIVE_ID : thm := BParticular.MULTIPLICATIVE_ID
unsafe def MULTIPLICATIVE_POWERSUM : thm := BParticular.MULTIPLICATIVE_POWERSUM
unsafe def sigma : thm := BParticular.sigma
unsafe def tau : thm := BParticular.tau
unsafe def MULTIPLICATIVE_SIGMA : thm := BParticular.MULTIPLICATIVE_SIGMA
unsafe def MULTIPLICATIVE_TAU : thm := BParticular.MULTIPLICATIVE_TAU
unsafe def MULTIPLICATIVE_PHI : thm := BParticular.MULTIPLICATIVE_PHI
unsafe def MULTIPLICATIVE_GCD : thm := BParticular.MULTIPLICATIVE_GCD
unsafe def PHI_EXPAND : thm := BParticular.PHI_EXPAND
unsafe def MULTIPLICATIVE_UNIQUE : thm := BParticular.MULTIPLICATIVE_UNIQUE
unsafe def PHI_DIVISORSUM : thm := BParticular.PHI_DIVISORSUM

-- Real
unsafe def real_multiplicative : thm := BReal.real_multiplicative
unsafe def REAL_MULTIPLICATIVE : thm := BReal.REAL_MULTIPLICATIVE
unsafe def REAL_MULTIPLICATIVE_CONST : thm := BReal.REAL_MULTIPLICATIVE_CONST
unsafe def REAL_MULTIPLICATIVE_DELTA : thm := BReal.REAL_MULTIPLICATIVE_DELTA
unsafe def REAL_MULTIPLICATIVE_IGNOREZERO : thm := BReal.REAL_MULTIPLICATIVE_IGNOREZERO
unsafe def REAL_MULTIPLICATIVE_CONVOLUTION : thm := BReal.REAL_MULTIPLICATIVE_CONVOLUTION
unsafe def REAL_MULTIPLICATIVE_DIVISORSUM : thm := BReal.REAL_MULTIPLICATIVE_DIVISORSUM

-- Mobius
unsafe def mobius : thm := BMobius.mobius
unsafe def MOBIUS_ALT : thm := BMobius.MOBIUS_ALT
unsafe def MOBIUS_0 : thm := BMobius.MOBIUS_0
unsafe def MOBIUS_1 : thm := BMobius.MOBIUS_1
unsafe def REAL_ABS_MOBIUS : thm := BMobius.REAL_ABS_MOBIUS
unsafe def MOBIUS_MULT : thm := BMobius.MOBIUS_MULT
unsafe def REAL_MULTIPLICATIVE_MOBIUS : thm := BMobius.REAL_MULTIPLICATIVE_MOBIUS
unsafe def MOBIUS_PRIME : thm := BMobius.MOBIUS_PRIME
unsafe def MOBIUS_PRIMEPOW : thm := BMobius.MOBIUS_PRIMEPOW
unsafe def DIVISORSUM_MOBIUS : thm := BMobius.DIVISORSUM_MOBIUS
unsafe def MOBIUS_INVERSION : thm := BMobius.MOBIUS_INVERSION
-- @@EXPORTS END

/-- `needs "Library/multiplicative.ml"`: build the bundles, in order. -/
unsafe def ensureMultiplicative : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BBasics.multiplicative
  let _ ← IO.mkRef BParticular.MULTIPLICATIVE_ID
  let _ ← IO.mkRef BReal.real_multiplicative
  let _ ← IO.mkRef BMobius.mobius  -- @@ENSURE END
  pure ()

end SessionLibrary.Multiplicative
