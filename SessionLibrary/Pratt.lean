/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/pratt.ml.                             -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Pratt.lean

  The `unsafe` half of the pratt.ml translation: it supplies HolLibrary.Pratt's
  dependencies from Session and SessionLibrary.Prime, builds the bundles once, in order,
  and exports every name under its HOL Light name.  `ensurePratt` is
  `needs "Library/pratt.ml"` (which first does `needs "Library/prime.ml"`).

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Pratt.lean by tools/prattdiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.Pratt
import SessionLibrary.Prime

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Pratt

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems pratt.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.Pratt.CoreThms1 where
  ADD_AC := Session.ADD_AC
  ADD_ASSOC := Session.ADD_ASSOC
  ADD_CLAUSES := Session.ADD_CLAUSES
  ALL := Session.listDefs.ALL
  ALL_IMP := Session.listThms1.ALL_IMP
  ARITH := Session.ARITH
  BEZOUT := SessionLibrary.Prime.«BEZOUT»
  BIT0 := Session.BIT0
  BIT1 := Session.BIT1
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_NUMSEG_LE := Session.CARD_NUMSEG_LE
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CARD_SUBSET := Session.CARD_SUBSET
  CARD_SUBSET_EQ := Session.CARD_SUBSET_EQ
  CONG := Session.CONG
  CONJ_ASSOC := Session.CONJ_ASSOC
  COPRIME_0 := SessionLibrary.Prime.«COPRIME_0»
  COPRIME_1 := SessionLibrary.Prime.«COPRIME_1»
  COPRIME_DIVPROD := SessionLibrary.Prime.«COPRIME_DIVPROD»
  COPRIME_EXP := SessionLibrary.Prime.«COPRIME_EXP»
  COPRIME_LMOD := Session.COPRIME_LMOD
  COPRIME_MUL := SessionLibrary.Prime.«COPRIME_MUL»
  COPRIME_REFL := SessionLibrary.Prime.«COPRIME_REFL»
  COPRIME_SYM := SessionLibrary.Prime.«COPRIME_SYM»
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIVIDES_ADD := SessionLibrary.Prime.«DIVIDES_ADD»
  DIVIDES_ADD_REVR := SessionLibrary.Prime.«DIVIDES_ADD_REVR»
  DIVIDES_EXP := SessionLibrary.Prime.«DIVIDES_EXP»
  DIVIDES_EXP2 := SessionLibrary.Prime.«DIVIDES_EXP2»
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_LMUL := SessionLibrary.Prime.«DIVIDES_LMUL»
  DIVIDES_ONE := Session.DIVIDES_ONE
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  DIVIDES_RMUL := SessionLibrary.Prime.«DIVIDES_RMUL»
  DIVIDES_SUB := SessionLibrary.Prime.«DIVIDES_SUB»
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  DIVISION := Session.DIVISION
  DIV_MULT := Session.DIV_MULT
  DIV_UNIQ := Session.DIV_UNIQ
  EQ_TRANS := Session.EQ_TRANS
  EXP := Session.EXP
  EXP_ADD := Session.EXP_ADD
  EXP_EQ_1 := Session.EXP_EQ_1
  EXP_EXP := Session.EXP_EXP
  EXP_ONE := Session.EXP_ONE
  EXTENSION := Session.EXTENSION
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_NUMSEG_LE := Session.FINITE_NUMSEG_LE
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_RECURSION := Session.FINITE_RECURSION
  FINITE_RULES := Session.FINITE_RULES
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_AND_THM := Session.FORALL_AND_THM
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_0 := Session.HAS_SIZE_0
  IMAGE := Session.IMAGE
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMP_CONJ := Session.IMP_CONJ
  IMP_IMP := Session.IMP_IMP
  INT_OF_NUM_SUB := Session.INT_OF_NUM_SUB
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_SING := Session.IN_SING
  ITLIST := Session.listDefs.ITLIST
  LEFT_ADD_DISTRIB := Session.LEFT_ADD_DISTRIB
  LEFT_SUB_DISTRIB := Session.LEFT_SUB_DISTRIB
  LE_0 := Session.LE_0
  LE_ANTISYM := Session.LE_ANTISYM
/-- The core theorems pratt.ml uses. -/
unsafe def core2 (_ : Unit) : HolLibrary.Pratt.CoreThms2 where
  LE_CASES := Session.LE_CASES
  LE_LT := Session.LE_LT
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_TRANS := Session.LE_TRANS
  LT := Session.LT
  LT_IMP_LE := Session.LT_IMP_LE
  LT_LE := Session.LT_LE
  LT_MULT_RCANCEL := Session.LT_MULT_RCANCEL
  LT_NZ := Session.LT_NZ
  LT_REFL := Session.LT_REFL
  LT_TRANS := Session.LT_TRANS
  MEM := Session.listDefs.MEM
  MOD_EQ_0 := Session.MOD_EQ_0
  MOD_EXP_MOD := Session.MOD_EXP_MOD
  MOD_LT := Session.MOD_LT
  MOD_MOD_REFL := Session.MOD_MOD_REFL
  MOD_MULT_LMOD := Session.MOD_MULT_LMOD
  MOD_MULT_RMOD := Session.MOD_MULT_RMOD
  MOD_UNIQ := Session.MOD_UNIQ
  MULT_AC := Session.MULT_AC
  MULT_ASSOC := Session.MULT_ASSOC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_SYM := Session.MULT_SYM
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LE := Session.NOT_LE
  NOT_LT := Session.NOT_LT
  NUMERAL := Session.NUMERAL
  PRIME_0 := SessionLibrary.Prime.«PRIME_0»
  PRIME_1 := SessionLibrary.Prime.«PRIME_1»
  PRIME_2 := SessionLibrary.Prime.«PRIME_2»
  PRIME_COPRIME := SessionLibrary.Prime.«PRIME_COPRIME»
  PRIME_DIVPROD := SessionLibrary.Prime.«PRIME_DIVPROD»
  PRIME_FACTOR := SessionLibrary.Prime.«PRIME_FACTOR»
  RIGHT_ADD_DISTRIB := Session.RIGHT_ADD_DISTRIB
  RIGHT_SUB_DISTRIB := Session.RIGHT_SUB_DISTRIB
  SUBSET := Session.SUBSET
  SUB_EQ_0 := Session.SUB_EQ_0
  SWAP_EXISTS_THM := Session.SWAP_EXISTS_THM
  cong := Session.cong
  coprime := Session.coprime
  divides := Session.divides
  num_WF := Session.num_WF
  num_WOP := Session.num_WOP
  num_congruent := Session.num_congruent
  num_divides := Session.num_divides
  prime := Session.prime
/-- The core theorems pratt.ml uses. -/
unsafe def core3 (_ : Unit) : HolLibrary.Pratt.CoreThms3 where
/-- The core theorems pratt.ml uses. -/
unsafe def core4 (_ : Unit) : HolLibrary.Pratt.CoreThms4 where
-- @@CORE END

/-- What pratt.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Pratt.PrattDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  prioritize_num := do
    match ← HolCore.Kernel.mk_type "num" [] with
    | .ok ty => Session.prioritize_overload ty
    | .error e => throw (IO.userError e)
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  NUMBER_RULE t := ExceptT.mk (Session.NUMBER_RULE t)
  NUMBER_TAC := Session.NUMBER_TAC
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  LIST_INDUCT_TAC := Session.LIST_INDUCT_TAC
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  let_CONV := Session.let_CONV
  NUM_EQ_CONV := Session.NUM_EQ_CONV
  NUM_LE_CONV := Session.NUM_LE_CONV
  NUM_SUB_CONV := Session.NUM_SUB_CONV
  NUM_MULT_CONV := Session.NUM_MULT_CONV
  NUM_DIV_CONV := Session.NUM_DIV_CONV
  mk_numeral := Session.mk_numeral
  mk_small_numeral := Session.mk_small_numeral
  mk_flist := Session.mk_flist
  core1 := core1 ()
  core2 := core2 ()
  core3 := core3 ()
  core4 := core4 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`, and MATCH_CONV's basic conversions, which HOL
    Light adds loading ind_types.ml), then prime.ml, which pratt.ml needs. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      SessionLibrary.Prime.ensurePrime
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.Pratt: {name}"

/- The bundles, in file order; each forces the one before it. -/

-- @@BUNDLES BEGIN
initialize theCompat : IO.Ref (Option HolLibrary.Pratt.Compat) ← IO.mkRef none
unsafe def BCompat : HolLibrary.Pratt.Compat :=
  cached theCompat "setupCompat" fun _ => do
    (HolLibrary.Pratt.setupCompat (deps ())).run

initialize theCong : IO.Ref (Option HolLibrary.Pratt.Cong) ← IO.mkRef none
unsafe def BCong : HolLibrary.Pratt.Cong :=
  cached theCong "setupCong" fun _ => do
    let _ ← IO.mkRef BCompat.nat_mod_lemma
    (HolLibrary.Pratt.setupCong (deps ()) BCompat).run

initialize thePhi : IO.Ref (Option HolLibrary.Pratt.Phi) ← IO.mkRef none
unsafe def BPhi : HolLibrary.Pratt.Phi :=
  cached thePhi "setupPhi" fun _ => do
    let _ ← IO.mkRef BCong.CONG_MOD_0
    (HolLibrary.Pratt.setupPhi (deps ()) BCompat).run

initialize theFermat : IO.Ref (Option HolLibrary.Pratt.Fermat) ← IO.mkRef none
unsafe def BFermat : HolLibrary.Pratt.Fermat :=
  cached theFermat "setupFermat" fun _ => do
    let _ ← IO.mkRef BPhi.phi
    (HolLibrary.Pratt.setupFermat (deps ()) BCompat BCong BPhi).run

initialize theLucas : IO.Ref (Option HolLibrary.Pratt.Lucas) ← IO.mkRef none
unsafe def BLucas : HolLibrary.Pratt.Lucas :=
  cached theLucas "setupLucas" fun _ => do
    let _ ← IO.mkRef BFermat.DIFFERENCE_POS_LEMMA
    (HolLibrary.Pratt.setupLucas (deps ()) BCong BPhi BFermat).run

initialize thePrimefact : IO.Ref (Option HolLibrary.Pratt.Primefact) ← IO.mkRef none
unsafe def BPrimefact : HolLibrary.Pratt.Primefact :=
  cached thePrimefact "setupPrimefact" fun _ => do
    let _ ← IO.mkRef BLucas.LUCAS_COPRIME_LEMMA
    (HolLibrary.Pratt.setupPrimefact (deps ()) BLucas).run

initialize theCertify : IO.Ref (Option HolLibrary.Pratt.Certify) ← IO.mkRef none
unsafe def BCertify : HolLibrary.Pratt.Certify :=
  cached theCertify "setupCertify" fun _ => do
    let _ ← IO.mkRef BPrimefact.primefact
    (HolLibrary.Pratt.setupCertify (deps ()) BPrimefact).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Compat
unsafe def nat_mod_lemma : thm := BCompat.nat_mod_lemma
unsafe def nat_mod : thm := BCompat.nat_mod
unsafe def PRIME : thm := BCompat.PRIME
unsafe def FINITE_NUMBER_SEGMENT : thm := BCompat.FINITE_NUMBER_SEGMENT

-- Cong
unsafe def CONG_MOD_0 : thm := BCong.CONG_MOD_0
unsafe def CONG_MOD_1 : thm := BCong.CONG_MOD_1
unsafe def CONG_0 : thm := BCong.CONG_0
unsafe def CONG_SUB_CASES : thm := BCong.CONG_SUB_CASES
unsafe def CONG_MULT_LCANCEL : thm := BCong.CONG_MULT_LCANCEL
unsafe def CONG_REFL : thm := BCong.CONG_REFL
unsafe def CONG_SYM : thm := BCong.CONG_SYM
unsafe def CONG_TRANS : thm := BCong.CONG_TRANS

-- Phi
unsafe def phi : thm := BPhi.phi
unsafe def PHI_ALT : thm := BPhi.PHI_ALT
unsafe def PHI_ANOTHER : thm := BPhi.PHI_ANOTHER
unsafe def PHI_LIMIT : thm := BPhi.PHI_LIMIT
unsafe def PHI_LIMIT_STRONG : thm := BPhi.PHI_LIMIT_STRONG
unsafe def PHI_0 : thm := BPhi.PHI_0
unsafe def PHI_1 : thm := BPhi.PHI_1
unsafe def PHI_LOWERBOUND_1_STRONG : thm := BPhi.PHI_LOWERBOUND_1_STRONG
unsafe def PHI_LOWERBOUND_1 : thm := BPhi.PHI_LOWERBOUND_1
unsafe def PHI_LOWERBOUND_2 : thm := BPhi.PHI_LOWERBOUND_2
unsafe def PHI_PRIME_EQ : thm := BPhi.PHI_PRIME_EQ
unsafe def PHI_PRIME : thm := BPhi.PHI_PRIME

-- Fermat
unsafe def DIFFERENCE_POS_LEMMA : thm := BFermat.DIFFERENCE_POS_LEMMA
unsafe def ITSET_MODMULT : thm := BFermat.ITSET_MODMULT
unsafe def ITSET_MODMULT_COPRIME : thm := BFermat.ITSET_MODMULT_COPRIME
unsafe def FERMAT_LITTLE : thm := BFermat.FERMAT_LITTLE
unsafe def FERMAT_LITTLE_PRIME : thm := BFermat.FERMAT_LITTLE_PRIME

-- Lucas
unsafe def LUCAS_COPRIME_LEMMA : thm := BLucas.LUCAS_COPRIME_LEMMA
unsafe def LUCAS_WEAK : thm := BLucas.LUCAS_WEAK
unsafe def LUCAS : thm := BLucas.LUCAS

-- Primefact
unsafe def primefact : thm := BPrimefact.primefact
unsafe def PRIMEFACT : thm := BPrimefact.PRIMEFACT
unsafe def PRIMAFACT_CONTAINS : thm := BPrimefact.PRIMAFACT_CONTAINS
unsafe def PRIMEFACT_VARIANT : thm := BPrimefact.PRIMEFACT_VARIANT
unsafe def LUCAS_PRIMEFACT : thm := BPrimefact.LUCAS_PRIMEFACT

-- Certify
unsafe def EXP_EQ_MOD_CONV : HolCore.Equal.ioconv := fun t => BCertify.EXP_EQ_MOD_CONV t
unsafe def prime_theorem_cache := BCertify.prime_theorem_cache
unsafe def check_certificate := BCertify.check_certificate
unsafe def PROVE_PRIME := BCertify.PROVE_PRIME
unsafe def PROVE_PRIMEFACT := BCertify.PROVE_PRIMEFACT
unsafe def PRIME_TEST : term → IO (Except String thm) := fun t => (BCertify.PRIME_TEST t).run
unsafe def PRIME_CONV : term → IO (Except String thm) := fun t => (BCertify.PRIME_CONV t).run
-- @@EXPORTS END

/-- `needs "Library/pratt.ml"`: build the bundles, in order. -/
unsafe def ensurePratt : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BCompat.nat_mod_lemma
  let _ ← IO.mkRef BCong.CONG_MOD_0
  let _ ← IO.mkRef BPhi.phi
  let _ ← IO.mkRef BFermat.DIFFERENCE_POS_LEMMA
  let _ ← IO.mkRef BLucas.LUCAS_COPRIME_LEMMA
  let _ ← IO.mkRef BPrimefact.primefact
  let _ ← IO.mkRef BCertify.EXP_EQ_MOD_CONV  -- @@ENSURE END
  pure ()

end SessionLibrary.Pratt
