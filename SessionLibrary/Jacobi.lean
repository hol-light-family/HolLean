/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/jacobi.ml.                            -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Jacobi.lean

  The `unsafe` half of the jacobi.ml translation: it supplies HolLibrary.Jacobi's
  dependencies from Session and SessionLibrary.Primitive, builds the bundles once, in order,
  and exports every name under its HOL Light name.  `ensureJacobi` is
  `needs "Library/jacobi.ml"` (which first does `needs "Library/primitive.ml"`).

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Jacobi.lean by tools/jacobidiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.Jacobi
import SessionLibrary.Primitive

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Jacobi

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems jacobi.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.Jacobi.CoreThms1 where
  ADD1 := Session.ADD1
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_SUB := Session.ADD_SUB
  ALL := Session.listDefs.ALL
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  BIJECTIONS_CARD_EQ := Session.BIJECTIONS_CARD_EQ
  CARD_CROSS := Session.CARD_CROSS
  CARD_IMAGE_INJ_EQ := Session.CARD_IMAGE_INJ_EQ
  CARD_NUMSEG := Session.CARD_NUMSEG
  CARD_NUMSEG_1 := Session.CARD_NUMSEG_1
  CARD_UNION := Session.CARD_UNION
  COMPLETE_FACTOR_INDUCT := SessionLibrary.Prime.«COMPLETE_FACTOR_INDUCT»
  COND_SWAP := Session.COND_SWAP
  CONG := Session.CONG
  CONG_ADD := SessionLibrary.Pocklington.«CONG_ADD»
  CONG_DIVIDES := SessionLibrary.Pocklington.«CONG_DIVIDES»
  CONG_IMP_EQ := SessionLibrary.Pocklington.«CONG_IMP_EQ»
  CONG_LMOD := Session.CONG_LMOD
  CONG_MOD_0 := SessionLibrary.Pocklington.«CONG_MOD_0»
  CONG_MOD_2 := SessionLibrary.Pocklington.«CONG_MOD_2»
  CONG_MOD_2_ALT := SessionLibrary.Pocklington.«CONG_MOD_2_ALT»
  CONG_MULT := SessionLibrary.Pocklington.«CONG_MULT»
  CONG_MULT_LCANCEL := SessionLibrary.Pocklington.«CONG_MULT_LCANCEL»
  CONG_REFL := SessionLibrary.Pocklington.«CONG_REFL»
  CONG_SQUARE_1_PRIME_POWER := SessionLibrary.Pocklington.«CONG_SQUARE_1_PRIME_POWER»
  CONG_SUB := SessionLibrary.Pocklington.«CONG_SUB»
  CONG_SYM := SessionLibrary.Pocklington.«CONG_SYM»
  CONG_TRANS := SessionLibrary.Pocklington.«CONG_TRANS»
  CONJ_ASSOC := Session.CONJ_ASSOC
  COPRIME_0 := SessionLibrary.Prime.«COPRIME_0»
  COPRIME_1 := SessionLibrary.Prime.«COPRIME_1»
  COPRIME_2 := SessionLibrary.Prime.«COPRIME_2»
  COPRIME_LMUL := SessionLibrary.Prime.«COPRIME_LMUL»
  COPRIME_PRIME_EQ := SessionLibrary.Prime.«COPRIME_PRIME_EQ»
  COPRIME_RMUL := SessionLibrary.Prime.«COPRIME_RMUL»
  COPRIME_SYM := SessionLibrary.Prime.«COPRIME_SYM»
  DISJOINT := Session.DISJOINT
  DIVIDES_0 := SessionLibrary.Prime.«DIVIDES_0»
  DIVIDES_2 := SessionLibrary.Prime.«DIVIDES_2»
  DIVIDES_ADD := SessionLibrary.Prime.«DIVIDES_ADD»
  DIVIDES_DIVIDES_DIV := Session.DIVIDES_DIVIDES_DIV
  DIVIDES_DIV_MULT := Session.DIVIDES_DIV_MULT
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_LMUL := SessionLibrary.Prime.«DIVIDES_LMUL»
  DIVIDES_LMUL2_EQ := SessionLibrary.Prime.«DIVIDES_LMUL2_EQ»
  DIVIDES_MOD := Session.DIVIDES_MOD
  DIVIDES_MUL2 := SessionLibrary.Prime.«DIVIDES_MUL2»
  DIVIDES_MUL_L := SessionLibrary.Prime.«DIVIDES_MUL_L»
  DIVIDES_ONE := Session.DIVIDES_ONE
  DIVIDES_PRIME_PRIME := SessionLibrary.Prime.«DIVIDES_PRIME_PRIME»
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  DIVIDES_RMUL := SessionLibrary.Prime.«DIVIDES_RMUL»
  DIVISION := Session.DIVISION
  DIV_ADD := Session.DIV_ADD
  DIV_MULT := Session.DIV_MULT
  DIV_MULT_ADD := Session.DIV_MULT_ADD
  EQ_IMP := Session.EQ_IMP
  EQ_TRANS := Session.EQ_TRANS
  EULER_CRITERION := SessionLibrary.Primitive.«EULER_CRITERION»
  EVEN_ADD := Session.EVEN_ADD
  EVEN_EXISTS := Session.EVEN_EXISTS
  EVEN_EXP := Session.EVEN_EXP
  EVEN_MULT := Session.EVEN_MULT
  EVEN_OR_ODD := Session.EVEN_OR_ODD
  EVEN_SUB := Session.EVEN_SUB
  EXISTS_IN_GSPEC := Session.EXISTS_IN_GSPEC
  EXISTS_PAIR_THM := Session.EXISTS_PAIR_THM
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXP := Session.EXP
/-- The core theorems jacobi.ml uses. -/
unsafe def core2 (_ : Unit) : HolLibrary.Jacobi.CoreThms2 where
  EXP_1 := Session.EXP_1
  EXP_2 := Session.EXP_2
  EXP_EXP := Session.EXP_EXP
  EXP_ONE := Session.EXP_ONE
  EXP_ZERO := Session.EXP_ZERO
  EXTENSION := Session.EXTENSION
  FERMAT_LITTLE_PRIME := SessionLibrary.Pocklington.«FERMAT_LITTLE_PRIME»
  FINITE_CROSS_EQ := Session.FINITE_CROSS_EQ
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SPECIAL_DIVISORS := SessionLibrary.Prime.«FINITE_SPECIAL_DIVISORS»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FUN_EQ_THM := Session.FUN_EQ_THM
  IMP_CONJ := Session.IMP_CONJ
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  IMP_IMP := Session.IMP_IMP
  INDEX_1 := SessionLibrary.Prime.«INDEX_1»
  INDEX_EQ_0 := SessionLibrary.Prime.«INDEX_EQ_0»
  INDEX_MUL := SessionLibrary.Prime.«INDEX_MUL»
  INDEX_REFL := SessionLibrary.Prime.«INDEX_REFL»
  INDEX_ZERO := SessionLibrary.Prime.«INDEX_ZERO»
  INFINITE := Session.INFINITE
  INT_ABS_ABS := Session.INT_ABS_ABS
  INT_ABS_MUL := Session.INT_ABS_MUL
  INT_ABS_NEG := Session.INT_ABS_NEG
  INT_ABS_NUM := Session.INT_ABS_NUM
  INT_ABS_POS := Session.INT_ABS_POS
  INT_ABS_POW := Session.INT_ABS_POW
  INT_ABS_ZERO := Session.INT_ABS_ZERO
  INT_CONG_IMP_EQ := SessionLibrary.Integer.«INT_CONG_IMP_EQ»
  INT_CONG_LREM := Session.INT_CONG_LREM
  INT_CONG_MOD_0 := SessionLibrary.Integer.«INT_CONG_MOD_0»
  INT_CONG_MOD_ABS := SessionLibrary.Integer.«INT_CONG_MOD_ABS»
  INT_CONG_POW := SessionLibrary.Integer.«INT_CONG_POW»
  INT_CONG_REFL := SessionLibrary.Integer.«INT_CONG_REFL»
  INT_CONG_RREM := Session.INT_CONG_RREM
  INT_CONG_TRANS := SessionLibrary.Integer.«INT_CONG_TRANS»
  INT_COPRIME_1 := SessionLibrary.Integer.«INT_COPRIME_1»
  INT_COPRIME_LREM := SessionLibrary.Integer.«INT_COPRIME_LREM»
  INT_COPRIME_RABS := SessionLibrary.Integer.«INT_COPRIME_RABS»
  INT_DIVIDES_RABS := Session.INT_DIVIDES_RABS
  INT_DIVIDES_REFL := SessionLibrary.Integer.«INT_DIVIDES_REFL»
  INT_DIVISION := Session.INT_DIVISION
  INT_ENTIRE := Session.INT_ENTIRE
  INT_FORALL_ABS := Session.INT_FORALL_ABS
  INT_FORALL_POS := Session.INT_FORALL_POS
  INT_LE_MUL := Session.INT_LE_MUL
  INT_LE_MUL2 := Session.INT_LE_MUL2
  INT_LE_REFL := Session.INT_LE_REFL
  INT_MUL_LID := Session.INT_MUL_LID
  INT_MUL_LNEG := Session.INT_MUL_LNEG
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_MUL_REM := Session.INT_MUL_REM
  INT_MUL_RNEG := Session.INT_MUL_RNEG
  INT_MUL_RZERO := Session.INT_MUL_RZERO
  INT_NEG_EQ_0 := Session.INT_NEG_EQ_0
  INT_NEG_MINUS1 := Session.INT_NEG_MINUS1
  INT_OF_NUM_ADD := Session.INT_OF_NUM_ADD
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LE := Session.INT_OF_NUM_LE
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_OF_INT := Session.INT_OF_NUM_OF_INT
  INT_OF_NUM_POW := Session.INT_OF_NUM_POW
  INT_OF_NUM_REM := Session.INT_OF_NUM_REM
  INT_OF_NUM_SUB := Session.INT_OF_NUM_SUB
  INT_POW := Session.INT_POW
/-- The core theorems jacobi.ml uses. -/
unsafe def core3 (_ : Unit) : HolLibrary.Jacobi.CoreThms3 where
  INT_POW_1 := Session.INT_POW_1
  INT_POW_1_LE := Session.INT_POW_1_LE
  INT_POW_ADD := Session.INT_POW_ADD
  INT_POW_EQ_0 := Session.INT_POW_EQ_0
  INT_POW_MUL := Session.INT_POW_MUL
  INT_POW_NEG := Session.INT_POW_NEG
  INT_POW_ONE := Session.INT_POW_ONE
  INT_POW_POW := Session.INT_POW_POW
  INT_POW_ZERO := Session.INT_POW_ZERO
  INT_REM_2_CASES := Session.INT_REM_2_CASES
  INT_REM_EQ := Session.INT_REM_EQ
  INT_REM_EQ_SELF := Session.INT_REM_EQ_SELF
  INT_REM_RABS := Session.INT_REM_RABS
  INT_REM_REM := Session.INT_REM_REM
  INT_REM_REM_MUL := Session.INT_REM_REM_MUL
  INT_REM_RNEG := Session.INT_REM_RNEG
  INT_REM_ZERO := Session.INT_REM_ZERO
  IN_CROSS := Session.IN_CROSS
  IN_ELIM_PAIR_THM := Session.IN_ELIM_PAIR_THM
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_INTER := Session.IN_INTER
  IN_NUMSEG := Session.IN_NUMSEG
  IN_UNION := Session.IN_UNION
  IPRODUCT_ABS := SessionLibrary.Products.«IPRODUCT_ABS»
  IPRODUCT_CLAUSES := Session.IPRODUCT_CLAUSES
  IPRODUCT_CLOSED := SessionLibrary.Products.«IPRODUCT_CLOSED»
  IPRODUCT_CONST := SessionLibrary.Products.«IPRODUCT_CONST»
  IPRODUCT_EQ := SessionLibrary.Products.«IPRODUCT_EQ»
  IPRODUCT_EQ_0 := SessionLibrary.Products.«IPRODUCT_EQ_0»
  IPRODUCT_EQ_1 := SessionLibrary.Products.«IPRODUCT_EQ_1»
  IPRODUCT_INJECTION := SessionLibrary.Products.«IPRODUCT_INJECTION»
  IPRODUCT_LE_1 := SessionLibrary.Products.«IPRODUCT_LE_1»
  IPRODUCT_MUL := SessionLibrary.Products.«IPRODUCT_MUL»
  IPRODUCT_ONE := SessionLibrary.Products.«IPRODUCT_ONE»
  IPRODUCT_RELATED := SessionLibrary.Products.«IPRODUCT_RELATED»
  IPRODUCT_RESTRICT_SET := SessionLibrary.Products.«IPRODUCT_RESTRICT_SET»
  IPRODUCT_SING := SessionLibrary.Products.«IPRODUCT_SING»
  IPRODUCT_SUPERSET := SessionLibrary.Products.«IPRODUCT_SUPERSET»
  LEFT_ADD_DISTRIB := Session.LEFT_ADD_DISTRIB
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LEFT_SUB_DISTRIB := Session.LEFT_SUB_DISTRIB
  LE_1 := Session.LE_1
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_MULT_RCANCEL := Session.LE_MULT_RCANCEL
  LTE_TRANS := Session.LTE_TRANS
  LT_ADD_LCANCEL := Session.LT_ADD_LCANCEL
  LT_IMP_LE := Session.LT_IMP_LE
  LT_MULT_LCANCEL := Session.LT_MULT_LCANCEL
  MOD_2_CASES := Session.MOD_2_CASES
  MOD_ADD_MOD := Session.MOD_ADD_MOD
  MOD_LT := Session.MOD_LT
  MOD_LT_EQ := Session.MOD_LT_EQ
  MOD_MULT := Session.MOD_MULT
  MOD_MULT_ADD := Session.MOD_MULT_ADD
  MOD_ZERO := Session.MOD_ZERO
  MONO_FORALL := Session.MONO_FORALL
  MULT_ASSOC := Session.MULT_ASSOC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_EQ_1 := Session.MULT_EQ_1
  MULT_SYM := Session.MULT_SYM
  NOT_EVEN := Session.NOT_EVEN
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LE := Session.NOT_LE
  NOT_ODD := Session.NOT_ODD
  NPRODUCT_CLAUSES := Session.NPRODUCT_CLAUSES
  NUM_OF_INT_MUL := Session.NUM_OF_INT_MUL
  NUM_OF_INT_OF_NUM := Session.NUM_OF_INT_OF_NUM
/-- The core theorems jacobi.ml uses. -/
unsafe def core4 (_ : Unit) : HolLibrary.Jacobi.CoreThms4 where
  ODD := Session.ODD
  ODD_EXISTS := Session.ODD_EXISTS
  ODD_MULT := Session.ODD_MULT
  ODD_PRIME := SessionLibrary.Prime.«ODD_PRIME»
  OR_EXISTS_THM := Session.OR_EXISTS_THM
  PAIRWISE := Session.listDefs.PAIRWISE
  PAIR_EQ := Session.PAIR_EQ
  PRIMES_INFINITE := SessionLibrary.Prime.«PRIMES_INFINITE»
  PRIME_0 := SessionLibrary.Prime.«PRIME_0»
  PRIME_1 := SessionLibrary.Prime.«PRIME_1»
  PRIME_2 := SessionLibrary.Prime.«PRIME_2»
  PRIME_COPRIME_EQ := SessionLibrary.Prime.«PRIME_COPRIME_EQ»
  PRIME_COPRIME_LT := SessionLibrary.Prime.«PRIME_COPRIME_LT»
  PRIME_DIVEXP_EQ := SessionLibrary.Prime.«PRIME_DIVEXP_EQ»
  PRIME_DIVPROD_EQ := SessionLibrary.Prime.«PRIME_DIVPROD_EQ»
  PRIME_FACTOR_INDUCT := SessionLibrary.Prime.«PRIME_FACTOR_INDUCT»
  PRIME_GE_2 := SessionLibrary.Prime.«PRIME_GE_2»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_ODD := SessionLibrary.Prime.«PRIME_ODD»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  SING_GSPEC := Session.SING_GSPEC
  SUBSET := Session.SUBSET
  SUB_EQ_0 := Session.SUB_EQ_0
  SUC_SUB1 := Session.SUC_SUB1
  coprime := Session.coprime
  num_congruent := Session.num_congruent
  num_coprime := Session.num_coprime
  num_divides := Session.num_divides
  numseg := Session.numseg
  o_DEF := Session.o_DEF
  o_THM := Session.o_THM
-- @@CORE END

/-- What jacobi.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Jacobi.JacobiDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)
  INT_ARITH_TAC := Session.INT_ARITH_TAC
  ASM_INT_ARITH_TAC := Session.ASM_INT_ARITH_TAC
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  NUMBER_RULE t := ExceptT.mk (Session.NUMBER_RULE t)
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  TAUT t := ExceptT.mk (Session.TAUT t)
  INT_REDUCE_CONV := Session.INT_REDUCE_CONV
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  INT_RING t := ExceptT.mk (Session.INT_RING t)
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  core1 := core1 ()
  core2 := core2 ()
  core3 := core3 ()
  core4 := core4 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`, and MATCH_CONV's basic conversions, which HOL
    Light adds loading ind_types.ml), then primitive.ml, which jacobi.ml needs. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      SessionLibrary.Primitive.ensurePrimitive
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.Jacobi: {name}"

/- The bundles, in file order; each forces the one before it. -/

-- @@BUNDLES BEGIN
initialize theGeneric : IO.Ref (Option HolLibrary.Jacobi.Generic) ← IO.mkRef none
unsafe def BGeneric : HolLibrary.Jacobi.Generic :=
  cached theGeneric "setupGeneric" fun _ => do
    (HolLibrary.Jacobi.setupGeneric (deps ())).run

initialize theJacobiDef : IO.Ref (Option HolLibrary.Jacobi.JacobiDef) ← IO.mkRef none
unsafe def BJacobiDef : HolLibrary.Jacobi.JacobiDef :=
  cached theJacobiDef "setupJacobiDef" fun _ => do
    let _ ← IO.mkRef BGeneric.COPRIME_IPRODUCT
    (HolLibrary.Jacobi.setupJacobiDef (deps ())).run

initialize theJacobiEuler : IO.Ref (Option HolLibrary.Jacobi.JacobiEuler) ← IO.mkRef none
unsafe def BJacobiEuler : HolLibrary.Jacobi.JacobiEuler :=
  cached theJacobiEuler "setupJacobiEuler" fun _ => do
    let _ ← IO.mkRef BJacobiDef.jacobi
    (HolLibrary.Jacobi.setupJacobiEuler (deps ()) BJacobiDef).run

initialize theGauss : IO.Ref (Option HolLibrary.Jacobi.Gauss) ← IO.mkRef none
unsafe def BGauss : HolLibrary.Jacobi.Gauss :=
  cached theGauss "setupGauss" fun _ => do
    let _ ← IO.mkRef BJacobiEuler.JACOBI_EULER
    (HolLibrary.Jacobi.setupGauss (deps ()) BGeneric BJacobiDef BJacobiEuler).run

initialize theJacobiOf2 : IO.Ref (Option HolLibrary.Jacobi.JacobiOf2) ← IO.mkRef none
unsafe def BJacobiOf2 : HolLibrary.Jacobi.JacobiOf2 :=
  cached theJacobiOf2 "setupJacobiOf2" fun _ => do
    let _ ← IO.mkRef BGauss.JACOBI_MINUS1
    (HolLibrary.Jacobi.setupJacobiOf2 (deps ()) BJacobiDef BJacobiEuler BGauss).run

initialize theOf2Cases : IO.Ref (Option HolLibrary.Jacobi.Of2Cases) ← IO.mkRef none
unsafe def BOf2Cases : HolLibrary.Jacobi.Of2Cases :=
  cached theOf2Cases "setupOf2Cases" fun _ => do
    let _ ← IO.mkRef BJacobiOf2.JACOBI_OF_2
    (HolLibrary.Jacobi.setupOf2Cases (deps ()) BJacobiOf2).run

initialize theReciprocity : IO.Ref (Option HolLibrary.Jacobi.Reciprocity) ← IO.mkRef none
unsafe def BReciprocity : HolLibrary.Jacobi.Reciprocity :=
  cached theReciprocity "setupReciprocity" fun _ => do
    let _ ← IO.mkRef BOf2Cases.JACOBI_OF_2_CASES
    (HolLibrary.Jacobi.setupReciprocity (deps ()) BJacobiDef BJacobiEuler BGauss).run

initialize theJacobi2 : IO.Ref (Option HolLibrary.Jacobi.Jacobi2) ← IO.mkRef none
unsafe def BJacobi2 : HolLibrary.Jacobi.Jacobi2 :=
  cached theJacobi2 "setupJacobi2" fun _ => do
    let _ ← IO.mkRef BReciprocity.JACOBI_RECIPROCITY_ALT
    (HolLibrary.Jacobi.setupJacobi2 (deps ()) BJacobiDef).run

initialize theIntJacobi1 : IO.Ref (Option HolLibrary.Jacobi.IntJacobi1) ← IO.mkRef none
unsafe def BIntJacobi1 : HolLibrary.Jacobi.IntJacobi1 :=
  cached theIntJacobi1 "setupIntJacobi1" fun _ => do
    let _ ← IO.mkRef BJacobi2.JACOBI_EQ_1
    (HolLibrary.Jacobi.setupIntJacobi1 (deps ()) BJacobiDef BJacobiEuler).run

initialize theIntJacobi2 : IO.Ref (Option HolLibrary.Jacobi.IntJacobi2) ← IO.mkRef none
unsafe def BIntJacobi2 : HolLibrary.Jacobi.IntJacobi2 :=
  cached theIntJacobi2 "setupIntJacobi2" fun _ => do
    let _ ← IO.mkRef BIntJacobi1.int_jacobi
    (HolLibrary.Jacobi.setupIntJacobi2 (deps ()) BJacobiDef BJacobiEuler BGauss BOf2Cases BIntJacobi1).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Generic
unsafe def COPRIME_IPRODUCT : thm := BGeneric.COPRIME_IPRODUCT
unsafe def CONG_IPRODUCT : thm := BGeneric.CONG_IPRODUCT

-- JacobiDef
unsafe def jacobi : thm := BJacobiDef.jacobi
unsafe def JACOBI_BOUND : thm := BJacobiDef.JACOBI_BOUND
unsafe def JACOBI_CASES : thm := BJacobiDef.JACOBI_CASES
unsafe def JACOBI_PRIME : thm := BJacobiDef.JACOBI_PRIME
unsafe def JACOBI : thm := BJacobiDef.JACOBI
unsafe def JACOBI_ALT : thm := BJacobiDef.JACOBI_ALT
unsafe def JACOBI_EQ_0 : thm := BJacobiDef.JACOBI_EQ_0
unsafe def JACOBI_ZERO : thm := BJacobiDef.JACOBI_ZERO
unsafe def JACOBI_1 : thm := BJacobiDef.JACOBI_1
unsafe def JACOBI_0 : thm := BJacobiDef.JACOBI_0
unsafe def JACOBI_2_CASES : thm := BJacobiDef.JACOBI_2_CASES
unsafe def JACOBI_2 : thm := BJacobiDef.JACOBI_2

-- JacobiEuler
unsafe def JACOBI_EULER : thm := BJacobiEuler.JACOBI_EULER
unsafe def JACOBI_EULER_ALT : thm := BJacobiEuler.JACOBI_EULER_ALT
unsafe def JACOBI_RMUL : thm := BJacobiEuler.JACOBI_RMUL
unsafe def JACOBI_LMUL : thm := BJacobiEuler.JACOBI_LMUL
unsafe def JACOBI_REXP : thm := BJacobiEuler.JACOBI_REXP
unsafe def JACOBI_LEXP : thm := BJacobiEuler.JACOBI_LEXP
unsafe def JACOBI_EXP_2 : thm := BJacobiEuler.JACOBI_EXP_2
unsafe def JACOBI_EXP_2_ALT : thm := BJacobiEuler.JACOBI_EXP_2_ALT
unsafe def JACOBI_NPRODUCT_RIGHT : thm := BJacobiEuler.JACOBI_NPRODUCT_RIGHT
unsafe def JACOBI_NPRODUCT_LEFT : thm := BJacobiEuler.JACOBI_NPRODUCT_LEFT
unsafe def JACOBI_CONG : thm := BJacobiEuler.JACOBI_CONG
unsafe def JACOBI_MOD_GEN : thm := BJacobiEuler.JACOBI_MOD_GEN
unsafe def JACOBI_MOD : thm := BJacobiEuler.JACOBI_MOD
unsafe def JACOBI_SQUARED : thm := BJacobiEuler.JACOBI_SQUARED

-- Gauss
unsafe def JACOBI_MINUS1 : thm := BGauss.JACOBI_MINUS1
unsafe def JACOBI_MINUS1_CASES : thm := BGauss.JACOBI_MINUS1_CASES
unsafe def JACOBI_GAUSS_LEMMA : thm := BGauss.JACOBI_GAUSS_LEMMA

-- JacobiOf2
unsafe def JACOBI_OF_2 : thm := BJacobiOf2.JACOBI_OF_2

-- Of2Cases
unsafe def JACOBI_OF_2_CASES : thm := BOf2Cases.JACOBI_OF_2_CASES

-- Reciprocity
unsafe def JACOBI_RECIPROCITY_ALT : thm := BReciprocity.JACOBI_RECIPROCITY_ALT
unsafe def JACOBI_RECIPROCITY : thm := BReciprocity.JACOBI_RECIPROCITY

-- Jacobi2
unsafe def JACOBI_EQ_1 : thm := BJacobi2.JACOBI_EQ_1
unsafe def JACOBI_NE_MINUS1 : thm := BJacobi2.JACOBI_NE_MINUS1

-- IntJacobi1
unsafe def int_jacobi : thm := BIntJacobi1.int_jacobi
unsafe def INT_JACOBI_RNEG : thm := BIntJacobi1.INT_JACOBI_RNEG
unsafe def INT_JACOBI_RABS : thm := BIntJacobi1.INT_JACOBI_RABS
unsafe def INT_JACOBI_NUMS : thm := BIntJacobi1.INT_JACOBI_NUMS
unsafe def INT_JACOBI_BOUND : thm := BIntJacobi1.INT_JACOBI_BOUND
unsafe def INT_JACOBI_CASES : thm := BIntJacobi1.INT_JACOBI_CASES
unsafe def INT_JACOBI_CONG : thm := BIntJacobi1.INT_JACOBI_CONG
unsafe def INT_JACOBI_REM_GEN : thm := BIntJacobi1.INT_JACOBI_REM_GEN
unsafe def INT_JACOBI_REM : thm := BIntJacobi1.INT_JACOBI_REM
unsafe def INT_JACOBI_1 : thm := BIntJacobi1.INT_JACOBI_1
unsafe def INT_JACOBI_0 : thm := BIntJacobi1.INT_JACOBI_0

-- IntJacobi2
unsafe def INT_JACOBI_RMUL : thm := BIntJacobi2.INT_JACOBI_RMUL
unsafe def INT_JACOBI_LMUL : thm := BIntJacobi2.INT_JACOBI_LMUL
unsafe def INT_JACOBI_RPOW : thm := BIntJacobi2.INT_JACOBI_RPOW
unsafe def INT_JACOBI_LPOW : thm := BIntJacobi2.INT_JACOBI_LPOW
unsafe def INT_JACOBI_2 : thm := BIntJacobi2.INT_JACOBI_2
unsafe def INT_JACOBI_POW_2 : thm := BIntJacobi2.INT_JACOBI_POW_2
unsafe def INT_JACOBI_EQ_0 : thm := BIntJacobi2.INT_JACOBI_EQ_0
unsafe def INT_JACOBI_MINUS1 : thm := BIntJacobi2.INT_JACOBI_MINUS1
unsafe def INT_JACOBI_OF_2 : thm := BIntJacobi2.INT_JACOBI_OF_2
unsafe def INT_JACOBI_LNEG : thm := BIntJacobi2.INT_JACOBI_LNEG
unsafe def INT_JACOBI_SQUARED : thm := BIntJacobi2.INT_JACOBI_SQUARED
-- @@EXPORTS END

/-- `needs "Library/jacobi.ml"`: build the bundles, in order. -/
unsafe def ensureJacobi : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BGeneric.COPRIME_IPRODUCT
  let _ ← IO.mkRef BJacobiDef.jacobi
  let _ ← IO.mkRef BJacobiEuler.JACOBI_EULER
  let _ ← IO.mkRef BGauss.JACOBI_MINUS1
  let _ ← IO.mkRef BJacobiOf2.JACOBI_OF_2
  let _ ← IO.mkRef BOf2Cases.JACOBI_OF_2_CASES
  let _ ← IO.mkRef BReciprocity.JACOBI_RECIPROCITY_ALT
  let _ ← IO.mkRef BJacobi2.JACOBI_EQ_1
  let _ ← IO.mkRef BIntJacobi1.int_jacobi
  let _ ← IO.mkRef BIntJacobi2.INT_JACOBI_RMUL
  -- @@ENSURE END
  pure ()

end SessionLibrary.Jacobi
