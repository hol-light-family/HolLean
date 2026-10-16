/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/rabintest.ml.                         -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/RabinTest.lean

  The `unsafe` half of the rabintest.ml translation: it supplies HolLibrary.RabinTest's
  dependencies from Session and SessionLibrary.FieldTheory, builds the bundles once, in order,
  and exports every name under its HOL Light name.  `ensureRabinTest` is
  `needs "Library/rabintest.ml"` (which first does `needs "Library/fieldtheory.ml"`).

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/RabinTest.lean by tools/rabintestdiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.RabinTest
import SessionLibrary.FieldTheory

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.RabinTest

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems rabin_test.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.RabinTest.CoreThms1 where
  ADD_SYM := Session.ADD_SYM
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_DELETE := Session.CARD_DELETE
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_IMAGE_LE := Session.CARD_IMAGE_LE
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CARD_SUBSET := Session.CARD_SUBSET
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIVIDES_0 := SessionLibrary.Prime.«DIVIDES_0»
  DIVIDES_DIVIDES_DIV := Session.DIVIDES_DIVIDES_DIV
  DIVIDES_DIVIDES_DIV_EQ := Session.DIVIDES_DIVIDES_DIV_EQ
  DIVIDES_DIV_MULT := Session.DIVIDES_DIV_MULT
  DIVIDES_DIV_SELF := Session.DIVIDES_DIV_SELF
  DIVIDES_PRIME_PRIME := SessionLibrary.Prime.«DIVIDES_PRIME_PRIME»
  DIVIDES_TRANS := SessionLibrary.Prime.«DIVIDES_TRANS»
  DIVISION_SIMP := Session.DIVISION_SIMP
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EXP := Session.EXP
  EXP_1 := Session.EXP_1
  EXP_ADD := Session.EXP_ADD
  EXP_EQ_0 := Session.EXP_EQ_0
  EXP_EXP := Session.EXP_EXP
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FIELD_MUL_EQ_0 := SessionLibrary.RingTheory.«FIELD_MUL_EQ_0»
  FIELD_MUL_LINV := SessionLibrary.RingTheory.«FIELD_MUL_LINV»
  FIELD_MUL_RINV := SessionLibrary.RingTheory.«FIELD_MUL_RINV»
  FIELD_NONTRIVIAL := SessionLibrary.RingTheory.«FIELD_NONTRIVIAL»
  FIELD_QUOTIENT_RING := SessionLibrary.RingTheory.«FIELD_QUOTIENT_RING»
  FIELD_UNIT := SessionLibrary.RingTheory.«FIELD_UNIT»
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_EXTENSION_BASIS := SessionLibrary.FieldTheory.«FINITE_EXTENSION_BASIS»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMP_ALGEBRAIC_EXTENSION_EXPLICIT := SessionLibrary.FieldTheory.«FINITE_IMP_ALGEBRAIC_EXTENSION_EXPLICIT»
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_INTEGRAL_DOMAIN_CHAR := SessionLibrary.RingTheory.«FINITE_INTEGRAL_DOMAIN_CHAR»
  FINITE_INTEGRAL_DOMAIN_SIZE := SessionLibrary.FieldTheory.«FINITE_INTEGRAL_DOMAIN_SIZE»
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_SIMPLE_ALGEBRAIC_EXTENSION := SessionLibrary.FieldTheory.«FINITE_SIMPLE_ALGEBRAIC_EXTENSION»
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_FINITE_EXTENSION := SessionLibrary.FieldTheory.«HAS_SIZE_FINITE_EXTENSION»
  IMAGE_POLY_EXTEND_1 := SessionLibrary.RingTheory.«IMAGE_POLY_EXTEND_1»
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTEGRAL_DOMAIN_MUL_RCANCEL := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_RCANCEL»
  INTEGRAL_DOMAIN_POLY_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_POLY_RING»
  INTEGRAL_DOMAIN_PRODUCT_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_PRODUCT_EQ_0»
  IN_DELETE := Session.IN_DELETE
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IDEAL_GENERATED_SELF := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SELF»
  IN_IDEAL_GENERATED_SING := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING»
  IN_IDEAL_GENERATED_SING_EQ := SessionLibrary.RingTheory.«IN_IDEAL_GENERATED_SING_EQ»
  IN_IMAGE := Session.IN_IMAGE
  IN_INSERT := Session.IN_INSERT
  IN_POLY_RING_CARRIER := SessionLibrary.RingTheory.«IN_POLY_RING_CARRIER»
  IN_UNIV := Session.IN_UNIV
  KRONECKER_FIELD_EXTENSION := SessionLibrary.FieldTheory.«KRONECKER_FIELD_EXTENSION»
  LE_ANTISYM := Session.LE_ANTISYM
  LE_EXP := Session.LE_EXP
  LE_REFL := Session.LE_REFL
  LE_TRANS := Session.LE_TRANS
  MAXIMAL_IMP_RING_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_RING_IDEAL»
  MOD_LT_EQ := Session.MOD_LT_EQ
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_1 := Session.MULT_EQ_1
  MULT_SYM := Session.MULT_SYM
  NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS := SessionLibrary.RingTheory.«NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS»
  NOT_FORALL_THM := Session.NOT_FORALL_THM
/-- The core theorems rabin_test.ml uses. -/
unsafe def core2 (_ : Unit) : HolLibrary.RabinTest.CoreThms2 where
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_SUC := Session.NOT_SUC
  PID_IMP_UFD := SessionLibrary.RingTheory.«PID_IMP_UFD»
  PID_POLY_RING := SessionLibrary.RingTheory.«PID_POLY_RING»
  POLY_CONST := SessionLibrary.RingTheory.«POLY_CONST»
  POLY_CONST_0 := SessionLibrary.RingTheory.«POLY_CONST_0»
  POLY_DEG_CONST := SessionLibrary.RingTheory.«POLY_DEG_CONST»
  POLY_DEG_EQ_0 := SessionLibrary.RingTheory.«POLY_DEG_EQ_0»
  POLY_DEG_MUL := SessionLibrary.RingTheory.«POLY_DEG_MUL»
  POLY_DEG_SUB_LE := SessionLibrary.RingTheory.«POLY_DEG_SUB_LE»
  POLY_DEG_VAR := SessionLibrary.RingTheory.«POLY_DEG_VAR»
  POLY_DEG_VAR_POW := SessionLibrary.RingTheory.«POLY_DEG_VAR_POW»
  POLY_EVAL_POW := SessionLibrary.RingTheory.«POLY_EVAL_POW»
  POLY_EVAL_SUB := SessionLibrary.RingTheory.«POLY_EVAL_SUB»
  POLY_EVAL_VAR := SessionLibrary.RingTheory.«POLY_EVAL_VAR»
  POLY_EXTEND_UNIQUE := SessionLibrary.RingTheory.«POLY_EXTEND_UNIQUE»
  POLY_RING := SessionLibrary.RingTheory.«POLY_RING»
  POLY_RING_CLAUSES := SessionLibrary.RingTheory.«POLY_RING_CLAUSES»
  POLY_ROOT_BOUND := SessionLibrary.RingTheory.«POLY_ROOT_BOUND»
  POLY_VAR_UNIV := SessionLibrary.RingTheory.«POLY_VAR_UNIV»
  PRIME_DIVEXP := SessionLibrary.Prime.«PRIME_DIVEXP»
  PRIME_FACTOR := SessionLibrary.Prime.«PRIME_FACTOR»
  PRIME_GE_2 := SessionLibrary.Prime.«PRIME_GE_2»
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  QUOTIENT_RING_CARRIER := SessionLibrary.RingTheory.«QUOTIENT_RING_CARRIER»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_CARRIER_NONEMPTY := SessionLibrary.RingTheory.«RING_CARRIER_NONEMPTY»
  RING_CHAR_DIVIDES_ORDER := SessionLibrary.RingTheory.«RING_CHAR_DIVIDES_ORDER»
  RING_CHAR_DIVIDES_PRIME := SessionLibrary.RingTheory.«RING_CHAR_DIVIDES_PRIME»
  RING_CHAR_HOMOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_CHAR_HOMOMORPHIC_IMAGE»
  RING_CHAR_MONOMORPHIC_IMAGE := SessionLibrary.RingTheory.«RING_CHAR_MONOMORPHIC_IMAGE»
  RING_COSET_EQ := SessionLibrary.RingTheory.«RING_COSET_EQ»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_DIVIDES_0 := SessionLibrary.RingTheory.«RING_DIVIDES_0»
  RING_DIVIDES_ADD := SessionLibrary.RingTheory.«RING_DIVIDES_ADD»
  RING_DIVIDES_SUB := SessionLibrary.RingTheory.«RING_DIVIDES_SUB»
  RING_DIVIDES_SUB_POW := SessionLibrary.RingTheory.«RING_DIVIDES_SUB_POW»
  RING_DIVIDES_TRANS := SessionLibrary.RingTheory.«RING_DIVIDES_TRANS»
  RING_ENDOMORPHISM_EQ := SessionLibrary.RingTheory.«RING_ENDOMORPHISM_EQ»
  RING_ENDOMORPHISM_FROBENIUS := SessionLibrary.RingTheory.«RING_ENDOMORPHISM_FROBENIUS»
  RING_EPIMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_EPIMORPHISM_RING_COSET»
  RING_HOMOMORPHISMS_EQ_FROM_POLY_RING := SessionLibrary.RingTheory.«RING_HOMOMORPHISMS_EQ_FROM_POLY_RING»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_ID := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ID»
  RING_HOMOMORPHISM_POLY_CONST := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POLY_CONST»
  RING_HOMOMORPHISM_POW := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_POW»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_SUB := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_SUB»
  RING_INDEPENDENT_LE_SPAN := SessionLibrary.FieldTheory.«RING_INDEPENDENT_LE_SPAN»
  RING_INV := SessionLibrary.RingTheory.«RING_INV»
  RING_IRREDUCIBLE_DIVIDES_OR_COPRIME := SessionLibrary.RingTheory.«RING_IRREDUCIBLE_DIVIDES_OR_COPRIME»
  RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL := SessionLibrary.RingTheory.«RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL»
  RING_KERNEL_RING_COSET := SessionLibrary.RingTheory.«RING_KERNEL_RING_COSET»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_MONOMORPHISM_POLY_CONST := SessionLibrary.RingTheory.«RING_MONOMORPHISM_POLY_CONST»
  RING_MUL := SessionLibrary.RingTheory.«RING_MUL»
  RING_MUL_ASSOC := SessionLibrary.RingTheory.«RING_MUL_ASSOC»
  RING_MUL_LID := SessionLibrary.RingTheory.«RING_MUL_LID»
  RING_MUL_LZERO := SessionLibrary.RingTheory.«RING_MUL_LZERO»
  RING_MUL_RID := SessionLibrary.RingTheory.«RING_MUL_RID»
  RING_MUL_RZERO := SessionLibrary.RingTheory.«RING_MUL_RZERO»
  RING_POLYNOMIAL_POW := SessionLibrary.RingTheory.«RING_POLYNOMIAL_POW»
  RING_POLYNOMIAL_VAR := SessionLibrary.RingTheory.«RING_POLYNOMIAL_VAR»
  RING_POW := SessionLibrary.RingTheory.«RING_POW»
  RING_POW_1 := SessionLibrary.RingTheory.«RING_POW_1»
  RING_POW_ADD := SessionLibrary.RingTheory.«RING_POW_ADD»
  RING_POW_MUL := SessionLibrary.RingTheory.«RING_POW_MUL»
  RING_POW_POW := SessionLibrary.RingTheory.«RING_POW_POW»
/-- The core theorems rabin_test.ml uses. -/
unsafe def core3 (_ : Unit) : HolLibrary.RabinTest.CoreThms3 where
  RING_POW_ZERO := SessionLibrary.RingTheory.«RING_POW_ZERO»
  RING_PRODUCT := SessionLibrary.RingTheory.«RING_PRODUCT»
  RING_PRODUCT_EQ_GENERAL_INVERSES := SessionLibrary.RingTheory.«RING_PRODUCT_EQ_GENERAL_INVERSES»
  RING_PRODUCT_LMUL := SessionLibrary.RingTheory.«RING_PRODUCT_LMUL»
  RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN := SessionLibrary.FieldTheory.«RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  RING_SUB_TELESCOPE := SessionLibrary.RingTheory.«RING_SUB_TELESCOPE»
  RING_UNIT_INV := SessionLibrary.RingTheory.«RING_UNIT_INV»
  RING_UNIT_POLY_CONST := SessionLibrary.RingTheory.«RING_UNIT_POLY_CONST»
  RING_UNIT_POLY_DOMAIN := SessionLibrary.RingTheory.«RING_UNIT_POLY_DOMAIN»
  SIMPLE_IMAGE_GEN := Session.SIMPLE_IMAGE_GEN
  SUBRING_GENERATED_SUPERSET := SessionLibrary.RingTheory.«SUBRING_GENERATED_SUPERSET»
  SUBSET := Session.SUBSET
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_UNIV := Session.SUBSET_UNIV
  TRIVIAL_RING_10 := SessionLibrary.RingTheory.«TRIVIAL_RING_10»
  UNIV_1 := Session.UNIV_1
  algebraic_over := SessionLibrary.FieldTheory.«algebraic_over»
  divides := Session.divides
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  o_THM := Session.o_THM
  one := Session.one
  ring_basis := SessionLibrary.FieldTheory.«ring_basis»
  ring_coprime := SessionLibrary.RingTheory.«ring_coprime»
  ring_divides := SessionLibrary.RingTheory.«ring_divides»
  ring_endomorphism := SessionLibrary.RingTheory.«ring_endomorphism»
  ring_epimorphism := SessionLibrary.RingTheory.«ring_epimorphism»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_independent := SessionLibrary.FieldTheory.«ring_independent»
  ring_irreducible := SessionLibrary.RingTheory.«ring_irreducible»
  ring_kernel := SessionLibrary.RingTheory.«ring_kernel»
  ring_pow := SessionLibrary.RingTheory.«ring_pow»
  ring_spanning := SessionLibrary.FieldTheory.«ring_spanning»
/-- The core theorems rabin_test.ml uses. -/
unsafe def core4 (_ : Unit) : HolLibrary.RabinTest.CoreThms4 where
-- @@CORE END

/-- What rabintest.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.RabinTest.RabinTestDeps where
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  SET_TAC := Session.SET_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  RING_RULE t := ExceptT.mk (SessionLibrary.RingTheory.RING_RULE t)
  TAUT t := ExceptT.mk (Session.TAUT t)
  core1 := core1 ()
  core2 := core2 ()
  core3 := core3 ()
  core4 := core4 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`, and MATCH_CONV's basic conversions, which HOL
    Light adds loading ind_types.ml), then fieldtheory.ml, which rabintest.ml needs. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      SessionLibrary.FieldTheory.ensureFieldTheory
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.RabinTest: {name}"

/- The bundles, in file order; each forces the one before it. -/

-- @@BUNDLES BEGIN
initialize theGeneralLemmas : IO.Ref (Option HolLibrary.RabinTest.GeneralLemmas) ← IO.mkRef none
unsafe def BGeneralLemmas : HolLibrary.RabinTest.GeneralLemmas :=
  cached theGeneralLemmas "setupGeneralLemmas" fun _ => do
    (HolLibrary.RabinTest.setupGeneralLemmas (deps ())).run

initialize theFiniteFieldFrobenius : IO.Ref (Option HolLibrary.RabinTest.FiniteFieldFrobenius) ← IO.mkRef none
unsafe def BFiniteFieldFrobenius : HolLibrary.RabinTest.FiniteFieldFrobenius :=
  cached theFiniteFieldFrobenius "setupFiniteFieldFrobenius" fun _ => do
    let _ ← IO.mkRef BGeneralLemmas.RING_DIVIDES_POW_ITERATE
    (HolLibrary.RabinTest.setupFiniteFieldFrobenius (deps ())).run

initialize theIrreducibleDivides : IO.Ref (Option HolLibrary.RabinTest.IrreducibleDivides) ← IO.mkRef none
unsafe def BIrreducibleDivides : HolLibrary.RabinTest.IrreducibleDivides :=
  cached theIrreducibleDivides "setupIrreducibleDivides" fun _ => do
    let _ ← IO.mkRef BFiniteFieldFrobenius.FIELD_NONZERO_PRODUCT_PERMUTE
    (HolLibrary.RabinTest.setupIrreducibleDivides (deps ()) BGeneralLemmas BFiniteFieldFrobenius).run

initialize theDegreeBound : IO.Ref (Option HolLibrary.RabinTest.DegreeBound) ← IO.mkRef none
unsafe def BDegreeBound : HolLibrary.RabinTest.DegreeBound :=
  cached theDegreeBound "setupDegreeBound" fun _ => do
    let _ ← IO.mkRef BIrreducibleDivides.IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN
    (HolLibrary.RabinTest.setupDegreeBound (deps ()) BFiniteFieldFrobenius BIrreducibleDivides).run

initialize theIrreducibleDividesDegree : IO.Ref (Option HolLibrary.RabinTest.IrreducibleDividesDegree) ← IO.mkRef none
unsafe def BIrreducibleDividesDegree : HolLibrary.RabinTest.IrreducibleDividesDegree :=
  cached theIrreducibleDividesDegree "setupIrreducibleDividesDegree" fun _ => do
    let _ ← IO.mkRef BDegreeBound.FIELD_ROOTS_BOUND
    (HolLibrary.RabinTest.setupIrreducibleDividesDegree (deps ()) BGeneralLemmas BIrreducibleDivides BDegreeBound).run

initialize theRabinTest : IO.Ref (Option HolLibrary.RabinTest.RabinTest) ← IO.mkRef none
unsafe def BRabinTest : HolLibrary.RabinTest.RabinTest :=
  cached theRabinTest "setupRabinTest" fun _ => do
    let _ ← IO.mkRef BIrreducibleDividesDegree.IRREDUCIBLE_DIVIDES_DEGREE
    (HolLibrary.RabinTest.setupRabinTest (deps ()) BGeneralLemmas BIrreducibleDivides BIrreducibleDividesDegree).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- GeneralLemmas
unsafe def RING_DIVIDES_POW_ITERATE : thm := BGeneralLemmas.RING_DIVIDES_POW_ITERATE
unsafe def POLY_NONUNIT_DEGREE_GE_1 : thm := BGeneralLemmas.POLY_NONUNIT_DEGREE_GE_1
unsafe def RING_DIVIDES_REDUCE : thm := BGeneralLemmas.RING_DIVIDES_REDUCE

-- FiniteFieldFrobenius
unsafe def FIELD_NONZERO_PRODUCT_PERMUTE : thm := BFiniteFieldFrobenius.FIELD_NONZERO_PRODUCT_PERMUTE
unsafe def FINITE_FIELD_ELEMENT_POW : thm := BFiniteFieldFrobenius.FINITE_FIELD_ELEMENT_POW
unsafe def QUOTIENT_POLY_RING_FINITE_CARD : thm := BFiniteFieldFrobenius.QUOTIENT_POLY_RING_FINITE_CARD

-- IrreducibleDivides
unsafe def IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN : thm := BIrreducibleDivides.IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN
unsafe def IRREDUCIBLE_DIVIDES_XQ_MINUS_X : thm := BIrreducibleDivides.IRREDUCIBLE_DIVIDES_XQ_MINUS_X
unsafe def FINITE_FIELD_POW_ITERATE : thm := BIrreducibleDivides.FINITE_FIELD_POW_ITERATE
unsafe def RING_ENDOMORPHISM_FROBENIUS_ITERATE : thm := BIrreducibleDivides.RING_ENDOMORPHISM_FROBENIUS_ITERATE

-- DegreeBound
unsafe def FIELD_ROOTS_BOUND : thm := BDegreeBound.FIELD_ROOTS_BOUND
unsafe def FINITE_FIELD_CARD_CHAR_POWER : thm := BDegreeBound.FINITE_FIELD_CARD_CHAR_POWER
unsafe def IRREDUCIBLE_DIVIDES_DEGREE_BOUND : thm := BDegreeBound.IRREDUCIBLE_DIVIDES_DEGREE_BOUND

-- IrreducibleDividesDegree
unsafe def IRREDUCIBLE_DIVIDES_DEGREE : thm := BIrreducibleDividesDegree.IRREDUCIBLE_DIVIDES_DEGREE

-- RabinTest
unsafe def RABIN_IRREDUCIBILITY_NECESSARY : thm := BRabinTest.RABIN_IRREDUCIBILITY_NECESSARY
unsafe def RABIN_IRREDUCIBILITY_SUFFICIENT : thm := BRabinTest.RABIN_IRREDUCIBILITY_SUFFICIENT
unsafe def RABIN_IRREDUCIBILITY_TEST : thm := BRabinTest.RABIN_IRREDUCIBILITY_TEST
-- @@EXPORTS END

/-- `needs "Library/rabintest.ml"`: build the bundles, in order. -/
unsafe def ensureRabinTest : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BGeneralLemmas.RING_DIVIDES_POW_ITERATE
  let _ ← IO.mkRef BFiniteFieldFrobenius.FIELD_NONZERO_PRODUCT_PERMUTE
  let _ ← IO.mkRef BIrreducibleDivides.IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN
  let _ ← IO.mkRef BDegreeBound.FIELD_ROOTS_BOUND
  let _ ← IO.mkRef BIrreducibleDividesDegree.IRREDUCIBLE_DIVIDES_DEGREE
  let _ ← IO.mkRef BRabinTest.RABIN_IRREDUCIBILITY_NECESSARY
  -- @@ENSURE END
  pure ()

end SessionLibrary.RabinTest
