/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/splitting_types.ml                            . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/SplittingTypes.lean

  The session half of the splitting_types.ml translation: it supplies HolANT.SplittingTypes's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/splitting_types.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.SplittingTypes
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Prime
import SessionLibrary.Pocklington
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.RingTheory
import SessionLibrary.Matroids
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionLibrary.FieldTheory
import SessionANT.IdealArith
import SessionLibrary.Isum
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.PrimeSplit
import SessionANT.NormIndex
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.FiniteFieldTrace
import SessionANT.Ramification
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.Classgroup
import SessionANT.RelativeSplit
import SessionANT.RelativeDegree

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.SplittingTypes

/-- The core theorems splitting_types.ml uses. -/
def core1 : HolANT.SplittingTypes.CoreThms1 where
  ARITH_EQ := Session.ARITH_EQ
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_EQ_NSUM := Session.CARD_EQ_NSUM
  CARD_SING := Session.CARD_SING
  CONJ_ASSOC := Session.CONJ_ASSOC
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIVIDES_ZERO := SessionLibrary.Prime.«DIVIDES_ZERO»
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EQ_MULT_RCANCEL := Session.EQ_MULT_RCANCEL
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_IN_IMAGE := Session.EXISTS_IN_IMAGE
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  FIELD_EXTENSION_SUBRING_GENERATED_FINITE := SessionLibrary.FieldTheory.«FIELD_EXTENSION_SUBRING_GENERATED_FINITE»
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_RING_HOMOMORPHISM_MONOMORPHISM := SessionLibrary.RingTheory.«FIELD_RING_HOMOMORPHISM_MONOMORPHISM»
  FINITE_EQ_FIELD_EXTENSION := SessionLibrary.FieldTheory.«FINITE_EQ_FIELD_EXTENSION»
  FINITE_FIELD_IMP_PERFECT := SessionLibrary.FieldTheory.«FINITE_FIELD_IMP_PERFECT»
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_IMP_ALGEBRAIC_EXTENSION := SessionLibrary.FieldTheory.«FINITE_IMP_ALGEBRAIC_EXTENSION»
  FINITE_INTEGRAL_DOMAIN_IMP_FIELD := SessionLibrary.RingTheory.«FINITE_INTEGRAL_DOMAIN_IMP_FIELD»
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBRING_GENERATED := SessionLibrary.RingTheory.«FINITE_SUBRING_GENERATED»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNIONS := Session.FINITE_UNIONS
  FIRST_RING_ISOMORPHISM_THEOREM := SessionLibrary.RingTheory.«FIRST_RING_ISOMORPHISM_THEOREM»
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  IDEAL_GENERATED_IMAGE_IDEAL_GENERATED := SessionANT.IdealArith.«IDEAL_GENERATED_IMAGE_IDEAL_GENERATED»
  IDEAL_GENERATED_INC := SessionLibrary.RingTheory.«IDEAL_GENERATED_INC»
  IDEAL_GENERATED_MINIMAL_EQ := SessionLibrary.RingTheory.«IDEAL_GENERATED_MINIMAL_EQ»
  IDEAL_GENERATED_SUBSET := SessionLibrary.RingTheory.«IDEAL_GENERATED_SUBSET»
  IDEAL_POW_1 := SessionANT.IdealArith.«IDEAL_POW_1»
  IDEAL_PRODUCT_EQ := SessionANT.IdealArith.«IDEAL_PRODUCT_EQ»
  IDEAL_PRODUCT_SING := SessionANT.IdealArith.«IDEAL_PRODUCT_SING»
  IMAGE_CLAUSES := Session.IMAGE_CLAUSES
  IMAGE_I := Session.IMAGE_I
  IMP_CONJ := Session.IMP_CONJ
  IMP_IMP := Session.IMP_IMP
  INTEGER_RING := SessionLibrary.RingTheory.«INTEGER_RING»
  INTEGRAL_DOMAIN_QUOTIENT_RING := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_QUOTIENT_RING»
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_SING := Session.IN_SING
  IN_UNIONS := Session.IN_UNIONS
  ISOMORPHIC_RING_PERFECT_FIELD := SessionLibrary.FieldTheory.«ISOMORPHIC_RING_PERFECT_FIELD»
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_EQ_1 := Session.MULT_EQ_1
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LT := Session.NOT_LT
  NSUM_ADD := Session.NSUM_ADD
  NSUM_EQ := Session.NSUM_EQ
  NSUM_EQ_0_IFF := Session.NSUM_EQ_0_IFF
  NSUM_SING := Session.NSUM_SING
  NUMBER_FIELD_FINITE_RAMIFIED_PRIMES := SessionANT.Ramification.«NUMBER_FIELD_FINITE_RAMIFIED_PRIMES»
  NUMBER_FIELD_FUNDAMENTAL_IDENTITY := SessionANT.RelativeDegree.«NUMBER_FIELD_FUNDAMENTAL_IDENTITY»
  NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q»
  NUMBER_FIELD_HOMOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«NUMBER_FIELD_HOMOMORPHIC_PREIMAGE»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_PRIME_FACTORIZATION := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_FACTORIZATION»
  NUMBER_FIELD_PRIME_FACTORIZATION_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_PRIME_FACTORIZATION_Q»
  NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE»
  NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_Q»
  NUMBER_FIELD_PRIME_IDEALS_ABOVE := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_IDEALS_ABOVE»
  NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q»
  NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q := SessionANT.RelativeSplit.«NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q»
  NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS := SessionANT.RelativeDegree.«NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS»
  NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q := SessionANT.PrimeSplit.«NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q»
  NUMBER_FIELD_RAMIFIED_DISCRIMINANT := SessionANT.Ramification.«NUMBER_FIELD_RAMIFIED_DISCRIMINANT»
  NUMBER_FIELD_SUBFIELD_GENERATED := SessionANT.RelativeSplit.«NUMBER_FIELD_SUBFIELD_GENERATED»
  PERFECT_FIELD_IMP_SEPARABLE_EXTENSION := SessionLibrary.FieldTheory.«PERFECT_FIELD_IMP_SEPARABLE_EXTENSION»
  PRIME_IMP_NZ := SessionLibrary.Prime.«PRIME_IMP_NZ»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRIME_SUBFIELD_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«PRIME_SUBFIELD_SUBFIELD_GENERATED»
  PROPER_IDEAL := SessionLibrary.RingTheory.«PROPER_IDEAL»
  PROPER_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PROPER_IMP_RING_IDEAL»
  QUOTIENT_RING_0 := SessionLibrary.RingTheory.«QUOTIENT_RING_0»
  RAMIFICATION_INDEX_PRIME_SUBFIELD := SessionANT.RelativeSplit.«RAMIFICATION_INDEX_PRIME_SUBFIELD»
  RESIDUE_DEGREE_PRIME_SUBFIELD := SessionANT.RelativeSplit.«RESIDUE_DEGREE_PRIME_SUBFIELD»
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_COSET_EQ_IDEAL := SessionLibrary.RingTheory.«RING_COSET_EQ_IDEAL»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_INTEGER_RING_OF_INT := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_INTEGER_RING_OF_INT»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_RING_COSET := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_COSET»
  RING_HOMOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_HOMOMORPHISM_RING_OF_INTEGERS»
  RING_HOMOMORPHISM_RING_OF_NUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_NUM»
  RING_HOMOMORPHISM_SUBFIELD_INCLUSION := SessionLibrary.FieldTheory.«RING_HOMOMORPHISM_SUBFIELD_INCLUSION»
  RING_IDEAL_HOMOMORPHIC_PREIMAGE := SessionLibrary.RingTheory.«RING_IDEAL_HOMOMORPHIC_PREIMAGE»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«RING_IDEAL_IMP_SUBSET»
  RING_OF_INT := SessionLibrary.RingTheory.«RING_OF_INT»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_PRIME_IDEAL_ABOVE := SessionANT.PrimeSplit.«RING_OF_INTEGERS_PRIME_IDEAL_ABOVE»
  RING_OF_INTEGERS_PRIME_IDEAL_BELOW := SessionANT.RelativeSplit.«RING_OF_INTEGERS_PRIME_IDEAL_BELOW»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_INT_OF_NUM := SessionLibrary.RingTheory.«RING_OF_INT_OF_NUM»
  RING_OF_NUM := SessionLibrary.RingTheory.«RING_OF_NUM»
  RING_OF_NUM_EQ_0 := SessionLibrary.RingTheory.«RING_OF_NUM_EQ_0»
  RING_OF_NUM_SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«RING_OF_NUM_SUBFIELD_GENERATED»
  SING_SUBSET := Session.SING_SUBSET
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_TRANS := Session.SUBSET_TRANS
  SUBSET_UNIV := Session.SUBSET_UNIV
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  maximal_ideal := SessionLibrary.RingTheory.«maximal_ideal»
  number_field := SessionANT.Numfield.«number_field»
  o_THM := Session.o_THM
  prime_ideal := SessionLibrary.RingTheory.«prime_ideal»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  ring_image := SessionLibrary.RingTheory.«ring_image»
  ring_kernel := SessionLibrary.RingTheory.«ring_kernel»
  ring_monomorphism := SessionLibrary.RingTheory.«ring_monomorphism»

/-- What splitting_types.ml uses from Session. -/
def deps : HolANT.SplittingTypes.SplittingTypesDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  new_recursive_definition ax s := do
    ExceptT.mk (Session.new_recursive_definition ax (← HolLight.q s))
  LIST_INDUCT_TAC := Session.LIST_INDUCT_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  METIS_TAC := Session.METIS_TAC
  ASM_METIS_TAC := Session.ASM_METIS_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  TAUT t := ExceptT.mk (Session.TAUT t)
  ITAUT t := ExceptT.mk (Session.ITAUT t)
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH t)
  REAL_FIELD t := ExceptT.mk (Session.REAL_FIELD t)
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC
  ASM_REAL_ARITH_TAC := Session.ASM_REAL_ARITH_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  INT_ARITH t := ExceptT.mk (Session.INT_ARITH t)
  INT_ARITH_TAC := Session.INT_ARITH_TAC
  ASM_INT_ARITH_TAC := Session.ASM_INT_ARITH_TAC
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  INTEGER_TAC := Session.INTEGER_TAC
  NUMBER_RULE := Session.NUMBER_RULE
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  INT_REDUCE_CONV := Session.INT_REDUCE_CONV
  INT_RED_CONV := Session.INT_RED_CONV
  INT_REM_DOWN_CONV := Session.INT_REM_DOWN_CONV
  HAS_SIZE_CONV := Session.HAS_SIZE_CONV
  let_CONV := Session.let_CONV
  num_CONV := Session.num_CONV
  mk_numeral := Session.mk_numeral
  PRIME_CONV t := ExceptT.mk (SessionLibrary.Pocklington.PRIME_CONV t)
  PRIME_RULE := SessionLibrary.Pocklington.PRIME_RULE
  RING_RULE t := ExceptT.mk (SessionLibrary.RingTheory.RING_RULE t)
  INTEGRAL_DOMAIN_RULE t := ExceptT.mk (SessionLibrary.RingTheory.INTEGRAL_DOMAIN_RULE t)
  FIELD_TAC := SessionLibrary.RingTheory.FIELD_TAC
  RING_CARRIER_TAC := SessionLibrary.RingTheory.RING_CARRIER_TAC
  RING_TAC := SessionLibrary.RingTheory.RING_TAC
  RING_PULL_DIV_TAC := SessionLibrary.RingTheory.RING_PULL_DIV_TAC
  LET_TAC := Session.LET_TAC
  basic_ss := Session.basic_ss
  INTEGER_MOD_RING_RED_CONV := SessionLibrary.RingTheory.INTEGER_MOD_RING_RED_CONV
  NUM_SUB_CONV := Session.NUM_SUB_CONV
  REAL_RAT_REDUCE_CONV := Session.REAL_RAT_REDUCE_CONV
  NUM_EQ_CONV := Session.NUM_EQ_CONV
  NUM_DIV_CONV := Session.NUM_DIV_CONV
  EXP_MOD_CONV := Session.EXP_MOD_CONV
  EXPAND_CASES_CONV := Session.EXPAND_CASES_CONV
  DIVIDES_CONV := SessionLibrary.Prime.DIVIDES_CONV
  COPRIME_CONV := SessionLibrary.Prime.COPRIME_CONV
  SIMP_RULE ths th := ExceptT.mk (Session.SIMP_RULE ths th)
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in splitting_types.ml order. -/
initialize BSplittingTypes01 : HolANT.SplittingTypes.SplittingTypes01 ←
  ioB "setupSplittingTypes01" (HolANT.SplittingTypes.setupSplittingTypes01 deps).run
initialize BSplittingTypes02 : HolANT.SplittingTypes.SplittingTypes02 ←
  ioB "setupSplittingTypes02" (HolANT.SplittingTypes.setupSplittingTypes02 deps BSplittingTypes01).run

-- SplittingTypes01
def weakly_unramified : thm := BSplittingTypes01.weakly_unramified
def unramified : thm := BSplittingTypes01.unramified
def totally_split : thm := BSplittingTypes01.totally_split
def inert : thm := BSplittingTypes01.inert
def totally_ramified : thm := BSplittingTypes01.totally_ramified
def UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED : thm := BSplittingTypes01.UNRAMIFIED_IMP_WEAKLY_UNRAMIFIED
def UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_FINITE : thm := BSplittingTypes01.UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_FINITE
def UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_PERFECT : thm := BSplittingTypes01.UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_PERFECT
def RING_OF_INTEGERS_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED : thm := BSplittingTypes01.RING_OF_INTEGERS_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED
def NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_Q : thm := BSplittingTypes01.NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED_Q
def NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED : thm := BSplittingTypes01.NUMBER_FIELD_UNRAMIFIED_EQ_WEAKLY_UNRAMIFIED
def SPLITTING_TYPES_PRINCIPAL : thm := BSplittingTypes01.SPLITTING_TYPES_PRINCIPAL
def SPLITTING_TYPES_INTEGER_RING : thm := BSplittingTypes01.SPLITTING_TYPES_INTEGER_RING
def IDEAL_PRODUCT_SPLITTING_TYPES : thm := BSplittingTypes01.IDEAL_PRODUCT_SPLITTING_TYPES
def NUMBER_FIELD_PRIME_DECOMPOSITION_Q : thm := BSplittingTypes01.NUMBER_FIELD_PRIME_DECOMPOSITION_Q
def NUMBER_FIELD_UNRAMIFIED_DISCRIMINANT : thm := BSplittingTypes01.NUMBER_FIELD_UNRAMIFIED_DISCRIMINANT
def NUMBER_FIELD_UNRAMIFIED_FACTORIZATION : thm := BSplittingTypes01.NUMBER_FIELD_UNRAMIFIED_FACTORIZATION
def NUMBER_FIELD_TOTALLY_SPLIT_CARD : thm := BSplittingTypes01.NUMBER_FIELD_TOTALLY_SPLIT_CARD
def NUMBER_FIELD_INERT_RESIDUE_DEGREE : thm := BSplittingTypes01.NUMBER_FIELD_INERT_RESIDUE_DEGREE
def NUMBER_FIELD_TOTALLY_RAMIFIED_RAMIFICATION_INDEX : thm := BSplittingTypes01.NUMBER_FIELD_TOTALLY_RAMIFIED_RAMIFICATION_INDEX
def NUMBER_FIELD_TOTALLY_RAMIFIED_IDEAL_POW : thm := BSplittingTypes01.NUMBER_FIELD_TOTALLY_RAMIFIED_IDEAL_POW
def NUMBER_FIELD_INERT_IMP_UNRAMIFIED : thm := BSplittingTypes01.NUMBER_FIELD_INERT_IMP_UNRAMIFIED
def NUMBER_FIELD_SPLITTING_TYPES_EXCLUSIVE : thm := BSplittingTypes01.NUMBER_FIELD_SPLITTING_TYPES_EXCLUSIVE
def NUMBER_FIELD_PRIME_DECOMPOSITION : thm := BSplittingTypes01.NUMBER_FIELD_PRIME_DECOMPOSITION

-- SplittingTypes02
def UNRAMIFIED_FACTORIZATION : thm := BSplittingTypes02.UNRAMIFIED_FACTORIZATION
def TOTALLY_SPLIT_CARD : thm := BSplittingTypes02.TOTALLY_SPLIT_CARD
def INERT_RESIDUE_DEGREE : thm := BSplittingTypes02.INERT_RESIDUE_DEGREE
def TOTALLY_RAMIFIED_RAMIFICATION_INDEX : thm := BSplittingTypes02.TOTALLY_RAMIFIED_RAMIFICATION_INDEX
def TOTALLY_RAMIFIED_IDEAL_POW : thm := BSplittingTypes02.TOTALLY_RAMIFIED_IDEAL_POW
def INERT_IMP_UNRAMIFIED : thm := BSplittingTypes02.INERT_IMP_UNRAMIFIED
def SPLITTING_TYPES_EXCLUSIVE : thm := BSplittingTypes02.SPLITTING_TYPES_EXCLUSIVE
def UNRAMIFIED_DISCRIMINANT : thm := BSplittingTypes02.UNRAMIFIED_DISCRIMINANT
def FINITE_RAMIFIED : thm := BSplittingTypes02.FINITE_RAMIFIED
def SPLITTING_TYPES_PRIME_SUBFIELD : thm := BSplittingTypes02.SPLITTING_TYPES_PRIME_SUBFIELD
def NUMBER_FIELD_SUBFIELD_UNRAMIFIED_DISCRIMINANT : thm := BSplittingTypes02.NUMBER_FIELD_SUBFIELD_UNRAMIFIED_DISCRIMINANT

/-- `needs "ANT/splitting_types.ml"`: already done by importing this module. -/
def ensureSplittingTypes : IO Unit := pure ()

end SessionANT.SplittingTypes
