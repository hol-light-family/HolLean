/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/hilbert_formula.ml                            . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/HilbertFormula.lean

  The session half of the hilbert_formula.ml translation: it supplies HolANT.HilbertFormula's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/hilbert_formula.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.HilbertFormula
import SessionLibrary.Frag
import SessionLibrary.Wo
import SessionLibrary.Card
import SessionLibrary.Prime
import SessionLibrary.GroupTheory
import SessionLibrary.Matroids
import SessionLibrary.Binomial
import SessionLibrary.Iter
import SessionLibrary.Pocklington
import SessionLibrary.RingTheory
import SessionLibrary.Permutations
import SessionLibrary.RingDet
import SessionLibrary.FieldTheory
import SessionLibrary.SymmetricGroup
import SessionLibrary.Galois
import SessionLibrary.Products
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionLibrary.Isum
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.PrimeSplit
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.NfValuation
import SessionANT.Integrality
import SessionANT.Different
import SessionANT.FiniteFieldTrace
import SessionANT.RelativeDegree
import SessionANT.DifferentExtension
import SessionLibrary.RingGroups
import SessionLibrary.FiniteFields
import SessionANT.Decomposition
import SessionANT.Ramification
import SessionANT.SplittingTypes
import SessionANT.NfDecomposition
import SessionANT.DecompositionField
import SessionLibrary.Integer
import SessionLibrary.Multiplicative
import SessionLibrary.Primitive
import SessionANT.DedekindKummer
import SessionANT.SplitPrimes
import SessionANT.ConjugateIdeals
import SessionANT.IdealNormExtension
import SessionANT.Hensel
import SessionANT.IdealEuler
import SessionANT.RamificationGroups
import SessionANT.PowerBasis
import SessionANT.PowerBasisIndex
import SessionANT.PowerBasisExtension

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.HilbertFormula

/-- The core theorems hilbert_formula.ml uses. -/
def core1 : HolANT.HilbertFormula.CoreThms1 where
  ADD_CLAUSES := Session.ADD_CLAUSES
  AND_FORALL_THM := Session.AND_FORALL_THM
  CARD_DELETE := Session.CARD_DELETE
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CARD_PSUBSET := Session.CARD_PSUBSET
  CARD_SING := Session.CARD_SING
  CARD_SUBSET := Session.CARD_SUBSET
  DECOMPOSITION_GROUP := SessionANT.Decomposition.«DECOMPOSITION_GROUP»
  DEDEKIND_IDEAL_POW_MUL_CANCEL := SessionANT.Dedekind.«DEDEKIND_IDEAL_POW_MUL_CANCEL»
  DEDEKIND_IDEAL_SUBSET_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IDEAL_SUBSET_POW_VALUATION»
  DEDEKIND_IN_IDEAL_POW_VALUATION := SessionANT.Dedekind.«DEDEKIND_IN_IDEAL_POW_VALUATION»
  DEDEKIND_RING_OF_INTEGERS := SessionANT.RingOfIntegers.«DEDEKIND_RING_OF_INTEGERS»
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EQ_TRANS := Session.EQ_TRANS
  EXISTS_UNIQUE_THM := Session.EXISTS_UNIQUE_THM
  EXTENSION := Session.EXTENSION
  FIELD_IMP_NONTRIVIAL_RING := SessionLibrary.RingTheory.«FIELD_IMP_NONTRIVIAL_RING»
  FIELD_RING_HOMOMORPHISM_MONOMORPHISM := SessionLibrary.RingTheory.«FIELD_RING_HOMOMORPHISM_MONOMORPHISM»
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_GALOIS_GROUP := SessionLibrary.Galois.«FINITE_GALOIS_GROUP»
  FINITE_INTER := Session.FINITE_INTER
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FUN_IN_IMAGE := Session.FUN_IN_IMAGE
  GALOIS_EXTENSION_INTERMEDIATE := SessionLibrary.Galois.«GALOIS_EXTENSION_INTERMEDIATE»
  GALOIS_GROUP_I := SessionLibrary.Galois.«GALOIS_GROUP_I»
  GALOIS_GROUP_PRIME_IDEAL_IMAGE := SessionANT.Decomposition.«GALOIS_GROUP_PRIME_IDEAL_IMAGE»
  GALOIS_GROUP_RING_HOMOMORPHISM := SessionLibrary.Galois.«GALOIS_GROUP_RING_HOMOMORPHISM»
  GALOIS_GROUP_RING_OF_INTEGERS := SessionANT.NfDecomposition.«GALOIS_GROUP_RING_OF_INTEGERS»
  GALOIS_IMP_FIELD_EXTENSION := SessionLibrary.Galois.«GALOIS_IMP_FIELD_EXTENSION»
  GALOIS_PRIMITIVE_ELEMENT_DERIVATIVE := SessionLibrary.Galois.«GALOIS_PRIMITIVE_ELEMENT_DERIVATIVE»
  GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET := SessionLibrary.GroupTheory.«GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET»
  GROUP_ID := SessionLibrary.GroupTheory.«GROUP_ID»
  GROUP_INV := SessionLibrary.GroupTheory.«GROUP_INV»
  GROUP_MUL := SessionLibrary.GroupTheory.«GROUP_MUL»
  IDEAL_GENERATED_SUBSET := SessionLibrary.RingTheory.«IDEAL_GENERATED_SUBSET»
  IDEAL_GENERATED_SUBSET_CARRIER := SessionLibrary.RingTheory.«IDEAL_GENERATED_SUBSET_CARRIER»
  IDEAL_POW_1 := SessionANT.IdealArith.«IDEAL_POW_1»
  IDEAL_VALUATION_IDEAL_PROD := SessionANT.Dedekind.«IDEAL_VALUATION_IDEAL_PROD»
  IDEAL_VALUATION_PRINCIPAL_PRODUCT := SessionANT.Dedekind.«IDEAL_VALUATION_PRINCIPAL_PRODUCT»
  IMAGE_I := Session.IMAGE_I
  IMAGE_SUBSET := Session.IMAGE_SUBSET
  IMAGE_o := Session.IMAGE_o
  INERTIA_GROUP := SessionANT.Decomposition.«INERTIA_GROUP»
  INERTIA_GROUP_IDEAL_POW := SessionANT.RamificationGroups.«INERTIA_GROUP_IDEAL_POW»
  INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL := SessionANT.RamificationGroups.«INERTIA_GROUP_IDEAL_POW_EVENTUALLY_TRIVIAL»
  INERTIA_GROUP_IDEAL_POW_MONO := SessionANT.RamificationGroups.«INERTIA_GROUP_IDEAL_POW_MONO»
  INERTIA_GROUP_INTERMEDIATE := SessionANT.Decomposition.«INERTIA_GROUP_INTERMEDIATE»
  INERTIA_GROUP_TOWER := SessionANT.Decomposition.«INERTIA_GROUP_TOWER»
  INERTIA_GROUP_WILD_SUBSET := SessionANT.RamificationGroups.«INERTIA_GROUP_WILD_SUBSET»
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTER_SUBSET := Session.INTER_SUBSET
  IN_DELETE := Session.IN_DELETE
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_GALOIS_GROUP := SessionLibrary.Galois.«IN_GALOIS_GROUP»
  IN_INTER := Session.IN_INTER
  IN_RING_IDEAL_0 := SessionLibrary.RingTheory.«IN_RING_IDEAL_0»
  IN_RING_IDEAL_ADD := SessionLibrary.RingTheory.«IN_RING_IDEAL_ADD»
  IN_RING_IDEAL_LMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_LMUL»
  IN_RING_IDEAL_NEG := SessionLibrary.RingTheory.«IN_RING_IDEAL_NEG»
  IN_RING_IDEAL_RMUL := SessionLibrary.RingTheory.«IN_RING_IDEAL_RMUL»
  IN_RING_IDEAL_SUB_SYM := SessionLibrary.RingTheory.«IN_RING_IDEAL_SUB_SYM»
  IN_SING := Session.IN_SING
  IN_UNIV := Session.IN_UNIV
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LEFT_SUB_DISTRIB := Session.LEFT_SUB_DISTRIB
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  MAXIMAL_IMP_PRIME_IDEAL := SessionLibrary.RingTheory.«MAXIMAL_IMP_PRIME_IDEAL»
  MAXIMAL_SUPERIDEAL_EXISTS := SessionLibrary.RingTheory.«MAXIMAL_SUPERIDEAL_EXISTS»
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_AC := Session.MULT_AC
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  NOT_LT := Session.NOT_LT
  NSUM_ADD := Session.NSUM_ADD
  NSUM_CONST := Session.NSUM_CONST
  NSUM_DELETE := Session.NSUM_DELETE
  NSUM_EQ := Session.NSUM_EQ
  NSUM_EQ_0 := Session.NSUM_EQ_0
  NSUM_RESTRICT_SET := Session.NSUM_RESTRICT_SET
  NSUM_SUPERSET := Session.NSUM_SUPERSET
  NSUM_SWAP := Session.NSUM_SWAP
  NUMBER_FIELD_DECOMPOSITION_FIELD := SessionANT.DecompositionField.«NUMBER_FIELD_DECOMPOSITION_FIELD»
  NUMBER_FIELD_DECOMPOSITION_GROUP := SessionANT.NfDecomposition.«NUMBER_FIELD_DECOMPOSITION_GROUP»
  NUMBER_FIELD_DIFFERENT_LOCAL_POWER_BASIS := SessionANT.PowerBasisExtension.«NUMBER_FIELD_DIFFERENT_LOCAL_POWER_BASIS»
  NUMBER_FIELD_DIFFERENT_NONZERO := SessionANT.Different.«NUMBER_FIELD_DIFFERENT_NONZERO»
  NUMBER_FIELD_DIFFERENT_RAMIFIED := SessionANT.DifferentExtension.«NUMBER_FIELD_DIFFERENT_RAMIFIED»
  NUMBER_FIELD_DIFFERENT_TOWER := SessionANT.DifferentExtension.«NUMBER_FIELD_DIFFERENT_TOWER»
  NUMBER_FIELD_GALOIS_CLOSURE := SessionANT.SplitPrimes.«NUMBER_FIELD_GALOIS_CLOSURE»
  NUMBER_FIELD_HOMOMORPHIC_PREIMAGE := SessionANT.RelativeSplit.«NUMBER_FIELD_HOMOMORPHIC_PREIMAGE»
  NUMBER_FIELD_IDEAL_VALUATION_EXTENSION := SessionANT.RelativeSplit.«NUMBER_FIELD_IDEAL_VALUATION_EXTENSION»
  NUMBER_FIELD_IMP_FIELD := SessionANT.Numfield.«NUMBER_FIELD_IMP_FIELD»
  NUMBER_FIELD_INTERMEDIATE_FIELD := SessionANT.DecompositionField.«NUMBER_FIELD_INTERMEDIATE_FIELD»
  NUMBER_FIELD_LOCAL_POWER_BASIS := SessionANT.PowerBasisExtension.«NUMBER_FIELD_LOCAL_POWER_BASIS»
  NUMBER_FIELD_PRIME_IDEAL_ABOVE := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_IDEAL_ABOVE»
  NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO := SessionANT.RelativeSplit.«NUMBER_FIELD_PRIME_IDEAL_ABOVE_NONZERO»
  NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE := SessionANT.DecompositionField.«NUMBER_FIELD_PRIME_IDEAL_INTERMEDIATE»
  NUMBER_FIELD_RAMIFICATION_INDEX_TOWER := SessionANT.RelativeSplit.«NUMBER_FIELD_RAMIFICATION_INDEX_TOWER»
  NUMBER_FIELD_SEPARABLE_EXTENSION := SessionANT.PowerBasisExtension.«NUMBER_FIELD_SEPARABLE_EXTENSION»
  NUMBER_FIELD_TOWER_LAW := SessionANT.RelativeSplit.«NUMBER_FIELD_TOWER_LAW»
  PRIME_IDEAL_IMP_SUBSET := SessionLibrary.RingTheory.«PRIME_IDEAL_IMP_SUBSET»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PSUBSET := Session.PSUBSET
  RING_0 := SessionLibrary.RingTheory.«RING_0»
  RING_1 := SessionLibrary.RingTheory.«RING_1»
  RING_HOMOMORPHISM_0 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_0»
  RING_HOMOMORPHISM_1 := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_1»
  RING_HOMOMORPHISM_ADD := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_ADD»
  RING_HOMOMORPHISM_COMPOSE := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_COMPOSE»
  RING_HOMOMORPHISM_IN_CARRIER := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_IN_CARRIER»
  RING_HOMOMORPHISM_MUL := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_MUL»
  RING_HOMOMORPHISM_NEG := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_NEG»
  RING_HOMOMORPHISM_RING_OF_INTEGERS := SessionANT.Numfield.«RING_HOMOMORPHISM_RING_OF_INTEGERS»
  RING_HOMOMORPHISM_RING_OF_NUM := SessionLibrary.RingTheory.«RING_HOMOMORPHISM_RING_OF_NUM»
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_IDEAL_IDEAL_POW := SessionANT.IdealArith.«RING_IDEAL_IDEAL_POW»
  RING_IDEAL_NUMBER_FIELD_DIFFERENT := SessionANT.Different.«RING_IDEAL_NUMBER_FIELD_DIFFERENT»
  RING_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.RingTheory.«RING_MONOMORPHISM_IMP_HOMOMORPHISM»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FRACTION_FIELD := SessionANT.NfValuation.«RING_OF_INTEGERS_FRACTION_FIELD»
  RING_OF_INTEGERS_IDEAL_EXTENSION := SessionANT.RelativeSplit.«RING_OF_INTEGERS_IDEAL_EXTENSION»
  RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME := SessionANT.RelativeSplit.«RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME»
  RING_OF_INTEGERS_PRIME_IDEAL_ABOVE := SessionANT.PrimeSplit.«RING_OF_INTEGERS_PRIME_IDEAL_ABOVE»
  RING_OF_INTEGERS_SUBRING := SessionANT.Numfield.«RING_OF_INTEGERS_SUBRING»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  RING_OF_NUM_IN_PRIME_IDEAL := SessionANT.PrimeSplit.«RING_OF_NUM_IN_PRIME_IDEAL»
  RING_PRODUCT_RING_OF_INTEGERS := SessionANT.Numfield.«RING_PRODUCT_RING_OF_INTEGERS»
  RING_SUB := SessionLibrary.RingTheory.«RING_SUB»
  RING_SUB_EQ_0 := SessionLibrary.RingTheory.«RING_SUB_EQ_0»
  RING_SUB_REFL := SessionLibrary.RingTheory.«RING_SUB_REFL»
  SING_SUBSET := Session.SING_SUBSET
  SUBFIELD_GENERATED := SessionLibrary.FieldTheory.«SUBFIELD_GENERATED»
  SUBRING_GENERATED_MINIMAL := SessionLibrary.RingTheory.«SUBRING_GENERATED_MINIMAL»
  SUBSET := Session.SUBSET
  SUBSET_INTER := Session.SUBSET_INTER
  SUBSET_TRANS := Session.SUBSET_TRANS
  SUBSET_UNIV := Session.SUBSET_UNIV
  SUB_REFL := Session.SUB_REFL
  field_extension := SessionLibrary.FieldTheory.«field_extension»
  inertia_group := SessionANT.Decomposition.«inertia_group»
  proper_ideal := SessionLibrary.RingTheory.«proper_ideal»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»
  subgroup_of := SessionLibrary.GroupTheory.«subgroup_of»
  subring_of := SessionLibrary.RingTheory.«subring_of»

/-- What hilbert_formula.ml uses from Session. -/
def deps : HolANT.HilbertFormula.HilbertFormulaDeps where
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
  GROUP_RULE t := ExceptT.mk (SessionLibrary.GroupTheory.GROUP_RULE t)
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
  core1 := core1

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in hilbert_formula.ml order. -/
initialize BHilbertFormula01 : HolANT.HilbertFormula.HilbertFormula01 ←
  ioB "setupHilbertFormula01" (HolANT.HilbertFormula.setupHilbertFormula01 deps).run
initialize BHilbertFormula02 : HolANT.HilbertFormula.HilbertFormula02 ←
  ioB "setupHilbertFormula02" (HolANT.HilbertFormula.setupHilbertFormula02 deps BHilbertFormula01).run

-- HilbertFormula01
def NSUM_CARD_SUBSETS_DELETE : thm := BHilbertFormula01.NSUM_CARD_SUBSETS_DELETE
def INERTIA_GROUP_IDEAL_POW_LOCAL_GENERATOR : thm := BHilbertFormula01.INERTIA_GROUP_IDEAL_POW_LOCAL_GENERATOR
def NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_ONE_PRIME : thm := BHilbertFormula01.NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_ONE_PRIME
def NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_LT : thm := BHilbertFormula01.NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA_LT
def NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA : thm := BHilbertFormula01.NUMBER_FIELD_DIFFERENT_HILBERT_FORMULA

-- HilbertFormula02
def NUMBER_FIELD_DIFFERENT_VALUATION_GALOIS_OVERFIELD : thm := BHilbertFormula02.NUMBER_FIELD_DIFFERENT_VALUATION_GALOIS_OVERFIELD
def NUMBER_FIELD_DIFFERENT_VALUATION_TAME : thm := BHilbertFormula02.NUMBER_FIELD_DIFFERENT_VALUATION_TAME
def NUMBER_FIELD_DIFFERENT_VALUATION_WILD : thm := BHilbertFormula02.NUMBER_FIELD_DIFFERENT_VALUATION_WILD

/-- `needs "ANT/hilbert_formula.ml"`: already done by importing this module. -/
def ensureHilbertFormula : IO Unit := pure ()

end SessionANT.HilbertFormula
