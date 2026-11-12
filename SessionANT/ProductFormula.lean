/- ---------------------------------------------------------------------- -/
/- Session wiring for ANT/product_formula.ml                            . -/
/- ---------------------------------------------------------------------- -/
/- File: SessionANT/ProductFormula.lean

  The session half of the product_formula.ml translation: it supplies HolANT.ProductFormula's
  dependencies from Session and the modules of its `needs`, and exports
  every name under its HOL Light name.  Importing this module is
  `needs "ANT/product_formula.ml"`.  The bundles are built by `initialize` when the module
  is loaded.
-/

import Session
import HolANT.ProductFormula
import SessionLibrary.Products
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
import SessionLibrary.Isum
import SessionANT.Algmisc
import SessionANT.Integral
import SessionANT.Zlattice
import SessionLibrary.Floor
import SessionANT.Numfield
import SessionANT.IdealArith
import SessionANT.Dedekind
import SessionANT.DedekindStruct
import SessionANT.IdealNorm
import SessionANT.RingOfIntegers
import SessionANT.DedekindLocal
import SessionANT.DedekindValuation
import SessionANT.NormIndex
import SessionANT.Classgroup
import SessionANT.NfValuation
import SessionANT.ValuationRing
import SessionANT.DedekindAbsolute
import SessionLibrary.Frag
import SessionLibrary.GroupTheory
import SessionANT.PrimeSplit
import SessionANT.Discriminant
import SessionANT.TraceForm
import SessionANT.RelativeSplit
import SessionANT.Integrality
import SessionLibrary.RingGroups
import SessionANT.FingenGroup
import SessionMultiLib.Misc
import SessionMultiLib.Metric
import SessionMultiLib.Homology
import SessionMultiLib.Vectors
import SessionMultiLib.Determinants
import SessionMultiLib.Topology
import SessionMultiLib.Convex
import SessionMultiLib.Paths
import SessionMultiLib.Polytope
import SessionMultiLib.Degree
import SessionMultiLib.Derivatives
import SessionMultiLib.Integration
import SessionMultiLib.Measure
import SessionMultiLib.ComplexAlgebra
import SessionMultiLib.Complexes
import SessionMultiLib.Canal
import SessionMultiLib.Transcendentals
import SessionMultiLib.RealAnalysis
import SessionMultiLib.MoreTop
import SessionMultiLib.Cauchy
import SessionMultiLib.ComplexRing
import SessionMultiLib.ComplexField
import SessionANT.ComplexEmbeddings
import SessionANT.PowerBasis
import SessionANT.InfinitePlaces

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionANT.ProductFormula

/-- The core theorems product_formula.ml uses. -/
def core1 : HolANT.ProductFormula.CoreThms1 where
  COMPLEX_EMBEDDINGS_MONOMORPHISM := SessionANT.ComplexEmbeddings.«COMPLEX_EMBEDDINGS_MONOMORPHISM»
  COMPLEX_EMBEDDINGS_NORM_MUL := SessionANT.InfinitePlaces.«COMPLEX_EMBEDDINGS_NORM_MUL»
  COMPLEX_EMBEDDINGS_NORM_POS := SessionANT.InfinitePlaces.«COMPLEX_EMBEDDINGS_NORM_POS»
  COMPLEX_NORM_MUL := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_MUL»
  COMPLEX_NORM_ZERO := SessionMultiLib.ComplexAlgebra.«COMPLEX_NORM_ZERO»
  COMPLEX_RING_CLAUSES := SessionMultiLib.ComplexRing.«COMPLEX_RING_CLAUSES»
  DEDEKIND_VALUATION_IDEAL_NORM := SessionANT.DedekindAbsolute.«DEDEKIND_VALUATION_IDEAL_NORM»
  DEDEKIND_VALUATION_MUL := SessionANT.DedekindValuation.«DEDEKIND_VALUATION_MUL»
  DEDEKIND_VALUATION_NORMALIZED_ABSOLUTE_VALUE := SessionANT.DedekindAbsolute.«DEDEKIND_VALUATION_NORMALIZED_ABSOLUTE_VALUE»
  EQ_TRANS := Session.EQ_TRANS
  EXTENSION := Session.EXTENSION
  FIELD_IMP_INTEGRAL_DOMAIN := SessionLibrary.RingTheory.«FIELD_IMP_INTEGRAL_DOMAIN»
  FINITE_COMPLEX_EMBEDDINGS := SessionANT.ComplexEmbeddings.«FINITE_COMPLEX_EMBEDDINGS»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  IDEAL_GENERATED_EQ_0 := SessionLibrary.RingTheory.«IDEAL_GENERATED_EQ_0»
  IDEAL_NORM_GT_1 := SessionANT.IdealNorm.«IDEAL_NORM_GT_1»
  INTEGRAL_DOMAIN_MUL_EQ_0 := SessionLibrary.RingTheory.«INTEGRAL_DOMAIN_MUL_EQ_0»
  INT_NEG_0 := Session.INT_NEG_0
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_UNION := Session.IN_UNION
  I_THM := Session.I_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  NORM_CPRODUCT := SessionMultiLib.ComplexAlgebra.«NORM_CPRODUCT»
  NORM_POS_LE := SessionMultiLib.Vectors.«NORM_POS_LE»
  NORM_TRIANGLE := SessionMultiLib.Vectors.«NORM_TRIANGLE»
  NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS := SessionANT.InfinitePlaces.«NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS»
  NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS := SessionANT.InfinitePlaces.«NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS»
  PRIME_IMP_PROPER_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_PROPER_IDEAL»
  PRIME_IMP_RING_IDEAL := SessionLibrary.RingTheory.«PRIME_IMP_RING_IDEAL»
  PRODUCT_DIV := SessionLibrary.Products.«PRODUCT_DIV»
  PRODUCT_EQ := SessionLibrary.Products.«PRODUCT_EQ»
  PRODUCT_MUL := SessionLibrary.Products.«PRODUCT_MUL»
  PRODUCT_POS_LT := SessionLibrary.Products.«PRODUCT_POS_LT»
  PRODUCT_SUPERSET := SessionLibrary.Products.«PRODUCT_SUPERSET»
  PROPER_IDEAL_ALT := SessionLibrary.RingTheory.«PROPER_IDEAL_ALT»
  REAL_LT_IMP_NZ := Session.REAL_LT_IMP_NZ
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_ZPOW_0 := Session.REAL_ZPOW_0
  REAL_ZPOW_MONO_LT := Session.REAL_ZPOW_MONO_LT
  REAL_ZPOW_SUB := Session.REAL_ZPOW_SUB
  RING_IDEAL_IDEAL_GENERATED := SessionLibrary.RingTheory.«RING_IDEAL_IDEAL_GENERATED»
  RING_MONOMORPHISM_ALT_EQ := SessionLibrary.RingTheory.«RING_MONOMORPHISM_ALT_EQ»
  RING_OF_INTEGERS := SessionANT.Numfield.«RING_OF_INTEGERS»
  RING_OF_INTEGERS_FINITE_QUOTIENT := SessionANT.RingOfIntegers.«RING_OF_INTEGERS_FINITE_QUOTIENT»
  RING_OF_INTEGERS_FRACTION_FIELD := SessionANT.NfValuation.«RING_OF_INTEGERS_FRACTION_FIELD»
  RING_OF_INTEGERS_SUBSET := SessionANT.Numfield.«RING_OF_INTEGERS_SUBSET»
  SUBSET := Session.SUBSET
  SUBSET_UNION := Session.SUBSET_UNION
  absolute_value := SessionANT.DedekindAbsolute.«absolute_value»
  field_of_fractions := SessionLibrary.RingTheory.«field_of_fractions»
  ring_homomorphism := SessionLibrary.RingTheory.«ring_homomorphism»

/-- What product_formula.ml uses from Session. -/
def deps : HolANT.ProductFormula.ProductFormulaDeps where
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

/- The bundles, in product_formula.ml order. -/
initialize BProductFormula : HolANT.ProductFormula.ProductFormula ←
  ioB "setupProductFormula" (HolANT.ProductFormula.setupProductFormula deps).run

-- ProductFormula
def NUMBER_FIELD_PRODUCT_FORMULA : thm := BProductFormula.NUMBER_FIELD_PRODUCT_FORMULA
def NUMBER_FIELD_PRODUCT_FORMULA_NORM : thm := BProductFormula.NUMBER_FIELD_PRODUCT_FORMULA_NORM
def COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE : thm := BProductFormula.COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE
def NUMBER_FIELD_PRODUCT_FORMULA_ABSOLUTE_VALUES : thm := BProductFormula.NUMBER_FIELD_PRODUCT_FORMULA_ABSOLUTE_VALUES

/-- `needs "ANT/product_formula.ml"`: already done by importing this module. -/
def ensureProductFormula : IO Unit := pure ()

end SessionANT.ProductFormula
