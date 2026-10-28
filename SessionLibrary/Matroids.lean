/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/matroids.ml.                          -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Matroids.lean

  The session half of the matroids.ml translation: it supplies
  HolLibrary.Matroids's dependencies from Session and SessionLibrary.Card,
  and exports every name under its HOL Light name.  Importing this module is
  `needs "Library/matroids.ml"`; its `needs "Library/card.ml"` is the import
  of SessionLibrary.Card.  The bundles are built by `initialize` when the
  module is loaded, in file order.
-/

import Session
import HolLibrary.Matroids
import SessionLibrary.Card

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Matroids

/-- The core theorems matroids.ml uses. -/
def core1 : HolLibrary.Matroids.CoreThms1 where
  ADD1 := Session.ADD1
  AND_FORALL_THM := Session.AND_FORALL_THM
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_DIFF := Session.CARD_DIFF
  CARD_LE_ANTISYM := SessionLibrary.Card.«CARD_LE_ANTISYM»
  CARD_LE_CARD := SessionLibrary.Card.«CARD_LE_CARD»
  CARD_LE_FINITE := SessionLibrary.Card.«CARD_LE_FINITE»
  CARD_LE_FINITE_INFINITE := SessionLibrary.Card.«CARD_LE_FINITE_INFINITE»
  CARD_LE_IMAGE := SessionLibrary.Card.«CARD_LE_IMAGE»
  CARD_LE_SUBSET := SessionLibrary.Card.«CARD_LE_SUBSET»
  CARD_LE_TRANS := SessionLibrary.Card.«CARD_LE_TRANS»
  CARD_LE_UNIONS := SessionLibrary.Card.«CARD_LE_UNIONS»
  CARD_PSUBSET := Session.CARD_PSUBSET
  CARD_SUBSET := Session.CARD_SUBSET
  CHOOSE_SUBSET_BETWEEN := Session.CHOOSE_SUBSET_BETWEEN
  CHOOSE_SUBSET_STRONG := Session.CHOOSE_SUBSET_STRONG
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  DELETE_SUBSET := Session.DELETE_SUBSET
  EMPTY_SUBSET := Session.EMPTY_SUBSET
  EQ_IMP := Session.EQ_IMP
  EQ_IMP_LE := Session.EQ_IMP_LE
  FINITE_DIFF := Session.FINITE_DIFF
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_INDUCT_STRONG := Session.FINITE_INDUCT_STRONG
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_RULES := Session.FINITE_RULES
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_SUBSET_UNIONS_CHAIN := Session.FINITE_SUBSET_UNIONS_CHAIN
  FINITE_UNION := Session.FINITE_UNION
  FORALL_IN_GSPEC := Session.FORALL_IN_GSPEC
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_IN_INSERT := Session.FORALL_IN_INSERT
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE := Session.HAS_SIZE
  IMP_CONJ := Session.IMP_CONJ
  IMP_CONJ_ALT := Session.IMP_CONJ_ALT
  IMP_IMP := Session.IMP_IMP
  INFINITE := Session.INFINITE
  INSERT_SUBSET := Session.INSERT_SUBSET
  INTERS_2 := Session.INTERS_2
  INTER_IDEMPOT := Session.INTER_IDEMPOT
  INTER_SUBSET := Session.INTER_SUBSET
  IN_DELETE := Session.IN_DELETE
  IN_DIFF := Session.IN_DIFF
  IN_INSERT := Session.IN_INSERT
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LE_ANTISYM := Session.LE_ANTISYM
  LE_REFL := Session.LE_REFL
  LE_TRANS := Session.LE_TRANS
  LTE_TRANS := Session.LTE_TRANS
  LT_REFL := Session.LT_REFL
  MONO_EXISTS := Session.MONO_EXISTS
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LT := Session.NOT_LT
  PAIR := Session.PAIR
  PAIR_EQ := Session.PAIR_EQ
  PSUBSET := Session.PSUBSET
  PSUBSET_ALT := Session.PSUBSET_ALT
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  SIMPLE_IMAGE := Session.SIMPLE_IMAGE
  SING_SUBSET := Session.SING_SUBSET
  SKOLEM_THM := Session.SKOLEM_THM
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM := Session.SUBSET_ANTISYM
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  SUBSET_DIFF := Session.SUBSET_DIFF
/-- The core theorems matroids.ml uses. -/
def core2 : HolLibrary.Matroids.CoreThms2 where
  SUBSET_INTER := Session.SUBSET_INTER
  SUBSET_INTERS := Session.SUBSET_INTERS
  SUBSET_REFL := Session.SUBSET_REFL
  SUBSET_TRANS := Session.SUBSET_TRANS
  SUBSET_UNION := Session.SUBSET_UNION
  SUB_ADD := Session.SUB_ADD
  SWAP_FORALL_THM := Session.SWAP_FORALL_THM
  UNIONS_0 := Session.UNIONS_0
  UNIONS_SUBSET := Session.UNIONS_SUBSET
  UNION_COMM := Session.UNION_COMM
  UNION_EMPTY := Session.UNION_EMPTY
  UNION_SUBSET := Session.UNION_SUBSET
  WF := Session.WF
  WF_PSUBSET := Session.WF_PSUBSET
  ZL_SUBSETS_UNIONS_NONEMPTY := SessionLibrary.Wo.«ZL_SUBSETS_UNIONS_NONEMPTY»
/-- The core theorems matroids.ml uses. -/
def core3 : HolLibrary.Matroids.CoreThms3 where
/-- The core theorems matroids.ml uses. -/
def core4 : HolLibrary.Matroids.CoreThms4 where

/-- What matroids.ml uses from Session. -/
def deps : HolLibrary.Matroids.MatroidsDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  define s := do ExceptT.mk (Session.define (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  new_type_definition ty names th :=
    ExceptT.mk (Session.new_type_definition ty names.1 names.2 th)
  core1 := core1
  core2 := core2
  core3 := core3
  core4 := core4

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} (name : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in matroids.ml order. -/
initialize BMatroidType : HolLibrary.Matroids.MatroidType ←
  ioB "setupMatroidType" (HolLibrary.Matroids.setupMatroidType deps).run
initialize BLinearNotions : HolLibrary.Matroids.LinearNotions ←
  ioB "setupLinearNotions" (HolLibrary.Matroids.setupLinearNotions deps BMatroidType).run
initialize BIndependentSets : HolLibrary.Matroids.IndependentSets ←
  ioB "setupIndependentSets"
    (HolLibrary.Matroids.setupIndependentSets deps BMatroidType BLinearNotions).run
initialize BSteinitzExchange : HolLibrary.Matroids.SteinitzExchange ←
  ioB "setupSteinitzExchange" (HolLibrary.Matroids.setupSteinitzExchange deps BMatroidType
    BLinearNotions BIndependentSets).run
initialize BSubspaces : HolLibrary.Matroids.Subspaces ←
  ioB "setupSubspaces"
    (HolLibrary.Matroids.setupSubspaces deps BMatroidType BIndependentSets).run
initialize BSubmatroids : HolLibrary.Matroids.Submatroids ←
  ioB "setupSubmatroids" (HolLibrary.Matroids.setupSubmatroids deps BMatroidType
    BLinearNotions BIndependentSets BSteinitzExchange BSubspaces).run
initialize BFiniteDim : HolLibrary.Matroids.FiniteDim ←
  ioB "setupFiniteDim" (HolLibrary.Matroids.setupFiniteDim deps BMatroidType BLinearNotions
    BIndependentSets BSteinitzExchange BSubmatroids).run
initialize BDimension : HolLibrary.Matroids.Dimension ←
  ioB "setupDimension" (HolLibrary.Matroids.setupDimension deps BMatroidType BLinearNotions
    BIndependentSets BSteinitzExchange BSubmatroids BFiniteDim).run
initialize BDimSpan : HolLibrary.Matroids.DimSpan ←
  ioB "setupDimSpan" (HolLibrary.Matroids.setupDimSpan deps BMatroidType BLinearNotions
    BIndependentSets BSubspaces BSubmatroids BFiniteDim BDimension).run

-- MatroidType
def matroid_tybij : thm := BMatroidType.matroid_tybij
def matroid_set : thm := BMatroidType.matroid_set
def matroid_span : thm := BMatroidType.matroid_span
def MATROID_SPAN_SUBSET : thm := BMatroidType.MATROID_SPAN_SUBSET
def MATROID_SPAN_SUPERSET : thm := BMatroidType.MATROID_SPAN_SUPERSET
def MATROID_SPAN_MONO : thm := BMatroidType.MATROID_SPAN_MONO
def MATROID_SPAN_SPAN : thm := BMatroidType.MATROID_SPAN_SPAN
def MATROID_SPAN_FINITARY : thm := BMatroidType.MATROID_SPAN_FINITARY
def MATROID_SPAN_EXCHANGE : thm := BMatroidType.MATROID_SPAN_EXCHANGE
def MATROID_SPAN_INC : thm := BMatroidType.MATROID_SPAN_INC
def SUBSET_MATROID_SPAN : thm := BMatroidType.SUBSET_MATROID_SPAN
def MATROID_SPAN_MINIMAL : thm := BMatroidType.MATROID_SPAN_MINIMAL
def MATROID_SPAN_SET : thm := BMatroidType.MATROID_SPAN_SET
def MATROID_SPAN_EQ : thm := BMatroidType.MATROID_SPAN_EQ
def MATROID_SPAN_EQ_SET : thm := BMatroidType.MATROID_SPAN_EQ_SET
def MATROID_SPAN_SUBSET_EQ : thm := BMatroidType.MATROID_SPAN_SUBSET_EQ
def MATROID_SPAN_INTER_SUBSET : thm := BMatroidType.MATROID_SPAN_INTER_SUBSET
def MATROID_SPAN_UNION : thm := BMatroidType.MATROID_SPAN_UNION
def MATROID_SPAN_UNION_LEFT : thm := BMatroidType.MATROID_SPAN_UNION_LEFT
def MATROID_SPAN_UNION_RIGHT : thm := BMatroidType.MATROID_SPAN_UNION_RIGHT
def MATROID_SPAN_UNION_SUBSET : thm := BMatroidType.MATROID_SPAN_UNION_SUBSET
def MATROID_SPAN_EXCHANGE_DELETE : thm := BMatroidType.MATROID_SPAN_EXCHANGE_DELETE
def MATROID_SPAN_UNION_EQ : thm := BMatroidType.MATROID_SPAN_UNION_EQ
def MATROID_SPAN_INSERT_EQ : thm := BMatroidType.MATROID_SPAN_INSERT_EQ
def MATROID_SPAN_DELETE_EQ : thm := BMatroidType.MATROID_SPAN_DELETE_EQ
def MATROID_SPAN_TRANS : thm := BMatroidType.MATROID_SPAN_TRANS
def MATROID_SPAN_FINITARY_GEN : thm := BMatroidType.MATROID_SPAN_FINITARY_GEN
def MATROID_SPAN_FINITARY_MINIMAL : thm := BMatroidType.MATROID_SPAN_FINITARY_MINIMAL

-- LinearNotions
def matroid_spanning : thm := BLinearNotions.matroid_spanning
def matroid_independent : thm := BLinearNotions.matroid_independent
def matroid_basis : thm := BLinearNotions.matroid_basis
def matroid_dependent : thm := BLinearNotions.matroid_dependent
def MATROID_SPANNING_IMP_SUBSET : thm := BLinearNotions.MATROID_SPANNING_IMP_SUBSET
def MATROID_INDEPENDENT_IMP_SUBSET : thm := BLinearNotions.MATROID_INDEPENDENT_IMP_SUBSET
def MATROID_DEPENDENT_IMP_SUBSET : thm := BLinearNotions.MATROID_DEPENDENT_IMP_SUBSET
def MATROID_BASIS_IMP_SUBSET : thm := BLinearNotions.MATROID_BASIS_IMP_SUBSET
def MATROID_SPANNING_ALT : thm := BLinearNotions.MATROID_SPANNING_ALT
def MATROID_SPANNING_SET : thm := BLinearNotions.MATROID_SPANNING_SET
def MATROID_INDEPENDENT : thm := BLinearNotions.MATROID_INDEPENDENT
def MATROID_DEPENDENT : thm := BLinearNotions.MATROID_DEPENDENT

-- IndependentSets
def MATROID_INDEPENDENT_EMPTY : thm := BIndependentSets.MATROID_INDEPENDENT_EMPTY
def MATROID_INDEPENDENT_MONO : thm := BIndependentSets.MATROID_INDEPENDENT_MONO
def MATROID_INDEPENDENT_FINITARY : thm := BIndependentSets.MATROID_INDEPENDENT_FINITARY
def MATROID_DEPENDENT_FINITARY : thm := BIndependentSets.MATROID_DEPENDENT_FINITARY
def MATROID_INDEPENDENT_INSERT : thm := BIndependentSets.MATROID_INDEPENDENT_INSERT
def MATROID_SPAN_PSUBSET_INDEPENDENT : thm := BIndependentSets.MATROID_SPAN_PSUBSET_INDEPENDENT
def MATROID_SPAN_PSUBSET_EXPLICIT : thm := BIndependentSets.MATROID_SPAN_PSUBSET_EXPLICIT
def MATROID_SPANNING_SUBSET_INDEPENDENT : thm := BIndependentSets.MATROID_SPANNING_SUBSET_INDEPENDENT
def MATROID_SPANNING_PSUBSET_INDEPENDENT : thm := BIndependentSets.MATROID_SPANNING_PSUBSET_INDEPENDENT
def MATROID_MAXIMAL_INDEPENDENT_SUBSET_SPAN : thm := BIndependentSets.MATROID_MAXIMAL_INDEPENDENT_SUBSET_SPAN
def MATROID_BASIS_EQ_MAXIMAL_INDEPENDENT : thm := BIndependentSets.MATROID_BASIS_EQ_MAXIMAL_INDEPENDENT
def MATROID_BASIS_EQ_MINIMAL_SPANNING : thm := BIndependentSets.MATROID_BASIS_EQ_MINIMAL_SPANNING
def MATROID_INDEPENDENT_CHAIN : thm := BIndependentSets.MATROID_INDEPENDENT_CHAIN
def MATROID_SPAN_CHAIN : thm := BIndependentSets.MATROID_SPAN_CHAIN
def MATROID_INTERMEDIATE_SPAN : thm := BIndependentSets.MATROID_INTERMEDIATE_SPAN
def MATROID_INTERMEDIATE_BASIS : thm := BIndependentSets.MATROID_INTERMEDIATE_BASIS
def MATROID_INDEPENDENT_EXTENDS_TO_BASIS : thm := BIndependentSets.MATROID_INDEPENDENT_EXTENDS_TO_BASIS
def MATROID_BASIS_EXISTS : thm := BIndependentSets.MATROID_BASIS_EXISTS
def MATROID_SPANNING_CONTAINS_BASIS : thm := BIndependentSets.MATROID_SPANNING_CONTAINS_BASIS
def MATROID_SPAN_DEPENDENCE : thm := BIndependentSets.MATROID_SPAN_DEPENDENCE

-- SteinitzExchange
def MATROID_STEINITZ_EXCHANGE : thm := BSteinitzExchange.MATROID_STEINITZ_EXCHANGE
def MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE : thm := BSteinitzExchange.MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE
def MATROID_EQ_SPANS_FINITE : thm := BSteinitzExchange.MATROID_EQ_SPANS_FINITE
def MATROID_EQ_SPANS_SIZE : thm := BSteinitzExchange.MATROID_EQ_SPANS_SIZE
def MATROID_BASES_FINITE : thm := BSteinitzExchange.MATROID_BASES_FINITE
def MATROID_BASES_SIZE : thm := BSteinitzExchange.MATROID_BASES_SIZE
def MATROID_INDEPENDENT_CARD_LE_SPAN : thm := BSteinitzExchange.MATROID_INDEPENDENT_CARD_LE_SPAN
def MATROID_INDEPENDENT_CARD_LE_SPANNING : thm := BSteinitzExchange.MATROID_INDEPENDENT_CARD_LE_SPANNING
def MATROID_EQ_SPANS_CARD_EQ : thm := BSteinitzExchange.MATROID_EQ_SPANS_CARD_EQ
def MATROID_BASES_CARD_EQ : thm := BSteinitzExchange.MATROID_BASES_CARD_EQ
def MATROID_INDEPENDENT_SPANNING_FINITE : thm := BSteinitzExchange.MATROID_INDEPENDENT_SPANNING_FINITE
def MATROID_DEPENDENT_FINITARY_MINIMAL : thm := BSteinitzExchange.MATROID_DEPENDENT_FINITARY_MINIMAL
def MATROID_MINIMALLY_DEPENDENT : thm := BSteinitzExchange.MATROID_MINIMALLY_DEPENDENT
def MATROID_MINIMALLY_DEPENDENT_SUBSET : thm := BSteinitzExchange.MATROID_MINIMALLY_DEPENDENT_SUBSET

-- Subspaces
def matroid_subspace : thm := BSubspaces.matroid_subspace
def MATROID_SUBSPACE_IMP_SUBSET : thm := BSubspaces.MATROID_SUBSPACE_IMP_SUBSET
def MATROID_SUBSPACE_SET : thm := BSubspaces.MATROID_SUBSPACE_SET
def MATROID_SUBSPACE_SPAN : thm := BSubspaces.MATROID_SUBSPACE_SPAN
def MATROID_SUBSPACE : thm := BSubspaces.MATROID_SUBSPACE
def MATROID_SUBSPACE_INTERS : thm := BSubspaces.MATROID_SUBSPACE_INTERS
def MATROID_SUBSPACE_INTER : thm := BSubspaces.MATROID_SUBSPACE_INTER
def MATROID_SPAN_INTER_SPANS : thm := BSubspaces.MATROID_SPAN_INTER_SPANS
def MATROID_SUBSPACE_CHAIN : thm := BSubspaces.MATROID_SUBSPACE_CHAIN
def MATROID_SPAN_SUBSPACE : thm := BSubspaces.MATROID_SPAN_SUBSPACE
def MATROID_SPAN_EQ_SELF : thm := BSubspaces.MATROID_SPAN_EQ_SELF
def MATROID_SPAN_OF_SUBSPACE : thm := BSubspaces.MATROID_SPAN_OF_SUBSPACE
def MATROID_SPAN_SUBSET_SUBSPACE : thm := BSubspaces.MATROID_SPAN_SUBSET_SUBSPACE

-- Submatroids
def submatroid : thm := BSubmatroids.submatroid
def SUBMATROID_GEN : thm := BSubmatroids.SUBMATROID_GEN
def SUBMATROID : thm := BSubmatroids.SUBMATROID
def SUBMATROID_SPAN : thm := BSubmatroids.SUBMATROID_SPAN
def SUBMATROID_SUBSET : thm := BSubmatroids.SUBMATROID_SUBSET
def SUBMATROID_SET : thm := BSubmatroids.SUBMATROID_SET
def MATROID_INDEPENDENT_SUBMATROID : thm := BSubmatroids.MATROID_INDEPENDENT_SUBMATROID
def MATROID_SPANNING_SUBMATROID : thm := BSubmatroids.MATROID_SPANNING_SUBMATROID
def MATROID_SPANNING_SUBMATROID_SELF : thm := BSubmatroids.MATROID_SPANNING_SUBMATROID_SELF
def MATROID_BASIS_SUBMATROID : thm := BSubmatroids.MATROID_BASIS_SUBMATROID
def MATROID_SUBSET_CONTAINS_BASIS : thm := BSubmatroids.MATROID_SUBSET_CONTAINS_BASIS
def MATROID_STEINITZ_EXCHANGE_FINITE : thm := BSubmatroids.MATROID_STEINITZ_EXCHANGE_FINITE
def MATROID_STEINITZ_EXCHANGE_ALT : thm := BSubmatroids.MATROID_STEINITZ_EXCHANGE_ALT

-- FiniteDim
def matroid_finite_dimensional : thm := BFiniteDim.matroid_finite_dimensional
def matroid_dimension : thm := BFiniteDim.matroid_dimension
def matroid_finite_dim : thm := BFiniteDim.matroid_finite_dim
def matroid_dim : thm := BFiniteDim.matroid_dim
def MATROID_FINITE_DIM_IMP_SUBSET : thm := BFiniteDim.MATROID_FINITE_DIM_IMP_SUBSET
def MATROID_FINITE_DIM_SET : thm := BFiniteDim.MATROID_FINITE_DIM_SET
def MATROID_DIM_SET : thm := BFiniteDim.MATROID_DIM_SET
def MATROID_FINITE_DIM_SPAN_EQ : thm := BFiniteDim.MATROID_FINITE_DIM_SPAN_EQ
def MATROID_FINITE_DIM_SPAN : thm := BFiniteDim.MATROID_FINITE_DIM_SPAN
def MATROID_DIM_SPAN : thm := BFiniteDim.MATROID_DIM_SPAN
def MATROID_FINITE_DIMENSIONAL : thm := BFiniteDim.MATROID_FINITE_DIMENSIONAL
def MATROID_FINITE_DIMENSIONAL_BASIS : thm := BFiniteDim.MATROID_FINITE_DIMENSIONAL_BASIS
def MATROID_FINITE_DIMENSIONAL_CONTAINS_BASIS : thm := BFiniteDim.MATROID_FINITE_DIMENSIONAL_CONTAINS_BASIS
def MATROID_FINITE_DIMENSIONAL_ANY : thm := BFiniteDim.MATROID_FINITE_DIMENSIONAL_ANY
def MATROID_FINITE_DIM : thm := BFiniteDim.MATROID_FINITE_DIM
def MATROID_FINITE_DIM_SUBSET : thm := BFiniteDim.MATROID_FINITE_DIM_SUBSET
def MATROID_FINITE_DIM_BASIS : thm := BFiniteDim.MATROID_FINITE_DIM_BASIS
def MATROID_FINITE_DIMENSIONAL_DIM : thm := BFiniteDim.MATROID_FINITE_DIMENSIONAL_DIM
def FINITE_IMP_MATROID_FINITE_DIM : thm := BFiniteDim.FINITE_IMP_MATROID_FINITE_DIM
def MATROID_FINITE_DIM_FINITE : thm := BFiniteDim.MATROID_FINITE_DIM_FINITE
def MATROID_FINITE_DIM_EMPTY : thm := BFiniteDim.MATROID_FINITE_DIM_EMPTY
def MATROID_FINITE_DIM_MONO : thm := BFiniteDim.MATROID_FINITE_DIM_MONO
def MATROID_FINITE_DIM_UNION : thm := BFiniteDim.MATROID_FINITE_DIM_UNION
def MATROID_FINITE_DIM_INSERT : thm := BFiniteDim.MATROID_FINITE_DIM_INSERT

-- Dimension
def MATROID_DIMENSION_ALT : thm := BDimension.MATROID_DIMENSION_ALT
def MATROID_DIM_BASIS : thm := BDimension.MATROID_DIM_BASIS
def MATROID_DIM_ALT : thm := BDimension.MATROID_DIM_ALT
def MATROID_DIMENSION_UNIQUE : thm := BDimension.MATROID_DIMENSION_UNIQUE
def MATROID_DIMENSION_EQ_CARD : thm := BDimension.MATROID_DIMENSION_EQ_CARD
def MATROID_DIM_UNIQUE_ALT : thm := BDimension.MATROID_DIM_UNIQUE_ALT
def MATROID_DIM_UNIQUE : thm := BDimension.MATROID_DIM_UNIQUE
def MATROID_SPAN_DIM_EQ : thm := BDimension.MATROID_SPAN_DIM_EQ
def MATROID_SPAN_INSERT_REFL : thm := BDimension.MATROID_SPAN_INSERT_REFL
def MATROID_BASIS_EXISTS_DIMENSION : thm := BDimension.MATROID_BASIS_EXISTS_DIMENSION
def MATROID_BASIS_EXISTS_DIM : thm := BDimension.MATROID_BASIS_EXISTS_DIM
def MATROID_CONTAINS_BASIS_DIM : thm := BDimension.MATROID_CONTAINS_BASIS_DIM
def MATROID_DIM_EQ_CARD_GEN : thm := BDimension.MATROID_DIM_EQ_CARD_GEN
def MATROID_DIM_EQ_CARD : thm := BDimension.MATROID_DIM_EQ_CARD
def MATROID_DIMENSION_LE : thm := BDimension.MATROID_DIMENSION_LE
def MATROID_DIMENSION_FINITE_LE : thm := BDimension.MATROID_DIMENSION_FINITE_LE
def MATROID_DIM_LE : thm := BDimension.MATROID_DIM_LE
def MATROID_DIM_FINITE_LE : thm := BDimension.MATROID_DIM_FINITE_LE
def MATROID_DIM_LE_CARD_GEN : thm := BDimension.MATROID_DIM_LE_CARD_GEN
def MATROID_DIM_LE_CARD : thm := BDimension.MATROID_DIM_LE_CARD
def MATROID_DIMENSION_GE_FINITE_CARD : thm := BDimension.MATROID_DIMENSION_GE_FINITE_CARD
def MATROID_DIMENSION_GE : thm := BDimension.MATROID_DIMENSION_GE
def MATROID_DIMENSION_GE_CARD : thm := BDimension.MATROID_DIMENSION_GE_CARD
def MATROID_DIM_GE_FINITE_CARD : thm := BDimension.MATROID_DIM_GE_FINITE_CARD
def MATROID_DIM_GE : thm := BDimension.MATROID_DIM_GE
def MATROID_DIM_GE_CARD_GEN : thm := BDimension.MATROID_DIM_GE_CARD_GEN
def MATROID_DIM_GE_CARD : thm := BDimension.MATROID_DIM_GE_CARD
def FINITE_IMP_MATROID_FINITE_DIM_SPAN : thm := BDimension.FINITE_IMP_MATROID_FINITE_DIM_SPAN
def MATROID_INDEPENDENT_IMP_FINITE : thm := BDimension.MATROID_INDEPENDENT_IMP_FINITE

-- DimSpan
def MATROID_DIM_EQ_FINITE_CARD_EQ : thm := BDimSpan.MATROID_DIM_EQ_FINITE_CARD_EQ
def MATROID_DIM_GE_FINITE_CARD_EQ : thm := BDimSpan.MATROID_DIM_GE_FINITE_CARD_EQ
def MATROID_DIM_EMPTY : thm := BDimSpan.MATROID_DIM_EMPTY
def MATROID_DIM_INSERT : thm := BDimSpan.MATROID_DIM_INSERT
def MATROID_DIM_SUBSET : thm := BDimSpan.MATROID_DIM_SUBSET
def MATROID_DIM_SUBSET_ALT : thm := BDimSpan.MATROID_DIM_SUBSET_ALT
def MATROID_DIM_SPAN_SUBSET : thm := BDimSpan.MATROID_DIM_SPAN_SUBSET
def MATROID_DIM_SPAN_PSUBSET : thm := BDimSpan.MATROID_DIM_SPAN_PSUBSET
def MATROID_DIM_SPAN_EQ_GEN : thm := BDimSpan.MATROID_DIM_SPAN_EQ_GEN
def MATROID_DIM_SPAN_EQ : thm := BDimSpan.MATROID_DIM_SPAN_EQ
def MATROID_DIM_EQ_SPAN : thm := BDimSpan.MATROID_DIM_EQ_SPAN
def MATROID_CHOOSE_SUBSET : thm := BDimSpan.MATROID_CHOOSE_SUBSET
def MATROID_CHOOSE_SUBSPACE : thm := BDimSpan.MATROID_CHOOSE_SUBSPACE
def MATROID_LOWDIM_EXPAND_BASIS : thm := BDimSpan.MATROID_LOWDIM_EXPAND_BASIS
def MATROID_LOWDIM_EXPAND_DIMENSION : thm := BDimSpan.MATROID_LOWDIM_EXPAND_DIMENSION
/-- `needs "Library/matroids.ml"`: already done by importing this module. -/
def ensureMatroids : IO Unit := pure ()

end SessionLibrary.Matroids
