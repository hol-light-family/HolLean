/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/matroids.ml.                          -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Matroids.lean

  The `unsafe` half of the matroids.ml translation: it supplies HolLibrary.Matroids's
  dependencies from Session and SessionLibrary.Card, builds the bundles once, in order,
  and exports every name under its HOL Light name.  `ensureMatroids` is
  `needs "Library/matroids.ml"` (which first does `needs "Library/card.ml"`).

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Matroids.lean by tools/matroidsdiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.Matroids
import SessionLibrary.Card

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Matroids

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems matroids.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.Matroids.CoreThms1 where
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
unsafe def core2 (_ : Unit) : HolLibrary.Matroids.CoreThms2 where
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
unsafe def core3 (_ : Unit) : HolLibrary.Matroids.CoreThms3 where
/-- The core theorems matroids.ml uses. -/
unsafe def core4 (_ : Unit) : HolLibrary.Matroids.CoreThms4 where
-- @@CORE END

/-- What matroids.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Matroids.MatroidsDeps where
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
  core1 := core1 ()
  core2 := core2 ()
  core3 := core3 ()
  core4 := core4 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`, and MATCH_CONV's basic conversions, which HOL
    Light adds loading ind_types.ml), then card.ml, which matroids.ml needs. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      SessionLibrary.Card.ensureCard
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.Matroids: {name}"

/- The bundles, in file order; each forces the one before it. -/

-- @@BUNDLES BEGIN
initialize theMatroidType : IO.Ref (Option HolLibrary.Matroids.MatroidType) ← IO.mkRef none
unsafe def BMatroidType : HolLibrary.Matroids.MatroidType :=
  cached theMatroidType "setupMatroidType" fun _ => do
    (HolLibrary.Matroids.setupMatroidType (deps ())).run

initialize theLinearNotions : IO.Ref (Option HolLibrary.Matroids.LinearNotions) ← IO.mkRef none
unsafe def BLinearNotions : HolLibrary.Matroids.LinearNotions :=
  cached theLinearNotions "setupLinearNotions" fun _ => do
    let _ ← IO.mkRef BMatroidType.matroid_tybij
    (HolLibrary.Matroids.setupLinearNotions (deps ()) BMatroidType).run

initialize theIndependentSets : IO.Ref (Option HolLibrary.Matroids.IndependentSets) ← IO.mkRef none
unsafe def BIndependentSets : HolLibrary.Matroids.IndependentSets :=
  cached theIndependentSets "setupIndependentSets" fun _ => do
    let _ ← IO.mkRef BLinearNotions.matroid_spanning
    (HolLibrary.Matroids.setupIndependentSets (deps ()) BMatroidType BLinearNotions).run

initialize theSteinitzExchange : IO.Ref (Option HolLibrary.Matroids.SteinitzExchange) ← IO.mkRef none
unsafe def BSteinitzExchange : HolLibrary.Matroids.SteinitzExchange :=
  cached theSteinitzExchange "setupSteinitzExchange" fun _ => do
    let _ ← IO.mkRef BIndependentSets.MATROID_INDEPENDENT_EMPTY
    (HolLibrary.Matroids.setupSteinitzExchange (deps ()) BMatroidType BLinearNotions BIndependentSets).run

initialize theSubspaces : IO.Ref (Option HolLibrary.Matroids.Subspaces) ← IO.mkRef none
unsafe def BSubspaces : HolLibrary.Matroids.Subspaces :=
  cached theSubspaces "setupSubspaces" fun _ => do
    let _ ← IO.mkRef BSteinitzExchange.MATROID_STEINITZ_EXCHANGE
    (HolLibrary.Matroids.setupSubspaces (deps ()) BMatroidType BIndependentSets).run

initialize theSubmatroids : IO.Ref (Option HolLibrary.Matroids.Submatroids) ← IO.mkRef none
unsafe def BSubmatroids : HolLibrary.Matroids.Submatroids :=
  cached theSubmatroids "setupSubmatroids" fun _ => do
    let _ ← IO.mkRef BSubspaces.matroid_subspace
    (HolLibrary.Matroids.setupSubmatroids (deps ()) BMatroidType BLinearNotions BIndependentSets BSteinitzExchange BSubspaces).run

initialize theFiniteDim : IO.Ref (Option HolLibrary.Matroids.FiniteDim) ← IO.mkRef none
unsafe def BFiniteDim : HolLibrary.Matroids.FiniteDim :=
  cached theFiniteDim "setupFiniteDim" fun _ => do
    let _ ← IO.mkRef BSubmatroids.submatroid
    (HolLibrary.Matroids.setupFiniteDim (deps ()) BMatroidType BLinearNotions BIndependentSets BSteinitzExchange BSubmatroids).run

initialize theDimension : IO.Ref (Option HolLibrary.Matroids.Dimension) ← IO.mkRef none
unsafe def BDimension : HolLibrary.Matroids.Dimension :=
  cached theDimension "setupDimension" fun _ => do
    let _ ← IO.mkRef BFiniteDim.matroid_finite_dimensional
    (HolLibrary.Matroids.setupDimension (deps ()) BMatroidType BLinearNotions BIndependentSets BSteinitzExchange BSubmatroids BFiniteDim).run

initialize theDimSpan : IO.Ref (Option HolLibrary.Matroids.DimSpan) ← IO.mkRef none
unsafe def BDimSpan : HolLibrary.Matroids.DimSpan :=
  cached theDimSpan "setupDimSpan" fun _ => do
    let _ ← IO.mkRef BDimension.MATROID_DIMENSION_ALT
    (HolLibrary.Matroids.setupDimSpan (deps ()) BMatroidType BLinearNotions BIndependentSets BSubspaces BSubmatroids BFiniteDim BDimension).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- MatroidType
unsafe def matroid_tybij : thm := BMatroidType.matroid_tybij
unsafe def matroid_set : thm := BMatroidType.matroid_set
unsafe def matroid_span : thm := BMatroidType.matroid_span
unsafe def MATROID_SPAN_SUBSET : thm := BMatroidType.MATROID_SPAN_SUBSET
unsafe def MATROID_SPAN_SUPERSET : thm := BMatroidType.MATROID_SPAN_SUPERSET
unsafe def MATROID_SPAN_MONO : thm := BMatroidType.MATROID_SPAN_MONO
unsafe def MATROID_SPAN_SPAN : thm := BMatroidType.MATROID_SPAN_SPAN
unsafe def MATROID_SPAN_FINITARY : thm := BMatroidType.MATROID_SPAN_FINITARY
unsafe def MATROID_SPAN_EXCHANGE : thm := BMatroidType.MATROID_SPAN_EXCHANGE
unsafe def MATROID_SPAN_INC : thm := BMatroidType.MATROID_SPAN_INC
unsafe def SUBSET_MATROID_SPAN : thm := BMatroidType.SUBSET_MATROID_SPAN
unsafe def MATROID_SPAN_MINIMAL : thm := BMatroidType.MATROID_SPAN_MINIMAL
unsafe def MATROID_SPAN_SET : thm := BMatroidType.MATROID_SPAN_SET
unsafe def MATROID_SPAN_EQ : thm := BMatroidType.MATROID_SPAN_EQ
unsafe def MATROID_SPAN_EQ_SET : thm := BMatroidType.MATROID_SPAN_EQ_SET
unsafe def MATROID_SPAN_SUBSET_EQ : thm := BMatroidType.MATROID_SPAN_SUBSET_EQ
unsafe def MATROID_SPAN_INTER_SUBSET : thm := BMatroidType.MATROID_SPAN_INTER_SUBSET
unsafe def MATROID_SPAN_UNION : thm := BMatroidType.MATROID_SPAN_UNION
unsafe def MATROID_SPAN_UNION_LEFT : thm := BMatroidType.MATROID_SPAN_UNION_LEFT
unsafe def MATROID_SPAN_UNION_RIGHT : thm := BMatroidType.MATROID_SPAN_UNION_RIGHT
unsafe def MATROID_SPAN_UNION_SUBSET : thm := BMatroidType.MATROID_SPAN_UNION_SUBSET
unsafe def MATROID_SPAN_EXCHANGE_DELETE : thm := BMatroidType.MATROID_SPAN_EXCHANGE_DELETE
unsafe def MATROID_SPAN_UNION_EQ : thm := BMatroidType.MATROID_SPAN_UNION_EQ
unsafe def MATROID_SPAN_INSERT_EQ : thm := BMatroidType.MATROID_SPAN_INSERT_EQ
unsafe def MATROID_SPAN_DELETE_EQ : thm := BMatroidType.MATROID_SPAN_DELETE_EQ
unsafe def MATROID_SPAN_TRANS : thm := BMatroidType.MATROID_SPAN_TRANS
unsafe def MATROID_SPAN_FINITARY_GEN : thm := BMatroidType.MATROID_SPAN_FINITARY_GEN
unsafe def MATROID_SPAN_FINITARY_MINIMAL : thm := BMatroidType.MATROID_SPAN_FINITARY_MINIMAL

-- LinearNotions
unsafe def matroid_spanning : thm := BLinearNotions.matroid_spanning
unsafe def matroid_independent : thm := BLinearNotions.matroid_independent
unsafe def matroid_basis : thm := BLinearNotions.matroid_basis
unsafe def matroid_dependent : thm := BLinearNotions.matroid_dependent
unsafe def MATROID_SPANNING_IMP_SUBSET : thm := BLinearNotions.MATROID_SPANNING_IMP_SUBSET
unsafe def MATROID_INDEPENDENT_IMP_SUBSET : thm := BLinearNotions.MATROID_INDEPENDENT_IMP_SUBSET
unsafe def MATROID_DEPENDENT_IMP_SUBSET : thm := BLinearNotions.MATROID_DEPENDENT_IMP_SUBSET
unsafe def MATROID_BASIS_IMP_SUBSET : thm := BLinearNotions.MATROID_BASIS_IMP_SUBSET
unsafe def MATROID_SPANNING_ALT : thm := BLinearNotions.MATROID_SPANNING_ALT
unsafe def MATROID_SPANNING_SET : thm := BLinearNotions.MATROID_SPANNING_SET
unsafe def MATROID_INDEPENDENT : thm := BLinearNotions.MATROID_INDEPENDENT
unsafe def MATROID_DEPENDENT : thm := BLinearNotions.MATROID_DEPENDENT

-- IndependentSets
unsafe def MATROID_INDEPENDENT_EMPTY : thm := BIndependentSets.MATROID_INDEPENDENT_EMPTY
unsafe def MATROID_INDEPENDENT_MONO : thm := BIndependentSets.MATROID_INDEPENDENT_MONO
unsafe def MATROID_INDEPENDENT_FINITARY : thm := BIndependentSets.MATROID_INDEPENDENT_FINITARY
unsafe def MATROID_DEPENDENT_FINITARY : thm := BIndependentSets.MATROID_DEPENDENT_FINITARY
unsafe def MATROID_INDEPENDENT_INSERT : thm := BIndependentSets.MATROID_INDEPENDENT_INSERT
unsafe def MATROID_SPAN_PSUBSET_INDEPENDENT : thm := BIndependentSets.MATROID_SPAN_PSUBSET_INDEPENDENT
unsafe def MATROID_SPAN_PSUBSET_EXPLICIT : thm := BIndependentSets.MATROID_SPAN_PSUBSET_EXPLICIT
unsafe def MATROID_SPANNING_SUBSET_INDEPENDENT : thm := BIndependentSets.MATROID_SPANNING_SUBSET_INDEPENDENT
unsafe def MATROID_SPANNING_PSUBSET_INDEPENDENT : thm := BIndependentSets.MATROID_SPANNING_PSUBSET_INDEPENDENT
unsafe def MATROID_MAXIMAL_INDEPENDENT_SUBSET_SPAN : thm := BIndependentSets.MATROID_MAXIMAL_INDEPENDENT_SUBSET_SPAN
unsafe def MATROID_BASIS_EQ_MAXIMAL_INDEPENDENT : thm := BIndependentSets.MATROID_BASIS_EQ_MAXIMAL_INDEPENDENT
unsafe def MATROID_BASIS_EQ_MINIMAL_SPANNING : thm := BIndependentSets.MATROID_BASIS_EQ_MINIMAL_SPANNING
unsafe def MATROID_INDEPENDENT_CHAIN : thm := BIndependentSets.MATROID_INDEPENDENT_CHAIN
unsafe def MATROID_SPAN_CHAIN : thm := BIndependentSets.MATROID_SPAN_CHAIN
unsafe def MATROID_INTERMEDIATE_SPAN : thm := BIndependentSets.MATROID_INTERMEDIATE_SPAN
unsafe def MATROID_INTERMEDIATE_BASIS : thm := BIndependentSets.MATROID_INTERMEDIATE_BASIS
unsafe def MATROID_INDEPENDENT_EXTENDS_TO_BASIS : thm := BIndependentSets.MATROID_INDEPENDENT_EXTENDS_TO_BASIS
unsafe def MATROID_BASIS_EXISTS : thm := BIndependentSets.MATROID_BASIS_EXISTS
unsafe def MATROID_SPANNING_CONTAINS_BASIS : thm := BIndependentSets.MATROID_SPANNING_CONTAINS_BASIS
unsafe def MATROID_SPAN_DEPENDENCE : thm := BIndependentSets.MATROID_SPAN_DEPENDENCE

-- SteinitzExchange
unsafe def MATROID_STEINITZ_EXCHANGE : thm := BSteinitzExchange.MATROID_STEINITZ_EXCHANGE
unsafe def MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE : thm := BSteinitzExchange.MATROID_INDEPENDENT_CARD_LE_SPAN_FINITE
unsafe def MATROID_EQ_SPANS_FINITE : thm := BSteinitzExchange.MATROID_EQ_SPANS_FINITE
unsafe def MATROID_EQ_SPANS_SIZE : thm := BSteinitzExchange.MATROID_EQ_SPANS_SIZE
unsafe def MATROID_BASES_FINITE : thm := BSteinitzExchange.MATROID_BASES_FINITE
unsafe def MATROID_BASES_SIZE : thm := BSteinitzExchange.MATROID_BASES_SIZE
unsafe def MATROID_INDEPENDENT_CARD_LE_SPAN : thm := BSteinitzExchange.MATROID_INDEPENDENT_CARD_LE_SPAN
unsafe def MATROID_INDEPENDENT_CARD_LE_SPANNING : thm := BSteinitzExchange.MATROID_INDEPENDENT_CARD_LE_SPANNING
unsafe def MATROID_EQ_SPANS_CARD_EQ : thm := BSteinitzExchange.MATROID_EQ_SPANS_CARD_EQ
unsafe def MATROID_BASES_CARD_EQ : thm := BSteinitzExchange.MATROID_BASES_CARD_EQ
unsafe def MATROID_INDEPENDENT_SPANNING_FINITE : thm := BSteinitzExchange.MATROID_INDEPENDENT_SPANNING_FINITE
unsafe def MATROID_DEPENDENT_FINITARY_MINIMAL : thm := BSteinitzExchange.MATROID_DEPENDENT_FINITARY_MINIMAL
unsafe def MATROID_MINIMALLY_DEPENDENT : thm := BSteinitzExchange.MATROID_MINIMALLY_DEPENDENT
unsafe def MATROID_MINIMALLY_DEPENDENT_SUBSET : thm := BSteinitzExchange.MATROID_MINIMALLY_DEPENDENT_SUBSET

-- Subspaces
unsafe def matroid_subspace : thm := BSubspaces.matroid_subspace
unsafe def MATROID_SUBSPACE_IMP_SUBSET : thm := BSubspaces.MATROID_SUBSPACE_IMP_SUBSET
unsafe def MATROID_SUBSPACE_SET : thm := BSubspaces.MATROID_SUBSPACE_SET
unsafe def MATROID_SUBSPACE_SPAN : thm := BSubspaces.MATROID_SUBSPACE_SPAN
unsafe def MATROID_SUBSPACE : thm := BSubspaces.MATROID_SUBSPACE
unsafe def MATROID_SUBSPACE_INTERS : thm := BSubspaces.MATROID_SUBSPACE_INTERS
unsafe def MATROID_SUBSPACE_INTER : thm := BSubspaces.MATROID_SUBSPACE_INTER
unsafe def MATROID_SPAN_INTER_SPANS : thm := BSubspaces.MATROID_SPAN_INTER_SPANS
unsafe def MATROID_SUBSPACE_CHAIN : thm := BSubspaces.MATROID_SUBSPACE_CHAIN
unsafe def MATROID_SPAN_SUBSPACE : thm := BSubspaces.MATROID_SPAN_SUBSPACE
unsafe def MATROID_SPAN_EQ_SELF : thm := BSubspaces.MATROID_SPAN_EQ_SELF
unsafe def MATROID_SPAN_OF_SUBSPACE : thm := BSubspaces.MATROID_SPAN_OF_SUBSPACE
unsafe def MATROID_SPAN_SUBSET_SUBSPACE : thm := BSubspaces.MATROID_SPAN_SUBSET_SUBSPACE

-- Submatroids
unsafe def submatroid : thm := BSubmatroids.submatroid
unsafe def SUBMATROID_GEN : thm := BSubmatroids.SUBMATROID_GEN
unsafe def SUBMATROID : thm := BSubmatroids.SUBMATROID
unsafe def SUBMATROID_SPAN : thm := BSubmatroids.SUBMATROID_SPAN
unsafe def SUBMATROID_SUBSET : thm := BSubmatroids.SUBMATROID_SUBSET
unsafe def SUBMATROID_SET : thm := BSubmatroids.SUBMATROID_SET
unsafe def MATROID_INDEPENDENT_SUBMATROID : thm := BSubmatroids.MATROID_INDEPENDENT_SUBMATROID
unsafe def MATROID_SPANNING_SUBMATROID : thm := BSubmatroids.MATROID_SPANNING_SUBMATROID
unsafe def MATROID_SPANNING_SUBMATROID_SELF : thm := BSubmatroids.MATROID_SPANNING_SUBMATROID_SELF
unsafe def MATROID_BASIS_SUBMATROID : thm := BSubmatroids.MATROID_BASIS_SUBMATROID
unsafe def MATROID_SUBSET_CONTAINS_BASIS : thm := BSubmatroids.MATROID_SUBSET_CONTAINS_BASIS
unsafe def MATROID_STEINITZ_EXCHANGE_FINITE : thm := BSubmatroids.MATROID_STEINITZ_EXCHANGE_FINITE
unsafe def MATROID_STEINITZ_EXCHANGE_ALT : thm := BSubmatroids.MATROID_STEINITZ_EXCHANGE_ALT

-- FiniteDim
unsafe def matroid_finite_dimensional : thm := BFiniteDim.matroid_finite_dimensional
unsafe def matroid_dimension : thm := BFiniteDim.matroid_dimension
unsafe def matroid_finite_dim : thm := BFiniteDim.matroid_finite_dim
unsafe def matroid_dim : thm := BFiniteDim.matroid_dim
unsafe def MATROID_FINITE_DIM_IMP_SUBSET : thm := BFiniteDim.MATROID_FINITE_DIM_IMP_SUBSET
unsafe def MATROID_FINITE_DIM_SET : thm := BFiniteDim.MATROID_FINITE_DIM_SET
unsafe def MATROID_DIM_SET : thm := BFiniteDim.MATROID_DIM_SET
unsafe def MATROID_FINITE_DIM_SPAN_EQ : thm := BFiniteDim.MATROID_FINITE_DIM_SPAN_EQ
unsafe def MATROID_FINITE_DIM_SPAN : thm := BFiniteDim.MATROID_FINITE_DIM_SPAN
unsafe def MATROID_DIM_SPAN : thm := BFiniteDim.MATROID_DIM_SPAN
unsafe def MATROID_FINITE_DIMENSIONAL : thm := BFiniteDim.MATROID_FINITE_DIMENSIONAL
unsafe def MATROID_FINITE_DIMENSIONAL_BASIS : thm := BFiniteDim.MATROID_FINITE_DIMENSIONAL_BASIS
unsafe def MATROID_FINITE_DIMENSIONAL_CONTAINS_BASIS : thm := BFiniteDim.MATROID_FINITE_DIMENSIONAL_CONTAINS_BASIS
unsafe def MATROID_FINITE_DIMENSIONAL_ANY : thm := BFiniteDim.MATROID_FINITE_DIMENSIONAL_ANY
unsafe def MATROID_FINITE_DIM : thm := BFiniteDim.MATROID_FINITE_DIM
unsafe def MATROID_FINITE_DIM_SUBSET : thm := BFiniteDim.MATROID_FINITE_DIM_SUBSET
unsafe def MATROID_FINITE_DIM_BASIS : thm := BFiniteDim.MATROID_FINITE_DIM_BASIS
unsafe def MATROID_FINITE_DIMENSIONAL_DIM : thm := BFiniteDim.MATROID_FINITE_DIMENSIONAL_DIM
unsafe def FINITE_IMP_MATROID_FINITE_DIM : thm := BFiniteDim.FINITE_IMP_MATROID_FINITE_DIM
unsafe def MATROID_FINITE_DIM_FINITE : thm := BFiniteDim.MATROID_FINITE_DIM_FINITE
unsafe def MATROID_FINITE_DIM_EMPTY : thm := BFiniteDim.MATROID_FINITE_DIM_EMPTY
unsafe def MATROID_FINITE_DIM_MONO : thm := BFiniteDim.MATROID_FINITE_DIM_MONO
unsafe def MATROID_FINITE_DIM_UNION : thm := BFiniteDim.MATROID_FINITE_DIM_UNION
unsafe def MATROID_FINITE_DIM_INSERT : thm := BFiniteDim.MATROID_FINITE_DIM_INSERT

-- Dimension
unsafe def MATROID_DIMENSION_ALT : thm := BDimension.MATROID_DIMENSION_ALT
unsafe def MATROID_DIM_BASIS : thm := BDimension.MATROID_DIM_BASIS
unsafe def MATROID_DIM_ALT : thm := BDimension.MATROID_DIM_ALT
unsafe def MATROID_DIMENSION_UNIQUE : thm := BDimension.MATROID_DIMENSION_UNIQUE
unsafe def MATROID_DIMENSION_EQ_CARD : thm := BDimension.MATROID_DIMENSION_EQ_CARD
unsafe def MATROID_DIM_UNIQUE_ALT : thm := BDimension.MATROID_DIM_UNIQUE_ALT
unsafe def MATROID_DIM_UNIQUE : thm := BDimension.MATROID_DIM_UNIQUE
unsafe def MATROID_SPAN_DIM_EQ : thm := BDimension.MATROID_SPAN_DIM_EQ
unsafe def MATROID_SPAN_INSERT_REFL : thm := BDimension.MATROID_SPAN_INSERT_REFL
unsafe def MATROID_BASIS_EXISTS_DIMENSION : thm := BDimension.MATROID_BASIS_EXISTS_DIMENSION
unsafe def MATROID_BASIS_EXISTS_DIM : thm := BDimension.MATROID_BASIS_EXISTS_DIM
unsafe def MATROID_CONTAINS_BASIS_DIM : thm := BDimension.MATROID_CONTAINS_BASIS_DIM
unsafe def MATROID_DIM_EQ_CARD_GEN : thm := BDimension.MATROID_DIM_EQ_CARD_GEN
unsafe def MATROID_DIM_EQ_CARD : thm := BDimension.MATROID_DIM_EQ_CARD
unsafe def MATROID_DIMENSION_LE : thm := BDimension.MATROID_DIMENSION_LE
unsafe def MATROID_DIMENSION_FINITE_LE : thm := BDimension.MATROID_DIMENSION_FINITE_LE
unsafe def MATROID_DIM_LE : thm := BDimension.MATROID_DIM_LE
unsafe def MATROID_DIM_FINITE_LE : thm := BDimension.MATROID_DIM_FINITE_LE
unsafe def MATROID_DIM_LE_CARD_GEN : thm := BDimension.MATROID_DIM_LE_CARD_GEN
unsafe def MATROID_DIM_LE_CARD : thm := BDimension.MATROID_DIM_LE_CARD
unsafe def MATROID_DIMENSION_GE_FINITE_CARD : thm := BDimension.MATROID_DIMENSION_GE_FINITE_CARD
unsafe def MATROID_DIMENSION_GE : thm := BDimension.MATROID_DIMENSION_GE
unsafe def MATROID_DIMENSION_GE_CARD : thm := BDimension.MATROID_DIMENSION_GE_CARD
unsafe def MATROID_DIM_GE_FINITE_CARD : thm := BDimension.MATROID_DIM_GE_FINITE_CARD
unsafe def MATROID_DIM_GE : thm := BDimension.MATROID_DIM_GE
unsafe def MATROID_DIM_GE_CARD_GEN : thm := BDimension.MATROID_DIM_GE_CARD_GEN
unsafe def MATROID_DIM_GE_CARD : thm := BDimension.MATROID_DIM_GE_CARD
unsafe def FINITE_IMP_MATROID_FINITE_DIM_SPAN : thm := BDimension.FINITE_IMP_MATROID_FINITE_DIM_SPAN
unsafe def MATROID_INDEPENDENT_IMP_FINITE : thm := BDimension.MATROID_INDEPENDENT_IMP_FINITE

-- DimSpan
unsafe def MATROID_DIM_EQ_FINITE_CARD_EQ : thm := BDimSpan.MATROID_DIM_EQ_FINITE_CARD_EQ
unsafe def MATROID_DIM_GE_FINITE_CARD_EQ : thm := BDimSpan.MATROID_DIM_GE_FINITE_CARD_EQ
unsafe def MATROID_DIM_EMPTY : thm := BDimSpan.MATROID_DIM_EMPTY
unsafe def MATROID_DIM_INSERT : thm := BDimSpan.MATROID_DIM_INSERT
unsafe def MATROID_DIM_SUBSET : thm := BDimSpan.MATROID_DIM_SUBSET
unsafe def MATROID_DIM_SUBSET_ALT : thm := BDimSpan.MATROID_DIM_SUBSET_ALT
unsafe def MATROID_DIM_SPAN_SUBSET : thm := BDimSpan.MATROID_DIM_SPAN_SUBSET
unsafe def MATROID_DIM_SPAN_PSUBSET : thm := BDimSpan.MATROID_DIM_SPAN_PSUBSET
unsafe def MATROID_DIM_SPAN_EQ_GEN : thm := BDimSpan.MATROID_DIM_SPAN_EQ_GEN
unsafe def MATROID_DIM_SPAN_EQ : thm := BDimSpan.MATROID_DIM_SPAN_EQ
unsafe def MATROID_DIM_EQ_SPAN : thm := BDimSpan.MATROID_DIM_EQ_SPAN
unsafe def MATROID_CHOOSE_SUBSET : thm := BDimSpan.MATROID_CHOOSE_SUBSET
unsafe def MATROID_CHOOSE_SUBSPACE : thm := BDimSpan.MATROID_CHOOSE_SUBSPACE
unsafe def MATROID_LOWDIM_EXPAND_BASIS : thm := BDimSpan.MATROID_LOWDIM_EXPAND_BASIS
unsafe def MATROID_LOWDIM_EXPAND_DIMENSION : thm := BDimSpan.MATROID_LOWDIM_EXPAND_DIMENSION
-- @@EXPORTS END

/-- `needs "Library/matroids.ml"`: build the bundles, in order. -/
unsafe def ensureMatroids : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BMatroidType.matroid_tybij
  let _ ← IO.mkRef BLinearNotions.matroid_spanning
  let _ ← IO.mkRef BIndependentSets.MATROID_INDEPENDENT_EMPTY
  let _ ← IO.mkRef BSteinitzExchange.MATROID_STEINITZ_EXCHANGE
  let _ ← IO.mkRef BSubspaces.matroid_subspace
  let _ ← IO.mkRef BSubmatroids.submatroid
  let _ ← IO.mkRef BFiniteDim.matroid_finite_dimensional
  let _ ← IO.mkRef BDimension.MATROID_DIMENSION_ALT
  let _ ← IO.mkRef BDimSpan.MATROID_DIM_EQ_FINITE_CARD_EQ
  -- @@ENSURE END
  pure ()

end SessionLibrary.Matroids
