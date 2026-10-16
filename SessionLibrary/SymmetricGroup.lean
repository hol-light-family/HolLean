/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/symmetricgroup.ml.                    -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/SymmetricGroup.lean

  The `unsafe` half of the symmetricgroup.ml translation: it supplies HolLibrary.SymmetricGroup's
  dependencies from Session and SessionLibrary.Permutations, SessionLibrary.GroupTheory, builds the bundles once, in order,
  and exports every name under its HOL Light name.  `ensureSymmetricGroup` is
  `needs "Library/symmetricgroup.ml"` (which first does `needs "Library/permutations.ml"`, `needs "Library/grouptheory.ml"`).

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/SymmetricGroup.lean by tools/symmetricgroupdiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.SymmetricGroup
import SessionLibrary.Permutations
import SessionLibrary.GroupTheory

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.SymmetricGroup

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems symmetric_group.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.SymmetricGroup.CoreThms1 where
  ABELIAN_QUOTIENT_COMMUTATOR := SessionLibrary.GroupTheory.«ABELIAN_QUOTIENT_COMMUTATOR»
  ADD1 := Session.ADD1
  AND_FORALL_THM := Session.AND_FORALL_THM
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_DELETE := Session.CARD_DELETE
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_LE_2 := Session.«CARD_LE_2»
  CARD_LE_3 := Session.«CARD_LE_3»
  CARD_LE_4 := Session.«CARD_LE_4»
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CARD_PERMUTATIONS := SessionLibrary.Permutations.«CARD_PERMUTATIONS»
  CARD_SING := Session.CARD_SING
  CARD_SUBSET := Session.CARD_SUBSET
  CARD_SUBSET_EQ := Session.CARD_SUBSET_EQ
  CARRIER_SUBGROUP_GENERATED_SUBGROUP := SessionLibrary.GroupTheory.«CARRIER_SUBGROUP_GENERATED_SUBGROUP»
  CARRIER_SUBGROUP_OF := SessionLibrary.GroupTheory.«CARRIER_SUBGROUP_OF»
  CAUCHY_GROUP_THEOREM := SessionLibrary.GroupTheory.«CAUCHY_GROUP_THEOREM»
  CONJ_ASSOC := Session.CONJ_ASSOC
  COPRIME_GCD := SessionLibrary.Prime.«COPRIME_GCD»
  DIVIDES_FACT_PRIME := SessionLibrary.Prime.«DIVIDES_FACT_PRIME»
  DIVIDES_LE := Session.DIVIDES_LE
  DIVIDES_REFL := SessionLibrary.Prime.«DIVIDES_REFL»
  DIV_1 := Session.DIV_1
  EQ_TRANS := Session.EQ_TRANS
  EXTENSION := Session.EXTENSION
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_INSERT := Session.FINITE_INSERT
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_PERMUTATIONS := SessionLibrary.Permutations.«FINITE_PERMUTATIONS»
  FINITE_SUBSET := Session.FINITE_SUBSET
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FUN_EQ_THM := Session.FUN_EQ_THM
  GROUP_ACTION_FROM_SUBGROUP := SessionLibrary.GroupTheory.«GROUP_ACTION_FROM_SUBGROUP»
  GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_DIVIDES_GROUP_ORDER»
  GROUP_ELEMENT_ORDER_EQ_1 := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_EQ_1»
  GROUP_ELEMENT_ORDER_ID := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_ID»
  GROUP_ELEMENT_ORDER_POW_GEN := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_POW_GEN»
  GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«GROUP_ELEMENT_ORDER_SUBGROUP_GENERATED»
  GROUP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_HOMOMORPHISM»
  GROUP_ID := SessionLibrary.GroupTheory.«GROUP_ID»
  GROUP_INV := SessionLibrary.GroupTheory.«GROUP_INV»
  GROUP_ISOMORPHISM_ONTO_IMAGE := SessionLibrary.GroupTheory.«GROUP_ISOMORPHISM_ONTO_IMAGE»
  GROUP_MONOMORPHISM_ALT := SessionLibrary.GroupTheory.«GROUP_MONOMORPHISM_ALT»
  GROUP_MONOMORPHISM_IMP_HOMOMORPHISM := SessionLibrary.GroupTheory.«GROUP_MONOMORPHISM_IMP_HOMOMORPHISM»
  GROUP_MUL := SessionLibrary.GroupTheory.«GROUP_MUL»
  GROUP_MUL_ASSOC := SessionLibrary.GroupTheory.«GROUP_MUL_ASSOC»
  GROUP_MUL_RID := SessionLibrary.GroupTheory.«GROUP_MUL_RID»
  GROUP_ORBIT_SUBSET := SessionLibrary.GroupTheory.«GROUP_ORBIT_SUBSET»
  GROUP_POW := SessionLibrary.GroupTheory.«GROUP_POW»
  GROUP_POW_1 := SessionLibrary.GroupTheory.«GROUP_POW_1»
  GROUP_POW_ADD := SessionLibrary.GroupTheory.«GROUP_POW_ADD»
  GROUP_POW_EQ_ID := SessionLibrary.GroupTheory.«GROUP_POW_EQ_ID»
  IMP_CONJ := Session.IMP_CONJ
  INTER_SUBSET := Session.INTER_SUBSET
  IN_DELETE := Session.IN_DELETE
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_GROUP_ORBIT := SessionLibrary.GroupTheory.«IN_GROUP_ORBIT»
  IN_IMAGE := Session.IN_IMAGE
  IN_INTER := Session.IN_INTER
  IN_SING := Session.IN_SING
  IN_SUBGROUP_CONJUGATION := SessionLibrary.GroupTheory.«IN_SUBGROUP_CONJUGATION»
  IN_SUBGROUP_INV := SessionLibrary.GroupTheory.«IN_SUBGROUP_INV»
  IN_SUBGROUP_MUL := SessionLibrary.GroupTheory.«IN_SUBGROUP_MUL»
  IN_SUBGROUP_POW := SessionLibrary.GroupTheory.«IN_SUBGROUP_POW»
  ISOMORPHIC_GROUP_SYM := SessionLibrary.GroupTheory.«ISOMORPHIC_GROUP_SYM»
  I_O_ID := Session.I_O_ID
  I_THM := Session.I_THM
  LE_REFL := Session.LE_REFL
/-- The core theorems symmetric_group.ml uses. -/
unsafe def core2 (_ : Unit) : HolLibrary.SymmetricGroup.CoreThms2 where
  LT_NZ := Session.LT_NZ
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MULT_SYM := Session.MULT_SYM
  NORMAL_SUBGROUP_IMP_SUBGROUP := SessionLibrary.GroupTheory.«NORMAL_SUBGROUP_IMP_SUBGROUP»
  ONE := Session.ONE
  ORBIT_STABILIZER_MUL := SessionLibrary.GroupTheory.«ORBIT_STABILIZER_MUL»
  PAIR_EQ := Session.PAIR_EQ
  PERMUTES_COMPOSE := SessionLibrary.Permutations.«PERMUTES_COMPOSE»
  PERMUTES_I := SessionLibrary.Permutations.«PERMUTES_I»
  PERMUTES_INDUCT_STRONG := SessionLibrary.Permutations.«PERMUTES_INDUCT_STRONG»
  PERMUTES_INJECTIVE := SessionLibrary.Permutations.«PERMUTES_INJECTIVE»
  PERMUTES_INVERSE := SessionLibrary.Permutations.«PERMUTES_INVERSE»
  PERMUTES_INVERSES_o := SessionLibrary.Permutations.«PERMUTES_INVERSES_o»
  PERMUTES_INVERSE_FUNCTION := SessionLibrary.Permutations.«PERMUTES_INVERSE_FUNCTION»
  PERMUTES_IN_IMAGE := SessionLibrary.Permutations.«PERMUTES_IN_IMAGE»
  PERMUTES_SUBSET := SessionLibrary.Permutations.«PERMUTES_SUBSET»
  PERMUTES_SUPERSET := SessionLibrary.Permutations.«PERMUTES_SUPERSET»
  PERMUTES_SWAP := SessionLibrary.Permutations.«PERMUTES_SWAP»
  PERMUTES_THREE_CYCLE := SessionLibrary.Permutations.«PERMUTES_THREE_CYCLE»
  PRIME_0 := SessionLibrary.Prime.«PRIME_0»
  PRIME_1 := SessionLibrary.Prime.«PRIME_1»
  PRIME_COPRIME_EQ := SessionLibrary.Prime.«PRIME_COPRIME_EQ»
  RESTRICT_COMPOSE := SessionLibrary.Permutations.«RESTRICT_COMPOSE»
  RESTRICT_I := SessionLibrary.Permutations.«RESTRICT_I»
  RESTRICT_INVERSE := SessionLibrary.Permutations.«RESTRICT_INVERSE»
  RESTRICT_PERMUTES_SUBSET := SessionLibrary.Permutations.«RESTRICT_PERMUTES_SUBSET»
  SUBGROUP_GENERATED := SessionLibrary.GroupTheory.«SUBGROUP_GENERATED»
  SUBGROUP_GROUP_IMAGE := SessionLibrary.GroupTheory.«SUBGROUP_GROUP_IMAGE»
  SUBGROUP_OF_IMP_SUBSET := SessionLibrary.GroupTheory.«SUBGROUP_OF_IMP_SUBSET»
  SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ := SessionLibrary.GroupTheory.«SUBGROUP_OF_SUBGROUP_GENERATED_SUBGROUP_EQ»
  SUBSET := Session.SUBSET
  SUBSET_ANTISYM_EQ := Session.SUBSET_ANTISYM_EQ
  SWAP_CONJUGATE := SessionLibrary.Permutations.«SWAP_CONJUGATE»
  SWAP_REFL := SessionLibrary.Permutations.«SWAP_REFL»
  SWAP_SYM := SessionLibrary.Permutations.«SWAP_SYM»
  SWAP_TRIPLE := SessionLibrary.Permutations.«SWAP_TRIPLE»
  SWAP_TRIPLE_ALT := SessionLibrary.Permutations.«SWAP_TRIPLE_ALT»
  THREE_CYCLE_COMMUTATOR := SessionLibrary.Permutations.«THREE_CYCLE_COMMUTATOR»
  THREE_CYCLE_NOT_I := SessionLibrary.Permutations.«THREE_CYCLE_NOT_I»
  divides := Session.divides
  group_action := SessionLibrary.GroupTheory.«group_action»
  group_carrier := SessionLibrary.GroupTheory.«group_carrier»
  group_conjugation := SessionLibrary.GroupTheory.«group_conjugation»
  group_homomorphism := SessionLibrary.GroupTheory.«group_homomorphism»
  group_id := SessionLibrary.GroupTheory.«group_id»
  group_inv := SessionLibrary.GroupTheory.«group_inv»
  group_mul := SessionLibrary.GroupTheory.«group_mul»
  group_pow := SessionLibrary.GroupTheory.«group_pow»
  group_tybij := SessionLibrary.GroupTheory.«group_tybij»
  isomorphic_group := SessionLibrary.GroupTheory.«isomorphic_group»
  o_ASSOC := Session.o_ASSOC
  o_THM := Session.o_THM
  prime := Session.prime
  solvable_group := SessionLibrary.GroupTheory.«solvable_group»
  subgroup_of := SessionLibrary.GroupTheory.«subgroup_of»
/-- The core theorems symmetric_group.ml uses. -/
unsafe def core3 (_ : Unit) : HolLibrary.SymmetricGroup.CoreThms3 where
/-- The core theorems symmetric_group.ml uses. -/
unsafe def core4 (_ : Unit) : HolLibrary.SymmetricGroup.CoreThms4 where
-- @@CORE END

/-- What symmetricgroup.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.SymmetricGroup.SymmetricGroupDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  INDUCT_TAC := Session.INDUCT_TAC
  GROUP_RULE t := ExceptT.mk (SessionLibrary.GroupTheory.GROUP_RULE t)
  core1 := core1 ()
  core2 := core2 ()
  core3 := core3 ()
  core4 := core4 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`, and MATCH_CONV's basic conversions, which HOL
    Light adds loading ind_types.ml), then permutations.ml, grouptheory.ml, which symmetricgroup.ml needs. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      SessionLibrary.Permutations.ensurePermutations
      SessionLibrary.GroupTheory.ensureGroupTheory
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.SymmetricGroup: {name}"

/- The bundles, in file order; each forces the one before it. -/

-- @@BUNDLES BEGIN
initialize theBasics : IO.Ref (Option HolLibrary.SymmetricGroup.Basics) ← IO.mkRef none
unsafe def BBasics : HolLibrary.SymmetricGroup.Basics :=
  cached theBasics "setupBasics" fun _ => do
    (HolLibrary.SymmetricGroup.setupBasics (deps ())).run

initialize theCayley : IO.Ref (Option HolLibrary.SymmetricGroup.Cayley) ← IO.mkRef none
unsafe def BCayley : HolLibrary.SymmetricGroup.Cayley :=
  cached theCayley "setupCayley" fun _ => do
    let _ ← IO.mkRef BBasics.symmetric_group
    (HolLibrary.SymmetricGroup.setupCayley (deps ()) BBasics).run

initialize theNotSolvable : IO.Ref (Option HolLibrary.SymmetricGroup.NotSolvable) ← IO.mkRef none
unsafe def BNotSolvable : HolLibrary.SymmetricGroup.NotSolvable :=
  cached theNotSolvable "setupNotSolvable" fun _ => do
    let _ ← IO.mkRef BCayley.CAYLEY_THEOREM_EXPLICIT
    (HolLibrary.SymmetricGroup.setupNotSolvable (deps ()) BBasics).run

initialize theTranspositions : IO.Ref (Option HolLibrary.SymmetricGroup.Transpositions) ← IO.mkRef none
unsafe def BTranspositions : HolLibrary.SymmetricGroup.Transpositions :=
  cached theTranspositions "setupTranspositions" fun _ => do
    let _ ← IO.mkRef BNotSolvable.CHAIN_STEP_THREE_CYCLES_GEN
    (HolLibrary.SymmetricGroup.setupTranspositions (deps ()) BBasics).run

initialize thePcycleMachinery : IO.Ref (Option HolLibrary.SymmetricGroup.PcycleMachinery) ← IO.mkRef none
unsafe def BPcycleMachinery : HolLibrary.SymmetricGroup.PcycleMachinery :=
  cached thePcycleMachinery "setupPcycleMachinery" fun _ => do
    let _ ← IO.mkRef BTranspositions.POINT_TRANSPOSITIONS_GENERATE_ALL
    (HolLibrary.SymmetricGroup.setupPcycleMachinery (deps ()) BBasics).run

initialize thePowOrbit : IO.Ref (Option HolLibrary.SymmetricGroup.PowOrbit) ← IO.mkRef none
unsafe def BPowOrbit : HolLibrary.SymmetricGroup.PowOrbit :=
  cached thePowOrbit "setupPowOrbit" fun _ => do
    let _ ← IO.mkRef BPcycleMachinery.SYMMETRIC_GROUP_POW
    (HolLibrary.SymmetricGroup.setupPowOrbit (deps ()) BBasics BPcycleMachinery).run

initialize theSwapGen : IO.Ref (Option HolLibrary.SymmetricGroup.SwapGen) ← IO.mkRef none
unsafe def BSwapGen : HolLibrary.SymmetricGroup.SwapGen :=
  cached theSwapGen "setupSwapGen" fun _ => do
    let _ ← IO.mkRef BPowOrbit.PRIME_ORDER_POW_PERM
    (HolLibrary.SymmetricGroup.setupSwapGen (deps ()) BBasics BTranspositions BPcycleMachinery BPowOrbit).run

initialize theTransitive : IO.Ref (Option HolLibrary.SymmetricGroup.Transitive) ← IO.mkRef none
unsafe def BTransitive : HolLibrary.SymmetricGroup.Transitive :=
  cached theTransitive "setupTransitive" fun _ => do
    let _ ← IO.mkRef BSwapGen.SWAP_CONJUGATE_IN_SUBGROUP
    (HolLibrary.SymmetricGroup.setupTransitive (deps ()) BBasics BCayley BSwapGen).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Basics
unsafe def symmetric_group : thm := BBasics.symmetric_group
unsafe def SYMMETRIC_GROUP : thm := BBasics.SYMMETRIC_GROUP
unsafe def FINITE_SYMMETRIC_GROUP : thm := BBasics.FINITE_SYMMETRIC_GROUP
unsafe def CARD_SYMMETRIC_GROUP : thm := BBasics.CARD_SYMMETRIC_GROUP
unsafe def SYMMETRIC_GROUP_MUL : thm := BBasics.SYMMETRIC_GROUP_MUL
unsafe def SYMMETRIC_GROUP_INV : thm := BBasics.SYMMETRIC_GROUP_INV
unsafe def SYMMETRIC_GROUP_ID : thm := BBasics.SYMMETRIC_GROUP_ID
unsafe def SWAP_IN_SYMMETRIC_GROUP : thm := BBasics.SWAP_IN_SYMMETRIC_GROUP
unsafe def THREE_CYCLE_IN_SYMMETRIC : thm := BBasics.THREE_CYCLE_IN_SYMMETRIC

-- Cayley
unsafe def CAYLEY_THEOREM_EXPLICIT : thm := BCayley.CAYLEY_THEOREM_EXPLICIT
unsafe def CAYLEY_THEOREM : thm := BCayley.CAYLEY_THEOREM
unsafe def SYMMETRIC_GROUP_ACTION : thm := BCayley.SYMMETRIC_GROUP_ACTION

-- NotSolvable
unsafe def CHAIN_STEP_THREE_CYCLES_GEN : thm := BNotSolvable.CHAIN_STEP_THREE_CYCLES_GEN
unsafe def NOT_SOLVABLE_SYMMETRIC_GROUP : thm := BNotSolvable.NOT_SOLVABLE_SYMMETRIC_GROUP

-- Transpositions
unsafe def POINT_TRANSPOSITIONS_GENERATE_ALL : thm := BTranspositions.POINT_TRANSPOSITIONS_GENERATE_ALL
unsafe def RESTRICT_SYMMETRIC_GROUP_HOMOMORPHISM : thm := BTranspositions.RESTRICT_SYMMETRIC_GROUP_HOMOMORPHISM
unsafe def SUBGROUP_RESTRICT_PERMUTES : thm := BTranspositions.SUBGROUP_RESTRICT_PERMUTES
unsafe def ALL_TRANSPOSITIONS_GENERATE_SYMMETRIC : thm := BTranspositions.ALL_TRANSPOSITIONS_GENERATE_SYMMETRIC

-- PcycleMachinery
unsafe def SYMMETRIC_GROUP_POW : thm := BPcycleMachinery.SYMMETRIC_GROUP_POW
unsafe def SYMMETRIC_GROUP_POW_IN : thm := BPcycleMachinery.SYMMETRIC_GROUP_POW_IN
unsafe def PRIME_ORDER_PERM_NO_FIXPOINT : thm := BPcycleMachinery.PRIME_ORDER_PERM_NO_FIXPOINT

-- PowOrbit
unsafe def PRIME_ORDER_POW_PERM : thm := BPowOrbit.PRIME_ORDER_POW_PERM
unsafe def PRIME_ORDER_PERM_ORBIT : thm := BPowOrbit.PRIME_ORDER_PERM_ORBIT

-- SwapGen
unsafe def SWAP_CONJUGATE_IN_SUBGROUP : thm := BSwapGen.SWAP_CONJUGATE_IN_SUBGROUP
unsafe def TRANSPOSITION_PCYCLE_GENERATES : thm := BSwapGen.TRANSPOSITION_PCYCLE_GENERATES

-- Transitive
unsafe def TRANSITIVE_TRANSPOSITION_GENERATES_SYMMETRIC : thm := BTransitive.TRANSITIVE_TRANSPOSITION_GENERATES_SYMMETRIC
-- @@EXPORTS END

/-- `needs "Library/symmetricgroup.ml"`: build the bundles, in order. -/
unsafe def ensureSymmetricGroup : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BBasics.symmetric_group
  let _ ← IO.mkRef BCayley.CAYLEY_THEOREM_EXPLICIT
  let _ ← IO.mkRef BNotSolvable.CHAIN_STEP_THREE_CYCLES_GEN
  let _ ← IO.mkRef BTranspositions.POINT_TRANSPOSITIONS_GENERATE_ALL
  let _ ← IO.mkRef BPcycleMachinery.SYMMETRIC_GROUP_POW
  let _ ← IO.mkRef BPowOrbit.PRIME_ORDER_POW_PERM
  let _ ← IO.mkRef BSwapGen.SWAP_CONJUGATE_IN_SUBGROUP
  let _ ← IO.mkRef BTransitive.TRANSITIVE_TRANSPOSITION_GENERATES_SYMMETRIC
  -- @@ENSURE END
  pure ()

end SessionLibrary.SymmetricGroup
