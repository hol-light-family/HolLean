/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/szemeredi.ml.                               -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Szemeredi.lean

  The session half of the szemeredi.ml translation: it supplies
  HolLibrary.Szemeredi's dependencies from Session, SessionLibrary.Prime,
  SessionLibrary.Products and SessionLibrary.Bertrand, and exports every
  name under its HOL Light name.  Importing this module is
  `needs "Library/szemeredi.ml"`; its `needs` are the imports of those
  modules.  The bundles are built by `initialize` when the module is loaded.
-/

import Session
import HolLibrary.Szemeredi
import SessionLibrary.Prime
import SessionLibrary.Products
import SessionLibrary.Bertrand

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Szemeredi

/-- The core theorems szemeredi.ml uses. -/
def core1 : HolLibrary.Szemeredi.CoreThms1 where
  ADD1 := Session.ADD1
  ADD_ASSOC := Session.ADD_ASSOC
  ADD_CLAUSES := Session.ADD_CLAUSES
  ADD_EQ_0 := Session.ADD_EQ_0
  ADD_SUB := Session.ADD_SUB
  ADD_SUB2 := Session.ADD_SUB2
  ADD_SYM := Session.ADD_SYM
  ARITH := Session.ARITH
  ARITH_EQ := Session.ARITH_EQ
  BERTRAND := SessionLibrary.Bertrand.«BERTRAND»
  CARD_CLAUSES := Session.CARD_CLAUSES
  CARD_DELETE := Session.CARD_DELETE
  CARD_DIFF := Session.CARD_DIFF
  CARD_EQ_0 := Session.CARD_EQ_0
  CARD_EQ_SUM := Session.CARD_EQ_SUM
  CARD_IMAGE_INJ := Session.CARD_IMAGE_INJ
  CARD_LE_INJ := Session.CARD_LE_INJ
  CARD_NUMSEG := Session.CARD_NUMSEG
  CARD_NUMSEG_1 := Session.CARD_NUMSEG_1
  CARD_NUMSEG_LT := Session.CARD_NUMSEG_LT
  CARD_SUBSET := Session.CARD_SUBSET
  CARD_SUBSET_EQ := Session.CARD_SUBSET_EQ
  CARD_UNION_EQ := Session.CARD_UNION_EQ
  CARD_UNION_LE := Session.CARD_UNION_LE
  COND_ID := Session.COND_ID
  CONG := Session.CONG
  CONG_LMOD := Session.CONG_LMOD
  CONG_MULT_RCANCEL_IFF := SessionLibrary.Prime.«CONG_MULT_RCANCEL_IFF»
  CONJ_ASSOC := Session.CONJ_ASSOC
  CONTRAPOS_THM := Session.CONTRAPOS_THM
  CROSS := Session.CROSS
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIVIDES_NSUM := SessionLibrary.Prime.«DIVIDES_NSUM»
  DIVIDES_RMUL := SessionLibrary.Prime.«DIVIDES_RMUL»
  DIVMOD_UNIQ := Session.DIVMOD_UNIQ
  DIV_LT := Session.DIV_LT
  DIV_MULT_ADD := Session.DIV_MULT_ADD
  EMPTY_GSPEC := Session.EMPTY_GSPEC
  EQ_ADD_RCANCEL := Session.EQ_ADD_RCANCEL
  EQ_IMP := Session.EQ_IMP
  EQ_IMP_LE := Session.EQ_IMP_LE
  EQ_MULT_LCANCEL := Session.EQ_MULT_LCANCEL
  EQ_TRANS := Session.EQ_TRANS
  ETA_AX := Session.ETA_AX
  EXISTS_PAIR_THM := Session.EXISTS_PAIR_THM
  EXP_1 := Session.EXP_1
  EXP_ADD := Session.EXP_ADD
  EXP_EQ_0 := Session.EXP_EQ_0
  EXP_MONO_LE := Session.EXP_MONO_LE
  EXTENSION := Session.EXTENSION
  FINITE_CROSS := Session.FINITE_CROSS
  FINITE_DELETE := Session.FINITE_DELETE
  FINITE_EMPTY := Session.FINITE_EMPTY
  FINITE_HAS_SIZE := Session.FINITE_HAS_SIZE
  FINITE_IMAGE := Session.FINITE_IMAGE
  FINITE_NUMSEG := Session.FINITE_NUMSEG
  FINITE_NUMSEG_LE := Session.FINITE_NUMSEG_LE
  FINITE_NUMSEG_LT := Session.FINITE_NUMSEG_LT
  FINITE_PRODUCT := Session.FINITE_PRODUCT
  FINITE_RESTRICT := Session.FINITE_RESTRICT
  FINITE_SING := Session.FINITE_SING
  FINITE_SUBSET := Session.FINITE_SUBSET
  FINITE_UNION := Session.FINITE_UNION
  FORALL_IN_IMAGE := Session.FORALL_IN_IMAGE
  FORALL_PAIR_THM := Session.FORALL_PAIR_THM
  FORALL_UNWIND_THM2 := Session.FORALL_UNWIND_THM2
  FST := Session.FST
  FUN_EQ_THM := Session.FUN_EQ_THM
  HAS_SIZE := Session.HAS_SIZE
  HAS_SIZE_0 := Session.HAS_SIZE_0
  HAS_SIZE_CARD := Session.HAS_SIZE_CARD
  HAS_SIZE_FUNSPACE := Session.HAS_SIZE_FUNSPACE
  HAS_SIZE_NUMSEG_LT := Session.HAS_SIZE_NUMSEG_LT
  INTER_SUBSET := Session.INTER_SUBSET
  INT_ADD_RID := Session.INT_ADD_RID
  INT_CONG_IMP_EQ := Session.INT_CONG_IMP_EQ
  INT_MUL_LZERO := Session.INT_MUL_LZERO
  INT_OF_NUM_ADD := Session.INT_OF_NUM_ADD
  INT_OF_NUM_EQ := Session.INT_OF_NUM_EQ
  INT_OF_NUM_LT := Session.INT_OF_NUM_LT
  INT_OF_NUM_MUL := Session.INT_OF_NUM_MUL
  INT_OF_NUM_SUB := Session.INT_OF_NUM_SUB
  INT_POS := Session.INT_POS
  INT_SUB_REFL := Session.INT_SUB_REFL
  IN_CROSS := Session.IN_CROSS
  IN_DELETE := Session.IN_DELETE
  IN_DIFF := Session.IN_DIFF
  IN_ELIM_PAIR_THM := Session.IN_ELIM_PAIR_THM
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_IMAGE := Session.IN_IMAGE
  IN_INTER := Session.IN_INTER
  IN_NUMSEG := Session.IN_NUMSEG
  IN_SING := Session.IN_SING
  IN_UNION := Session.IN_UNION
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LET_TRANS := Session.LET_TRANS
  LE_0 := Session.LE_0
  LE_ANTISYM := Session.LE_ANTISYM
  LE_EXP := Session.LE_EXP
  LE_LT := Session.LE_LT
  LE_MULT2 := Session.LE_MULT2
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_MULT_RCANCEL := Session.LE_MULT_RCANCEL
  LE_REFL := Session.LE_REFL
  LE_TRANS := Session.LE_TRANS
  LT := Session.LT
  LTE_TRANS := Session.LTE_TRANS
  LT_ADD_LCANCEL := Session.LT_ADD_LCANCEL
  LT_IMP_LE := Session.LT_IMP_LE
  LT_MULT := Session.LT_MULT
  LT_NZ := Session.LT_NZ
  LT_REFL := Session.LT_REFL
  LT_TRANS := Session.LT_TRANS
  MEMBER_NOT_EMPTY := Session.MEMBER_NOT_EMPTY
  MINIMAL := Session.MINIMAL
  MINIMAL_UNIQUE := Session.MINIMAL_UNIQUE
  MOD_LT := Session.MOD_LT
  MOD_LT_EQ := Session.MOD_LT_EQ
  MOD_MOD_REFL := Session.MOD_MOD_REFL
  MOD_MULT_ADD := Session.MOD_MULT_ADD
  MONO_EXISTS := Session.MONO_EXISTS
  MULT_CLAUSES := Session.MULT_CLAUSES
  MULT_EQ_0 := Session.MULT_EQ_0
  MULT_SYM := Session.MULT_SYM
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IMP := Session.NOT_IMP
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
/-- The core theorems szemeredi.ml uses. -/
def core2 : HolLibrary.Szemeredi.CoreThms2 where
  NOT_LE := Session.NOT_LE
  NOT_LT := Session.NOT_LT
  NOT_SUC := Session.NOT_SUC
  NSUM_ADD := Session.NSUM_ADD
  NSUM_CLAUSES_NUMSEG := Session.NSUM_CLAUSES_NUMSEG
  NSUM_CLAUSES_NUMSEG_LT := Session.NSUM_CLAUSES_NUMSEG_LT
  NSUM_CONST := Session.NSUM_CONST
  NSUM_DIGITS_BOUND := Session.NSUM_DIGITS_BOUND
  NSUM_DIGITS_UNIQUE := Session.NSUM_DIGITS_UNIQUE
  NSUM_EQ := Session.NSUM_EQ
  NSUM_RESTRICT_SET := Session.NSUM_RESTRICT_SET
  NSUM_SING := Session.NSUM_SING
  NSUM_UNION_NONZERO := Session.NSUM_UNION_NONZERO
  PAIR := Session.PAIR
  PAIR_EQ := Session.PAIR_EQ
  PRIME_0 := SessionLibrary.Prime.«PRIME_0»
  PRIME_COPRIME_LT := SessionLibrary.Prime.«PRIME_COPRIME_LT»
  PRODUCT_CONST := SessionLibrary.Products.«PRODUCT_CONST»
  PRODUCT_EQ := SessionLibrary.Products.«PRODUCT_EQ»
  PRODUCT_EQ_0 := SessionLibrary.Products.«PRODUCT_EQ_0»
  PRODUCT_EQ_1 := SessionLibrary.Products.«PRODUCT_EQ_1»
  PRODUCT_LE := SessionLibrary.Products.«PRODUCT_LE»
  PRODUCT_MUL := SessionLibrary.Products.«PRODUCT_MUL»
  PRODUCT_POS_LE := SessionLibrary.Products.«PRODUCT_POS_LE»
  REAL_ABS_DIV := Session.REAL_ABS_DIV
  REAL_ABS_NUM := Session.REAL_ABS_NUM
  REAL_ADD_LID := Session.REAL_ADD_LID
  REAL_ADD_RDISTRIB := Session.REAL_ADD_RDISTRIB
  REAL_ADD_RID := Session.REAL_ADD_RID
  REAL_ARCH := Session.REAL_ARCH
  REAL_ARCH_POW_INV := Session.REAL_ARCH_POW_INV
  REAL_ARCH_SIMPLE := Session.REAL_ARCH_SIMPLE
  REAL_DIV_RMUL := Session.REAL_DIV_RMUL
  REAL_EQ_IMP_LE := Session.REAL_EQ_IMP_LE
  REAL_INV_0 := Session.REAL_INV_0
  REAL_INV_MUL := Session.REAL_INV_MUL
  REAL_LE_ADD2 := Session.REAL_LE_ADD2
  REAL_LE_ANTISYM := Session.REAL_LE_ANTISYM
  REAL_LE_DIV := Session.REAL_LE_DIV
  REAL_LE_INV2 := Session.REAL_LE_INV2
  REAL_LE_INV_EQ := Session.REAL_LE_INV_EQ
  REAL_LE_LADD := Session.REAL_LE_LADD
  REAL_LE_LDIV_EQ := Session.REAL_LE_LDIV_EQ
  REAL_LE_LMUL := Session.REAL_LE_LMUL
  REAL_LE_LMUL_EQ := Session.REAL_LE_LMUL_EQ
  REAL_LE_MUL := Session.REAL_LE_MUL
  REAL_LE_RDIV_EQ := Session.REAL_LE_RDIV_EQ
  REAL_LE_REFL := Session.REAL_LE_REFL
  REAL_LE_RMUL := Session.REAL_LE_RMUL
  REAL_LE_TRANS := Session.REAL_LE_TRANS
  REAL_LT_DIV := Session.REAL_LT_DIV
  REAL_LT_IMP_LE := Session.REAL_LT_IMP_LE
  REAL_LT_IMP_NZ := Session.REAL_LT_IMP_NZ
  REAL_LT_INV_EQ := Session.REAL_LT_INV_EQ
  REAL_LT_LDIV_EQ := Session.REAL_LT_LDIV_EQ
  REAL_LT_MUL := Session.REAL_LT_MUL
  REAL_LT_REFL := Session.REAL_LT_REFL
  REAL_LT_RMUL := Session.REAL_LT_RMUL
  REAL_MUL_AC := Session.REAL_MUL_AC
  REAL_MUL_ASSOC := Session.REAL_MUL_ASSOC
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_LINV := Session.REAL_MUL_LINV
  REAL_MUL_LZERO := Session.REAL_MUL_LZERO
  REAL_MUL_RID := Session.REAL_MUL_RID
  REAL_MUL_RZERO := Session.REAL_MUL_RZERO
  REAL_MUL_SYM := Session.REAL_MUL_SYM
  REAL_NOT_LE := Session.REAL_NOT_LE
  REAL_NOT_LT := Session.REAL_NOT_LT
  REAL_OF_NUM_ADD := Session.REAL_OF_NUM_ADD
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_LE := Session.REAL_OF_NUM_LE
  REAL_OF_NUM_LT := Session.REAL_OF_NUM_LT
  REAL_OF_NUM_MUL := Session.REAL_OF_NUM_MUL
  REAL_OF_NUM_POW := Session.REAL_OF_NUM_POW
  REAL_OF_NUM_SUB := Session.REAL_OF_NUM_SUB
  REAL_OF_NUM_SUC := Session.REAL_OF_NUM_SUC
  REAL_POS := Session.REAL_POS
  REAL_POW_2 := Session.REAL_POW_2
  REAL_POW_ADD := Session.REAL_POW_ADD
  REAL_POW_DIV := Session.REAL_POW_DIV
  REAL_POW_LE := Session.REAL_POW_LE
  REAL_POW_LE2 := Session.REAL_POW_LE2
  REAL_POW_LT := Session.REAL_POW_LT
  REAL_POW_MONO_INV := Session.REAL_POW_MONO_INV
  REAL_POW_MUL := Session.REAL_POW_MUL
  REAL_POW_ONE := Session.REAL_POW_ONE
  RIGHT_ADD_DISTRIB := Session.RIGHT_ADD_DISTRIB
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SKOLEM_THM := Session.SKOLEM_THM
  SND := Session.SND
  SUBSET := Session.SUBSET
  SUBSET_TRANS := Session.SUBSET_TRANS
  SUB_0 := Session.SUB_0
  SUB_ADD := Session.SUB_ADD
  SUB_REFL := Session.SUB_REFL
  SUC_SUB1 := Session.SUC_SUB1
  SUM_0 := Session.SUM_0
  SUM_ABS := Session.SUM_ABS
  SUM_ADD := Session.SUM_ADD
  SUM_BOUND := Session.SUM_BOUND
  SUM_CASES := Session.SUM_CASES
  SUM_CLAUSES := Session.SUM_CLAUSES
  SUM_CONST := Session.SUM_CONST
  SUM_DELETE := Session.SUM_DELETE
  SUM_DELTA := Session.SUM_DELTA
  SUM_EQ := Session.SUM_EQ
  SUM_EQ_0 := Session.SUM_EQ_0
  SUM_EQ_GENERAL_INVERSES := Session.SUM_EQ_GENERAL_INVERSES
  SUM_GROUP := Session.SUM_GROUP
  SUM_IMAGE := Session.SUM_IMAGE
  SUM_INJECTION := Session.SUM_INJECTION
  SUM_LE := Session.SUM_LE
  SUM_LMUL := Session.SUM_LMUL
  SUM_LT_ALL := Session.SUM_LT_ALL
  SUM_POS_LE := Session.SUM_POS_LE
  SUM_RESTRICT_SET := Session.SUM_RESTRICT_SET
  SUM_RMUL := Session.SUM_RMUL
  SUM_SUB := Session.SUM_SUB
  SUM_SUM_PRODUCT := Session.SUM_SUM_PRODUCT
  SUM_SWAP := Session.SUM_SWAP
  divides := Session.divides
  num_FINITE := Session.num_FINITE
  num_RECURSION := Session.num_RECURSION
  num_congruent := Session.num_congruent
  o_DEF := Session.o_DEF
  real_div := Session.real_div

/-- What szemeredi.ml uses from Session. -/
def deps : HolLibrary.Szemeredi.SzemerediDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  prioritize_real := Session.prioritize_real
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_ARITH_TAC := Session.ASM_ARITH_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  TAUT t := ExceptT.mk (Session.TAUT t)
  INDUCT_TAC := Session.INDUCT_TAC
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH t)
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC
  ASM_REAL_ARITH_TAC := Session.ASM_REAL_ARITH_TAC
  REAL_FIELD t := ExceptT.mk (Session.REAL_FIELD t)
  REAL_RING t := ExceptT.mk (Session.REAL_RING t)
  NUM_RING := Session.NUM_RING
  INT_ARITH_TAC := Session.INT_ARITH_TAC
  MOD_DOWN_CONV := Session.MOD_DOWN_CONV
  NUMBER_RULE := Session.NUMBER_RULE
  INTEGER_RULE t := ExceptT.mk (Session.INTEGER_RULE t)
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  SELECT_CONV t := pure (Session.SELECT_CONV t)
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← Session.quietly x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in szemeredi.ml order. -/
initialize BFiniteMeans : HolLibrary.Szemeredi.FiniteMeans ←
  ioB "setupFiniteMeans" (HolLibrary.Szemeredi.setupFiniteMeans deps).run
initialize BWords : HolLibrary.Szemeredi.Words ←
  ioB "setupWords" (HolLibrary.Szemeredi.setupWords deps).run
initialize BLines : HolLibrary.Szemeredi.Lines ←
  ioB "setupLines" (HolLibrary.Szemeredi.setupLines deps BWords).run
initialize BDensities : HolLibrary.Szemeredi.Densities ←
  ioB "setupDensities" (HolLibrary.Szemeredi.setupDensities deps BFiniteMeans BWords).run
initialize BTemplates : HolLibrary.Szemeredi.Templates ←
  ioB "setupTemplates" (HolLibrary.Szemeredi.setupTemplates deps).run
initialize BHJTKey : HolLibrary.Szemeredi.HJTKey ←
  ioB "setupHJTKey" (HolLibrary.Szemeredi.setupHJTKey deps BTemplates).run
initialize BHJTemplate : HolLibrary.Szemeredi.HJTemplate ←
  ioB "setupHJTemplate" (HolLibrary.Szemeredi.setupHJTemplate deps BWords BLines BTemplates BHJTKey).run
initialize BHalesJewett : HolLibrary.Szemeredi.HalesJewett ←
  ioB "setupHalesJewett" (HolLibrary.Szemeredi.setupHalesJewett deps BWords BLines BTemplates BHJTemplate).run
initialize BFirstWildcard : HolLibrary.Szemeredi.FirstWildcard ←
  ioB "setupFirstWildcard" (HolLibrary.Szemeredi.setupFirstWildcard deps BWords BLines).run
initialize BFolkman : HolLibrary.Szemeredi.Folkman ←
  ioB "setupFolkman" (HolLibrary.Szemeredi.setupFolkman deps BWords BLines BDensities BHalesJewett BFirstWildcard).run
initialize BWildcards : HolLibrary.Szemeredi.Wildcards ←
  ioB "setupWildcards" (HolLibrary.Szemeredi.setupWildcards deps BWords BLines).run
initialize BGrahamRothschild : HolLibrary.Szemeredi.GrahamRothschild ←
  ioB "setupGrahamRothschild" (HolLibrary.Szemeredi.setupGrahamRothschild deps BWords BLines BHalesJewett BFolkman BWildcards).run
initialize BDensityHJ : HolLibrary.Szemeredi.DensityHJ ←
  ioB "setupDensityHJ" (HolLibrary.Szemeredi.setupDensityHJ deps BWords BLines BDensities BHalesJewett BWildcards).run
initialize BUniformSubspaces : HolLibrary.Szemeredi.UniformSubspaces ←
  ioB "setupUniformSubspaces" (HolLibrary.Szemeredi.setupUniformSubspaces deps BFiniteMeans BWords BLines BDensities).run
initialize BDKTCor5 : HolLibrary.Szemeredi.DKTCor5 ←
  ioB "setupDKTCor5" (HolLibrary.Szemeredi.setupDKTCor5 deps BFiniteMeans BWords BLines BDensities BDensityHJ BUniformSubspaces).run
initialize BGoodLines : HolLibrary.Szemeredi.GoodLines ←
  ioB "setupGoodLines" (HolLibrary.Szemeredi.setupGoodLines deps BFiniteMeans BWords BLines BDensities BFirstWildcard BGrahamRothschild BDensityHJ BUniformSubspaces BDKTCor5).run
initialize BLemma8 : HolLibrary.Szemeredi.Lemma8 ←
  ioB "setupLemma8" (HolLibrary.Szemeredi.setupLemma8 deps BFiniteMeans BWords BLines BDensities BDensityHJ BDKTCor5 BGoodLines).run
initialize BInsensitive : HolLibrary.Szemeredi.Insensitive ←
  ioB "setupInsensitive" (HolLibrary.Szemeredi.setupInsensitive deps BFiniteMeans BWords BLines BDensities BWildcards).run
initialize BLemma10 : HolLibrary.Szemeredi.Lemma10 ←
  ioB "setupLemma10" (HolLibrary.Szemeredi.setupLemma10 deps BFiniteMeans BWords BLines BDensities BInsensitive).run
initialize BCor11 : HolLibrary.Szemeredi.Cor11 ←
  ioB "setupCor11" (HolLibrary.Szemeredi.setupCor11 deps BFiniteMeans BWords BLines BDensities BLemma8 BInsensitive BLemma10).run
initialize BTilings : HolLibrary.Szemeredi.Tilings ←
  ioB "setupTilings" (HolLibrary.Szemeredi.setupTilings deps BWords BDensities BCor11).run
initialize BBlockInsert : HolLibrary.Szemeredi.BlockInsert ←
  ioB "setupBlockInsert" (HolLibrary.Szemeredi.setupBlockInsert deps BFiniteMeans BWords BLines BDensities BDKTCor5 BInsensitive).run
initialize BTileStep : HolLibrary.Szemeredi.TileStep ←
  ioB "setupTileStep" (HolLibrary.Szemeredi.setupTileStep deps BWords BLines BDensities BDensityHJ BUniformSubspaces BDKTCor5 BInsensitive BCor11 BTilings BBlockInsert).run
initialize BLemma12 : HolLibrary.Szemeredi.Lemma12 ←
  ioB "setupLemma12" (HolLibrary.Szemeredi.setupLemma12 deps BFiniteMeans BWords BDensities BUniformSubspaces BTilings BTileStep).run
initialize BCor13 : HolLibrary.Szemeredi.Cor13 ←
  ioB "setupCor13" (HolLibrary.Szemeredi.setupCor13 deps BWords BDensities BCor11 BTilings BBlockInsert BLemma12).run
initialize BDensityHJThm : HolLibrary.Szemeredi.DensityHJThm ←
  ioB "setupDensityHJThm" (HolLibrary.Szemeredi.setupDensityHJThm deps BWords BLines BDensities BDensityHJ BCor11 BTilings BCor13).run
initialize BWeightedDefs : HolLibrary.Szemeredi.WeightedDefs ←
  ioB "setupWeightedDefs" (HolLibrary.Szemeredi.setupWeightedDefs deps BFiniteMeans BWords BLines BDKTCor5).run
initialize BAPBound : HolLibrary.Szemeredi.APBound ←
  ioB "setupAPBound" (HolLibrary.Szemeredi.setupAPBound deps BFiniteMeans BWords BLines BDensities BDensityHJ BDKTCor5 BWeightedDefs).run
initialize BWeightedThm : HolLibrary.Szemeredi.WeightedThm ←
  ioB "setupWeightedThm" (HolLibrary.Szemeredi.setupWeightedThm deps BFiniteMeans BDensityHJThm BWeightedDefs BAPBound).run
initialize BModAP : HolLibrary.Szemeredi.ModAP ←
  ioB "setupModAP" (HolLibrary.Szemeredi.setupModAP deps BFiniteMeans).run
initialize BUpDown : HolLibrary.Szemeredi.UpDown ←
  ioB "setupUpDown" (HolLibrary.Szemeredi.setupUpDown deps BModAP).run
initialize BPairs : HolLibrary.Szemeredi.Pairs ←
  ioB "setupPairs" (HolLibrary.Szemeredi.setupPairs deps BModAP BUpDown).run
initialize BSzemerediThm : HolLibrary.Szemeredi.SzemerediThm ←
  ioB "setupSzemerediThm" (HolLibrary.Szemeredi.setupSzemerediThm deps BFiniteMeans BLemma8 BWeightedDefs BWeightedThm BModAP BPairs).run
initialize BVdW : HolLibrary.Szemeredi.VdW ←
  ioB "setupVdW" (HolLibrary.Szemeredi.setupVdW deps BFiniteMeans BWords BDensities BDKTCor5 BModAP BSzemerediThm).run
initialize BMultidim : HolLibrary.Szemeredi.Multidim ←
  ioB "setupMultidim" (HolLibrary.Szemeredi.setupMultidim deps BWords BLines BDensities BDensityHJ BDensityHJThm BWeightedDefs BVdW).run

-- FiniteMeans
def fmean : thm := BFiniteMeans.fmean
def FMEAN_ADD : thm := BFiniteMeans.FMEAN_ADD
def FMEAN_SUB : thm := BFiniteMeans.FMEAN_SUB
def FMEAN_LMUL : thm := BFiniteMeans.FMEAN_LMUL
def FMEAN_CONST : thm := BFiniteMeans.FMEAN_CONST
def FMEAN_EQ : thm := BFiniteMeans.FMEAN_EQ
def FMEAN_LE : thm := BFiniteMeans.FMEAN_LE
def FMEAN_ABS_LE : thm := BFiniteMeans.FMEAN_ABS_LE
def FMEAN_SUM : thm := BFiniteMeans.FMEAN_SUM
def FMEAN_POS : thm := BFiniteMeans.FMEAN_POS
def SUM_SHIFT_MOD : thm := BFiniteMeans.SUM_SHIFT_MOD
def FMEAN_SHIFT_MOD : thm := BFiniteMeans.FMEAN_SHIFT_MOD

-- Words
def hj_cube : thm := BWords.hj_cube
def IN_HJ_CUBE : thm := BWords.IN_HJ_CUBE
def HAS_SIZE_HJ_CUBE : thm := BWords.HAS_SIZE_HJ_CUBE
def FINITE_HJ_CUBE : thm := BWords.FINITE_HJ_CUBE
def CARD_HJ_CUBE : thm := BWords.CARD_HJ_CUBE
def HJ_CUBE_NONEMPTY : thm := BWords.HJ_CUBE_NONEMPTY
def HJ_CUBE_MONO : thm := BWords.HJ_CUBE_MONO
def HJ_CUBE_0 : thm := BWords.HJ_CUBE_0
def hj_concat : thm := BWords.hj_concat
def hj_take : thm := BWords.hj_take
def hj_drop : thm := BWords.hj_drop
def HJ_CONCAT_CUBE : thm := BWords.HJ_CONCAT_CUBE
def HJ_TAKE_CUBE : thm := BWords.HJ_TAKE_CUBE
def HJ_DROP_CUBE : thm := BWords.HJ_DROP_CUBE
def HJ_CONCAT_SPLIT : thm := BWords.HJ_CONCAT_SPLIT
def HJ_TAKE_CONCAT : thm := BWords.HJ_TAKE_CONCAT
def HJ_DROP_CONCAT : thm := BWords.HJ_DROP_CONCAT
def HJ_CONCAT_INJ : thm := BWords.HJ_CONCAT_INJ
def HJ_CUBE_CONCAT_IMAGE : thm := BWords.HJ_CUBE_CONCAT_IMAGE
def SUM_HJ_CONCAT : thm := BWords.SUM_HJ_CONCAT
def hj_subspace : thm := BWords.hj_subspace
def hj_subst : thm := BWords.hj_subst
def HJ_SUBSPACE_0 : thm := BWords.HJ_SUBSPACE_0
def HJ_SUBSPACE_CUBE : thm := BWords.HJ_SUBSPACE_CUBE
def HJ_SUBST_SUBST : thm := BWords.HJ_SUBST_SUBST
def HJ_SUBSPACE_SUBST : thm := BWords.HJ_SUBSPACE_SUBST
def HJ_SUBST_CUBE : thm := BWords.HJ_SUBST_CUBE
def HJ_SUBST_INJ : thm := BWords.HJ_SUBST_INJ
def HJ_SUBST_WORD : thm := BWords.HJ_SUBST_WORD
def hj_identity : thm := BWords.hj_identity
def HJ_SUBSPACE_IDENTITY : thm := BWords.HJ_SUBSPACE_IDENTITY
def HJ_SUBST_IDENTITY : thm := BWords.HJ_SUBST_IDENTITY
def HJ_SUBST_RID : thm := BWords.HJ_SUBST_RID

-- Lines
def hj_line : thm := BLines.hj_line
def hj_line_point : thm := BLines.hj_line_point
def hj_has_line : thm := BLines.hj_has_line
def HJ_LETTER_IN_CUBE : thm := BLines.HJ_LETTER_IN_CUBE
def HJ_LINE_CUBE : thm := BLines.HJ_LINE_CUBE
def HJ_LINE_VAR : thm := BLines.HJ_LINE_VAR
def HJ_LINE_POINT_CUBE : thm := BLines.HJ_LINE_POINT_CUBE
def HJ_LINE_SUBST : thm := BLines.HJ_LINE_SUBST
def HJ_LINE_POINT_SUBST : thm := BLines.HJ_LINE_POINT_SUBST
def HJ_HAS_LINE_PULLBACK : thm := BLines.HJ_HAS_LINE_PULLBACK
def hj_join : thm := BLines.hj_join
def HJ_SUBST_JOIN : thm := BLines.HJ_SUBST_JOIN
def HJ_SUBSPACE_JOIN : thm := BLines.HJ_SUBSPACE_JOIN
def hj_lift : thm := BLines.hj_lift
def HJ_SUBST_LIFT : thm := BLines.HJ_SUBST_LIFT
def HJ_SUBSPACE_LIFT : thm := BLines.HJ_SUBSPACE_LIFT

-- Densities
def hj_density : thm := BDensities.hj_density
def FMEAN_HJ_CONCAT : thm := BDensities.FMEAN_HJ_CONCAT
def HJ_DENSITY_SECTIONS : thm := BDensities.HJ_DENSITY_SECTIONS
def HJ_DENSITY_CARD : thm := BDensities.HJ_DENSITY_CARD
def HJ_DENSITY_POS : thm := BDensities.HJ_DENSITY_POS
def HJ_DENSITY_LE_1 : thm := BDensities.HJ_DENSITY_LE_1
def HJ_DENSITY_MONO : thm := BDensities.HJ_DENSITY_MONO
def HJ_DENSITY_EQ : thm := BDensities.HJ_DENSITY_EQ
def FMEAN_MARKOV : thm := BDensities.FMEAN_MARKOV
def HJ_DENSITY_MARKOV : thm := BDensities.HJ_DENSITY_MARKOV
def CARD_PIGEONHOLE : thm := BDensities.CARD_PIGEONHOLE
def FMEAN_EXISTS_GE : thm := BDensities.FMEAN_EXISTS_GE

-- Templates
def hjt_subst : thm := BTemplates.hjt_subst
def hjt_line : thm := BTemplates.hjt_line
def hjt_mono : thm := BTemplates.hjt_mono
def hales_jewett_template : thm := BTemplates.hales_jewett_template
def HJT_1 : thm := BTemplates.HJT_1
def HJT_MONO_N : thm := BTemplates.HJT_MONO_N
def hjt_prod : thm := BTemplates.hjt_prod
def HJT_SUBST_PROD : thm := BTemplates.HJT_SUBST_PROD
def hjt_almost_mono : thm := BTemplates.hjt_almost_mono
def hjt_focused : thm := BTemplates.hjt_focused
def HJT_ALMOST_MONO_LT : thm := BTemplates.HJT_ALMOST_MONO_LT
def HJT_COLLAPSE : thm := BTemplates.HJT_COLLAPSE
def hjt_lift : thm := BTemplates.hjt_lift
def NSUM_NUMSEG_LT_SHIFT : thm := BTemplates.NSUM_NUMSEG_LT_SHIFT
def HJT_NSUM_DIGIT_SPLIT : thm := BTemplates.HJT_NSUM_DIGIT_SPLIT
def HJT_DIGIT_RECOVER : thm := BTemplates.HJT_DIGIT_RECOVER
def HJT_RECOLOUR : thm := BTemplates.HJT_RECOLOUR
def HJT_LIFT_SUBST_LE : thm := BTemplates.HJT_LIFT_SUBST_LE
def HJT_PROD_LIFT_SUBST_LE : thm := BTemplates.HJT_PROD_LIFT_SUBST_LE
def HJT_SUBST_FIXED : thm := BTemplates.HJT_SUBST_FIXED
def HJT_GEN_ALMOST_MONO : thm := BTemplates.HJT_GEN_ALMOST_MONO
def HJT_PROD_LINE : thm := BTemplates.HJT_PROD_LINE
def HJT_FIXED_LINE_MONO : thm := BTemplates.HJT_FIXED_LINE_MONO

-- HJTKey
def HJT_KEY : thm := BHJTKey.HJT_KEY

-- HJTemplate
def HJT_STEP : thm := BHJTemplate.HJT_STEP
def HALES_JEWETT_TEMPLATE : thm := BHJTemplate.HALES_JEWETT_TEMPLATE
def HJ_FINITE_INDEX : thm := BHJTemplate.HJ_FINITE_INDEX
def HJ_LINE_POINT_TEMPLATE : thm := BHJTemplate.HJ_LINE_POINT_TEMPLATE

-- HalesJewett
def HALES_JEWETT : thm := BHalesJewett.HALES_JEWETT
def HALES_JEWETT_FINITE : thm := BHalesJewett.HALES_JEWETT_FINITE
def HJ_SUBST_LINE : thm := BHalesJewett.HJ_SUBST_LINE
def HJ_SUBST_TAKE : thm := BHalesJewett.HJ_SUBST_TAKE
def HJ_PATTERN_INDEX : thm := BHalesJewett.HJ_PATTERN_INDEX
def MULTIDIM_HALES_JEWETT : thm := BHalesJewett.MULTIDIM_HALES_JEWETT

-- FirstWildcard
def hj_first_wildcard : thm := BFirstWildcard.hj_first_wildcard
def HJ_FIRST_WILDCARD : thm := BFirstWildcard.HJ_FIRST_WILDCARD
def HJ_FIRST_WILDCARD_UNIQUE : thm := BFirstWildcard.HJ_FIRST_WILDCARD_UNIQUE
def HJ_LINE_1_DROP : thm := BFirstWildcard.HJ_LINE_1_DROP
def HJ_FIRST_WILDCARD_DROP : thm := BFirstWildcard.HJ_FIRST_WILDCARD_DROP
def HJ_SUBST_IN_CUBE : thm := BFirstWildcard.HJ_SUBST_IN_CUBE
def HJ_SUBSPACE_HEAD1 : thm := BFirstWildcard.HJ_SUBSPACE_HEAD1
def HJ_SUBST_HEAD1 : thm := BFirstWildcard.HJ_SUBST_HEAD1
def HJ_SUBST_HEAD0 : thm := BFirstWildcard.HJ_SUBST_HEAD0
def HJ_SUBST_HEAD1E : thm := BFirstWildcard.HJ_SUBST_HEAD1E
def HJ_SUBSPACE_1_UNIT : thm := BFirstWildcard.HJ_SUBSPACE_1_UNIT

-- Folkman
def FOLKMAN_FOCUS : thm := BFolkman.FOLKMAN_FOCUS
def HJ_LINE_1_UNIT : thm := BFolkman.HJ_LINE_1_UNIT
def FOLKMAN : thm := BFolkman.FOLKMAN

-- Wildcards
def hj_wildcards : thm := BWildcards.hj_wildcards
def hj_wlift : thm := BWildcards.hj_wlift
def hj_dlift : thm := BWildcards.hj_dlift
def HJ_LINE_EQ : thm := BWildcards.HJ_LINE_EQ
def HJ_WILDCARDS_LINE : thm := BWildcards.HJ_WILDCARDS_LINE
def HJ_WLIFT_LINE : thm := BWildcards.HJ_WLIFT_LINE
def HJ_WILDCARDS_WLIFT : thm := BWildcards.HJ_WILDCARDS_WLIFT
def HJ_SUBSPACE_DLIFT : thm := BWildcards.HJ_SUBSPACE_DLIFT
def HJ_WILDCARDS_DLIFT : thm := BWildcards.HJ_WILDCARDS_DLIFT
def HJ_LINE_POINT_K : thm := BWildcards.HJ_LINE_POINT_K
def HJ_WILDCARDS_TAKE : thm := BWildcards.HJ_WILDCARDS_TAKE
def HJ_PAIR_CODE : thm := BWildcards.HJ_PAIR_CODE
def HJ_PAIR_DECODE : thm := BWildcards.HJ_PAIR_DECODE
def HJ_LINE_SUC_CASES : thm := BWildcards.HJ_LINE_SUC_CASES
def HJ_WILDCARDS_EQ_VAR : thm := BWildcards.HJ_WILDCARDS_EQ_VAR

-- GrahamRothschild
def HJ_LETTER_INDEP : thm := BGrahamRothschild.HJ_LETTER_INDEP
def GRAHAM_ROTHSCHILD_LINES : thm := BGrahamRothschild.GRAHAM_ROTHSCHILD_LINES

-- DensityHJ
def density_hales_jewett : thm := BDensityHJ.density_hales_jewett
def HJ_DENSITY_POS_EXISTS : thm := BDensityHJ.HJ_DENSITY_POS_EXISTS
def FINITE_HJ_LINES : thm := BDensityHJ.FINITE_HJ_LINES
def HJ_LINES_NONEMPTY : thm := BDensityHJ.HJ_LINES_NONEMPTY
def HJ_DENSITY_PIGEONHOLE : thm := BDensityHJ.HJ_DENSITY_PIGEONHOLE
def MULTIDIM_DENSITY_HALES_JEWETT : thm := BDensityHJ.MULTIDIM_DENSITY_HALES_JEWETT

-- UniformSubspaces
def HJ_CONCAT_ASSOC : thm := BUniformSubspaces.HJ_CONCAT_ASSOC
def HJ_CONCAT_0 : thm := BUniformSubspaces.HJ_CONCAT_0
def FMEAN_SPREAD : thm := BUniformSubspaces.FMEAN_SPREAD
def HJ_SECTION_CONCAT : thm := BUniformSubspaces.HJ_SECTION_CONCAT
def HJ_SUBSPACE_JOIN_POINT : thm := BUniformSubspaces.HJ_SUBSPACE_JOIN_POINT
def HJ_SUBST_JOIN_POINT : thm := BUniformSubspaces.HJ_SUBST_JOIN_POINT
def DKT_UNIFORM_STEP : thm := BUniformSubspaces.DKT_UNIFORM_STEP
def DKT_LEMMA4 : thm := BUniformSubspaces.DKT_LEMMA4

-- DKTCor5
def FMEAN_SWAP2 : thm := BDKTCor5.FMEAN_SWAP2
def HJ_CUBE_MONO_IN : thm := BDKTCor5.HJ_CUBE_MONO_IN
def DKT_COR5 : thm := BDKTCor5.DKT_COR5

-- GoodLines
def DKT_GOOD_LINE : thm := BGoodLines.DKT_GOOD_LINE
def HJ_SUBSPACE_MONO_LENGTH : thm := BGoodLines.HJ_SUBSPACE_MONO_LENGTH
def DKT_LEMMA7 : thm := BGoodLines.DKT_LEMMA7

-- Lemma8
def FMEAN_REVERSE_MARKOV : thm := BLemma8.FMEAN_REVERSE_MARKOV
def HJ_JOIN_POINT_RIGHT : thm := BLemma8.HJ_JOIN_POINT_RIGHT
def HJ_DENSITY_COMMON : thm := BLemma8.HJ_DENSITY_COMMON
def HJ_DENSITY_COMPL : thm := BLemma8.HJ_DENSITY_COMPL
def CARD_RESTRICT_SUM : thm := BLemma8.CARD_RESTRICT_SUM
def DKT_ETA_BOUND : thm := BLemma8.DKT_ETA_BOUND
def DKT_LEMMA8 : thm := BLemma8.DKT_LEMMA8

-- Insensitive
def hj_replace : thm := BInsensitive.hj_replace
def hj_insensitive : thm := BInsensitive.hj_insensitive
def HJ_INSENSITIVE_COMPL : thm := BInsensitive.HJ_INSENSITIVE_COMPL
def HJ_INSENSITIVE_UNIV : thm := BInsensitive.HJ_INSENSITIVE_UNIV
def HJ_INSENSITIVE_REPLACE : thm := BInsensitive.HJ_INSENSITIVE_REPLACE
def HJ_REPLACE_WORD : thm := BInsensitive.HJ_REPLACE_WORD
def HJ_REPLACE_LINE : thm := BInsensitive.HJ_REPLACE_LINE
def HJ_CUBE_SUC_CASES : thm := BInsensitive.HJ_CUBE_SUC_CASES
def HJ_LINE_NOT_WORD : thm := BInsensitive.HJ_LINE_NOT_WORD
def HJ_LINES_EQ_DIFF : thm := BInsensitive.HJ_LINES_EQ_DIFF
def CARD_HJ_LINES : thm := BInsensitive.CARD_HJ_LINES
def HJ_LINE_EXTEND : thm := BInsensitive.HJ_LINE_EXTEND
def HJ_LINE_FREE_POINTS : thm := BInsensitive.HJ_LINE_FREE_POINTS
def HJ_DENSITY_SMALL_CUBE : thm := BInsensitive.HJ_DENSITY_SMALL_CUBE
def DKT_POW_RATIO_SMALL : thm := BInsensitive.DKT_POW_RATIO_SMALL
def DKT_PARTITION_SUM : thm := BInsensitive.DKT_PARTITION_SUM
def HJ_DENSITY_PARTITION : thm := BInsensitive.HJ_DENSITY_PARTITION

-- Lemma10
def DKT_PARTITION_INCREMENT : thm := BLemma10.DKT_PARTITION_INCREMENT
def DKT_LEMMA10 : thm := BLemma10.DKT_LEMMA10

-- Cor11
def HJ_DENSITY_CUBE : thm := BCor11.HJ_DENSITY_CUBE
def HJ_DENSITY_COMPL_CUBE : thm := BCor11.HJ_DENSITY_COMPL_CUBE
def DKT_COR11 : thm := BCor11.DKT_COR11

-- Tilings
def hj_tiling : thm := BTilings.hj_tiling
def hj_tiling_union : thm := BTilings.hj_tiling_union
def HJ_TILING_EMPTY : thm := BTilings.HJ_TILING_EMPTY
def HJ_TILING_UNION_EMPTY : thm := BTilings.HJ_TILING_UNION_EMPTY
def HJ_TILING_UNION_SUBSET : thm := BTilings.HJ_TILING_UNION_SUBSET
def HJ_TILING_UNION_CUBE : thm := BTilings.HJ_TILING_UNION_CUBE
def HJ_TILING_INJ : thm := BTilings.HJ_TILING_INJ
def CARD_HJ_TILING_UNION_RESTRICT : thm := BTilings.CARD_HJ_TILING_UNION_RESTRICT
def HJ_DENSITY_TILING_UNION_RESTRICT : thm := BTilings.HJ_DENSITY_TILING_UNION_RESTRICT
def HJ_TILING_AVERAGE : thm := BTilings.HJ_TILING_AVERAGE

-- BlockInsert
def HJ_REPLACE_CONCAT : thm := BBlockInsert.HJ_REPLACE_CONCAT
def HJ_INSENSITIVE_SECTION_PREFIX : thm := BBlockInsert.HJ_INSENSITIVE_SECTION_PREFIX
def HJ_INSENSITIVE_SECTION_SUFFIX : thm := BBlockInsert.HJ_INSENSITIVE_SECTION_SUFFIX
def HJ_INSENSITIVE_FORALL : thm := BBlockInsert.HJ_INSENSITIVE_FORALL
def HJ_INSENSITIVE_DIFF : thm := BBlockInsert.HJ_INSENSITIVE_DIFF
def HJ_INSENSITIVE_PULLBACK : thm := BBlockInsert.HJ_INSENSITIVE_PULLBACK
def HJ_INSENSITIVE_TRANSFER : thm := BBlockInsert.HJ_INSENSITIVE_TRANSFER
def hj_insert : thm := BBlockInsert.hj_insert
def HJ_INSERT_CUBE : thm := BBlockInsert.HJ_INSERT_CUBE
def HJ_INSERT_CONCAT : thm := BBlockInsert.HJ_INSERT_CONCAT
def HJ_INSERT_INJ : thm := BBlockInsert.HJ_INSERT_INJ
def SUM_HJ_INSERT : thm := BBlockInsert.SUM_HJ_INSERT
def HJ_DENSITY_INSERT : thm := BBlockInsert.HJ_DENSITY_INSERT
def FINITE_HJ_SUBSPACES : thm := BBlockInsert.FINITE_HJ_SUBSPACES
def HJ_DROP_ZERO : thm := BBlockInsert.HJ_DROP_ZERO
def HJ_SUBST_TILE : thm := BBlockInsert.HJ_SUBST_TILE

-- TileStep
def HJ_INSENSITIVE_EQ : thm := BTileStep.HJ_INSENSITIVE_EQ
def HJ_INSENSITIVE_LEFTOVER : thm := BTileStep.HJ_INSENSITIVE_LEFTOVER
def DKT_TILE_STEP : thm := BTileStep.DKT_TILE_STEP

-- Lemma12
def HJ_DENSITY_SPLIT : thm := BLemma12.HJ_DENSITY_SPLIT
def HJ_TILING_UNION_UNION : thm := BLemma12.HJ_TILING_UNION_UNION
def HJ_TILING_APPEND : thm := BLemma12.HJ_TILING_APPEND
def HJ_TILING_ITER : thm := BLemma12.HJ_TILING_ITER
def HJ_TILING_INSENSITIVE : thm := BLemma12.HJ_TILING_INSENSITIVE

-- Cor13
def HJ_DENSITY_SUBADD : thm := BCor13.HJ_DENSITY_SUBADD
def HJ_TILING_COMPOSE : thm := BCor13.HJ_TILING_COMPOSE
def HJ_TILING_COMPOSE_DENS : thm := BCor13.HJ_TILING_COMPOSE_DENS
def HJ_TILING_STRUCTURED : thm := BCor13.HJ_TILING_STRUCTURED

-- DensityHJThm
def DKT_PROP6 : thm := BDensityHJThm.DKT_PROP6
def DENSITY_HALES_JEWETT_STEP : thm := BDensityHJThm.DENSITY_HALES_JEWETT_STEP
def DENSITY_HALES_JEWETT_1 : thm := BDensityHJThm.DENSITY_HALES_JEWETT_1
def DENSITY_HALES_JEWETT : thm := BDensityHJThm.DENSITY_HALES_JEWETT

-- WeightedDefs
def weighted_szemeredi : thm := BWeightedDefs.weighted_szemeredi
def MOD_AFFINE_MOD : thm := BWeightedDefs.MOD_AFFINE_MOD
def FMEAN_DIL_MOD : thm := BWeightedDefs.FMEAN_DIL_MOD
def FMEAN_AP_AFFINE : thm := BWeightedDefs.FMEAN_AP_AFFINE
def NSUM_HJ_LINE_POINT_GEN : thm := BWeightedDefs.NSUM_HJ_LINE_POINT_GEN
def HJ_LINE_WILDCARDS : thm := BWeightedDefs.HJ_LINE_WILDCARDS
def NSUM_HJ_LINE_POINT : thm := BWeightedDefs.NSUM_HJ_LINE_POINT

-- APBound
def FMEAN_HJ_DENSITY_AFFINE : thm := BAPBound.FMEAN_HJ_DENSITY_AFFINE
def FMEAN_HJ_LINE_AP : thm := BAPBound.FMEAN_HJ_LINE_AP
def HJ_LINE_COUNT_BOUND : thm := BAPBound.HJ_LINE_COUNT_BOUND
def SZEMEREDI_AP_INDICATOR_BOUND : thm := BAPBound.SZEMEREDI_AP_INDICATOR_BOUND

-- WeightedThm
def WEIGHTED_SZEMEREDI_DHJ : thm := BWeightedThm.WEIGHTED_SZEMEREDI_DHJ
def WEIGHTED_SZEMEREDI : thm := BWeightedThm.WEIGHTED_SZEMEREDI

-- ModAP
def CARD_PAIRS_SUM : thm := BModAP.CARD_PAIRS_SUM
def AP_COUNT_NONTRIVIAL : thm := BModAP.AP_COUNT_NONTRIVIAL
def MOD_AP_LINEAR : thm := BModAP.MOD_AP_LINEAR
def MOD_AP_CASES : thm := BModAP.MOD_AP_CASES
def MOD_ADD_LCANCEL : thm := BModAP.MOD_ADD_LCANCEL

-- UpDown
def SZEMEREDI_UP_PROGRESSION : thm := BUpDown.SZEMEREDI_UP_PROGRESSION
def SZEMEREDI_DOWN_PROGRESSION : thm := BUpDown.SZEMEREDI_DOWN_PROGRESSION

-- Pairs
def PROGRESSIONS_FROM_PAIRS : thm := BPairs.PROGRESSIONS_FROM_PAIRS

-- SzemerediThm
def SZEMEREDI_COUNT : thm := BSzemerediThm.SZEMEREDI_COUNT
def SZEMEREDI : thm := BSzemerediThm.SZEMEREDI
def ROTH : thm := BSzemerediThm.ROTH
def SZEMEREDI_DENSITY : thm := BSzemerediThm.SZEMEREDI_DENSITY

-- VdW
def VAN_DER_WAERDEN : thm := BVdW.VAN_DER_WAERDEN
def FMEAN_SHIFT_HJ_CUBE : thm := BVdW.FMEAN_SHIFT_HJ_CUBE
def HJ_DENSITY_SHIFT_MEAN : thm := BVdW.HJ_DENSITY_SHIFT_MEAN

-- Multidim
def MULTIDIM_SZEMEREDI : thm := BMultidim.MULTIDIM_SZEMEREDI
def GALLAI_WITT : thm := BMultidim.GALLAI_WITT
def CORNERS : thm := BMultidim.CORNERS

/-- `needs "Library/szemeredi.ml"`: already done by importing this module. -/
def ensureSzemeredi : IO Unit := pure ()

end SessionLibrary.Szemeredi
