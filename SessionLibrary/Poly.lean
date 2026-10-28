/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/poly.ml.                              -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Poly.lean

  The session half of the poly.ml translation: it supplies
  HolLibrary.Poly's dependencies from Session and SessionLibrary.Analysis,
  and exports every name under its HOL Light name.  Importing this module is
  `needs "Library/poly.ml"`; its `needs "Library/analysis.ml"` is the import
  of SessionLibrary.Analysis.  The bundles are built by `initialize` when
  the module is loaded, in file order.
-/

import Session
import HolLibrary.Poly
import SessionLibrary.Analysis

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Poly

/-- The core theorems poly.ml uses. -/
def core1 : HolLibrary.Poly.CoreThms1 where
  ADD1 := Session.ADD1
  ADD_CLAUSES := Session.ADD_CLAUSES
  ALL := Session.listDefs.ALL
  ARITH := Session.ARITH
  COND_CLAUSES := Session.COND_CLAUSES
  CONS_11 := Session.listThms1.CONS_11
  CONS_HD_TL := Session.listThms2.CONS_HD_TL
  DE_MORGAN_THM := Session.DE_MORGAN_THM
  DIFF_ADD := SessionLibrary.Analysis.«DIFF_ADD»
  DIFF_CMUL := SessionLibrary.Analysis.«DIFF_CMUL»
  DIFF_CONST := SessionLibrary.Analysis.«DIFF_CONST»
  DIFF_CONT := SessionLibrary.Analysis.«DIFF_CONT»
  DIFF_POW := SessionLibrary.Analysis.«DIFF_POW»
  DIFF_UNIQ := SessionLibrary.Analysis.«DIFF_UNIQ»
  EL := Session.listDefs.EL
  EQ_REFL := Session.EQ_REFL
  EQ_TRANS := Session.EQ_TRANS
  EXTENSION := Session.EXTENSION
  FINITE_RULES := Session.FINITE_RULES
  FINITE_SUBSET := Session.FINITE_SUBSET
  FUN_EQ_THM := Session.FUN_EQ_THM
  HD := Session.listDefs.HD
  IN_ELIM_THM := Session.IN_ELIM_THM
  IN_INSERT := Session.IN_INSERT
  ITERATE_CLAUSES_NUMSEG := Session.ITERATE_CLAUSES_NUMSEG
  IVT := SessionLibrary.Analysis.«IVT»
  LE := Session.LE
  LEFT_AND_FORALL_THM := Session.LEFT_AND_FORALL_THM
  LEFT_IMP_EXISTS_THM := Session.LEFT_IMP_EXISTS_THM
  LENGTH := Session.listDefs.LENGTH
  LENGTH_EQ_NIL := Session.listThms1.LENGTH_EQ_NIL
  LE_0 := Session.LE_0
  LE_EXISTS := Session.LE_EXISTS
  LE_REFL := Session.LE_REFL
  LE_SUC_LT := Session.LE_SUC_LT
  LT := Session.LT
  LT_ADD_LCANCEL := Session.LT_ADD_LCANCEL
  LT_CASES := Session.LT_CASES
  LT_SUC_LE := Session.LT_SUC_LE
  MAP := Session.listDefs.MAP
  MONOIDAL_REAL_ADD := Session.MONOIDAL_REAL_ADD
  MVT := SessionLibrary.Analysis.«MVT»
  NOT_CONS_NIL := Session.listThms1.NOT_CONS_NIL
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_FORALL_THM := Session.NOT_FORALL_THM
  NOT_IN_EMPTY := Session.NOT_IN_EMPTY
  NOT_LE := Session.NOT_LE
  NOT_SUC := Session.NOT_SUC
  NSUM_LMUL := Session.NSUM_LMUL
  POW_1 := SessionLibrary.Analysis.«POW_1»
  PRE := Session.PRE
  REAL_ABS_0 := Session.REAL_ABS_0
  REAL_ABS_MUL := Session.REAL_ABS_MUL
  REAL_ABS_POS := Session.REAL_ABS_POS
  REAL_ABS_TRIANGLE := Session.REAL_ABS_TRIANGLE
  REAL_ADD_AC := Session.REAL_ADD_AC
  REAL_ADD_ASSOC := Session.REAL_ADD_ASSOC
  REAL_ADD_LDISTRIB := Session.REAL_ADD_LDISTRIB
  REAL_ADD_LID := Session.REAL_ADD_LID
  REAL_ADD_RDISTRIB := Session.REAL_ADD_RDISTRIB
  REAL_ADD_RID := Session.REAL_ADD_RID
  REAL_ADD_SYM := Session.REAL_ADD_SYM
  REAL_ENTIRE := Session.REAL_ENTIRE
  REAL_EQ_ADD_LCANCEL := Session.REAL_EQ_ADD_LCANCEL
  REAL_EQ_MUL_LCANCEL := Session.REAL_EQ_MUL_LCANCEL
  REAL_LDISTRIB := SessionLibrary.Analysis.«REAL_LDISTRIB»
  REAL_LE_LADD := SessionLibrary.Analysis.«REAL_LE_LADD»
  REAL_LE_MUL2 := Session.REAL_LE_MUL2
  REAL_LE_REFL := SessionLibrary.Analysis.«REAL_LE_REFL»
  REAL_LE_TRANS := SessionLibrary.Analysis.«REAL_LE_TRANS»
/-- The core theorems poly.ml uses. -/
def core2 : HolLibrary.Poly.CoreThms2 where
  REAL_LT_ADDR := Session.REAL_LT_ADDR
  REAL_LT_IMP_LE := SessionLibrary.Analysis.«REAL_LT_IMP_LE»
  REAL_LT_LE := SessionLibrary.Analysis.«REAL_LT_LE»
  REAL_LT_NEGTOTAL := SessionLibrary.Analysis.«REAL_LT_NEGTOTAL»
  REAL_LT_REFL := Session.REAL_LT_REFL
  REAL_MUL_AC := Session.REAL_MUL_AC
  REAL_MUL_ASSOC := Session.REAL_MUL_ASSOC
  REAL_MUL_LID := Session.REAL_MUL_LID
  REAL_MUL_LNEG := Session.REAL_MUL_LNEG
  REAL_MUL_LZERO := SessionLibrary.Analysis.«REAL_MUL_LZERO»
  REAL_MUL_RID := SessionLibrary.Analysis.«REAL_MUL_RID»
  REAL_MUL_RINV := SessionLibrary.Analysis.«REAL_MUL_RINV»
  REAL_MUL_RNEG := Session.REAL_MUL_RNEG
  REAL_MUL_RZERO := SessionLibrary.Analysis.«REAL_MUL_RZERO»
  REAL_MUL_SYM := Session.REAL_MUL_SYM
  REAL_NEG_NEG := SessionLibrary.Analysis.«REAL_NEG_NEG»
  REAL_OF_NUM_ADD := Session.REAL_OF_NUM_ADD
  REAL_OF_NUM_EQ := Session.REAL_OF_NUM_EQ
  REAL_OF_NUM_SUC := Session.REAL_OF_NUM_SUC
  REAL_SUB_REFL := SessionLibrary.Analysis.«REAL_SUB_REFL»
  RIGHT_FORALL_IMP_THM := Session.RIGHT_FORALL_IMP_THM
  RIGHT_IMP_EXISTS_THM := Session.RIGHT_IMP_EXISTS_THM
  SELECT_UNIQUE := Session.SELECT_UNIQUE
  SUBSET := Session.SUBSET
  SUC_INJ := Session.SUC_INJ
  SUC_SUB1 := SessionLibrary.Analysis.«SUC_SUB1»
  SUM_COMBINE_R := Session.SUM_COMBINE_R
  SUM_LMUL := Session.SUM_LMUL
  SUM_OFFSET_0 := Session.SUM_OFFSET_0
  SUM_SING := Session.SUM_SING
  TL := Session.listDefs.TL
  differentiable := SessionLibrary.Analysis.«differentiable»
  list_RECURSION := Session.list_RECURSION
  monoidal := Session.monoidal
  neutral := Session.neutral
  num_RECURSION := Session.num_RECURSION
  pow := SessionLibrary.Analysis.«pow»
  real_gt := Session.real_gt
  real_pow := Session.real_pow
  real_sub := Session.real_sub
/-- The core theorems poly.ml uses. -/
def core3 : HolLibrary.Poly.CoreThms3 where
/-- The core theorems poly.ml uses. -/
def core4 : HolLibrary.Poly.CoreThms4 where

/-- What poly.ml uses from Session. -/
def deps : HolLibrary.Poly.PolyDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  new_recursive_definition ax s := do
    ExceptT.mk (Session.new_recursive_definition ax (← HolLight.q s))
  prioritize_real := Session.prioritize_real
  parse_as_infix := Session.parse_as_infix
  overload_interface s t := ExceptT.mk (Session.overload_interface s t)
  override_interface s t := ExceptT.mk (Session.override_interface s t)
  num_CONV := Session.num_CONV
  ETA_CONV t := pure (Session.ETA_CONV t)
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  MESON_TAC := Session.MESON_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH3 t)
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC2
  INDUCT_TAC := Session.INDUCT_TAC
  LIST_INDUCT_TAC := Session.LIST_INDUCT_TAC
  prove_recursive_functions_exist ax t :=
    ExceptT.mk (Session.prove_recursive_functions_exist ax t)
  REAL_RAT_MUL_CONV := Session.REAL_RAT_MUL_CONV
  REAL_RAT_ADD_CONV := Session.REAL_RAT_ADD_CONV
  REAL_RAT_EQ_CONV := Session.REAL_RAT_EQ_CONV
  NUM_SUC_CONV := Session.NUM_SUC_CONV
  SIMP_RULE ths th := ExceptT.mk (Session.SIMP_RULE ths th)
  SELECT_ELIM_TAC := Session.SELECT_ELIM_TAC
  NUMSEG_CONV := Session.NUMSEG_CONV
  reduce_interface s t := ExceptT.mk (Session.reduce_interface s t)
  unparse_as_infix := HolCore.Printer.unparse_as_infix
  core1 := core1
  core2 := core2
  core3 := core3
  core4 := core4

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} (name : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in poly.ml order. -/

initialize BDefs : HolLibrary.Poly.Defs ←
  ioB "setupDefs" <|
    (HolLibrary.Poly.setupDefs deps).run

initialize BConsequences : HolLibrary.Poly.Consequences ←
  ioB "setupConsequences" <|
    (HolLibrary.Poly.setupConsequences deps BDefs).run

initialize BDerivs : HolLibrary.Poly.Derivs ←
  ioB "setupDerivs" <|
    (HolLibrary.Poly.setupDerivs deps BDefs BConsequences).run

initialize BRootsFinite : HolLibrary.Poly.RootsFinite ←
  ioB "setupRootsFinite" <|
    (HolLibrary.Poly.setupRootsFinite deps BDefs BConsequences BDerivs).run

initialize BEntire : HolLibrary.Poly.Entire ←
  ioB "setupEntire" <|
    (HolLibrary.Poly.setupEntire deps BDefs BConsequences BRootsFinite).run

initialize BZero : HolLibrary.Poly.Zero ←
  ioB "setupZero" <|
    (HolLibrary.Poly.setupZero deps BDefs BRootsFinite).run

initialize BTrivial : HolLibrary.Poly.Trivial ←
  ioB "setupTrivial" <|
    (HolLibrary.Poly.setupTrivial deps BDefs BConsequences BDerivs BZero).run

initialize BDivides : HolLibrary.Poly.Divides ←
  ioB "setupDivides" <|
    (HolLibrary.Poly.setupDivides deps BDefs BConsequences BDerivs).run

initialize BOrder : HolLibrary.Poly.Order ←
  ioB "setupOrder" <|
    (HolLibrary.Poly.setupOrder deps BDefs BConsequences BDerivs BEntire BTrivial BDivides).run

initialize BSquarefree : HolLibrary.Poly.Squarefree ←
  ioB "setupSquarefree" <|
    (HolLibrary.Poly.setupSquarefree deps BDefs BConsequences BDerivs BEntire BTrivial BDivides BOrder).run

initialize BNormalize : HolLibrary.Poly.Normalize ←
  ioB "setupNormalize" <|
    (HolLibrary.Poly.setupNormalize deps BDefs BRootsFinite BZero).run

initialize BConvs : HolLibrary.Poly.Convs ←
  ioB "setupConvs" <|
    (HolLibrary.Poly.setupConvs deps BDefs BNormalize).run

initialize BNonNil : HolLibrary.Poly.NonNil ←
  ioB "setupNonNil" <|
    (HolLibrary.Poly.setupNonNil deps BDefs).run

initialize BHeadsTails : HolLibrary.Poly.HeadsTails ←
  ioB "setupHeadsTails" <|
    (HolLibrary.Poly.setupHeadsTails deps BDefs BNonNil).run

initialize BAdditionalLemmas : HolLibrary.Poly.AdditionalLemmas ←
  ioB "setupAdditionalLemmas" <|
    (HolLibrary.Poly.setupAdditionalLemmas deps BDefs BNonNil BHeadsTails).run

initialize BLengths : HolLibrary.Poly.Lengths ←
  ioB "setupLengths" <|
    (HolLibrary.Poly.setupLengths deps BDefs BConsequences BNonNil BHeadsTails BAdditionalLemmas).run


-- Defs
def poly : thm := BDefs.poly
def POLY_CONST : thm := BDefs.POLY_CONST
def POLY_X : thm := BDefs.POLY_X
def poly_add : thm := BDefs.poly_add
def poly_cmul : thm := BDefs.poly_cmul
def poly_neg : thm := BDefs.poly_neg
def poly_mul : thm := BDefs.poly_mul
def poly_exp : thm := BDefs.poly_exp
def poly_diff_aux : thm := BDefs.poly_diff_aux
def poly_diff : thm := BDefs.poly_diff
def LENGTH_POLY_DIFF_AUX : thm := BDefs.LENGTH_POLY_DIFF_AUX
def LENGTH_POLY_DIFF : thm := BDefs.LENGTH_POLY_DIFF
def POLY_ADD_CLAUSES : thm := BDefs.POLY_ADD_CLAUSES
def POLY_CMUL_CLAUSES : thm := BDefs.POLY_CMUL_CLAUSES
def POLY_NEG_CLAUSES : thm := BDefs.POLY_NEG_CLAUSES
def POLY_MUL_CLAUSES : thm := BDefs.POLY_MUL_CLAUSES
def POLY_DIFF_CLAUSES : thm := BDefs.POLY_DIFF_CLAUSES

-- Consequences
def POLY_ADD : thm := BConsequences.POLY_ADD
def POLY_CMUL : thm := BConsequences.POLY_CMUL
def POLY_NEG : thm := BConsequences.POLY_NEG
def POLY_MUL : thm := BConsequences.POLY_MUL
def POLY_EXP : thm := BConsequences.POLY_EXP
def POLY_DIFF_LEMMA : thm := BConsequences.POLY_DIFF_LEMMA
def POLY_DIFF : thm := BConsequences.POLY_DIFF
def POLY_DIFFERENTIABLE : thm := BConsequences.POLY_DIFFERENTIABLE
def POLY_CONT : thm := BConsequences.POLY_CONT
def POLY_IVT_POS : thm := BConsequences.POLY_IVT_POS
def POLY_IVT_NEG : thm := BConsequences.POLY_IVT_NEG
def POLY_MVT : thm := BConsequences.POLY_MVT
def POLY_MVT_ADD : thm := BConsequences.POLY_MVT_ADD

-- Derivs
def POLY_ADD_RZERO : thm := BDerivs.POLY_ADD_RZERO
def POLY_MUL_ASSOC : thm := BDerivs.POLY_MUL_ASSOC
def POLY_EXP_ADD : thm := BDerivs.POLY_EXP_ADD
def POLY_DIFF_AUX_ADD : thm := BDerivs.POLY_DIFF_AUX_ADD
def POLY_DIFF_AUX_CMUL : thm := BDerivs.POLY_DIFF_AUX_CMUL
def POLY_DIFF_AUX_NEG : thm := BDerivs.POLY_DIFF_AUX_NEG
def POLY_DIFF_AUX_MUL_LEMMA : thm := BDerivs.POLY_DIFF_AUX_MUL_LEMMA
def POLY_DIFF_ADD : thm := BDerivs.POLY_DIFF_ADD
def POLY_DIFF_CMUL : thm := BDerivs.POLY_DIFF_CMUL
def POLY_DIFF_NEG : thm := BDerivs.POLY_DIFF_NEG
def POLY_DIFF_MUL_LEMMA : thm := BDerivs.POLY_DIFF_MUL_LEMMA
def POLY_DIFF_MUL : thm := BDerivs.POLY_DIFF_MUL
def POLY_DIFF_EXP : thm := BDerivs.POLY_DIFF_EXP
def POLY_DIFF_EXP_PRIME : thm := BDerivs.POLY_DIFF_EXP_PRIME
def POLY_LINEAR_REM : thm := BDerivs.POLY_LINEAR_REM
def POLY_LINEAR_DIVIDES : thm := BDerivs.POLY_LINEAR_DIVIDES
def POLY_LENGTH_MUL : thm := BDerivs.POLY_LENGTH_MUL

-- RootsFinite
def POLY_ROOTS_INDEX_LEMMA : thm := BRootsFinite.POLY_ROOTS_INDEX_LEMMA
def POLY_ROOTS_INDEX_LENGTH : thm := BRootsFinite.POLY_ROOTS_INDEX_LENGTH
def POLY_ROOTS_FINITE_LEMMA : thm := BRootsFinite.POLY_ROOTS_FINITE_LEMMA
def FINITE_LEMMA : thm := BRootsFinite.FINITE_LEMMA
def POLY_ROOTS_FINITE : thm := BRootsFinite.POLY_ROOTS_FINITE

-- Entire
def POLY_ENTIRE_LEMMA : thm := BEntire.POLY_ENTIRE_LEMMA
def POLY_ENTIRE : thm := BEntire.POLY_ENTIRE
def POLY_MUL_LCANCEL : thm := BEntire.POLY_MUL_LCANCEL
def POLY_EXP_EQ_0 : thm := BEntire.POLY_EXP_EQ_0
def POLY_PRIME_EQ_0 : thm := BEntire.POLY_PRIME_EQ_0
def POLY_EXP_PRIME_EQ_0 : thm := BEntire.POLY_EXP_PRIME_EQ_0

-- Zero
def POLY_ZERO_LEMMA : thm := BZero.POLY_ZERO_LEMMA
def POLY_ZERO : thm := BZero.POLY_ZERO

-- Trivial
def POLY_DIFF_AUX_ISZERO : thm := BTrivial.POLY_DIFF_AUX_ISZERO
def POLY_DIFF_ISZERO : thm := BTrivial.POLY_DIFF_ISZERO
def POLY_DIFF_ZERO : thm := BTrivial.POLY_DIFF_ZERO
def POLY_DIFF_WELLDEF : thm := BTrivial.POLY_DIFF_WELLDEF

-- Divides
def divides : thm := BDivides.divides
def POLY_PRIMES : thm := BDivides.POLY_PRIMES
def POLY_DIVIDES_REFL : thm := BDivides.POLY_DIVIDES_REFL
def POLY_DIVIDES_TRANS : thm := BDivides.POLY_DIVIDES_TRANS
def POLY_DIVIDES_EXP : thm := BDivides.POLY_DIVIDES_EXP
def POLY_EXP_DIVIDES : thm := BDivides.POLY_EXP_DIVIDES
def POLY_DIVIDES_ADD : thm := BDivides.POLY_DIVIDES_ADD
def POLY_DIVIDES_SUB : thm := BDivides.POLY_DIVIDES_SUB
def POLY_DIVIDES_SUB2 : thm := BDivides.POLY_DIVIDES_SUB2
def POLY_DIVIDES_ZERO : thm := BDivides.POLY_DIVIDES_ZERO

-- Order
def POLY_ORDER_EXISTS : thm := BOrder.POLY_ORDER_EXISTS
def POLY_ORDER : thm := BOrder.POLY_ORDER
def order : thm := BOrder.order
def ORDER : thm := BOrder.ORDER
def ORDER_THM : thm := BOrder.ORDER_THM
def ORDER_UNIQUE : thm := BOrder.ORDER_UNIQUE
def ORDER_POLY : thm := BOrder.ORDER_POLY
def ORDER_ROOT : thm := BOrder.ORDER_ROOT
def ORDER_DIVIDES : thm := BOrder.ORDER_DIVIDES
def ORDER_DECOMP : thm := BOrder.ORDER_DECOMP
def ORDER_MUL : thm := BOrder.ORDER_MUL
def ORDER_DIFF : thm := BOrder.ORDER_DIFF

-- Squarefree
def POLY_SQUAREFREE_DECOMP_ORDER : thm := BSquarefree.POLY_SQUAREFREE_DECOMP_ORDER
def rsquarefree : thm := BSquarefree.rsquarefree
def RSQUAREFREE_ROOTS : thm := BSquarefree.RSQUAREFREE_ROOTS
def RSQUAREFREE_DECOMP : thm := BSquarefree.RSQUAREFREE_DECOMP
def POLY_SQUAREFREE_DECOMP : thm := BSquarefree.POLY_SQUAREFREE_DECOMP

-- Normalize
def normalize : thm := BNormalize.normalize
def POLY_NORMALIZE : thm := BNormalize.POLY_NORMALIZE
def degree : thm := BNormalize.degree
def DEGREE_ZERO : thm := BNormalize.DEGREE_ZERO
def POLY_ROOTS_FINITE_SET : thm := BNormalize.POLY_ROOTS_FINITE_SET
def POLY_MONO : thm := BNormalize.POLY_MONO

-- Convs
def POLY_DIFF_CONV : term → IO (Except String thm) := fun t => (BConvs.POLY_DIFF_CONV t).run
def POLY_CMUL_CONV : term → IO (Except String thm) := fun t => (BConvs.POLY_CMUL_CONV t).run
def POLY_ADD_CONV : term → IO (Except String thm) := fun t => (BConvs.POLY_ADD_CONV t).run
def POLY_MUL_CONV : term → IO (Except String thm) := fun t => (BConvs.POLY_MUL_CONV t).run
def POLY_NORMALIZE_CONV : term → IO (Except String thm) := fun t => (BConvs.POLY_NORMALIZE_CONV t).run

-- NonNil
def NOT_POLY_CMUL_NIL : thm := BNonNil.NOT_POLY_CMUL_NIL
def NOT_POLY_MUL_NIL : thm := BNonNil.NOT_POLY_MUL_NIL
def NOT_POLY_EXP_NIL : thm := BNonNil.NOT_POLY_EXP_NIL
def NOT_POLY_EXP_X_NIL : thm := BNonNil.NOT_POLY_EXP_X_NIL
def POLY_CMUL_LID : thm := BNonNil.POLY_CMUL_LID
def POLY_MUL_LID : thm := BNonNil.POLY_MUL_LID
def POLY_MUL_RID : thm := BNonNil.POLY_MUL_RID
def POLY_ADD_SYM : thm := BNonNil.POLY_ADD_SYM
def POLY_ADD_ASSOC : thm := BNonNil.POLY_ADD_ASSOC

-- HeadsTails
def TL_POLY_MUL_X : thm := BHeadsTails.TL_POLY_MUL_X
def HD_POLY_MUL_X : thm := BHeadsTails.HD_POLY_MUL_X
def TL_POLY_EXP_X_SUC : thm := BHeadsTails.TL_POLY_EXP_X_SUC
def HD_POLY_EXP_X_SUC : thm := BHeadsTails.HD_POLY_EXP_X_SUC
def HD_POLY_ADD : thm := BHeadsTails.HD_POLY_ADD
def HD_POLY_CMUL : thm := BHeadsTails.HD_POLY_CMUL
def TL_POLY_CMUL : thm := BHeadsTails.TL_POLY_CMUL
def HD_POLY_MUL : thm := BHeadsTails.HD_POLY_MUL
def HD_POLY_EXP : thm := BHeadsTails.HD_POLY_EXP

-- AdditionalLemmas
def POLY_ADD_IDENT : thm := BAdditionalLemmas.POLY_ADD_IDENT
def POLY_ADD_NEUTRAL : thm := BAdditionalLemmas.POLY_ADD_NEUTRAL
def MONOIDAL_POLY_ADD : thm := BAdditionalLemmas.MONOIDAL_POLY_ADD
def POLY_DIFF_AUX_ADD_LEMMA : thm := BAdditionalLemmas.POLY_DIFF_AUX_ADD_LEMMA
def POLYDIFF_ADD : thm := BAdditionalLemmas.POLYDIFF_ADD
def POLY_DIFF_AUX_POLY_CMUL : thm := BAdditionalLemmas.POLY_DIFF_AUX_POLY_CMUL
def POLY_CMUL_POLY_DIFF : thm := BAdditionalLemmas.POLY_CMUL_POLY_DIFF

-- Lengths
def POLY_CMUL_LENGTH : thm := BLengths.POLY_CMUL_LENGTH
def POLY_ADD_LENGTH : thm := BLengths.POLY_ADD_LENGTH
def POLY_MUL_LENGTH : thm := BLengths.POLY_MUL_LENGTH
def POLY_EXP_X_REC : thm := BLengths.POLY_EXP_X_REC
def POLY_MUL_LENGTH2 : thm := BLengths.POLY_MUL_LENGTH2
def POLY_EXP_X_LENGTH : thm := BLengths.POLY_EXP_X_LENGTH
def POLY_SUM_EQUIV : thm := BLengths.POLY_SUM_EQUIV
def ITERATE_RADD_POLYADD : thm := BLengths.ITERATE_RADD_POLYADD
/-- `needs "Library/poly.ml"`: already done by importing this module. -/
def ensurePoly : IO Unit := pure ()

end SessionLibrary.Poly
