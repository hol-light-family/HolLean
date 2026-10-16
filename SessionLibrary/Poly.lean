/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/poly.ml.                              -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/Poly.lean

  The `unsafe` half of the poly.ml translation: it supplies HolLibrary.Poly's
  dependencies from Session and SessionLibrary.Analysis, builds the bundles once, in order,
  and exports every name under its HOL Light name.  `ensurePoly` is
  `needs "Library/poly.ml"` (which first does `needs "Library/analysis.ml"`).

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/Poly.lean by tools/polydiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.Poly
import SessionLibrary.Analysis

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.Poly

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems poly.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.Poly.CoreThms1 where
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
unsafe def core2 (_ : Unit) : HolLibrary.Poly.CoreThms2 where
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
unsafe def core3 (_ : Unit) : HolLibrary.Poly.CoreThms3 where
/-- The core theorems poly.ml uses. -/
unsafe def core4 (_ : Unit) : HolLibrary.Poly.CoreThms4 where
-- @@CORE END

/-- What poly.ml uses from Session. -/
unsafe def deps (_ : Unit) : HolLibrary.Poly.PolyDeps where
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
  core1 := core1 ()
  core2 := core2 ()
  core3 := core3 ()
  core4 := core4 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`, and MATCH_CONV's basic conversions, which HOL
    Light adds loading ind_types.ml), then analysis.ml, which poly.ml needs. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      SessionLibrary.Analysis.ensureAnalysis
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.Poly: {name}"

/- The bundles, in file order; each forces the one before it. -/

-- @@BUNDLES BEGIN
initialize theDefs : IO.Ref (Option HolLibrary.Poly.Defs) ← IO.mkRef none
unsafe def BDefs : HolLibrary.Poly.Defs :=
  cached theDefs "setupDefs" fun _ => do
    (HolLibrary.Poly.setupDefs (deps ())).run

initialize theConsequences : IO.Ref (Option HolLibrary.Poly.Consequences) ← IO.mkRef none
unsafe def BConsequences : HolLibrary.Poly.Consequences :=
  cached theConsequences "setupConsequences" fun _ => do
    let _ ← IO.mkRef BDefs.poly
    (HolLibrary.Poly.setupConsequences (deps ()) BDefs).run

initialize theDerivs : IO.Ref (Option HolLibrary.Poly.Derivs) ← IO.mkRef none
unsafe def BDerivs : HolLibrary.Poly.Derivs :=
  cached theDerivs "setupDerivs" fun _ => do
    let _ ← IO.mkRef BConsequences.POLY_ADD
    (HolLibrary.Poly.setupDerivs (deps ()) BDefs BConsequences).run

initialize theRootsFinite : IO.Ref (Option HolLibrary.Poly.RootsFinite) ← IO.mkRef none
unsafe def BRootsFinite : HolLibrary.Poly.RootsFinite :=
  cached theRootsFinite "setupRootsFinite" fun _ => do
    let _ ← IO.mkRef BDerivs.POLY_ADD_RZERO
    (HolLibrary.Poly.setupRootsFinite (deps ()) BDefs BConsequences BDerivs).run

initialize theEntire : IO.Ref (Option HolLibrary.Poly.Entire) ← IO.mkRef none
unsafe def BEntire : HolLibrary.Poly.Entire :=
  cached theEntire "setupEntire" fun _ => do
    let _ ← IO.mkRef BRootsFinite.POLY_ROOTS_INDEX_LEMMA
    (HolLibrary.Poly.setupEntire (deps ()) BDefs BConsequences BRootsFinite).run

initialize theZero : IO.Ref (Option HolLibrary.Poly.Zero) ← IO.mkRef none
unsafe def BZero : HolLibrary.Poly.Zero :=
  cached theZero "setupZero" fun _ => do
    let _ ← IO.mkRef BEntire.POLY_ENTIRE_LEMMA
    (HolLibrary.Poly.setupZero (deps ()) BDefs BRootsFinite).run

initialize theTrivial : IO.Ref (Option HolLibrary.Poly.Trivial) ← IO.mkRef none
unsafe def BTrivial : HolLibrary.Poly.Trivial :=
  cached theTrivial "setupTrivial" fun _ => do
    let _ ← IO.mkRef BZero.POLY_ZERO_LEMMA
    (HolLibrary.Poly.setupTrivial (deps ()) BDefs BConsequences BDerivs BZero).run

initialize theDivides : IO.Ref (Option HolLibrary.Poly.Divides) ← IO.mkRef none
unsafe def BDivides : HolLibrary.Poly.Divides :=
  cached theDivides "setupDivides" fun _ => do
    let _ ← IO.mkRef BTrivial.POLY_DIFF_AUX_ISZERO
    (HolLibrary.Poly.setupDivides (deps ()) BDefs BConsequences BDerivs).run

initialize theOrder : IO.Ref (Option HolLibrary.Poly.Order) ← IO.mkRef none
unsafe def BOrder : HolLibrary.Poly.Order :=
  cached theOrder "setupOrder" fun _ => do
    let _ ← IO.mkRef BDivides.divides
    (HolLibrary.Poly.setupOrder (deps ()) BDefs BConsequences BDerivs BEntire BTrivial BDivides).run

initialize theSquarefree : IO.Ref (Option HolLibrary.Poly.Squarefree) ← IO.mkRef none
unsafe def BSquarefree : HolLibrary.Poly.Squarefree :=
  cached theSquarefree "setupSquarefree" fun _ => do
    let _ ← IO.mkRef BOrder.POLY_ORDER_EXISTS
    (HolLibrary.Poly.setupSquarefree (deps ()) BDefs BConsequences BDerivs BEntire BTrivial BDivides BOrder).run

initialize theNormalize : IO.Ref (Option HolLibrary.Poly.Normalize) ← IO.mkRef none
unsafe def BNormalize : HolLibrary.Poly.Normalize :=
  cached theNormalize "setupNormalize" fun _ => do
    let _ ← IO.mkRef BSquarefree.POLY_SQUAREFREE_DECOMP_ORDER
    (HolLibrary.Poly.setupNormalize (deps ()) BDefs BRootsFinite BZero).run

initialize theConvs : IO.Ref (Option HolLibrary.Poly.Convs) ← IO.mkRef none
unsafe def BConvs : HolLibrary.Poly.Convs :=
  cached theConvs "setupConvs" fun _ => do
    let _ ← IO.mkRef BNormalize.normalize
    (HolLibrary.Poly.setupConvs (deps ()) BDefs BNormalize).run

initialize theNonNil : IO.Ref (Option HolLibrary.Poly.NonNil) ← IO.mkRef none
unsafe def BNonNil : HolLibrary.Poly.NonNil :=
  cached theNonNil "setupNonNil" fun _ => do
    let _ ← IO.mkRef BConvs.POLY_DIFF_CONV
    (HolLibrary.Poly.setupNonNil (deps ()) BDefs).run

initialize theHeadsTails : IO.Ref (Option HolLibrary.Poly.HeadsTails) ← IO.mkRef none
unsafe def BHeadsTails : HolLibrary.Poly.HeadsTails :=
  cached theHeadsTails "setupHeadsTails" fun _ => do
    let _ ← IO.mkRef BNonNil.NOT_POLY_CMUL_NIL
    (HolLibrary.Poly.setupHeadsTails (deps ()) BDefs BNonNil).run

initialize theAdditionalLemmas : IO.Ref (Option HolLibrary.Poly.AdditionalLemmas) ← IO.mkRef none
unsafe def BAdditionalLemmas : HolLibrary.Poly.AdditionalLemmas :=
  cached theAdditionalLemmas "setupAdditionalLemmas" fun _ => do
    let _ ← IO.mkRef BHeadsTails.TL_POLY_MUL_X
    (HolLibrary.Poly.setupAdditionalLemmas (deps ()) BDefs BNonNil BHeadsTails).run

initialize theLengths : IO.Ref (Option HolLibrary.Poly.Lengths) ← IO.mkRef none
unsafe def BLengths : HolLibrary.Poly.Lengths :=
  cached theLengths "setupLengths" fun _ => do
    let _ ← IO.mkRef BAdditionalLemmas.POLY_ADD_IDENT
    (HolLibrary.Poly.setupLengths (deps ()) BDefs BConsequences BNonNil BHeadsTails BAdditionalLemmas).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Defs
unsafe def poly : thm := BDefs.poly
unsafe def POLY_CONST : thm := BDefs.POLY_CONST
unsafe def POLY_X : thm := BDefs.POLY_X
unsafe def poly_add : thm := BDefs.poly_add
unsafe def poly_cmul : thm := BDefs.poly_cmul
unsafe def poly_neg : thm := BDefs.poly_neg
unsafe def poly_mul : thm := BDefs.poly_mul
unsafe def poly_exp : thm := BDefs.poly_exp
unsafe def poly_diff_aux : thm := BDefs.poly_diff_aux
unsafe def poly_diff : thm := BDefs.poly_diff
unsafe def LENGTH_POLY_DIFF_AUX : thm := BDefs.LENGTH_POLY_DIFF_AUX
unsafe def LENGTH_POLY_DIFF : thm := BDefs.LENGTH_POLY_DIFF
unsafe def POLY_ADD_CLAUSES : thm := BDefs.POLY_ADD_CLAUSES
unsafe def POLY_CMUL_CLAUSES : thm := BDefs.POLY_CMUL_CLAUSES
unsafe def POLY_NEG_CLAUSES : thm := BDefs.POLY_NEG_CLAUSES
unsafe def POLY_MUL_CLAUSES : thm := BDefs.POLY_MUL_CLAUSES
unsafe def POLY_DIFF_CLAUSES : thm := BDefs.POLY_DIFF_CLAUSES

-- Consequences
unsafe def POLY_ADD : thm := BConsequences.POLY_ADD
unsafe def POLY_CMUL : thm := BConsequences.POLY_CMUL
unsafe def POLY_NEG : thm := BConsequences.POLY_NEG
unsafe def POLY_MUL : thm := BConsequences.POLY_MUL
unsafe def POLY_EXP : thm := BConsequences.POLY_EXP
unsafe def POLY_DIFF_LEMMA : thm := BConsequences.POLY_DIFF_LEMMA
unsafe def POLY_DIFF : thm := BConsequences.POLY_DIFF
unsafe def POLY_DIFFERENTIABLE : thm := BConsequences.POLY_DIFFERENTIABLE
unsafe def POLY_CONT : thm := BConsequences.POLY_CONT
unsafe def POLY_IVT_POS : thm := BConsequences.POLY_IVT_POS
unsafe def POLY_IVT_NEG : thm := BConsequences.POLY_IVT_NEG
unsafe def POLY_MVT : thm := BConsequences.POLY_MVT
unsafe def POLY_MVT_ADD : thm := BConsequences.POLY_MVT_ADD

-- Derivs
unsafe def POLY_ADD_RZERO : thm := BDerivs.POLY_ADD_RZERO
unsafe def POLY_MUL_ASSOC : thm := BDerivs.POLY_MUL_ASSOC
unsafe def POLY_EXP_ADD : thm := BDerivs.POLY_EXP_ADD
unsafe def POLY_DIFF_AUX_ADD : thm := BDerivs.POLY_DIFF_AUX_ADD
unsafe def POLY_DIFF_AUX_CMUL : thm := BDerivs.POLY_DIFF_AUX_CMUL
unsafe def POLY_DIFF_AUX_NEG : thm := BDerivs.POLY_DIFF_AUX_NEG
unsafe def POLY_DIFF_AUX_MUL_LEMMA : thm := BDerivs.POLY_DIFF_AUX_MUL_LEMMA
unsafe def POLY_DIFF_ADD : thm := BDerivs.POLY_DIFF_ADD
unsafe def POLY_DIFF_CMUL : thm := BDerivs.POLY_DIFF_CMUL
unsafe def POLY_DIFF_NEG : thm := BDerivs.POLY_DIFF_NEG
unsafe def POLY_DIFF_MUL_LEMMA : thm := BDerivs.POLY_DIFF_MUL_LEMMA
unsafe def POLY_DIFF_MUL : thm := BDerivs.POLY_DIFF_MUL
unsafe def POLY_DIFF_EXP : thm := BDerivs.POLY_DIFF_EXP
unsafe def POLY_DIFF_EXP_PRIME : thm := BDerivs.POLY_DIFF_EXP_PRIME
unsafe def POLY_LINEAR_REM : thm := BDerivs.POLY_LINEAR_REM
unsafe def POLY_LINEAR_DIVIDES : thm := BDerivs.POLY_LINEAR_DIVIDES
unsafe def POLY_LENGTH_MUL : thm := BDerivs.POLY_LENGTH_MUL

-- RootsFinite
unsafe def POLY_ROOTS_INDEX_LEMMA : thm := BRootsFinite.POLY_ROOTS_INDEX_LEMMA
unsafe def POLY_ROOTS_INDEX_LENGTH : thm := BRootsFinite.POLY_ROOTS_INDEX_LENGTH
unsafe def POLY_ROOTS_FINITE_LEMMA : thm := BRootsFinite.POLY_ROOTS_FINITE_LEMMA
unsafe def FINITE_LEMMA : thm := BRootsFinite.FINITE_LEMMA
unsafe def POLY_ROOTS_FINITE : thm := BRootsFinite.POLY_ROOTS_FINITE

-- Entire
unsafe def POLY_ENTIRE_LEMMA : thm := BEntire.POLY_ENTIRE_LEMMA
unsafe def POLY_ENTIRE : thm := BEntire.POLY_ENTIRE
unsafe def POLY_MUL_LCANCEL : thm := BEntire.POLY_MUL_LCANCEL
unsafe def POLY_EXP_EQ_0 : thm := BEntire.POLY_EXP_EQ_0
unsafe def POLY_PRIME_EQ_0 : thm := BEntire.POLY_PRIME_EQ_0
unsafe def POLY_EXP_PRIME_EQ_0 : thm := BEntire.POLY_EXP_PRIME_EQ_0

-- Zero
unsafe def POLY_ZERO_LEMMA : thm := BZero.POLY_ZERO_LEMMA
unsafe def POLY_ZERO : thm := BZero.POLY_ZERO

-- Trivial
unsafe def POLY_DIFF_AUX_ISZERO : thm := BTrivial.POLY_DIFF_AUX_ISZERO
unsafe def POLY_DIFF_ISZERO : thm := BTrivial.POLY_DIFF_ISZERO
unsafe def POLY_DIFF_ZERO : thm := BTrivial.POLY_DIFF_ZERO
unsafe def POLY_DIFF_WELLDEF : thm := BTrivial.POLY_DIFF_WELLDEF

-- Divides
unsafe def divides : thm := BDivides.divides
unsafe def POLY_PRIMES : thm := BDivides.POLY_PRIMES
unsafe def POLY_DIVIDES_REFL : thm := BDivides.POLY_DIVIDES_REFL
unsafe def POLY_DIVIDES_TRANS : thm := BDivides.POLY_DIVIDES_TRANS
unsafe def POLY_DIVIDES_EXP : thm := BDivides.POLY_DIVIDES_EXP
unsafe def POLY_EXP_DIVIDES : thm := BDivides.POLY_EXP_DIVIDES
unsafe def POLY_DIVIDES_ADD : thm := BDivides.POLY_DIVIDES_ADD
unsafe def POLY_DIVIDES_SUB : thm := BDivides.POLY_DIVIDES_SUB
unsafe def POLY_DIVIDES_SUB2 : thm := BDivides.POLY_DIVIDES_SUB2
unsafe def POLY_DIVIDES_ZERO : thm := BDivides.POLY_DIVIDES_ZERO

-- Order
unsafe def POLY_ORDER_EXISTS : thm := BOrder.POLY_ORDER_EXISTS
unsafe def POLY_ORDER : thm := BOrder.POLY_ORDER
unsafe def order : thm := BOrder.order
unsafe def ORDER : thm := BOrder.ORDER
unsafe def ORDER_THM : thm := BOrder.ORDER_THM
unsafe def ORDER_UNIQUE : thm := BOrder.ORDER_UNIQUE
unsafe def ORDER_POLY : thm := BOrder.ORDER_POLY
unsafe def ORDER_ROOT : thm := BOrder.ORDER_ROOT
unsafe def ORDER_DIVIDES : thm := BOrder.ORDER_DIVIDES
unsafe def ORDER_DECOMP : thm := BOrder.ORDER_DECOMP
unsafe def ORDER_MUL : thm := BOrder.ORDER_MUL
unsafe def ORDER_DIFF : thm := BOrder.ORDER_DIFF

-- Squarefree
unsafe def POLY_SQUAREFREE_DECOMP_ORDER : thm := BSquarefree.POLY_SQUAREFREE_DECOMP_ORDER
unsafe def rsquarefree : thm := BSquarefree.rsquarefree
unsafe def RSQUAREFREE_ROOTS : thm := BSquarefree.RSQUAREFREE_ROOTS
unsafe def RSQUAREFREE_DECOMP : thm := BSquarefree.RSQUAREFREE_DECOMP
unsafe def POLY_SQUAREFREE_DECOMP : thm := BSquarefree.POLY_SQUAREFREE_DECOMP

-- Normalize
unsafe def normalize : thm := BNormalize.normalize
unsafe def POLY_NORMALIZE : thm := BNormalize.POLY_NORMALIZE
unsafe def degree : thm := BNormalize.degree
unsafe def DEGREE_ZERO : thm := BNormalize.DEGREE_ZERO
unsafe def POLY_ROOTS_FINITE_SET : thm := BNormalize.POLY_ROOTS_FINITE_SET
unsafe def POLY_MONO : thm := BNormalize.POLY_MONO

-- Convs
unsafe def POLY_DIFF_CONV : term → IO (Except String thm) := fun t => (BConvs.POLY_DIFF_CONV t).run
unsafe def POLY_CMUL_CONV : term → IO (Except String thm) := fun t => (BConvs.POLY_CMUL_CONV t).run
unsafe def POLY_ADD_CONV : term → IO (Except String thm) := fun t => (BConvs.POLY_ADD_CONV t).run
unsafe def POLY_MUL_CONV : term → IO (Except String thm) := fun t => (BConvs.POLY_MUL_CONV t).run
unsafe def POLY_NORMALIZE_CONV : term → IO (Except String thm) := fun t => (BConvs.POLY_NORMALIZE_CONV t).run

-- NonNil
unsafe def NOT_POLY_CMUL_NIL : thm := BNonNil.NOT_POLY_CMUL_NIL
unsafe def NOT_POLY_MUL_NIL : thm := BNonNil.NOT_POLY_MUL_NIL
unsafe def NOT_POLY_EXP_NIL : thm := BNonNil.NOT_POLY_EXP_NIL
unsafe def NOT_POLY_EXP_X_NIL : thm := BNonNil.NOT_POLY_EXP_X_NIL
unsafe def POLY_CMUL_LID : thm := BNonNil.POLY_CMUL_LID
unsafe def POLY_MUL_LID : thm := BNonNil.POLY_MUL_LID
unsafe def POLY_MUL_RID : thm := BNonNil.POLY_MUL_RID
unsafe def POLY_ADD_SYM : thm := BNonNil.POLY_ADD_SYM
unsafe def POLY_ADD_ASSOC : thm := BNonNil.POLY_ADD_ASSOC

-- HeadsTails
unsafe def TL_POLY_MUL_X : thm := BHeadsTails.TL_POLY_MUL_X
unsafe def HD_POLY_MUL_X : thm := BHeadsTails.HD_POLY_MUL_X
unsafe def TL_POLY_EXP_X_SUC : thm := BHeadsTails.TL_POLY_EXP_X_SUC
unsafe def HD_POLY_EXP_X_SUC : thm := BHeadsTails.HD_POLY_EXP_X_SUC
unsafe def HD_POLY_ADD : thm := BHeadsTails.HD_POLY_ADD
unsafe def HD_POLY_CMUL : thm := BHeadsTails.HD_POLY_CMUL
unsafe def TL_POLY_CMUL : thm := BHeadsTails.TL_POLY_CMUL
unsafe def HD_POLY_MUL : thm := BHeadsTails.HD_POLY_MUL
unsafe def HD_POLY_EXP : thm := BHeadsTails.HD_POLY_EXP

-- AdditionalLemmas
unsafe def POLY_ADD_IDENT : thm := BAdditionalLemmas.POLY_ADD_IDENT
unsafe def POLY_ADD_NEUTRAL : thm := BAdditionalLemmas.POLY_ADD_NEUTRAL
unsafe def MONOIDAL_POLY_ADD : thm := BAdditionalLemmas.MONOIDAL_POLY_ADD
unsafe def POLY_DIFF_AUX_ADD_LEMMA : thm := BAdditionalLemmas.POLY_DIFF_AUX_ADD_LEMMA
unsafe def POLYDIFF_ADD : thm := BAdditionalLemmas.POLYDIFF_ADD
unsafe def POLY_DIFF_AUX_POLY_CMUL : thm := BAdditionalLemmas.POLY_DIFF_AUX_POLY_CMUL
unsafe def POLY_CMUL_POLY_DIFF : thm := BAdditionalLemmas.POLY_CMUL_POLY_DIFF

-- Lengths
unsafe def POLY_CMUL_LENGTH : thm := BLengths.POLY_CMUL_LENGTH
unsafe def POLY_ADD_LENGTH : thm := BLengths.POLY_ADD_LENGTH
unsafe def POLY_MUL_LENGTH : thm := BLengths.POLY_MUL_LENGTH
unsafe def POLY_EXP_X_REC : thm := BLengths.POLY_EXP_X_REC
unsafe def POLY_MUL_LENGTH2 : thm := BLengths.POLY_MUL_LENGTH2
unsafe def POLY_EXP_X_LENGTH : thm := BLengths.POLY_EXP_X_LENGTH
unsafe def POLY_SUM_EQUIV : thm := BLengths.POLY_SUM_EQUIV
unsafe def ITERATE_RADD_POLYADD : thm := BLengths.ITERATE_RADD_POLYADD
-- @@EXPORTS END

/-- `needs "Library/poly.ml"`: build the bundles, in order. -/
unsafe def ensurePoly : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BDefs.poly
  let _ ← IO.mkRef BConsequences.POLY_ADD
  let _ ← IO.mkRef BDerivs.POLY_ADD_RZERO
  let _ ← IO.mkRef BRootsFinite.POLY_ROOTS_INDEX_LEMMA
  let _ ← IO.mkRef BEntire.POLY_ENTIRE_LEMMA
  let _ ← IO.mkRef BZero.POLY_ZERO_LEMMA
  let _ ← IO.mkRef BTrivial.POLY_DIFF_AUX_ISZERO
  let _ ← IO.mkRef BDivides.divides
  let _ ← IO.mkRef BOrder.POLY_ORDER_EXISTS
  let _ ← IO.mkRef BSquarefree.POLY_SQUAREFREE_DECOMP_ORDER
  let _ ← IO.mkRef BNormalize.normalize
  let _ ← IO.mkRef BConvs.POLY_DIFF_CONV
  let _ ← IO.mkRef BNonNil.NOT_POLY_CMUL_NIL
  let _ ← IO.mkRef BHeadsTails.TL_POLY_MUL_X
  let _ ← IO.mkRef BAdditionalLemmas.POLY_ADD_IDENT
  let _ ← IO.mkRef BLengths.POLY_CMUL_LENGTH
  -- @@ENSURE END
  pure ()

end SessionLibrary.Poly
