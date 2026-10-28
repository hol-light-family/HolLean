/- ---------------------------------------------------------------------- -/
/- Session wiring for Multivariate/clifford.ml.                           -/
/- ---------------------------------------------------------------------- -/
/- File: SessionMultiLib/Clifford.lean

  The session half of the clifford.ml translation: it supplies
  HolMultiLib.Clifford's dependencies from Session, SessionMultiLib.Vectors
  and SessionLibrary.Binary, and exports every theorem by name.  Importing
  this module is `needs "Multivariate/clifford.ml"`: its own `needs` are the
  imports below, and each bundle is built by `initialize` when the module is
  loaded, in file order.
-/

import Session
import SessionMultiLib.Vectors
import SessionLibrary.Binary
import HolMultiLib.Clifford

open HolCore HolCore.Kernel

namespace SessionMultiLib.Clifford

open Session SessionMultiLib.Vectors in
/-- The core theorems clifford.ml uses. -/
def core : HolMultiLib.Clifford.CoreThms :=
  { ADD_SUB2, ARITH, ARITH_GE, ARITH_GT, CARD_CLAUSES, CARD_DELETE, CARD_EQ_0, CARD_UNION,
    CARD_UNION_EQ, CART_EQ, COND_ID, COND_RAND, COND_RATOR, CONJ_ACI, DELETE_INSERT,
    DE_MORGAN_THM, DIMINDEX_UNIQUE, EMPTY_SUBSET, EMPTY_UNION, EQ_SYM_EQ, EQ_TRANS, ETA_AX,
    EVEN_ADD, EVEN_MULT, EXISTS_PAIR_THM, EXTENSION, FINITE_DELETE, FINITE_DIFF, FINITE_IMAGE,
    FINITE_INDUCT_DELETE, FINITE_INDUCT_STRONG, FINITE_INSERT, FINITE_NUMSEG,
    FINITE_POWERSET, FINITE_PRODUCT, FINITE_RULES, FINITE_SUBSET, FORALL_IN_IMAGE,
    FORALL_PAIR_THM, FORALL_SIMP, FUN_EQ_THM, GT, HAS_SIZE, HAS_SIZE_IMAGE_INJ,
    HAS_SIZE_NUMSEG_1, HAS_SIZE_POWERSET, IMAGE_SUBSET, IMAGE_o, IMP_CONJ, IMP_IMP, INFINITE,
    INTER_ACI, INTER_EMPTY, IN_DELETE, IN_DIFF, IN_ELIM_PAIR_THM, IN_ELIM_THM, IN_IMAGE,
    IN_INSERT, IN_INTER, IN_NUMSEG, IN_SING, IN_UNION, IN_UNIV, ITERATE_CLAUSES,
    LAMBDA_BETA, LET_DEF, LET_END_DEF, LT_ANTISYM, LT_CASES, LT_REFL, MEASURE,
    MEMBER_NOT_EMPTY, MINIMAL, MONO_EXISTS, NOT_INSERT_EMPTY, NOT_IN_EMPTY, PAIR_EQ, PRE,
    REAL_MUL_AC, REAL_MUL_ASSOC, REAL_MUL_LID, REAL_MUL_LZERO, REAL_MUL_RID, REAL_MUL_RZERO,
    REAL_POW_ADD, REAL_POW_NEG, REAL_POW_ONE, RIGHT_FORALL_IMP_THM, RIGHT_IMP_FORALL_THM,
    SELECT_UNIQUE, SKOLEM_THM, SUBSET, SUBSET_REFL, SUM_DELTA, SUM_EQ, SUM_LMUL, SUM_RMUL,
    SUM_SWAP, UNION_ASSOC, UNION_EMPTY, UNION_SUBSET, WF_MEASURE, WF_REC, minimal, monoidal,
    neutral, num_WOP, o_DEF, real_pow }

open SessionMultiLib.Vectors in
/-- The vectors.ml theorems clifford.ml uses. -/
def vec : HolMultiLib.Clifford.VecThms :=
  { BILINEAR_EQ, BILINEAR_LADD, BILINEAR_LMUL, BILINEAR_LNEG, BILINEAR_LZERO, BILINEAR_RADD,
    BILINEAR_RMUL, BILINEAR_RNEG, BILINEAR_RZERO, COND_COMPONENT, LINEAR_EQ, SPAN_MUL,
    SPAN_SUPERSET, SPAN_VSUM, VECTOR_ADD_AC, VECTOR_ADD_ASSOC, VECTOR_ADD_COMPONENT,
    VECTOR_ADD_LDISTRIB, VECTOR_ADD_LID, VECTOR_ADD_RDISTRIB, VECTOR_ADD_RID,
    VECTOR_MUL_ASSOC, VECTOR_MUL_COMPONENT, VECTOR_MUL_LID, VECTOR_MUL_LZERO,
    VECTOR_MUL_RZERO, VECTOR_NEG_0, VECTOR_NEG_MINUS1, VECTOR_NEG_NEG, VECTOR_SUB,
    VEC_COMPONENT, VSUM_0, VSUM_ADD, VSUM_CLAUSES, VSUM_DELTA, VSUM_EQ, VSUM_LMUL, bilinear,
    linear, vsum }

open SessionLibrary.Binary in
/-- The Library/binary.ml theorems clifford.ml uses. -/
def bin : HolMultiLib.Clifford.BinThms :=
  { BINARYSUM_BITSET, BINARYSUM_BOUND, BITSET_BINARYSUM, BITSET_BOUND }

/-- What clifford.ml uses from hol.ml's library. -/
def deps : HolMultiLib.Clifford.CliffordDeps where
  new_definition s := do
    let t ← ExceptT.mk (HolCore.Parser.parse_term s)
    ExceptT.mk (Session.new_definition t)
  new_type_definition ty names th :=
    ExceptT.mk (Session.new_type_definition ty names.1 names.2 th)
  new_specification ns th := ExceptT.mk (Session.new_specification ns th)
  parse_as_infix := Session.parse_as_infix
  parse_as_binder := HolCore.Printer.parse_as_binder
  overload_interface s t := ExceptT.mk (Session.overload_interface s t)
  prioritize_real := Session.prioritize_real
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  ASM_MESON_TAC := Session.ASM_MESON_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  MESON_TAC := Session.MESON_TAC
  REAL_ARITH t := ExceptT.mk (Session.REAL_ARITH3 t)
  REAL_ARITH_TAC := Session.REAL_ARITH_TAC2
  SET_RULE t := ExceptT.mk (Session.SET_RULE t)
  SET_TAC := Session.SET_TAC
  SIMP_RULE ths th := ExceptT.mk (Session.SIMP_RULE ths th)
  DISJ_ACI_RULE t := liftExcept (Session.DISJ_ACI_RULE t)
  LET_TAC := Session.LET_TAC
  let_CONV := Session.let_CONV
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  REAL_RAT_REDUCE_CONV := Session.REAL_RAT_REDUCE_CONV
  REAL_POLY_CONV := Session.REAL_POLY_CONV
  PURE_SIMP_CONV ths := Session.PURE_SIMP_CONV ths
  dest_setenum := Session.dest_setenum
  mk_setenum l := ExceptT.mk (Session.mk_setenum l)
  mk_numeral := Session.mk_numeral
  is_numeral := Session.is_numeral
  VECTOR_ARITH t := ExceptT.mk (SessionMultiLib.Vectors.VECTOR_ARITH t)
  VECTOR_ARITH_TAC := SessionMultiLib.Vectors.VECTOR_ARITH_TAC
  core := core
  vec := vec
  bin := bin

private def ioB {α : Type} (name : String) (x : IO (Except String α)) : IO α := do
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in clifford.ml order. -/
initialize BBasics : HolMultiLib.Clifford.Basics ←
  ioB "setupBasics" (HolMultiLib.Clifford.setupBasics deps).run

-- Basics (clifford.ml 10-99)
def CARD_UNION_LEMMA : thm := BBasics.CARD_UNION_LEMMA
def CARD_DIFF_INTER : thm := BBasics.CARD_DIFF_INTER
def CARD_ADD_SYMDIFF_INTER : thm := BBasics.CARD_ADD_SYMDIFF_INTER
def SYMDIFF_PARITY_LEMMA : thm := BBasics.SYMDIFF_PARITY_LEMMA
def FINITE_CART_SUBSET_LEMMA : thm := BBasics.FINITE_CART_SUBSET_LEMMA
def multivector_tybij_th : thm := BBasics.multivector_tybij_th
def multivector_tybij : thm := BBasics.multivector_tybij
def MULTIVECTOR_IMAGE : thm := BBasics.MULTIVECTOR_IMAGE
def HAS_SIZE_MULTIVECTOR : thm := BBasics.HAS_SIZE_MULTIVECTOR
def FINITE_MULTIVECTOR : thm := BBasics.FINITE_MULTIVECTOR
def DIMINDEX_MULTIVECTOR : thm := BBasics.DIMINDEX_MULTIVECTOR
def DEST_MK_MULTIVECTOR : thm := BBasics.DEST_MK_MULTIVECTOR
def FORALL_MULTIVECTOR : thm := BBasics.FORALL_MULTIVECTOR

initialize BIndexing : HolMultiLib.Clifford.Indexing ←
  ioB "setupIndexing" (HolMultiLib.Clifford.setupIndexing deps BBasics).run

-- Indexing (clifford.ml 108-225)
def setcode : thm := BIndexing.setcode
def codeset : thm := BIndexing.codeset
def CODESET_SETCODE_BIJECTIONS : thm := BIndexing.CODESET_SETCODE_BIJECTIONS
def FORALL_SETCODE : thm := BIndexing.FORALL_SETCODE
def SETCODE_BOUNDS : thm := BIndexing.SETCODE_BOUNDS
def sindex : thm := BIndexing.sindex
def lambdas : thm := BIndexing.lambdas
def MULTIVECTOR_EQ : thm := BIndexing.MULTIVECTOR_EQ
def MULTIVECTOR_BETA : thm := BIndexing.MULTIVECTOR_BETA
def MULTIVECTOR_UNIQUE : thm := BIndexing.MULTIVECTOR_UNIQUE
def MULTIVECTOR_ETA : thm := BIndexing.MULTIVECTOR_ETA
def MULTIVECTOR_ADD_COMPONENT : thm := BIndexing.MULTIVECTOR_ADD_COMPONENT
def MULTIVECTOR_MUL_COMPONENT : thm := BIndexing.MULTIVECTOR_MUL_COMPONENT
def MULTIVECTOR_VEC_COMPONENT : thm := BIndexing.MULTIVECTOR_VEC_COMPONENT
def MULTIVECTOR_VSUM_COMPONENT : thm := BIndexing.MULTIVECTOR_VSUM_COMPONENT
def MULTIVECTOR_VSUM : thm := BIndexing.MULTIVECTOR_VSUM

initialize BMbasis : HolMultiLib.Clifford.Mbasis ←
  ioB "setupMbasis" (HolMultiLib.Clifford.setupMbasis deps BIndexing).run

-- Mbasis (clifford.ml 230-364)
def mbasis : thm := BMbasis.mbasis
def MBASIS_COMPONENT : thm := BMbasis.MBASIS_COMPONENT
def MBASIS_EQ_0 : thm := BMbasis.MBASIS_EQ_0
def MBASIS_NONZERO : thm := BMbasis.MBASIS_NONZERO
def MBASIS_EXPANSION : thm := BMbasis.MBASIS_EXPANSION
def SPAN_MBASIS : thm := BMbasis.SPAN_MBASIS
def LINEAR_EQ_MBASIS : thm := BMbasis.LINEAR_EQ_MBASIS
def BILINEAR_EQ_MBASIS : thm := BMbasis.BILINEAR_EQ_MBASIS
def LINEAR_PROPERTY : thm := BMbasis.LINEAR_PROPERTY
def MBASIS_EXTENSION : thm := BMbasis.MBASIS_EXTENSION
def multivec : thm := BMbasis.multivec
def multivector : thm := BMbasis.multivector
def grade : thm := BMbasis.grade
def MULTIVECTOR_GRADE : thm := BMbasis.MULTIVECTOR_GRADE
def GRADE_ADD : thm := BMbasis.GRADE_ADD
def GRADE_CMUL : thm := BMbasis.GRADE_CMUL

initialize BProduct : HolMultiLib.Clifford.Product ←
  ioB "setupProduct" (HolMultiLib.Clifford.setupProduct deps BIndexing BMbasis).run

-- Product (clifford.ml 370-436)
def Product_DEF : thm := BProduct.Product_DEF
def BILINEAR_PRODUCT : thm := BProduct.BILINEAR_PRODUCT
def PRODUCT_LADD : thm := BProduct.PRODUCT_LADD
def PRODUCT_RADD : thm := BProduct.PRODUCT_RADD
def PRODUCT_LMUL : thm := BProduct.PRODUCT_LMUL
def PRODUCT_RMUL : thm := BProduct.PRODUCT_RMUL
def PRODUCT_LNEG : thm := BProduct.PRODUCT_LNEG
def PRODUCT_RNEG : thm := BProduct.PRODUCT_RNEG
def PRODUCT_LZERO : thm := BProduct.PRODUCT_LZERO
def PRODUCT_RZERO : thm := BProduct.PRODUCT_RZERO
def PRODUCT_ASSOCIATIVE : thm := BProduct.PRODUCT_ASSOCIATIVE

initialize BGeom : HolMultiLib.Clifford.Geom ←
  ioB "setupGeom" (HolMultiLib.Clifford.setupGeom deps BBasics BProduct).run

-- Geom (clifford.ml 442-488)
def geom_mul : thm := BGeom.geom_mul
def BILINEAR_GEOM : thm := BGeom.BILINEAR_GEOM
def GEOM_LADD : thm := BGeom.GEOM_LADD
def GEOM_RADD : thm := BGeom.GEOM_RADD
def GEOM_LMUL : thm := BGeom.GEOM_LMUL
def GEOM_RMUL : thm := BGeom.GEOM_RMUL
def GEOM_LNEG : thm := BGeom.GEOM_LNEG
def GEOM_RNEG : thm := BGeom.GEOM_RNEG
def GEOM_LZERO : thm := BGeom.GEOM_LZERO
def GEOM_RZERO : thm := BGeom.GEOM_RZERO
def GEOM_ASSOC : thm := BGeom.GEOM_ASSOC

initialize BOuterInner : HolMultiLib.Clifford.OuterInner ←
  ioB "setupOuterInner" (HolMultiLib.Clifford.setupOuterInner deps BBasics BProduct).run

-- OuterInner (clifford.ml 494-583)
def outer : thm := BOuterInner.outer
def OUTER : thm := BOuterInner.OUTER
def BILINEAR_OUTER : thm := BOuterInner.BILINEAR_OUTER
def OUTER_LADD : thm := BOuterInner.OUTER_LADD
def OUTER_RADD : thm := BOuterInner.OUTER_RADD
def OUTER_LMUL : thm := BOuterInner.OUTER_LMUL
def OUTER_RMUL : thm := BOuterInner.OUTER_RMUL
def OUTER_LNEG : thm := BOuterInner.OUTER_LNEG
def OUTER_RNEG : thm := BOuterInner.OUTER_RNEG
def OUTER_LZERO : thm := BOuterInner.OUTER_LZERO
def OUTER_RZERO : thm := BOuterInner.OUTER_RZERO
def OUTER_ASSOC : thm := BOuterInner.OUTER_ASSOC
def inner : thm := BOuterInner.inner
def BILINEAR_INNER : thm := BOuterInner.BILINEAR_INNER
def INNER_LADD : thm := BOuterInner.INNER_LADD
def INNER_RADD : thm := BOuterInner.INNER_RADD
def INNER_LMUL : thm := BOuterInner.INNER_LMUL
def INNER_RMUL : thm := BOuterInner.INNER_RMUL
def INNER_LNEG : thm := BOuterInner.INNER_LNEG
def INNER_RNEG : thm := BOuterInner.INNER_RNEG
def INNER_LZERO : thm := BOuterInner.INNER_LZERO
def INNER_RZERO : thm := BOuterInner.INNER_RZERO

initialize BMbasisProd : HolMultiLib.Clifford.MbasisProd ←
  ioB "setupMbasisProd"
    (HolMultiLib.Clifford.setupMbasisProd deps BIndexing BMbasis BProduct BGeom
      BOuterInner).run

-- MbasisProd (clifford.ml 589-701)
def PRODUCT_MBASIS : thm := BMbasisProd.PRODUCT_MBASIS
def PRODUCT_MBASIS_SING : thm := BMbasisProd.PRODUCT_MBASIS_SING
def GEOM_MBASIS : thm := BMbasisProd.GEOM_MBASIS
def GEOM_MBASIS_SING : thm := BMbasisProd.GEOM_MBASIS_SING
def OUTER_MBASIS : thm := BMbasisProd.OUTER_MBASIS
def OUTER_MBASIS_SING : thm := BMbasisProd.OUTER_MBASIS_SING

initialize BMbasisCons : HolMultiLib.Clifford.MbasisCons ←
  ioB "setupMbasisCons"
    (HolMultiLib.Clifford.setupMbasisCons deps BMbasis BOuterInner BMbasisProd).run

-- MbasisCons (clifford.ml 707-750)
def OUTER_MBASIS_SKEWSYM : thm := BMbasisCons.OUTER_MBASIS_SKEWSYM
def OUTER_MBASIS_REFL : thm := BMbasisCons.OUTER_MBASIS_REFL
def OUTER_MBASIS_LSCALAR : thm := BMbasisCons.OUTER_MBASIS_LSCALAR
def OUTER_MBASIS_RSCALAR : thm := BMbasisCons.OUTER_MBASIS_RSCALAR
def MBASIS_SPLIT : thm := BMbasisCons.MBASIS_SPLIT

initialize BOuterConv1 : HolMultiLib.Clifford.OuterConv1 ←
  ioB "setupOuterConv1" (HolMultiLib.Clifford.setupOuterConv1 deps BMbasisCons).run

-- OuterConv1 (clifford.ml 756-797)
def SETENUM_NORM_CONV : HolCore.Equal.ioconv := fun tm => BOuterConv1.SETENUM_NORM_CONV tm
def MBASIS_SPLIT_CONV : HolCore.Equal.ioconv := fun tm => BOuterConv1.MBASIS_SPLIT_CONV tm
def MBASIS_MERGE_CONV : HolCore.Equal.ioconv := fun tm => BOuterConv1.MBASIS_MERGE_CONV tm

initialize BOuterConv2 : HolMultiLib.Clifford.OuterConv2 ←
  ioB "setupOuterConv2"
    (HolMultiLib.Clifford.setupOuterConv2 deps BOuterInner BMbasisCons BOuterConv1).run

-- OuterConv2 (clifford.ml 803-865)
def OUTER_ACI : thm := BOuterConv2.OUTER_ACI
def MBASIS_GROUP_CONV : HolCore.Equal.ioconv := fun tm => BOuterConv2.MBASIS_GROUP_CONV tm
def OUTER_CANON_CONV : HolCore.Equal.ioconv := fun tm => BOuterConv2.OUTER_CANON_CONV tm

initialize BSeqiterate : HolMultiLib.Clifford.Seqiterate ←
  ioB "setupSeqiterate" (HolMultiLib.Clifford.setupSeqiterate deps BMbasis BMbasisCons).run

-- Seqiterate (clifford.ml 872-979)
def seqiterate_EXISTS : thm := BSeqiterate.seqiterate_EXISTS
def EXISTS_SWAP : thm := BSeqiterate.EXISTS_SWAP
def seqiterate : thm := BSeqiterate.seqiterate
def MINIMAL_IN_INSERT : thm := BSeqiterate.MINIMAL_IN_INSERT
def SEQITERATE_CLAUSES : thm := BSeqiterate.SEQITERATE_CLAUSES
def SEQITERATE_ITERATE : thm := BSeqiterate.SEQITERATE_ITERATE
def outermorphism : thm := BSeqiterate.outermorphism
def NEUTRAL_OUTER : thm := BSeqiterate.NEUTRAL_OUTER
def OUTERMORPHISM_MBASIS : thm := BSeqiterate.OUTERMORPHISM_MBASIS
def OUTERMORPHISM_MBASIS_EMPTY : thm := BSeqiterate.OUTERMORPHISM_MBASIS_EMPTY
def reversion : thm := BSeqiterate.reversion

/-- `needs "Multivariate/clifford.ml"`: already done by importing this module. -/
def ensureClifford : IO Unit := pure ()

end SessionMultiLib.Clifford
