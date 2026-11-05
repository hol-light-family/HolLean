/- ---------------------------------------------------------------------- -/
/- Session wiring for Multivariate/misc.ml.                               -/
/- ---------------------------------------------------------------------- -/
/- File: SessionMultiLib/Misc.lean

  The session half of the misc.ml translation: it supplies
  HolMultiLib.Misc's dependencies from Session, SessionLibrary.Card and
  SessionLibrary.Floor, and exports every theorem by name.  Importing this
  module is `needs "Multivariate/misc.ml"`: misc.ml's own `needs` of
  Library/card.ml and Library/floor.ml are the imports below, and each bundle
  is built by `initialize` when the module is loaded, in file order.
-/

import Session
import SessionLibrary.Card
import SessionLibrary.Floor
import HolMultiLib.Misc

open HolCore HolCore.Kernel
open Session

namespace SessionMultiLib.Misc

open SessionLibrary.Card SessionLibrary.Floor in
/-- The core theorems misc.ml uses, ADD1 to IN_CROSS (in CoreThms1's order). -/
def core1 : HolMultiLib.Misc.CoreThms1 :=
  ⟨Session.ADD1, Session.ADD_ASSOC, Session.ADD_CLAUSES, Session.ADD_SUB,
   Session.ADD_SUB2, Session.AND_FORALL_THM, Session.ARBITRARY,
   Session.ARBITRARY_UNION_OF_IDEMPOT, Session.ARBITRARY_UNION_OF_UNIONS,
   Session.ARITH, Session.ARITH_EQ, Session.ARITH_EVEN,
   Session.BIJECTIVE_LEFT_RIGHT_INVERSE, Session.CARD_EQ_0,
   Session.CARD_EQ_BIJECTIONS_SPECIAL, Session.CARD_NUMSEG_1, Session.CART_EQ,
   Session.COMPL_COMPL, Session.CONJ_ASSOC, Session.CONJ_SYM,
   Session.CONTRAPOS_THM, Session.CROSS, Session.DEPENDENT_CHOICE,
   Session.DE_MORGAN_THM, Session.DIMINDEX_FINITE_PROD, Session.DIMINDEX_GE_1,
   Session.DISJOINT, Session.DISJOINT_SYM, Session.DIVISION, Session.DIV_UNIQ,
   Session.EMPTY_SUBSET, Session.EMPTY_UNIONS, Session.EQ_IMP,
   Session.EQ_SYM_EQ, Session.EQ_TRANS, Session.ETA_AX, Session.EVEN_ADD,
   Session.EVEN_EXISTS, Session.EVEN_MULT, Session.EVEN_OR_ODD,
   Session.EXISTS_IN_GSPEC, Session.EXISTS_IN_IMAGE, Session.EXISTS_PAIR_THM,
   Session.EXP, Session.EXP_ADD, Session.EXTENSION, Session.FINITE_EMPTY,
   Session.FINITE_IMAGE, Session.FINITE_INDUCT_STRONG, Session.FINITE_INSERT,
   Session.FINITE_INTERSECTION_OF_INC, Session.FINITE_INTERSECTION_OF_INTERS,
   Session.FINITE_NUMSEG, Session.FINITE_NUMSEG_LT, Session.FINITE_RESTRICT,
   Session.FINITE_RULES, Session.FINITE_SING, Session.FINITE_SUBSET,
   Session.FINITE_UNION, Session.FORALL_AND_THM, Session.FORALL_INTERSECTION_OF,
   Session.FORALL_IN_GSPEC, Session.FORALL_IN_IMAGE, Session.FORALL_IN_IMAGE_2,
   Session.FORALL_IN_INSERT, Session.FORALL_PAIR_THM, Session.FORALL_UNWIND_THM2,
   Session.FUNCTION_FACTORS_LEFT, Session.FUN_EQ_THM, Session.FUN_IN_IMAGE,
   Session.GE, Session.IMAGE_CLAUSES, Session.IMAGE_CONST, Session.IMAGE_EQ,
   Session.IMAGE_EQ_EMPTY, Session.IMAGE_SUBSET, Session.IMAGE_o,
   Session.IMP_CONJ, Session.IMP_CONJ_ALT, Session.IMP_IMP, Session.IN,
   Session.INFINITE_DIFF_FINITE, Session.INFINITE_ENUMERATE,
   Session.INFINITE_IMAGE, Session.INFINITE_SUPERSET, Session.INFINITE_UNIV_PAIR,
   Session.INJECTIVE_ON_ALT, Session.INJECTIVE_ON_LEFT_INVERSE,
   Session.INSERT_SUBSET, Session.INTERSECTION_OF, Session.INTERSECTION_OF_INC,
   Session.INTERS_0, Session.INTERS_1, Session.INTERS_2, Session.INTERS_GSPEC,
   Session.INTERS_IMAGE, Session.INTERS_INSERT, Session.INTER_INTERS,
   Session.INTER_SUBSET, Session.INTER_UNIONS, Session.INTER_UNIV,
   Session.IN_CROSS⟩

/-- The core theorems misc.ml uses, IN_DELETE to REAL_LT_RMUL_EQ. -/
def core2 : HolMultiLib.Misc.CoreThms2 :=
  ⟨Session.IN_DELETE, Session.IN_DIFF, Session.IN_ELIM_PAIR_THM,
   Session.IN_ELIM_THM, Session.IN_IMAGE, Session.IN_INSERT, Session.IN_INTER,
   Session.IN_INTERS, Session.IN_NUMSEG, Session.IN_SING, Session.IN_UNION,
   Session.IN_UNIV, Session.ITERATE_EXPAND_CASES, Session.LAMBDA_BETA,
   Session.LE, Session.LEFT_ADD_DISTRIB, Session.LEFT_EXISTS_AND_THM,
   Session.LEFT_IMP_EXISTS_THM, Session.LET_TRANS, Session.LE_0, Session.LE_1,
   Session.LE_ADD_LCANCEL, Session.LE_CASES, Session.LE_EXISTS, Session.LE_LT,
   Session.LE_MULT_LCANCEL, Session.LE_MULT_RCANCEL, Session.LE_REFL,
   Session.LE_TRANS, Session.LT, Session.LTE_TRANS, Session.LT_CASES,
   Session.LT_IMP_LE, Session.LT_LE, Session.LT_NZ, Session.LT_REFL,
   Session.LT_SUC_LE, Session.LT_TRANS, Session.MOD_UNIQ, Session.MONO_AND,
   Session.MONO_EXISTS, Session.MONO_FORALL, Session.MULT_ASSOC,
   Session.MULT_CLAUSES, Session.NEUTRAL_REAL_ADD, Session.NOT_EXISTS_THM,
   Session.NOT_FORALL_THM, Session.NOT_IMP, Session.NOT_INSERT_EMPTY,
   Session.NOT_IN_EMPTY, Session.NOT_LT, Session.NOT_SUC, Session.NUMSEG_EMPTY,
   Session.ODD_EXISTS, Session.OR_EXISTS_THM, Session.PAIRWISE_CHAIN_UNIONS,
   Session.PAIRWISE_EMPTY, Session.PAIRWISE_INSERT, Session.PAIR_EQ,
   Session.RDIV_LT_EQ, Session.REAL_ABS_MUL, Session.REAL_ABS_NEG,
   Session.REAL_ABS_NUM, Session.REAL_ADD_LDISTRIB, Session.REAL_ADD_LID,
   Session.REAL_ADD_SYM, Session.REAL_ARCH, Session.REAL_ARCH_INV,
   Session.REAL_COMPLETE, Session.REAL_DIV_LMUL, Session.REAL_DIV_POW2,
   Session.REAL_ENTIRE, Session.REAL_EQ_LCANCEL_IMP, Session.REAL_EQ_NEG2,
   Session.REAL_INF_LE_FINITE, Session.REAL_LET_ANTISYM, Session.REAL_LET_TRANS,
   Session.REAL_LE_ADD, Session.REAL_LE_ANTISYM, Session.REAL_LE_LT,
   Session.REAL_LE_MUL, Session.REAL_LE_NEG2, Session.REAL_LE_RDIV_EQ,
   Session.REAL_LE_REFL, Session.REAL_LE_RMUL, Session.REAL_LE_TOTAL,
   Session.REAL_LE_TRANS, Session.REAL_LTE_TRANS, Session.REAL_LT_01,
   Session.REAL_LT_ANTISYM, Session.REAL_LT_DIV2_EQ, Session.REAL_LT_IMP_LE,
   Session.REAL_LT_INF_FINITE, Session.REAL_LT_INV_EQ, Session.REAL_LT_LDIV_EQ,
   Session.REAL_LT_LE, Session.REAL_LT_MIN, Session.REAL_LT_NEG2,
   Session.REAL_LT_POW2, Session.REAL_LT_RDIV_EQ, Session.REAL_LT_REFL,
   Session.REAL_LT_RMUL_EQ⟩

/-- The core theorems misc.ml uses, REAL_LT_SQUARE_ABS to support, and the
    lists.ml theorems (held in Session's list bundles). -/
def core3 : HolMultiLib.Misc.CoreThms3 :=
  ⟨Session.REAL_LT_SQUARE_ABS, Session.REAL_LT_TOTAL, Session.REAL_LT_TRANS,
   Session.REAL_MUL_ASSOC, Session.REAL_MUL_LID, Session.REAL_MUL_LZERO,
   Session.REAL_MUL_RID, Session.REAL_MUL_RZERO, Session.REAL_MUL_SYM,
   Session.REAL_NOT_LE, Session.REAL_NOT_LT, Session.REAL_OF_NUM_ADD,
   Session.REAL_OF_NUM_EQ, Session.REAL_OF_NUM_LE, Session.REAL_OF_NUM_LT,
   Session.REAL_OF_NUM_MUL, Session.REAL_OF_NUM_POW, Session.REAL_OF_NUM_SUC,
   Session.REAL_POS, Session.REAL_POW_2, Session.REAL_POW_ADD,
   Session.REAL_POW_EQ_0, Session.REAL_POW_LT2, Session.REAL_POW_ONE,
   Session.REAL_SHRINK_GALOIS, Session.REAL_SHRINK_GROW, Session.REAL_SHRINK_LE,
   Session.REAL_SHRINK_RANGE, Session.REAL_SUB_0, Session.REAL_SUB_RDISTRIB,
   Session.REAL_SUP_LT_FINITE, Session.REAL_SUP_UNIQUE,
   Session.RIGHT_EXISTS_AND_THM, Session.RIGHT_FORALL_IMP_THM,
   Session.RIGHT_IMP_EXISTS_THM, Session.RIGHT_IMP_FORALL_THM,
   Session.RIGHT_OR_EXISTS_THM, Session.SIMPLE_IMAGE, Session.SIMPLE_IMAGE_GEN,
   Session.SKOLEM_THM, Session.SUBSET, Session.SUBSET_ANTISYM,
   Session.SUBSET_ANTISYM_EQ, Session.SUBSET_DIFF, Session.SUBSET_EMPTY,
   Session.SUBSET_INTERS, Session.SUBSET_REFL, Session.SUBSET_TRANS,
   Session.SUBSET_UNION, Session.SUBSET_UNIV, Session.SUB_ADD, Session.SUM_ABS,
   Session.SUM_CLAUSES, Session.SUM_CLAUSES_LEFT, Session.SUM_CLAUSES_NUMSEG,
   Session.SUM_CONST_NUMSEG, Session.SUM_LE, Session.SUM_LMUL,
   Session.SUM_LT_ALL, Session.SUM_OFFSET, Session.SUM_OFFSET_0,
   Session.SUM_RESTRICT_SET, Session.SUM_RMUL, Session.SUM_SUB,
   Session.SUM_TRIV_NUMSEG, Session.SWAP_EXISTS_THM, Session.SWAP_FORALL_THM,
   Session.TRANSITIVE_STEPWISE_LE, Session.TRANSITIVE_STEPWISE_LT,
   Session.UNIONS_0, Session.UNIONS_1, Session.UNIONS_2, Session.UNIONS_GSPEC,
   Session.UNIONS_INSERT, Session.UNIONS_SUBSET, Session.UNION_OF,
   Session.UNION_OF_INC, Session.UNION_OF_MONO, Session.UNION_SUBSET,
   Session.UNIV_NOT_EMPTY, Session.UNWIND_THM1, Session.UNWIND_THM2,
   Session.WLOG_LE, Session.WLOG_LT, Session.le_c, Session.num_CASES,
   Session.num_INDUCTION, Session.num_INFINITE, Session.num_RECURSION,
   Session.num_WOP, Session.numseg, Session.o_ASSOC, Session.o_THM,
   Session.pairwise, Session.real_div, Session.real_pow, Session.sum,
   Session.support,
   Session.listThms2.EL_LIST_OF_SEQ, Session.listThms1.LENGTH_EQ_NIL,
   Session.listThms2.LENGTH_LIST_OF_SEQ, Session.listThms1.LIST_EQ,
   Session.listThms2.LIST_OF_SEQ_EQ_NIL, Session.listThms1.NOT_CONS_NIL⟩

/-- The theorems misc.ml uses from Library/card.ml and Library/floor.ml. -/
def lib : HolMultiLib.Misc.LibThms :=
  ⟨SessionLibrary.Card.CARD_DIFF_ABSORB, SessionLibrary.Card.CARD_EQ_IMP_LE,
   SessionLibrary.Card.CARD_EQ_LIST, SessionLibrary.Card.CARD_EQ_REAL,
   SessionLibrary.Card.CARD_EQ_REFL, SessionLibrary.Card.CARD_EQ_SYM,
   SessionLibrary.Card.CARD_EQ_TRANS, SessionLibrary.Card.CARD_EXP_CONG,
   SessionLibrary.Card.CARD_EXP_MUL, SessionLibrary.Card.CARD_EXP_UNIV,
   SessionLibrary.Card.CARD_LE_ANTISYM, SessionLibrary.Card.CARD_LE_EXP_LEFT,
   SessionLibrary.Card.CARD_LE_IMAGE, SessionLibrary.Card.CARD_LE_SUBSET,
   SessionLibrary.Card.CARD_LE_TRANS, SessionLibrary.Card.CARD_LTE_TRANS,
   SessionLibrary.Card.CARD_MUL_CONG, SessionLibrary.Card.CARD_SQUARE_NUM,
   SessionLibrary.Card.COUNTABLE_ALT, SessionLibrary.Card.COUNTABLE_AS_IMAGE,
   SessionLibrary.Card.COUNTABLE_AS_IMAGE_SUBSET,
   SessionLibrary.Card.COUNTABLE_CART, SessionLibrary.Card.COUNTABLE_CROSS,
   SessionLibrary.Card.COUNTABLE_EMPTY, SessionLibrary.Card.COUNTABLE_IMAGE,
   SessionLibrary.Card.COUNTABLE_IMAGE_INJ_EQ,
   SessionLibrary.Card.COUNTABLE_INSERT, SessionLibrary.Card.COUNTABLE_INTER,
   SessionLibrary.Card.COUNTABLE_INTERSECTION_OF_INC,
   SessionLibrary.Card.COUNTABLE_INTERSECTION_OF_INTERS,
   SessionLibrary.Card.COUNTABLE_LIST,
   SessionLibrary.Card.COUNTABLE_PRODUCT_DEPENDENT,
   SessionLibrary.Card.COUNTABLE_SUBSET, SessionLibrary.Card.COUNTABLE_SUBSET_NUM,
   SessionLibrary.Card.COUNTABLE_UNION, SessionLibrary.Card.COUNTABLE_UNION_OF_INC,
   SessionLibrary.Card.EQ_C_BIJECTIONS, SessionLibrary.Card.FINITE_CARD_LT,
   SessionLibrary.Card.MUL_C_UNIV, SessionLibrary.Card.NUM_COUNTABLE,
   SessionLibrary.Card.UNCOUNTABLE_REAL, SessionLibrary.Card.exp_c,
   SessionLibrary.Card.mul_c,
   SessionLibrary.Floor.INTEGER_CASES, SessionLibrary.Floor.INTEGER_CLOSED,
   SessionLibrary.Floor.RATIONAL_APPROXIMATION,
   SessionLibrary.Floor.RATIONAL_APPROXIMATION_STRADDLE,
   SessionLibrary.Floor.RATIONAL_CLOSED, SessionLibrary.Floor.rational⟩

/-- What misc.ml uses from hol.ml's library. -/
def deps : HolMultiLib.Misc.MiscDeps where
  new_definition s := do
    let t ← ExceptT.mk (HolCore.Parser.parse_term s)
    ExceptT.mk (Session.new_definition t)
  define s := do
    let t ← ExceptT.mk (HolCore.Parser.parse_term s)
    ExceptT.mk (Session.define t)
  parse_as_infix := Session.parse_as_infix
  make_overloadable s ty := ExceptT.mk (Session.make_overloadable s ty)
  overload_interface s t := ExceptT.mk (Session.overload_interface s t)
  prove_recursive_functions_exist ax t :=
    ExceptT.mk (Session.prove_recursive_functions_exist ax t)
  ARITH_RULE t := ExceptT.mk (ARITH_RULE t)
  ARITH_TAC := ARITH_TAC
  ASM_ARITH_TAC := ASM_ARITH_TAC
  ASM_MESON_TAC := ASM_MESON_TAC
  ASM_METIS_TAC := ASM_METIS_TAC
  ASM_REAL_ARITH_TAC := ASM_REAL_ARITH_TAC
  INDUCT_TAC := INDUCT_TAC
  MESON ths t := ExceptT.mk (MESON ths t)
  MESON_TAC := MESON_TAC
  METIS_TAC := METIS_TAC
  REAL_ARITH t := ExceptT.mk (REAL_ARITH3 t)
  REAL_ARITH_TAC := REAL_ARITH_TAC2
  REAL_FIELD t := ExceptT.mk (REAL_FIELD t)
  REAL_RING t := ExceptT.mk (REAL_RING t)
  SET_RULE t := ExceptT.mk (SET_RULE t)
  SET_TAC := SET_TAC
  CNF_CONV := CNF_CONV
  HAS_SIZE_CONV := HAS_SIZE_CONV
  NNFC_CONV := NNFC_CONV
  NUM_REDUCE_CONV := NUM_REDUCE_CONV
  REAL_RAT_REDUCE_CONV := REAL_RAT_REDUCE_CONV
  num_CONV := num_CONV
  SELECT_CONV t := pure (Session.SELECT_CONV t)
  core1 := core1
  core2 := core2
  core3 := core3
  lib := lib

/-- misc.ml 10: `prioritize_real()`, after its `needs` (the imports) and before
    the first bundle. -/
initialize miscPrelude : Unit ← Session.prioritize_real

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in misc.ml order. -/
initialize BLemmas : HolMultiLib.Misc.Lemmas ←
  ioB "setupLemmas" (HolMultiLib.Misc.setupLemmas deps).run
initialize BRealInterval : HolMultiLib.Misc.RealInterval ←
  ioB "setupRealInterval" (HolMultiLib.Misc.setupRealInterval deps BLemmas).run
initialize BVectorize : HolMultiLib.Misc.Vectorize ←
  ioB "setupVectorize" (HolMultiLib.Misc.setupVectorize deps).run
initialize BHull : HolMultiLib.Misc.Hull ←
  ioB "setupHull" (HolMultiLib.Misc.setupHull deps).run
initialize BLimits : HolMultiLib.Misc.Limits ←
  ioB "setupLimits" (HolMultiLib.Misc.setupLimits deps BLemmas).run
initialize BSubseq : HolMultiLib.Misc.Subseq ←
  ioB "setupSubseq" (HolMultiLib.Misc.setupSubseq deps).run
initialize BDiagonal : HolMultiLib.Misc.Diagonal ←
  ioB "setupDiagonal" (HolMultiLib.Misc.setupDiagonal deps BSubseq).run
initialize BIrrational : HolMultiLib.Misc.Irrational ←
  ioB "setupIrrational" (HolMultiLib.Misc.setupIrrational deps BDiagonal).run
initialize BRelativeTo : HolMultiLib.Misc.RelativeTo ←
  ioB "setupRelativeTo" (HolMultiLib.Misc.setupRelativeTo deps BLemmas).run
initialize BReduction : HolMultiLib.Misc.Reduction ←
  ioB "setupReduction" (HolMultiLib.Misc.setupReduction deps).run
initialize BBackAndForth : HolMultiLib.Misc.BackAndForth ←
  ioB "setupBackAndForth" (HolMultiLib.Misc.setupBackAndForth deps).run
initialize BDyadic : HolMultiLib.Misc.Dyadic ←
  ioB "setupDyadic" (HolMultiLib.Misc.setupDyadic deps).run
initialize BSuslin : HolMultiLib.Misc.Suslin ←
  ioB "setupSuslin" (HolMultiLib.Misc.setupSuslin deps).run
initialize BSuslin2 : HolMultiLib.Misc.Suslin2 ←
  ioB "setupSuslin2" (HolMultiLib.Misc.setupSuslin2 deps BLemmas BSuslin).run

/- The theorems, by name. -/
/-- `ASSERT_TAC tm` (misc.ml 16). -/
def ASSERT_TAC (tm : term) : HolCore.Tactics.tactic := HolMultiLib.Misc.ASSERT_TAC tm
/-- `EQ_TRANS_TAC tm` (misc.ml 19). -/
def EQ_TRANS_TAC (tm : term) : HolCore.Tactics.tactic := HolMultiLib.Misc.EQ_TRANS_TAC deps tm
-- Lemmas (misc.ml 26-311)
def FORALL_DIFF                  : thm := BLemmas.FORALL_DIFF
def EXISTS_DIFF                  : thm := BLemmas.EXISTS_DIFF
def FORALL_DIFF_ALT              : thm := BLemmas.FORALL_DIFF_ALT
def FORALL_DIFF_GEN              : thm := BLemmas.FORALL_DIFF_GEN
def GE_REFL                      : thm := BLemmas.GE_REFL
def FORALL_SUC                   : thm := BLemmas.FORALL_SUC
def SEQ_MONO_LEMMA               : thm := BLemmas.SEQ_MONO_LEMMA
def REAL_HALF                    : thm := BLemmas.REAL_HALF
def ABS_SQUARE_LT_1              : thm := BLemmas.ABS_SQUARE_LT_1
def ABS_SQUARE_LE_1              : thm := BLemmas.ABS_SQUARE_LE_1
def ABS_SQUARE_EQ_1              : thm := BLemmas.ABS_SQUARE_EQ_1
def UPPER_BOUND_FINITE_SET       : thm := BLemmas.UPPER_BOUND_FINITE_SET
def UPPER_BOUND_FINITE_SET_REAL  : thm := BLemmas.UPPER_BOUND_FINITE_SET_REAL
def LOWER_BOUND_FINITE_SET       : thm := BLemmas.LOWER_BOUND_FINITE_SET
def LOWER_BOUND_FINITE_SET_REAL  : thm := BLemmas.LOWER_BOUND_FINITE_SET_REAL
def REAL_CONVEX_SUM_BOUND_LE     : thm := BLemmas.REAL_CONVEX_SUM_BOUND_LE
def REAL_CONVEX_SUM_BOUND_LT     : thm := BLemmas.REAL_CONVEX_SUM_BOUND_LT
def APPROACHABLE_LT_LE           : thm := BLemmas.APPROACHABLE_LT_LE
def REAL_LE_BETWEEN              : thm := BLemmas.REAL_LE_BETWEEN
def REAL_LET_BETWEEN             : thm := BLemmas.REAL_LET_BETWEEN
def REAL_LTE_BETWEEN             : thm := BLemmas.REAL_LTE_BETWEEN
def REAL_LT_BETWEEN              : thm := BLemmas.REAL_LT_BETWEEN
def REAL_LT_BETWEEN_GEN          : thm := BLemmas.REAL_LT_BETWEEN_GEN
def TRIANGLE_LEMMA               : thm := BLemmas.TRIANGLE_LEMMA
def LAMBDA_SKOLEM                : thm := BLemmas.LAMBDA_SKOLEM
def EPSILON_DELTA_MINIMAL        : thm := BLemmas.EPSILON_DELTA_MINIMAL
def HAS_SIZE_1_EXISTS            : thm := BLemmas.HAS_SIZE_1_EXISTS
def LINEAR_EQUATIONS_1_EQ        : thm := BLemmas.LINEAR_EQUATIONS_1_EQ
def LINEAR_EQUATIONS_2_EQ        : thm := BLemmas.LINEAR_EQUATIONS_2_EQ
-- RealInterval (misc.ml 313-475)
def is_realinterval                   : thm := BRealInterval.is_realinterval
def IS_REALINTERVAL_EMPTY             : thm := BRealInterval.IS_REALINTERVAL_EMPTY
def IS_REALINTERVAL_UNION             : thm := BRealInterval.IS_REALINTERVAL_UNION
def IS_REALINTERVAL_UNIV              : thm := BRealInterval.IS_REALINTERVAL_UNIV
def IS_REALINTERVAL_INTER             : thm := BRealInterval.IS_REALINTERVAL_INTER
def open_real_interval                : thm := BRealInterval.open_real_interval
def closed_real_interval              : thm := BRealInterval.closed_real_interval
def real_interval                     : thm := BRealInterval.real_interval
def IN_REAL_INTERVAL                  : thm := BRealInterval.IN_REAL_INTERVAL
def EMPTY_AS_REAL_INTERVAL            : thm := BRealInterval.EMPTY_AS_REAL_INTERVAL
def REAL_INTERVAL_OPEN_SUBSET_CLOSED  : thm := BRealInterval.REAL_INTERVAL_OPEN_SUBSET_CLOSED
def REAL_INTERVAL_EQ_EMPTY            : thm := BRealInterval.REAL_INTERVAL_EQ_EMPTY
def REAL_INTERVAL_NE_EMPTY            : thm := BRealInterval.REAL_INTERVAL_NE_EMPTY
def REAL_INTERVAL_SING                : thm := BRealInterval.REAL_INTERVAL_SING
def ENDS_IN_REAL_INTERVAL             : thm := BRealInterval.ENDS_IN_REAL_INTERVAL
def IN_REAL_INTERVAL_REFLECT          : thm := BRealInterval.IN_REAL_INTERVAL_REFLECT
def REFLECT_REAL_INTERVAL             : thm := BRealInterval.REFLECT_REAL_INTERVAL
def IS_REALINTERVAL_INTERVAL          : thm := BRealInterval.IS_REALINTERVAL_INTERVAL
def ENDS_IN_UNIT_REAL_INTERVAL        : thm := BRealInterval.ENDS_IN_UNIT_REAL_INTERVAL
def INTER_REAL_INTERVAL               : thm := BRealInterval.INTER_REAL_INTERVAL
def REAL_OPEN_CLOSED_INTERVAL         : thm := BRealInterval.REAL_OPEN_CLOSED_INTERVAL
def REAL_CLOSED_OPEN_INTERVAL         : thm := BRealInterval.REAL_CLOSED_OPEN_INTERVAL
def IS_REALINTERVAL_SING              : thm := BRealInterval.IS_REALINTERVAL_SING
def IS_REALINTERVAL_CONTAINS_INTERVAL : thm := BRealInterval.IS_REALINTERVAL_CONTAINS_INTERVAL
def IS_REALINTERVAL_SHRINK            : thm := BRealInterval.IS_REALINTERVAL_SHRINK
def SUBSET_REAL_INTERVAL              : thm := BRealInterval.SUBSET_REAL_INTERVAL
-- Vectorize (misc.ml 477-570)
def vectorize            : thm := BVectorize.vectorize
def matrify              : thm := BVectorize.matrify
def VECTORIZE_COMPONENT  : thm := BVectorize.VECTORIZE_COMPONENT
def MATRIFY_COMPONENT    : thm := BVectorize.MATRIFY_COMPONENT
def VECTORIZE_MATRIFY    : thm := BVectorize.VECTORIZE_MATRIFY
def MATRIFY_VECTORIZE    : thm := BVectorize.MATRIFY_VECTORIZE
def FORALL_VECTORIZE     : thm := BVectorize.FORALL_VECTORIZE
def FORALL_MATRIFY       : thm := BVectorize.FORALL_MATRIFY
def EXISTS_VECTORIZE     : thm := BVectorize.EXISTS_VECTORIZE
def EXISTS_MATRIFY       : thm := BVectorize.EXISTS_MATRIFY
def VECTORIZE_GSPEC      : thm := BVectorize.VECTORIZE_GSPEC
def VECTORIZE_EQ         : thm := BVectorize.VECTORIZE_EQ
def MATRIFY_EQ           : thm := BVectorize.MATRIFY_EQ
-- Hull (misc.ml 572-746)
def hull                 : thm := BHull.hull
def HULL_P               : thm := BHull.HULL_P
def P_HULL               : thm := BHull.P_HULL
def HULL_EQ              : thm := BHull.HULL_EQ
def HULL_HULL            : thm := BHull.HULL_HULL
def HULL_SUBSET          : thm := BHull.HULL_SUBSET
def HULL_MONO            : thm := BHull.HULL_MONO
def HULL_ANTIMONO        : thm := BHull.HULL_ANTIMONO
def HULL_UNIV            : thm := BHull.HULL_UNIV
def HULL_MINIMAL         : thm := BHull.HULL_MINIMAL
def SUBSET_HULL          : thm := BHull.SUBSET_HULL
def HULL_UNIQUE          : thm := BHull.HULL_UNIQUE
def HULL_UNION_SUBSET    : thm := BHull.HULL_UNION_SUBSET
def HULL_UNION           : thm := BHull.HULL_UNION
def HULL_UNION_LEFT      : thm := BHull.HULL_UNION_LEFT
def HULL_UNION_RIGHT     : thm := BHull.HULL_UNION_RIGHT
def HULL_INSERT          : thm := BHull.HULL_INSERT
def HULL_REDUNDANT_EQ    : thm := BHull.HULL_REDUNDANT_EQ
def HULL_REDUNDANT       : thm := BHull.HULL_REDUNDANT
def HULL_INDUCT          : thm := BHull.HULL_INDUCT
def HULL_INC             : thm := BHull.HULL_INC
def HULL_IMAGE_SUBSET    : thm := BHull.HULL_IMAGE_SUBSET
def HULL_IMAGE_GALOIS    : thm := BHull.HULL_IMAGE_GALOIS
def HULL_IMAGE           : thm := BHull.HULL_IMAGE
def IS_HULL              : thm := BHull.IS_HULL
def HULLS_EQ             : thm := BHull.HULLS_EQ
def HULL_P_AND_Q         : thm := BHull.HULL_P_AND_Q
def HULL_UNIONS_SUBSET   : thm := BHull.HULL_UNIONS_SUBSET
def HULL_INTERS_SUBSET   : thm := BHull.HULL_INTERS_SUBSET
def HULL_INTER_SUBSET    : thm := BHull.HULL_INTER_SUBSET
-- Limits (misc.ml 748-893)
def FORALL_POS_MONO              : thm := BLimits.FORALL_POS_MONO
def FORALL_POS_MONO_1            : thm := BLimits.FORALL_POS_MONO_1
def FORALL_POS_MONO_EQ           : thm := BLimits.FORALL_POS_MONO_EQ
def FORALL_POS_MONO_1_EQ         : thm := BLimits.FORALL_POS_MONO_1_EQ
def REAL_ARCH_RDIV_EQ_0          : thm := BLimits.REAL_ARCH_RDIV_EQ_0
def FINITE_INDEX_NUMSEG_SPECIAL  : thm := BLimits.FINITE_INDEX_NUMSEG_SPECIAL
def SUM_GP_BASIC                 : thm := BLimits.SUM_GP_BASIC
def SUM_GP_MULTIPLIED            : thm := BLimits.SUM_GP_MULTIPLIED
def SUM_GP                       : thm := BLimits.SUM_GP
def SUM_GP_OFFSET                : thm := BLimits.SUM_GP_OFFSET
def «from»                       : thm := BLimits.«from»
def FROM_0                       : thm := BLimits.FROM_0
def IN_FROM                      : thm := BLimits.IN_FROM
def FROM_MONO                    : thm := BLimits.FROM_MONO
def FROM_INTER_NUMSEG_GEN        : thm := BLimits.FROM_INTER_NUMSEG_GEN
def FROM_INTER_NUMSEG_MAX        : thm := BLimits.FROM_INTER_NUMSEG_MAX
def FROM_INTER_NUMSEG            : thm := BLimits.FROM_INTER_NUMSEG
def INFINITE_FROM                : thm := BLimits.INFINITE_FROM
def FINITE_INTER_NUMSEG          : thm := BLimits.FINITE_INTER_NUMSEG
def FROM_NONEMPTY                : thm := BLimits.FROM_NONEMPTY
-- Subseq (misc.ml 895-1007)
/-- `HORNER_SUM_CONV` (misc.ml 898). -/
def HORNER_SUM_CONV : HolCore.Equal.ioconv := fun t => BSubseq.HORNER_SUM_CONV t
def SUBSEQUENCE_STEPWISE           : thm := BSubseq.SUBSEQUENCE_STEPWISE
def SUBSEQUENCE_IMP_INJECTIVE      : thm := BSubseq.SUBSEQUENCE_IMP_INJECTIVE
def MONOTONE_BIGGER                : thm := BSubseq.MONOTONE_BIGGER
def INFINITE_ENUMERATE_WEAK        : thm := BSubseq.INFINITE_ENUMERATE_WEAK
def INFINITE_ENUMERATE_EQ_ALT      : thm := BSubseq.INFINITE_ENUMERATE_EQ_ALT
def MONOTONE_SUBSEQUENCE           : thm := BSubseq.MONOTONE_SUBSEQUENCE
def CONVERGENT_BOUNDED_INCREASING  : thm := BSubseq.CONVERGENT_BOUNDED_INCREASING
def CONVERGENT_BOUNDED_MONOTONE    : thm := BSubseq.CONVERGENT_BOUNDED_MONOTONE
-- Diagonal (misc.ml 1009-1184)
def STRICTLY_INCREASING_ALT            : thm := BDiagonal.STRICTLY_INCREASING_ALT
def STRICTLY_DECREASING_ALT            : thm := BDiagonal.STRICTLY_DECREASING_ALT
def REAL_NON_MONOTONE                  : thm := BDiagonal.REAL_NON_MONOTONE
def SUBSEQUENCE_DIAGONALIZATION_LEMMA  : thm := BDiagonal.SUBSEQUENCE_DIAGONALIZATION_LEMMA
def COUNTABLE_INTEGER                  : thm := BDiagonal.COUNTABLE_INTEGER
def CARD_EQ_INTEGER                    : thm := BDiagonal.CARD_EQ_INTEGER
def COUNTABLE_RATIONAL                 : thm := BDiagonal.COUNTABLE_RATIONAL
def CARD_EQ_RATIONAL                   : thm := BDiagonal.CARD_EQ_RATIONAL
def COUNTABLE_INTEGER_COORDINATES      : thm := BDiagonal.COUNTABLE_INTEGER_COORDINATES
def COUNTABLE_RATIONAL_COORDINATES     : thm := BDiagonal.COUNTABLE_RATIONAL_COORDINATES
-- Irrational (misc.ml 1186-1340)
def IRRATIONAL_APPROXIMATION           : thm := BIrrational.IRRATIONAL_APPROXIMATION
def IRRATIONAL_BETWEEN                 : thm := BIrrational.IRRATIONAL_BETWEEN
def IRRATIONAL_BETWEEN_EQ              : thm := BIrrational.IRRATIONAL_BETWEEN_EQ
def IRRATIONAL_APPROXIMATION_STRADDLE  : thm := BIrrational.IRRATIONAL_APPROXIMATION_STRADDLE
def IRRATIONAL_APPROXIMATION_ABOVE     : thm := BIrrational.IRRATIONAL_APPROXIMATION_ABOVE
def IRRATIONAL_APPROXIMATION_BELOW     : thm := BIrrational.IRRATIONAL_APPROXIMATION_BELOW
def INFINITE_IRRATIONAL_IN_RANGE       : thm := BIrrational.INFINITE_IRRATIONAL_IN_RANGE
def COUNTABLE_LOCAL_MAXIMA             : thm := BIrrational.COUNTABLE_LOCAL_MAXIMA
def COUNTABLE_LOCAL_MINIMA             : thm := BIrrational.COUNTABLE_LOCAL_MINIMA
def COUNTABLE_STRICT_LOCAL_MAXIMA      : thm := BIrrational.COUNTABLE_STRICT_LOCAL_MAXIMA
def COUNTABLE_STRICT_LOCAL_MINIMA      : thm := BIrrational.COUNTABLE_STRICT_LOCAL_MINIMA
-- RelativeTo (misc.ml 1342-1647)
def relative_to                                     : thm := BRelativeTo.relative_to
def RELATIVE_TO_UNIV                                : thm := BRelativeTo.RELATIVE_TO_UNIV
def RELATIVE_TO_IMP_SUBSET                          : thm := BRelativeTo.RELATIVE_TO_IMP_SUBSET
def FORALL_RELATIVE_TO                              : thm := BRelativeTo.FORALL_RELATIVE_TO
def RELATIVE_TO_INC                                 : thm := BRelativeTo.RELATIVE_TO_INC
def RELATIVE_TO                                     : thm := BRelativeTo.RELATIVE_TO
def RELATIVE_TO_RELATIVE_TO                         : thm := BRelativeTo.RELATIVE_TO_RELATIVE_TO
def RELATIVE_TO_COMPL                               : thm := BRelativeTo.RELATIVE_TO_COMPL
def RELATIVE_TO_SUBSET                              : thm := BRelativeTo.RELATIVE_TO_SUBSET
def RELATIVE_TO_SUBSET_TRANS                        : thm := BRelativeTo.RELATIVE_TO_SUBSET_TRANS
def RELATIVE_TO_MONO                                : thm := BRelativeTo.RELATIVE_TO_MONO
def RELATIVE_TO_SUBSET_INC                          : thm := BRelativeTo.RELATIVE_TO_SUBSET_INC
def RELATIVE_TO_INTER                               : thm := BRelativeTo.RELATIVE_TO_INTER
def RELATIVE_TO_UNION                               : thm := BRelativeTo.RELATIVE_TO_UNION
def ARBITRARY_UNION_OF_RELATIVE_TO                  : thm := BRelativeTo.ARBITRARY_UNION_OF_RELATIVE_TO
def FINITE_UNION_OF_RELATIVE_TO                     : thm := BRelativeTo.FINITE_UNION_OF_RELATIVE_TO
def COUNTABLE_UNION_OF_RELATIVE_TO                  : thm := BRelativeTo.COUNTABLE_UNION_OF_RELATIVE_TO
def ARBITRARY_INTERSECTION_OF_RELATIVE_TO           : thm := BRelativeTo.ARBITRARY_INTERSECTION_OF_RELATIVE_TO
def FINITE_INTERSECTION_OF_RELATIVE_TO              : thm := BRelativeTo.FINITE_INTERSECTION_OF_RELATIVE_TO
def COUNTABLE_INTERSECTION_OF_RELATIVE_TO           : thm := BRelativeTo.COUNTABLE_INTERSECTION_OF_RELATIVE_TO
def FINITE_INTERSECTION_OF_RELATIVE_TO_ALT          : thm := BRelativeTo.FINITE_INTERSECTION_OF_RELATIVE_TO_ALT
def COUNTABLE_INTERSECTION_OF_RELATIVE_TO_ALT       : thm := BRelativeTo.COUNTABLE_INTERSECTION_OF_RELATIVE_TO_ALT
def ARBITRARY_UNION_OF_NONEMPTY_FINITE_INTERSECTION : thm := BRelativeTo.ARBITRARY_UNION_OF_NONEMPTY_FINITE_INTERSECTION
-- Reduction (misc.ml 1649-1803)
def GENERAL_REDUCTION_THEOREM      : thm := BReduction.GENERAL_REDUCTION_THEOREM
def GENERAL_REDUCTION_THEOREM_2    : thm := BReduction.GENERAL_REDUCTION_THEOREM_2
-- BackAndForth (misc.ml 1805-2013)
def BACK_AND_FORTH_ALT             : thm := BBackAndForth.BACK_AND_FORTH_ALT
def BACK_AND_FORTH                 : thm := BBackAndForth.BACK_AND_FORTH
def BACK_AND_FORTH_2               : thm := BBackAndForth.BACK_AND_FORTH_2
-- Dyadic (misc.ml 2015-2128)
def RECURSION_ON_DYADIC_FRACTIONS  : thm := BDyadic.RECURSION_ON_DYADIC_FRACTIONS
-- Suslin (misc.ml 2130-2218)
def suslin_operation               : thm := BSuslin.suslin_operation
def suslin                         : thm := BSuslin.suslin
def SUSLIN_INC                     : thm := BSuslin.SUSLIN_INC
def SUSLIN_SUPERSET                : thm := BSuslin.SUSLIN_SUPERSET
def SUSLIN_SUBSET                  : thm := BSuslin.SUSLIN_SUBSET
def SUSLIN_MONO                    : thm := BSuslin.SUSLIN_MONO
def SUSLIN_REGULAR                 : thm := BSuslin.SUSLIN_REGULAR
-- Suslin2 (misc.ml 2219-2593)
def SUSLIN_SUSLIN                  : thm := BSuslin2.SUSLIN_SUSLIN
def SUSLIN_INTERS                  : thm := BSuslin2.SUSLIN_INTERS
def SUSLIN_INTER                   : thm := BSuslin2.SUSLIN_INTER
def SUSLIN_UNIONS                  : thm := BSuslin2.SUSLIN_UNIONS
def SUSLIN_UNION                   : thm := BSuslin2.SUSLIN_UNION
def CARD_SUSLIN_LE                 : thm := BSuslin2.CARD_SUSLIN_LE
def CARD_SUSLIN_EQ                 : thm := BSuslin2.CARD_SUSLIN_EQ

/-- `needs "Multivariate/misc.ml"`: already done by importing this module. -/
def ensureMisc : IO Unit := pure ()

end SessionMultiLib.Misc
