/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/bitmatch.ml.                                -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/BitMatch.lean

  The session half of the bitmatch.ml translation: it supplies
  HolLibrary.BitMatch's dependencies from Session and SessionLibrary.Words,
  and exports every name under its HOL Light name.  Importing this module is
  `needs "Library/bitmatch.ml"`; its `needs "Library/words.ml"` is the import
  of SessionLibrary.Words.  Each bundle is built by `initialize` when the
  module is loaded, in file order.
-/

import Session
import HolLibrary.BitMatch
import SessionLibrary.Words

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.BitMatch

/-- The core theorems bitmatch.ml uses. -/
def core1 : HolLibrary.BitMatch.CoreThms1 where
  ADD := Session.ADD
  ADD_0 := Session.ADD_0
  ADD_SYM := Session.ADD_SYM
  ARITH_ZERO := Session.ARITH_ZERO
  BIT0_0 := Session.BIT0_0
  BIT1_0 := Session.BIT1_0
  CONG := Session.CONG
  DIMINDEX_CLAUSES := Session.DIMINDEX_CLAUSES
  DIVISION := Session.DIVISION
  DIV_1 := Session.DIV_1
  DIV_DIV := Session.DIV_DIV
  DIV_LT := Session.DIV_LT
  DIV_MOD := Session.DIV_MOD
  DIV_MULT_ADD := Session.DIV_MULT_ADD
  EVEN_ADD := Session.EVEN_ADD
  EVEN_DOUBLE := Session.EVEN_DOUBLE
  EVEN_MOD := Session.EVEN_MOD
  EXISTS_DEF := Session.EXISTS_DEF
  EXP := Session.EXP
  EXP_1 := Session.EXP_1
  EXP_2_NE_0 := Session.EXP_2_NE_0
  EXP_ADD := Session.EXP_ADD
  LE_MULT_LCANCEL := Session.LE_MULT_LCANCEL
  LE_SUC_LT := Session.LE_SUC_LT
  LTE_TRANS := Session.LTE_TRANS
  LT_ADD_RCANCEL := Session.LT_ADD_RCANCEL
  MOD_ADD_MOD := Session.MOD_ADD_MOD
  MOD_MOD := Session.MOD_MOD
  MOD_MOD_REFL := Session.MOD_MOD_REFL
  MOD_MULT := Session.MOD_MULT
  MOD_MULT_ADD := Session.MOD_MULT_ADD
  MULT_AC := Session.MULT_AC
  MULT_SUC := Session.MULT_SUC
  MULT_SYM := Session.MULT_SYM
  NOT_EVEN := Session.NOT_EVEN
  NOT_EXISTS_THM := Session.NOT_EXISTS_THM
  NOT_ODD := Session.NOT_ODD
  NUMERAL := Session.NUMERAL
  ODD_MOD := Session.ODD_MOD
  ONE := Session.ONE
  RDIV_LT_EQ := Session.RDIV_LT_EQ
  SND := Session.SND
  _MATCH := Session.pairSugarDefs.MATCH
  _SEQPATTERN := Session.pairSugarDefs.SEQPATTERN
  _UNGUARDED_PATTERN := Session.pairSugarDefs.UNGUARDED_PATTERN
  o_DEF := Session.o_DEF
/-- The core theorems bitmatch.ml uses. -/
def core2 : HolLibrary.BitMatch.CoreThms2 where
  BITVAL_CLAUSES := SessionLibrary.Words.«BITVAL_CLAUSES»
  BIT_LSB := SessionLibrary.Words.«BIT_LSB»
  NUMBIT_VAL := SessionLibrary.Words.«NUMBIT_VAL»
  VAL_BOUND := SessionLibrary.Words.«VAL_BOUND»
  VAL_WORD := SessionLibrary.Words.«VAL_WORD»
  VAL_WORD_BITVAL := SessionLibrary.Words.«VAL_WORD_BITVAL»
  VAL_WORD_EQ := SessionLibrary.Words.«VAL_WORD_EQ»
  WORD_EQ := SessionLibrary.Words.«WORD_EQ»
  WORD_VAL := SessionLibrary.Words.«WORD_VAL»
  WORD_VAL_GALOIS := SessionLibrary.Words.«WORD_VAL_GALOIS»
  bitval := SessionLibrary.Words.«bitval»
  num_shift_add := SessionLibrary.Words.«num_shift_add»
  num_shift_add_0 := SessionLibrary.Words.«num_shift_add_0»
  num_shift_add_SUC := SessionLibrary.Words.«num_shift_add_SUC»
  numbit := SessionLibrary.Words.«numbit»

/-- What bitmatch.ml uses from Session and words.ml. -/
def deps : HolLibrary.BitMatch.BitMatchDeps where
  new_definition s := do ExceptT.mk (Session.new_definition (← HolLight.q s))
  new_type_definition ty names th :=
    ExceptT.mk (Session.new_type_definition ty names.1 names.2 th)
  prioritize_num := do
    match ← HolCore.Kernel.mk_type "num" [] with
    | .ok ty => Session.prioritize_overload ty
    | .error e => throw (IO.userError e)
  mk_numeral := Session.mk_numeral
  ARITH_RULE t := ExceptT.mk (Session.ARITH_RULE t)
  ARITH_TAC := Session.ARITH_TAC
  DIMINDEX_TAC := Session.DIMINDEX_TAC
  IMP_REWRITE_TAC := Session.IMP_REWRITE_TAC
  MESON ths t := ExceptT.mk (Session.MESON ths t)
  METIS ths t := ExceptT.mk (Session.METIS ths t)
  METIS_TAC := Session.METIS_TAC
  NUM_REDUCE_TAC := Session.NUM_REDUCE_TAC
  DIMINDEX_CONV t := pure (Session.DIMINDEX_CONV t)
  ETA_CONV t := pure (Session.ETA_CONV t)
  let_CONV := Session.let_CONV
  NUM_ADD_CONV := Session.NUM_ADD_CONV
  NUM_LT_CONV := Session.NUM_LT_CONV
  NUM_REDUCE_CONV := Session.NUM_REDUCE_CONV
  NUMBIT_CONV := SessionLibrary.Words.NUMBIT_CONV
  WORD_RED_CONV := SessionLibrary.Words.WORD_RED_CONV
  NUM_SHIFT_ADD_CORE a b i := ExceptT.mk (pure (SessionLibrary.Words.NUM_SHIFT_ADD_CORE a b i))
  core1 := core1
  core2 := core2

/-- Run one bundle's setup at load, failing the load if it fails. -/
private def ioB {α : Type} [Inhabited α] (name : String) (x : IO (Except String α)) :
    IO α := do
  if !(← Session.bundlesWanted) then return default
  match ← x with
  | .ok d => pure d
  | .error e => throw (IO.userError s!"{name} failed: {e}")

/- The bundles, in bitmatch.ml order. -/
initialize BDefs : HolLibrary.BitMatch.Defs ←
  ioB "setupDefs" (HolLibrary.BitMatch.setupDefs deps).run
initialize BSyntax : HolLibrary.BitMatch.Syntax ←
  ioB "setupSyntax" (HolLibrary.BitMatch.setupSyntax deps).run
initialize BAnalyze : HolLibrary.BitMatch.Analyze ←
  ioB "setupAnalyze" (HolLibrary.BitMatch.setupAnalyze deps BDefs).run
initialize BTree : HolLibrary.BitMatch.Tree ←
  ioB "setupTree" (HolLibrary.BitMatch.setupTree deps BDefs BAnalyze).run
initialize BCases : HolLibrary.BitMatch.Cases ←
  ioB "setupCases" (HolLibrary.BitMatch.setupCases deps BDefs BAnalyze BTree).run
initialize BNumeral : HolLibrary.BitMatch.Numeral ←
  ioB "setupNumeral" (HolLibrary.BitMatch.setupNumeral deps BDefs BAnalyze).run
initialize BConv : HolLibrary.BitMatch.Conv ←
  ioB "setupConv" (HolLibrary.BitMatch.setupConv deps BDefs BAnalyze BCases BNumeral).run
initialize BTactics : HolLibrary.BitMatch.Tactics ←
  ioB "setupTactics"
    (HolLibrary.BitMatch.setupTactics deps BDefs BAnalyze BCases BNumeral BConv).run

-- Defs
def TRIV_CHOOSE := BDefs.TRIV_CHOOSE
def WITH_GOAL := BDefs.WITH_GOAL
def _BITMATCH : thm := BDefs._BITMATCH
def _ELSEPATTERN : thm := BDefs._ELSEPATTERN
def bitpat : thm := BDefs.bitpat
def pat_size : thm := BDefs.pat_size
def pat_set : thm := BDefs.pat_set
def pat_set_lt : thm := BDefs.pat_set_lt
def pat_thm : thm := BDefs.pat_thm
def NILPAT : thm := BDefs.NILPAT
def NILPAT_pat_size : thm := BDefs.NILPAT_pat_size
def NILPAT_pat_set : thm := BDefs.NILPAT_pat_set
def CONSPAT : thm := BDefs.CONSPAT
def CONSPAT_pat_size : thm := BDefs.CONSPAT_pat_size
def CONSPAT_pat_set : thm := BDefs.CONSPAT_pat_set
def word1 : thm := BDefs.word1
def BIT0_WORD1 : thm := BDefs.BIT0_WORD1
def VAL_WORD1 : thm := BDefs.VAL_WORD1
def WORD1_ODD : thm := BDefs.WORD1_ODD

-- Syntax
def preparse_bitpat := BSyntax.preparse_bitpat
def preparse_bitmatch := BSyntax.preparse_bitmatch
def pp_print_bitpat := BSyntax.pp_print_bitpat
def pp_print_colored_bitpat := BSyntax.pp_print_colored_bitpat
def pp_print_bitmatch := BSyntax.pp_print_bitmatch
def pp_print_colored_bitmatch := BSyntax.pp_print_colored_bitmatch
def print_bitpat := BSyntax.print_bitpat
def string_of_bitpat := BSyntax.string_of_bitpat
def print_bitmatch := BSyntax.print_bitmatch
def string_of_bitmatch := BSyntax.string_of_bitmatch

-- Analyze
def dest_word_ty := BAnalyze.dest_word_ty
def SPLIT_IF := BAnalyze.SPLIT_IF
def MATCH_SEQPATTERN : thm := BAnalyze.MATCH_SEQPATTERN
def BITMATCH_SEQPATTERN : thm := BAnalyze.BITMATCH_SEQPATTERN
def BITMATCH_SEQPATTERN2 : thm := BAnalyze.BITMATCH_SEQPATTERN2
def MATCH_ELSEPATTERN : thm := BAnalyze.MATCH_ELSEPATTERN
def BITMATCH_ELSEPATTERN : thm := BAnalyze.BITMATCH_ELSEPATTERN
def pat_extract : thm := BAnalyze.pat_extract
def PAT_EXTRACT_THM := BAnalyze.PAT_EXTRACT_THM
def pat_to_bit := BAnalyze.pat_to_bit
def bm_analyze_pat := BAnalyze.bm_analyze_pat
def bm_analyze_clauses := BAnalyze.bm_analyze_clauses
def bm_skip_clause := BAnalyze.bm_skip_clause

-- Tree
def bm_build_tree' := BTree.bm_build_tree'
def bm_build_tree := BTree.bm_build_tree
def BM_IF_CONV : term → IO (Except String thm) := fun t => (BTree.BM_IF_CONV t).run
def MATCH_EQ : thm := BTree.MATCH_EQ
def bitpat_inverts : thm := BTree.bitpat_inverts
def bitpat_down : thm := BTree.bitpat_down
def CONSPAT_down_inverts : thm := BTree.CONSPAT_down_inverts
def CONSPAT_word_inverts : thm := BTree.CONSPAT_word_inverts
def bitpat_inverts_comp : thm := BTree.bitpat_inverts_comp
def CONSPAT_word1_inverts : thm := BTree.CONSPAT_word1_inverts
def build_inverts := BTree.build_inverts

-- Cases
def BM_FIRST_CASE_CONV : term → IO (Except String thm) := fun t => (BCases.BM_FIRST_CASE_CONV t).run
def bm_add_pos := BCases.bm_add_pos
def bm_build_pos_tree := BCases.bm_build_pos_tree
def BM_CASES := BCases.BM_CASES

-- Numeral
def inst_bitpat_numeral := BNumeral.inst_bitpat_numeral

-- Conv
def BITMATCH_CONV : term → IO (Except String thm) := fun t => (BConv.BITMATCH_CONV t).run
def BITMATCH_SIMP_CONV := BConv.BITMATCH_SIMP_CONV
def bitpat_irrefutable_thm : term → IO (Except String thm) := fun t => (BConv.bitpat_irrefutable_thm t).run

-- Tactics
def ONLY_BITMATCH_CASES_THEN := BTactics.ONLY_BITMATCH_CASES_THEN
def BITMATCH_ASM_CASES_TAC : HolCore.Tactics.tactic := fun g => BTactics.BITMATCH_ASM_CASES_TAC g
def BITMATCH_CASES_TAC : HolCore.Tactics.tactic := fun g => BTactics.BITMATCH_CASES_TAC g
def bm_seq_numeral := BTactics.bm_seq_numeral
def BITMATCH_SEQ_CONV : term → IO (Except String thm) := fun t => (BTactics.BITMATCH_SEQ_CONV t).run
def bm_check_disjointness := BTactics.bm_check_disjointness























/- bitmatch.ml's names that HolLibrary.BitMatch defines at top level (they
   need no bundle). -/
export HolLibrary.BitMatch (discrim_tree map_dt get_dt bitpat_matches bitpat_irrefutable)

/-- `needs "Library/bitmatch.ml"`: already done by importing this module. -/
def ensureBitMatch : IO Unit := pure ()

end SessionLibrary.BitMatch
