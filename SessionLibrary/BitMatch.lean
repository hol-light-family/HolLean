/- ---------------------------------------------------------------------- -/
/- Session wiring for Library/bitmatch.ml.                                -/
/- ---------------------------------------------------------------------- -/
/- File: SessionLibrary/BitMatch.lean

  The `unsafe` half of the bitmatch.ml translation: it supplies
  HolLibrary.BitMatch's dependencies from Session and SessionLibrary.Words,
  builds each bundle once, in file order, and exports every name under its
  HOL Light name.  `ensureBitMatch` is `needs "Library/bitmatch.ml"` (which
  first does `needs "Library/words.ml"`).

  The blocks between `@@CORE` and `@@EXPORTS` markers are generated from
  HolLibrary/BitMatch.lean by tools/bitmatchdiff/gen_session.py and scope.py
  (bookkeeping only: field-by-field copies and accessors).
-/

import Session
import HolLibrary.BitMatch
import SessionLibrary.Words

open HolCore HolCore.Kernel
open HolCore.Equal (ioconv)

namespace SessionLibrary.BitMatch

/-- The core bundles, for HolLibrary's tactics. -/
unsafe instance : HolLight.HolBase := ⟨Session.sessionB, Session.sessionC, Session.sessionT⟩

-- @@CORE BEGIN
/-- The core theorems bitmatch.ml uses. -/
unsafe def core1 (_ : Unit) : HolLibrary.BitMatch.CoreThms1 where
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
unsafe def core2 (_ : Unit) : HolLibrary.BitMatch.CoreThms2 where
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
  numbit := SessionLibrary.Words.«numbit»-- @@CORE END

/-- What bitmatch.ml uses from Session and words.ml. -/
unsafe def deps (_ : Unit) : HolLibrary.BitMatch.BitMatchDeps where
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
  core1 := core1 ()
  core2 := core2 ()

/-- Build a bundle once.  `setup` is a thunk, so that `deps` is not built
    before the bundle is needed.  The whole core library is built first
    (`Session.ensureDefine`, and MATCH_CONV's basic conversions, which HOL
    Light adds loading ind_types.ml), then words.ml, which bitmatch.ml
    needs. -/
private unsafe def cached {α : Type} [Inhabited α] (r : IO.Ref (Option α)) (name : String)
    (setup : Unit → IO (Except String α)) : α :=
  match unsafeIO (do
    match ← r.get with
    | some d => pure d
    | none => do
      Session.ensureDefine
      let _ ← Session.MATCH_CONV (HolCore.Kernel.mk_var "p" HolCore.Kernel.bool_ty)
      SessionLibrary.Words.ensureWords
      match ← setup () with
      | .ok d => do r.set (some d); pure d
      | .error e => panic! s!"{name} failed: {e}") with
  | .ok d => d | _ => panic! s!"SessionLibrary.BitMatch: {name}"

/- The bundles, in bitmatch.ml order.  Each forces the one before it, so
   that any bundle builds every earlier one first, as HOL Light's load does. -/

-- @@BUNDLES BEGIN
initialize theDefs : IO.Ref (Option HolLibrary.BitMatch.Defs) ← IO.mkRef none
unsafe def BDefs : HolLibrary.BitMatch.Defs :=
  cached theDefs "setupDefs" fun _ => do
    (HolLibrary.BitMatch.setupDefs (deps ())).run

initialize theSyntax : IO.Ref (Option HolLibrary.BitMatch.Syntax) ← IO.mkRef none
unsafe def BSyntax : HolLibrary.BitMatch.Syntax :=
  cached theSyntax "setupSyntax" fun _ => do
    let _ ← IO.mkRef BDefs.TRIV_CHOOSE
    (HolLibrary.BitMatch.setupSyntax (deps ())).run

initialize theAnalyze : IO.Ref (Option HolLibrary.BitMatch.Analyze) ← IO.mkRef none
unsafe def BAnalyze : HolLibrary.BitMatch.Analyze :=
  cached theAnalyze "setupAnalyze" fun _ => do
    let _ ← IO.mkRef BSyntax.preparse_bitpat
    (HolLibrary.BitMatch.setupAnalyze (deps ()) BDefs).run

initialize theTree : IO.Ref (Option HolLibrary.BitMatch.Tree) ← IO.mkRef none
unsafe def BTree : HolLibrary.BitMatch.Tree :=
  cached theTree "setupTree" fun _ => do
    let _ ← IO.mkRef BAnalyze.dest_word_ty
    (HolLibrary.BitMatch.setupTree (deps ()) BDefs BAnalyze).run

initialize theCases : IO.Ref (Option HolLibrary.BitMatch.Cases) ← IO.mkRef none
unsafe def BCases : HolLibrary.BitMatch.Cases :=
  cached theCases "setupCases" fun _ => do
    let _ ← IO.mkRef BTree.bm_build_tree'
    (HolLibrary.BitMatch.setupCases (deps ()) BDefs BAnalyze BTree).run

initialize theNumeral : IO.Ref (Option HolLibrary.BitMatch.Numeral) ← IO.mkRef none
unsafe def BNumeral : HolLibrary.BitMatch.Numeral :=
  cached theNumeral "setupNumeral" fun _ => do
    let _ ← IO.mkRef BCases.BM_FIRST_CASE_CONV
    (HolLibrary.BitMatch.setupNumeral (deps ()) BDefs BAnalyze).run

initialize theConv : IO.Ref (Option HolLibrary.BitMatch.Conv) ← IO.mkRef none
unsafe def BConv : HolLibrary.BitMatch.Conv :=
  cached theConv "setupConv" fun _ => do
    let _ ← IO.mkRef BNumeral.inst_bitpat_numeral
    (HolLibrary.BitMatch.setupConv (deps ()) BDefs BAnalyze BCases BNumeral).run

initialize theTactics : IO.Ref (Option HolLibrary.BitMatch.Tactics) ← IO.mkRef none
unsafe def BTactics : HolLibrary.BitMatch.Tactics :=
  cached theTactics "setupTactics" fun _ => do
    let _ ← IO.mkRef BConv.BITMATCH_CONV
    (HolLibrary.BitMatch.setupTactics (deps ()) BDefs BAnalyze BCases BNumeral BConv).run

-- @@BUNDLES END

-- @@EXPORTS BEGIN
-- Defs
unsafe def TRIV_CHOOSE := BDefs.TRIV_CHOOSE
unsafe def WITH_GOAL := BDefs.WITH_GOAL
unsafe def _BITMATCH : thm := BDefs._BITMATCH
unsafe def _ELSEPATTERN : thm := BDefs._ELSEPATTERN
unsafe def bitpat : thm := BDefs.bitpat
unsafe def pat_size : thm := BDefs.pat_size
unsafe def pat_set : thm := BDefs.pat_set
unsafe def pat_set_lt : thm := BDefs.pat_set_lt
unsafe def pat_thm : thm := BDefs.pat_thm
unsafe def NILPAT : thm := BDefs.NILPAT
unsafe def NILPAT_pat_size : thm := BDefs.NILPAT_pat_size
unsafe def NILPAT_pat_set : thm := BDefs.NILPAT_pat_set
unsafe def CONSPAT : thm := BDefs.CONSPAT
unsafe def CONSPAT_pat_size : thm := BDefs.CONSPAT_pat_size
unsafe def CONSPAT_pat_set : thm := BDefs.CONSPAT_pat_set
unsafe def word1 : thm := BDefs.word1
unsafe def BIT0_WORD1 : thm := BDefs.BIT0_WORD1
unsafe def VAL_WORD1 : thm := BDefs.VAL_WORD1
unsafe def WORD1_ODD : thm := BDefs.WORD1_ODD

-- Syntax
unsafe def preparse_bitpat := BSyntax.preparse_bitpat
unsafe def preparse_bitmatch := BSyntax.preparse_bitmatch
unsafe def pp_print_bitpat := BSyntax.pp_print_bitpat
unsafe def pp_print_colored_bitpat := BSyntax.pp_print_colored_bitpat
unsafe def pp_print_bitmatch := BSyntax.pp_print_bitmatch
unsafe def pp_print_colored_bitmatch := BSyntax.pp_print_colored_bitmatch
unsafe def print_bitpat := BSyntax.print_bitpat
unsafe def string_of_bitpat := BSyntax.string_of_bitpat
unsafe def print_bitmatch := BSyntax.print_bitmatch
unsafe def string_of_bitmatch := BSyntax.string_of_bitmatch

-- Analyze
unsafe def dest_word_ty := BAnalyze.dest_word_ty
unsafe def SPLIT_IF := BAnalyze.SPLIT_IF
unsafe def MATCH_SEQPATTERN : thm := BAnalyze.MATCH_SEQPATTERN
unsafe def BITMATCH_SEQPATTERN : thm := BAnalyze.BITMATCH_SEQPATTERN
unsafe def BITMATCH_SEQPATTERN2 : thm := BAnalyze.BITMATCH_SEQPATTERN2
unsafe def MATCH_ELSEPATTERN : thm := BAnalyze.MATCH_ELSEPATTERN
unsafe def BITMATCH_ELSEPATTERN : thm := BAnalyze.BITMATCH_ELSEPATTERN
unsafe def pat_extract : thm := BAnalyze.pat_extract
unsafe def PAT_EXTRACT_THM := BAnalyze.PAT_EXTRACT_THM
unsafe def pat_to_bit := BAnalyze.pat_to_bit
unsafe def bm_analyze_pat := BAnalyze.bm_analyze_pat
unsafe def bm_analyze_clauses := BAnalyze.bm_analyze_clauses
unsafe def bm_skip_clause := BAnalyze.bm_skip_clause

-- Tree
unsafe def bm_build_tree' := BTree.bm_build_tree'
unsafe def bm_build_tree := BTree.bm_build_tree
unsafe def BM_IF_CONV : term → IO (Except String thm) := fun t => (BTree.BM_IF_CONV t).run
unsafe def MATCH_EQ : thm := BTree.MATCH_EQ
unsafe def bitpat_inverts : thm := BTree.bitpat_inverts
unsafe def bitpat_down : thm := BTree.bitpat_down
unsafe def CONSPAT_down_inverts : thm := BTree.CONSPAT_down_inverts
unsafe def CONSPAT_word_inverts : thm := BTree.CONSPAT_word_inverts
unsafe def bitpat_inverts_comp : thm := BTree.bitpat_inverts_comp
unsafe def CONSPAT_word1_inverts : thm := BTree.CONSPAT_word1_inverts
unsafe def build_inverts := BTree.build_inverts

-- Cases
unsafe def BM_FIRST_CASE_CONV : term → IO (Except String thm) := fun t => (BCases.BM_FIRST_CASE_CONV t).run
unsafe def bm_add_pos := BCases.bm_add_pos
unsafe def bm_build_pos_tree := BCases.bm_build_pos_tree
unsafe def BM_CASES := BCases.BM_CASES

-- Numeral
unsafe def inst_bitpat_numeral := BNumeral.inst_bitpat_numeral

-- Conv
unsafe def BITMATCH_CONV : term → IO (Except String thm) := fun t => (BConv.BITMATCH_CONV t).run
unsafe def BITMATCH_SIMP_CONV := BConv.BITMATCH_SIMP_CONV
unsafe def bitpat_irrefutable_thm : term → IO (Except String thm) := fun t => (BConv.bitpat_irrefutable_thm t).run

-- Tactics
unsafe def ONLY_BITMATCH_CASES_THEN := BTactics.ONLY_BITMATCH_CASES_THEN
unsafe def BITMATCH_ASM_CASES_TAC : HolCore.Tactics.tactic := fun g => BTactics.BITMATCH_ASM_CASES_TAC g
unsafe def BITMATCH_CASES_TAC : HolCore.Tactics.tactic := fun g => BTactics.BITMATCH_CASES_TAC g
unsafe def bm_seq_numeral := BTactics.bm_seq_numeral
unsafe def BITMATCH_SEQ_CONV : term → IO (Except String thm) := fun t => (BTactics.BITMATCH_SEQ_CONV t).run
unsafe def bm_check_disjointness := BTactics.bm_check_disjointness






















-- @@EXPORTS END

/- bitmatch.ml's names that HolLibrary.BitMatch defines at top level (they
   need no bundle). -/
export HolLibrary.BitMatch (discrim_tree map_dt get_dt bitpat_matches bitpat_irrefutable)

/-- `needs "Library/bitmatch.ml"`: build every bundle, in file order. -/
unsafe def ensureBitMatch : IO Unit := do
  -- @@ENSURE BEGIN
  let _ ← IO.mkRef BDefs._BITMATCH
  let _ ← IO.mkRef BSyntax.preparse_bitpat
  let _ ← IO.mkRef BAnalyze.MATCH_SEQPATTERN
  let _ ← IO.mkRef BTree.MATCH_EQ
  let _ ← IO.mkRef BCases.BM_FIRST_CASE_CONV
  let _ ← IO.mkRef BNumeral.inst_bitpat_numeral
  let _ ← IO.mkRef BConv.BITMATCH_CONV
  let _ ← IO.mkRef BTactics.ONLY_BITMATCH_CASES_THEN  -- @@ENSURE END
  pure ()

end SessionLibrary.BitMatch
